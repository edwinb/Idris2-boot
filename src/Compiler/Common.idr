module Compiler.Common

import Compiler.CompileExpr
import Compiler.Inline
import Compiler.LambdaLift

import Core.Context
import Core.Directory
import Core.Options
import Core.TT
import Utils.Binary

import Data.IOArray
import Data.NameMap

import System.Info

%include C "sys/stat.h"

||| Generic interface to some code generator
public export
record Codegen where
  constructor MkCG
  ||| Compile an Idris 2 expression, saving it to a file.
  compileExpr : Ref Ctxt Defs -> (execDir : String) ->
                ClosedTerm -> (outfile : String) -> Core (Maybe String)
  ||| Execute an Idris 2 expression directly.
  executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()

||| compile
||| Given a value of type Codegen, produce a standalone function
||| that executes the `compileExpr` method of the Codegen
export
compile : {auto c : Ref Ctxt Defs} ->
          Codegen ->
          ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile {c} cg tm out
    = do makeExecDirectory
         d <- getDirs
         compileExpr cg c (exec_dir d) tm out

||| execute
||| As with `compile`, produce a functon that executes
||| the `executeExpr` method of the given Codegen
export
execute : {auto c : Ref Ctxt Defs} ->
          Codegen -> ClosedTerm -> Core ()
execute {c} cg tm
    = do makeExecDirectory
         d <- getDirs
         executeExpr cg c (exec_dir d) tm
         pure ()

-- ||| Recursively get all calls in a function definition
getAllDesc : {auto c : Ref Ctxt Defs} ->
             List Name -> -- calls to check
             IOArray Int -> -- which nodes have been visited. If the entry is
                            -- present, it's visited
             Defs -> Core ()
getAllDesc [] arr defs = pure ()
getAllDesc (n@(Resolved i) :: rest) arr defs
  = do Nothing <- coreLift $ readArray arr i
           | Just _ => getAllDesc rest arr defs
       case !(lookupCtxtExact n (gamma defs)) of
            Nothing => getAllDesc rest arr defs
            Just def =>
              do coreLift $ writeArray arr i i
                 let refs = refersToRuntime def
                 getAllDesc (keys refs ++ rest) arr defs
getAllDesc (n :: rest) arr defs
  = getAllDesc rest arr defs

-- Calculate a unique tag for each type constructor name we're compiling
-- This is so that type constructor names get globally unique tags
mkNameTags : Defs -> NameTags -> Int -> List Name -> Core NameTags
mkNameTags defs tags t [] = pure tags
mkNameTags defs tags t (n :: ns)
    = case !(lookupDefExact n (gamma defs)) of
           Just (TCon _ _ _ _ _ _ _ _)
              => mkNameTags defs (insert n t tags) (t + 1) ns
           _ => mkNameTags defs tags t ns

natHackNames : List Name
natHackNames
    = [UN "prim__add_Integer",
       UN "prim__sub_Integer",
       UN "prim__mul_Integer",
       NS ["Prelude"] (UN "natToInteger"),
       NS ["Prelude"] (UN "integerToNat")]

export
fastAppend : List String -> String
fastAppend xs
    = let len = cast (foldr (+) 0 (map length xs)) in
          unsafePerformIO $
             do b <- newStringBuffer (len+1)
                build b xs
                getStringFromBuffer b
  where
    build : StringBuffer -> List String -> IO ()
    build b [] = pure ()
    build b (x :: xs) = do addToStringBuffer b x
                           build b xs

dumpCases : Defs -> String -> List Name ->
            Core ()
dumpCases defs fn cns
    = do cstrs <- traverse dumpCase cns
         Right () <- coreLift $ writeFile fn (fastAppend cstrs)
               | Left err => throw (FileErr fn err)
         pure ()
  where
    fullShow : Name -> String
    fullShow (DN _ n) = show n
    fullShow n = show n

    dumpCase : Name -> Core String
    dumpCase n
        = case !(lookupCtxtExact n (gamma defs)) of
               Nothing => pure ""
               Just d =>
                    case namedcompexpr d of
                         Nothing => pure ""
                         Just def => pure (fullShow n ++ " = " ++ show def ++ "\n")

dumpLifted : String -> List (Name, LiftedDef) -> Core ()
dumpLifted fn lns
    = do let cstrs = map dumpDef lns
         Right () <- coreLift $ writeFile fn (fastAppend cstrs)
               | Left err => throw (FileErr fn err)
         pure ()
  where
    fullShow : Name -> String
    fullShow (DN _ n) = show n
    fullShow n = show n

    dumpDef : (Name, LiftedDef) -> String
    dumpDef (n, d) = fullShow n ++ " = " ++ show d ++ "\n"

public export
record CompileData where
  constructor MkCompileData
  allNames : List Name -- names which need to be compiled
  nameTags : NameTags -- a mapping from type names to constructor tags
  mainExpr : CExp [] -- main expression to execute
  lambdaLifted : List (Name, LiftedDef)
       -- ^ lambda lifted definitions, if required. Only the top level names
       -- will be in the context, and (for the moment...) I don't expect to
       -- need to look anything up, so it's just an alist.

-- Find all the names which need compiling, from a given expression, and compile
-- them to CExp form (and update that in the Defs).
-- Return the names, the type tags, and a compiled version of the expression
export
getCompileData : {auto c : Ref Ctxt Defs} ->
                 ClosedTerm -> Core CompileData
getCompileData tm
    = do defs <- get Ctxt
         sopts <- getSession
         let ns = getRefs (Resolved (-1)) tm
         natHackNames' <- traverse toResolvedNames natHackNames
         -- make an array of Bools to hold which names we've found (quicker
         -- to check than a NameMap!)
         asize <- getNextEntry
         arr <- coreLift $ newArray asize
         logTime "Get names" $ getAllDesc (natHackNames' ++ keys ns) arr defs
         let allNs = mapMaybe (maybe Nothing (Just . Resolved))
                              !(coreLift (toList arr))
         cns <- traverse toFullNames allNs
         -- Initialise the type constructor list with explicit names for
         -- the primitives (this is how we look up the tags)
         -- Use '1' for '->' constructor
         let tyconInit = insert (UN "->") 1 $
                         insert (UN "Type") 2 $
                            primTags 3 empty
                                     [IntType, IntegerType, StringType,
                                      CharType, DoubleType, WorldType]
         tycontags <- mkNameTags defs tyconInit 100 cns
         logTime ("Compile defs " ++ show (length cns) ++ "/" ++ show asize) $
           traverse_ (compileDef tycontags) cns
         logTime "Inline" $ traverse_ inlineDef cns
         logTime "Merge lambda" $ traverse_ mergeLamDef cns
         logTime "Fix arity" $ traverse_ fixArityDef cns
         logTime "Forget names" $ traverse_ mkForgetDef cns

         lifted <- logTime "Lambda lift" $ traverse lambdaLift cns

         compiledtm <- fixArityExp !(compileExp tycontags tm)

         defs <- get Ctxt
         maybe (pure ())
               (\f => do coreLift $ putStrLn $ "Dumping case trees to " ++ f
                         dumpCases defs f cns)
               (dumpcases sopts)
         maybe (pure ())
               (\f => do coreLift $ putStrLn $ "Dumping lambda lifted defs to " ++ f
                         dumpLifted f (concat lifted))
               (dumplifted sopts)
         pure (MkCompileData cns tycontags compiledtm (concat lifted))
  where
    primTags : Int -> NameTags -> List Constant -> NameTags
    primTags t tags [] = tags
    primTags t tags (c :: cs)
        = primTags (t + 1) (insert (UN (show c)) t tags) cs

-- Some things missing from Prelude.File

||| check to see if a given file exists
export
exists : String -> IO Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

||| generate a temporary file/name
export
tmpName : IO String
tmpName = foreign FFI_C "tmpnam" (Ptr -> IO String) null

||| change the access rights for a file
export
chmod : String -> Int -> IO ()
chmod f m = foreign FFI_C "chmod" (String -> Int -> IO ()) f m

-- Parse a calling convention into a backend/target for the call, and
-- a comma separated list of any other location data.
-- e.g. "scheme:display" - call the scheme function 'display'
--      "C:puts,libc,stdio.h" - call the C function 'puts' which is in
--      the library libc and the header stdio.h
-- Returns Nothing if the string is empty (which a backend can interpret
-- however it likes)
export
parseCC : String -> Maybe (String, List String)
parseCC "" = Nothing
parseCC str
    = case span (/= ':') str of
           (target, "") => Just (trim target, [])
           (target, opts) => Just (trim target,
                                   map trim (getOpts
                                       (assert_total (strTail opts))))
  where
    getOpts : String -> List String
    getOpts "" = []
    getOpts str
        = case span (/= ',') str of
               (opt, "") => [opt]
               (opt, rest) => opt :: getOpts (assert_total (strTail rest))

export
dylib_suffix : String
dylib_suffix
    = cond [(os `elem` ["windows", "mingw32", "cygwin32"], "dll"),
            (os == "darwin", "dylib")]
           "so"

export
locate : {auto c : Ref Ctxt Defs} ->
         String -> Core (String, String)
locate libspec
    = do -- Attempt to turn libspec into an appropriate filename for the system
         let fname
              = case words libspec of
                     [] => ""
                     [fn] => if '.' `elem` unpack fn
                                then fn -- full filename given
                                else -- add system extension
                                     fn ++ "." ++ dylib_suffix
                     (fn :: ver :: _) =>
                          -- library and version given, build path name as
                          -- appropriate for the system
                          cond [(dylib_suffix == "dll",
                                      fn ++ "-" ++ ver ++ ".dll"),
                                (dylib_suffix == "dylib",
                                      fn ++ "." ++ ver ++ ".dylib")]
                                (fn ++ "." ++ dylib_suffix ++ "." ++ ver)

         fullname <- catch (findLibraryFile fname)
                           (\err => -- assume a system library so not
                                    -- in our library path
                                    pure fname)
         pure (fname, fullname)

export
copyLib : (String, String) -> Core ()
copyLib (lib, fullname)
    = if lib == fullname
         then pure ()
         else do Right bin <- coreLift $ readFromFile fullname
                    | Left err => throw (FileErr fullname err)
                 Right _ <- coreLift $ writeToFile lib bin
                    | Left err => throw (FileErr lib err)
                 pure ()
