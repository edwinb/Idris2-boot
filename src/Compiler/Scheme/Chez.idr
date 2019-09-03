module Compiler.Scheme.Chez

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.NameMap
import Data.Vect
import System
import System.Info

%default covering

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

findChez : IO String
findChez
    = do env <- getEnv "CHEZ"
         case env of
            Just n => pure n
            Nothing => do e <- firstExists [p ++ x | p <- ["/usr/bin/", "/usr/local/bin/"],
                                    x <- ["scheme", "chez", "chezscheme9.5"]]
                          maybe (pure "/usr/bin/env scheme") pure e

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

-- Given the chez compiler directives, return a list of pairs of:
--   - the library file name
--   - the full absolute path of the library file name, if it's in one
--     of the library paths managed by Idris
-- If it can't be found, we'll assume it's a system library and that chez
-- will thus be able to find it.
findLibs : {auto c : Ref Ctxt Defs} ->
           List String -> Core (List (String, String))
findLibs ds
    = do let libs = mapMaybe (isLib . trim) ds
         traverse locate (nub libs)
  where
    isLib : String -> Maybe String
    isLib d
        = if isPrefixOf "lib" d
             then Just (trim (substr 3 (length d) d))
             else Nothing

escapeQuotes : String -> String
escapeQuotes s = pack $ foldr escape [] $ unpack s
  where
    escape : Char -> List Char -> List Char
    escape '"' cs = '\\' :: '\"' :: cs
    escape c   cs = c :: cs

schHeader : String -> List String -> String
schHeader chez libs
  = (if os /= "windows" then "#!" ++ chez ++ " --script\n\n" else "") ++
    "(import (chezscheme))\n" ++
    "(case (machine-type)\n" ++
    "  [(i3le ti3le a6le ta6le) (load-shared-object \"libc.so.6\")]\n" ++
    "  [(i3osx ti3osx a6osx ta6osx) (load-shared-object \"libc.dylib\")]\n" ++
    "  [(i3nt ti3nt a6nt ta6nt) (load-shared-object \"msvcrt.dll\")]\n" ++
    "  [else (load-shared-object \"libc.so\")])\n\n" ++
    showSep "\n" (map (\x => "(load-shared-object \"" ++ escapeQuotes x ++ "\")") libs) ++ "\n\n" ++
    "(let ()\n"

schFooter : String
schFooter = ")"

mutual
  tySpec : CExp vars -> Core String
  -- Primitive types have been converted to names for the purpose of matching
  -- on types
  tySpec (CCon fc (UN "Int") _ []) = pure "int"
  tySpec (CCon fc (UN "String") _ []) = pure "string"
  tySpec (CCon fc (UN "Double") _ []) = pure "double"
  tySpec (CCon fc (UN "Char") _ []) = pure "char"
  tySpec (CCon fc (NS _ n) _ [])
     = cond [(n == UN "Unit", pure "void"),
             (n == UN "Ptr", pure "void*")]
          (throw (GenericMsg fc ("Can't pass argument of type " ++ show n ++ " to foreign function")))
  tySpec ty = throw (GenericMsg (getFC ty) ("Can't pass argument of type " ++ show ty ++ " to foreign function"))

  handleRet : String -> String -> String
  handleRet "void" op = op ++ " " ++ mkWorld (schConstructor 0 [])
  handleRet _ op = mkWorld op

  getFArgs : CExp vars -> Core (List (CExp vars, CExp vars))
  getFArgs (CCon fc _ 0 _) = pure []
  getFArgs (CCon fc _ 1 [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
  getFArgs arg = throw (GenericMsg (getFC arg) ("Badly formed c call argument list " ++ show arg))

  chezExtPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  chezExtPrim i vs CCall [ret, CPrimVal fc (Str fn), fargs, world]
      = do args <- getFArgs fargs
           argTypes <- traverse tySpec (map fst args)
           retType <- tySpec ret
           argsc <- traverse (schExp chezExtPrim 0 vs) (map snd args)
           pure $ handleRet retType ("((foreign-procedure #f " ++ show fn ++ " ("
                    ++ showSep " " argTypes ++ ") " ++ retType ++ ") "
                    ++ showSep " " argsc ++ ")")
  chezExtPrim i vs CCall [ret, fn, args, world]
      = pure "(error \"bad ffi call\")"
      -- throw (InternalError ("C FFI calls must be to statically known functions (" ++ show fn ++ ")"))
  chezExtPrim i vs GetStr [world]
      = pure $ mkWorld "(get-line (current-input-port))"
  chezExtPrim i vs prim args
      = schExtCommon chezExtPrim i vs prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

cftySpec : FC -> CFType -> Core String
cftySpec fc CFUnit = pure "void"
cftySpec fc CFInt = pure "int"
cftySpec fc CFString = pure "string"
cftySpec fc CFDouble = pure "double"
cftySpec fc CFChar = pure "char"
cftySpec fc CFPtr = pure "void*"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))

cCall : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> (cfn : String) -> (clib : String) ->
        List (Name, CFType) -> CFType -> Core (String, String)
cCall fc cfn clib args ret
    = do loaded <- get Loaded
         lib <- if clib `elem` loaded
                   then pure ""
                   else do (fname, fullname) <- locate clib
                           put Loaded (clib :: loaded)
                           pure $ "(load-shared-object \"" 
                                    ++ escapeQuotes fullname
                                    ++ "\")\n"
         argTypes <- traverse (\a => do s <- cftySpec fc (snd a)
                                        pure (fst a, s)) args
         retType <- cftySpec fc ret
         let call = "((foreign-procedure #f " ++ show cfn ++ " ("
                      ++ showSep " " (map snd argTypes) ++ ") " ++ retType ++ ") "
                      ++ showSep " " (map (schName . fst) argTypes) ++ ")"

         pure (lib, case ret of
                         CFIORes _ => handleRet retType call
                         _ => call)

schemeCall : FC -> (sfn : String) ->
             List Name -> CFType -> Core String
schemeCall fc sfn argns ret
    = let call = "(" ++ sfn ++ " " ++ showSep " " (map schName argns) ++ ")" in
          case ret of
               CFIORes _ => pure $ mkWorld call
               _ => pure call

-- Use a calling convention to compile a foreign def.
-- Returns any preamble needed for loading libraries, and the body of the
-- function call.
useCC : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> List String -> List (Name, CFType) -> CFType -> Core (String, String)
useCC fc [] args ret
    = throw (GenericMsg fc "No recognised foreign calling convention")
useCC fc (cc :: ccs) args ret
    = case parseCC cc of
           Nothing => useCC fc ccs args ret
           Just ("scheme", [sfn]) => 
               do body <- schemeCall fc sfn (map fst args) ret
                  pure ("", body)
           Just ("C", [cfn, clib]) => cCall fc cfn clib args ret
           Just ("C", [cfn, clib, chdr]) => cCall fc cfn clib args ret
           _ => useCC fc ccs args ret

-- For every foreign arg type, return a name, and whether to pass it to the
-- foreign call (we don't pass '%World')
mkArgs : Int -> List CFType -> List (Name, Bool)
mkArgs i [] = []
mkArgs i (CFWorld :: cs) = (MN "farg" i, False) :: mkArgs i cs
mkArgs i (c :: cs) = (MN "farg" i, True) :: mkArgs (i + 1) cs

schFgnDef : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref Loaded (List String)} ->
            FC -> Name -> CDef -> Core (String, String)
schFgnDef fc n (MkForeign cs args ret) 
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         (load, body) <- useCC fc cs (zip useargns args) ret
         defs <- get Ctxt
         pure (load,
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ showSep " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ = pure ("", "")

getFgnCall : {auto c : Ref Ctxt Defs} ->
             {auto l : Ref Loaded (List String)} ->
             Name -> Core (String, String)
getFgnCall n
    = do defs <- get Ctxt
         case !(lookupCtxtExact n (gamma defs)) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just def => case compexpr def of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => schFgnDef (location def) n d

||| Compile a TT expression to Chez Scheme
compileToSS : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core ()
compileToSS c tm outfile
    = do ds <- getDirectives Chez
         libs <- findLibs ds
         (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         l <- newRef {t = List String} Loaded ["libc", "libc 6"]
         fgndefs <- traverse getFgnCall ns
         compdefs <- traverse (getScheme chezExtPrim defs) ns
         let code = concat (map snd fgndefs) ++ concat compdefs
         main <- schExp chezExtPrim 0 [] !(compileExp tags tm)
         chez <- coreLift findChez
         support <- readDataFile "chez/support.ss"
         let scm = schHeader chez (map snd libs) ++ 
                   support ++ code ++ 
                   concat (map fst fgndefs) ++
                   main ++ schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

||| Compile a Chez Scheme source file to an executable, daringly with runtime checks off.
compileToSO : (ssFile : String) -> Core ()
compileToSO ssFile
    = do tmpFile <- coreLift $ tmpName
         chez <- coreLift $ findChez
         let build= "#!" ++ chez ++ " --script\n" ++
                    "(parameterize ([optimize-level 3]) (compile-program \"" ++
                    ssFile ++ "\"))"
         Right () <- coreLift $ writeFile tmpFile build
            | Left err => throw (FileErr tmpFile err)
         coreLift $ chmod tmpFile 0o755
         coreLift $ system tmpFile
         pure ()

||| Chez Scheme implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tm outfile
    = do let outSs = outfile ++ ".ss"
         compileToSS c tm outSs
         compileToSO outSs
         pure (Just (outfile ++ ".so"))

||| Chez Scheme implementation of the `executeExpr` interface.
||| This implementation simply runs the usual compiler, saving it to a temp file, then interpreting it.
executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core ()
executeExpr c tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".ss"
         compileToSS c tm outn
         chez <- coreLift findChez
         coreLift $ system outn
         pure ()

||| Codegen wrapper for Chez scheme implementation.
export
codegenChez : Codegen
codegenChez = MkCG compileExpr executeExpr

