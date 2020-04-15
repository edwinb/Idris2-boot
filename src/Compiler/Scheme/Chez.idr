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
import Utils.Hex

import Data.NameMap
import Data.Vect
import System
import System.Info

%default covering


pathLookup : IO String
pathLookup
    = do path <- getEnv "PATH"
         let pathList = split (== ':') $ fromMaybe "/usr/bin:/usr/local/bin" path
         let candidates = [p ++ "/" ++ x | p <- pathList,
                                           x <- ["chez", "chezscheme9.5", "scheme"]]
         e <- firstExists candidates
         pure $ fromMaybe "/usr/bin/env scheme" e

findChez : IO String
findChez
    = do Just chez <- getEnv "CHEZ" | Nothing => pathLookup
         pure chez

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

showChezChar : Char -> String -> String
showChezChar '\\' = ("\\\\" ++)
showChezChar c
   = if c < chr 32 || c > chr 126
        then (("\\x" ++ asHex (cast c) ++ ";") ++)
        else strCons c

showChezString : List Char -> String -> String
showChezString [] = id
showChezString ('"'::cs) = ("\\\"" ++) . showChezString cs
showChezString (c ::cs) = (showChezChar c) . showChezString cs

chezString : String -> String
chezString cs = strCons '"' (showChezString (unpack cs) "\"")

mutual
  tySpec : NamedCExp -> Core String
  -- Primitive types have been converted to names for the purpose of matching
  -- on types
  tySpec (NmCon fc (UN "Int") _ []) = pure "int"
  tySpec (NmCon fc (UN "String") _ []) = pure "string"
  tySpec (NmCon fc (UN "Double") _ []) = pure "double"
  tySpec (NmCon fc (UN "Char") _ []) = pure "char"
  tySpec (NmCon fc (NS _ n) _ [_])
     = cond [(n == UN "Ptr", pure "void*")]
          (throw (GenericMsg fc ("Can't pass argument of type " ++ show n ++ " to foreign function")))
  tySpec (NmCon fc (NS _ n) _ [])
     = cond [(n == UN "Unit", pure "void"),
             (n == UN "AnyPtr", pure "void*")]
          (throw (GenericMsg fc ("Can't pass argument of type " ++ show n ++ " to foreign function")))
  tySpec ty = throw (GenericMsg (getFC ty) ("Can't pass argument of type " ++ show ty ++ " to foreign function"))

  handleRet : String -> String -> String
  handleRet "void" op = op ++ " " ++ mkWorld (schConstructor 0 [])
  handleRet _ op = mkWorld op

  getFArgs : NamedCExp -> Core (List (NamedCExp, NamedCExp))
  getFArgs (NmCon fc _ 0 _) = pure []
  getFArgs (NmCon fc _ 1 [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
  getFArgs arg = throw (GenericMsg (getFC arg) ("Badly formed c call argument list " ++ show arg))

  chezExtPrim : Int -> ExtPrim -> List NamedCExp -> Core String
  chezExtPrim i CCall [ret, NmPrimVal fc (Str fn), fargs, world]
      = do args <- getFArgs fargs
           argTypes <- traverse tySpec (map fst args)
           retType <- tySpec ret
           argsc <- traverse (schExp chezExtPrim chezString 0) (map snd args)
           pure $ handleRet retType ("((foreign-procedure #f " ++ show fn ++ " ("
                    ++ showSep " " argTypes ++ ") " ++ retType ++ ") "
                    ++ showSep " " argsc ++ ")")
  chezExtPrim i CCall [ret, fn, args, world]
      = pure "(error \"bad ffi call\")"
      -- throw (InternalError ("C FFI calls must be to statically known functions (" ++ show fn ++ ")"))
  chezExtPrim i GetStr [world]
      = pure $ mkWorld "(get-line (current-input-port))"
  chezExtPrim i GetField [NmPrimVal _ (Str s), _, _, struct,
                             NmPrimVal _ (Str fld), _]
      = do structsc <- schExp chezExtPrim chezString 0 struct
           pure $ "(ftype-ref " ++ s ++ " (" ++ fld ++ ") " ++ structsc ++ ")"
  chezExtPrim i GetField [_,_,_,_,_,_]
      = pure "(error \"bad setField\")"
  chezExtPrim i SetField [NmPrimVal _ (Str s), _, _, struct,
                             NmPrimVal _ (Str fld), _, val, world]
      = do structsc <- schExp chezExtPrim chezString 0 struct
           valsc <- schExp chezExtPrim chezString 0 val
           pure $ mkWorld $
              "(ftype-set! " ++ s ++ " (" ++ fld ++ ") " ++ structsc ++
              " " ++ valsc ++ ")"
  chezExtPrim i SetField [_,_,_,_,_,_,_,_]
      = pure "(error \"bad setField\")"
  chezExtPrim i SysCodegen []
      = pure $ "\"chez\""
  chezExtPrim i prim args
      = schExtCommon chezExtPrim chezString i prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

-- Label for noting which struct types are declared
data Structs : Type where

cftySpec : FC -> CFType -> Core String
cftySpec fc CFUnit = pure "void"
cftySpec fc CFInt = pure "int"
cftySpec fc CFString = pure "string"
cftySpec fc CFDouble = pure "double"
cftySpec fc CFChar = pure "char"
cftySpec fc CFPtr = pure "void*"
cftySpec fc (CFFun s t) = pure "void*"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ "(* " ++ n ++ ")"
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
                           copyLib (fname, fullname)
                           put Loaded (clib :: loaded)
                           pure $ "(load-shared-object \""
                                    ++ escapeQuotes fname
                                    ++ "\")\n"
         argTypes <- traverse (\a => cftySpec fc (snd a)) args
         retType <- cftySpec fc ret
         let call = "((foreign-procedure #f " ++ show cfn ++ " ("
                      ++ showSep " " argTypes ++ ") " ++ retType ++ ") "
                      ++ showSep " " !(traverse buildArg args) ++ ")"

         pure (lib, case ret of
                         CFIORes _ => handleRet retType call
                         _ => call)
  where
    mkNs : Int -> List CFType -> List (Maybe String)
    mkNs i [] = []
    mkNs i (CFWorld :: xs) = Nothing :: mkNs i xs
    mkNs i (x :: xs) = Just ("cb" ++ show i) :: mkNs (i + 1) xs

    applyLams : String -> List (Maybe String) -> String
    applyLams n [] = n
    applyLams n (Nothing :: as) = applyLams ("(" ++ n ++ " #f)") as
    applyLams n (Just a :: as) = applyLams ("(" ++ n ++ " " ++ a ++ ")") as

    mkFun : List CFType -> CFType -> String -> String
    mkFun args ret n
        = let argns = mkNs 0 args in
              "(lambda (" ++ showSep " " (mapMaybe id argns) ++ ") " ++
              (applyLams n argns ++ ")")

    notWorld : CFType -> Bool
    notWorld CFWorld = False
    notWorld _ = True

    callback : String -> List CFType -> CFType -> Core String
    callback n args (CFFun s t) = callback n (s :: args) t
    callback n args_rev retty
        = do let args = reverse args_rev
             argTypes <- traverse (cftySpec fc) (filter notWorld args)
             retType <- cftySpec fc retty
             pure $
                 "(let ([c-code (foreign-callable #f " ++
                       mkFun args retty n ++
                       " (" ++ showSep " " argTypes ++ ") " ++ retType ++ ")])" ++
                       " (lock-object c-code) (foreign-callable-entry-point c-code))"

    buildArg : (Name, CFType) -> Core String
    buildArg (n, CFFun s t) = callback (schName n) [s] t
    buildArg (n, _) = pure $ schName n

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

mkStruct : {auto s : Ref Structs (List String)} ->
           CFType -> Core String
mkStruct (CFStruct n flds)
    = do defs <- traverse mkStruct (map snd flds)
         strs <- get Structs
         if n `elem` strs
            then pure (concat defs)
            else do put Structs (n :: strs)
                    pure $ concat defs ++ "(define-ftype " ++ n ++ " (struct\n\t"
                           ++ showSep "\n\t" !(traverse showFld flds) ++ "))\n"
  where
    showFld : (String, CFType) -> Core String
    showFld (n, ty) = pure $ "[" ++ n ++ " " ++ !(cftySpec emptyFC ty) ++ "]"
mkStruct (CFIORes t) = mkStruct t
mkStruct (CFFun a b) = do mkStruct a; mkStruct b
mkStruct _ = pure ""

schFgnDef : {auto c : Ref Ctxt Defs} ->
            {auto l : Ref Loaded (List String)} ->
            {auto s : Ref Structs (List String)} ->
            FC -> Name -> CDef -> Core (String, String)
schFgnDef fc n (MkForeign cs args ret)
    = do let argns = mkArgs 0 args
         let allargns = map fst argns
         let useargns = map fst (filter snd argns)
         argStrs <- traverse mkStruct args
         retStr <- mkStruct ret
         (load, body) <- useCC fc cs (zip useargns args) ret
         defs <- get Ctxt
         pure (load,
                concat argStrs ++ retStr ++
                "(define " ++ schName !(full (gamma defs) n) ++
                " (lambda (" ++ showSep " " (map schName allargns) ++ ") " ++
                body ++ "))\n")
schFgnDef _ _ _ = pure ("", "")

getFgnCall : {auto c : Ref Ctxt Defs} ->
             {auto l : Ref Loaded (List String)} ->
             {auto s : Ref Structs (List String)} ->
             Name -> Core (String, String)
getFgnCall n
    = do defs <- get Ctxt
         case !(lookupCtxtExact n (gamma defs)) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just def => case compexpr def of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => schFgnDef (location def) n d

startChez : String -> String
startChez target = unlines
    [ "#!/bin/sh"
    , ""
    , "export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:`dirname " ++ target ++ "`"
    , target ++ " \"$@\""
    ]

||| Compile a TT expression to Chez Scheme
compileToSS : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core ()
compileToSS c tm outfile
    = do ds <- getDirectives Chez
         libs <- findLibs ds
         traverse_ copyLib libs
         (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         l <- newRef {t = List String} Loaded ["libc", "libc 6"]
         s <- newRef {t = List String} Structs []
         fgndefs <- traverse getFgnCall ns
         compdefs <- traverse (getScheme chezExtPrim chezString defs) ns
         let code = fastAppend (map snd fgndefs ++ compdefs)
         main <- schExp chezExtPrim chezString 0 !(compileExp tags tm)
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
compileToSO : {auto c : Ref Ctxt Defs} ->
              (appDirRel : String) -> (outSsAbs : String) -> Core ()
compileToSO appDirRel outSsAbs
    = do tmpFileAbs <- coreLift tmpName
         chez <- coreLift $ findChez
         let build= "#!" ++ chez ++ " --script\n" ++
                    "(parameterize ([optimize-level 3]) (compile-program \"" ++
                    outSsAbs ++ "\"))"
         Right () <- coreLift $ writeFile tmpFileAbs build
            | Left err => throw (FileErr tmpFileAbs err)
         coreLift $ chmod tmpFileAbs 0o755
         coreLift $ system tmpFileAbs
         pure ()

makeSh : String -> String -> Core ()
makeSh outShRel outAbs
    = do Right () <- coreLift $ writeFile outShRel (startChez outAbs)
            | Left err => throw (FileErr outShRel err)
         pure ()

||| Chez Scheme implementation of the `compileExpr` interface.
compileExpr : Bool -> Ref Ctxt Defs -> (execDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr makeitso c execDir tm outfile
    = do let appDirRel = execDir ++ dirSep ++ outfile ++ "_app"
         coreLift $ mkdirs (splitDir appDirRel)
         cwd <- coreLift currentDir
         let outSsAbs = cwd ++ dirSep ++ appDirRel ++ dirSep ++ outfile ++ ".ss"
         let outSoAbs = cwd ++ dirSep ++ appDirRel ++ dirSep ++ outfile ++ ".so"
         compileToSS c tm outSsAbs
         logTime "Make SO" $ when makeitso $ compileToSO appDirRel outSsAbs
         let outShRel = execDir ++ dirSep ++ outfile
         makeSh outShRel (if makeitso then outSoAbs else outSsAbs)
         coreLift $ chmod outShRel 0o755
         pure (Just outShRel)

||| Chez Scheme implementation of the `executeExpr` interface.
||| This implementation simply runs the usual compiler, saving it to a temp file, then interpreting it.
executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c execDir tm
    = do Just sh <- compileExpr False c execDir tm "_tmpchez"
            | Nothing => throw (InternalError "compileExpr returned Nothing")
         coreLift $ system sh
         pure ()

||| Codegen wrapper for Chez scheme implementation.
export
codegenChez : Codegen
codegenChez = MkCG (compileExpr True) executeExpr
