module Compiler.Scheme.Racket

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.Common

import Core.Options
import Core.Context
import Core.Directory
import Core.Name
import Core.TT

import Utils.Hex

import Data.NameMap
import Data.Vect
import System
import System.Info

%default covering

findRacket : IO String
findRacket =
  do env <- getEnv "RACKET"
     pure $ fromMaybe "/usr/bin/env racket" env

findRacoExe : IO String
findRacoExe =
  do env <- getEnv "RACKET_RACO"
     pure $ (fromMaybe "/usr/bin/env raco" env) ++ " exe"

schHeader : String -> String
schHeader libs
  = "#lang racket/base\n" ++
    "(require racket/math)\n" ++ -- for math ops
    "(require racket/promise)\n" ++ -- for force/delay
    "(require racket/system)\n" ++ -- for system
    "(require rnrs/bytevectors-6)\n" ++ -- for buffers
    "(require rnrs/io/ports-6)\n" ++ -- for file handling
    "(require ffi/unsafe ffi/unsafe/define)\n" ++ -- for calling C
    libs ++
    "(let ()\n"

schFooter : String
schFooter = ")"

showRacketChar : Char -> String -> String
showRacketChar '\\' = ("\\\\" ++)
showRacketChar c
   = if c < chr 32 || c > chr 126
        then (("\\u" ++ pad (asHex (cast c))) ++)
        else strCons c
  where
    pad : String -> String
    pad str
        = case isLTE (length str) 4 of
               Yes _ => cast (List.replicate (4 - length str) '0') ++ str
               No _ => str

showRacketString : List Char -> String -> String
showRacketString [] = id
showRacketString ('"'::cs) = ("\\\"" ++) . showRacketString cs
showRacketString (c ::cs) = (showRacketChar c) . showRacketString cs

racketString : String -> String
racketString cs = strCons '"' (showRacketString (unpack cs) "\"")

mutual
  racketPrim : Int -> ExtPrim -> List NamedCExp -> Core String
  racketPrim i CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Racket yet"))
  racketPrim i GetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _]
      = do structsc <- schExp racketPrim racketString 0 struct
           pure $ "(" ++ s ++ "-" ++ fld ++ " " ++ structsc ++ ")"
  racketPrim i GetField [_,_,_,_,_,_]
      = pure "(error \"bad getField\")"
  racketPrim i SetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _, val, world]
      = do structsc <- schExp racketPrim racketString 0 struct
           valsc <- schExp racketPrim racketString 0 val
           pure $ mkWorld $
                "(set-" ++ s ++ "-" ++ fld ++ "! " ++ structsc ++ " " ++ valsc ++ ")"
  racketPrim i SetField [_,_,_,_,_,_,_,_]
      = pure "(error \"bad setField\")"
  racketPrim i SysCodegen []
      = pure $ "\"racket\""
  racketPrim i prim args
      = schExtCommon racketPrim racketString i prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

-- Label for noting which struct types are declared
data Structs : Type where

cftySpec : FC -> CFType -> Core String
cftySpec fc CFUnit = pure "_void"
cftySpec fc CFInt = pure "_int"
cftySpec fc CFString = pure "_string/utf-8"
cftySpec fc CFDouble = pure "_double"
cftySpec fc CFChar = pure "_int8"
cftySpec fc CFPtr = pure "_pointer"
cftySpec fc (CFIORes t) = cftySpec fc t
cftySpec fc (CFStruct n t) = pure $ "_" ++ n ++ "-pointer"
cftySpec fc (CFFun s t) = funTySpec [s] t
  where
    funTySpec : List CFType -> CFType -> Core String
    funTySpec args (CFFun CFWorld t) = funTySpec args t
    funTySpec args (CFFun s t) = funTySpec (s :: args) t
    funTySpec args retty
        = do rtyspec <- cftySpec fc retty
             argspecs <- traverse (cftySpec fc) (reverse args)
             pure $ "(_fun " ++ showSep " " argspecs ++ " -> " ++ rtyspec ++ ")"
cftySpec fc t = throw (GenericMsg fc ("Can't pass argument of type " ++ show t ++
                         " to foreign function"))

loadlib : String -> String -> String
loadlib libn ver
    = "(define-ffi-definer define-" ++ libn ++
      " (ffi-lib \"" ++ libn ++ "\" " ++ ver ++ "))\n"

getLibVers : String -> (String, String)
getLibVers libspec
    = case words libspec of
           [] => ("", "")
           [fn] => case span (/='.') libspec of
                        (root, rest) => (root, "")
           (fn :: vers) =>
               (fst (span (/='.') fn),
                  "'(" ++ showSep " " (map show vers) ++ " #f)" )

cToRkt : CFType -> String -> String
cToRkt CFChar op = "(integer->char " ++ op ++ ")"
cToRkt _ op = op

rktToC : CFType -> String -> String
rktToC CFChar op = "(char->integer " ++ op ++ ")"
rktToC _ op = op

handleRet : CFType -> String -> String
handleRet CFUnit op = op ++ " " ++ mkWorld (schConstructor 0 [])
handleRet ret op = mkWorld (cToRkt ret op)

cCall : {auto c : Ref Ctxt Defs} ->
        {auto l : Ref Loaded (List String)} ->
        FC -> (cfn : String) -> (clib : String) ->
        List (Name, CFType) -> CFType -> Core (String, String)
cCall fc cfn libspec args ret
    = do loaded <- get Loaded
         let (libn, vers) = getLibVers libspec
         lib <- if libn `elem` loaded
                   then pure ""
                   else do put Loaded (libn :: loaded)
                           ldata <- locate libspec
                           copyLib ldata
                           pure (loadlib libn vers)

         argTypes <- traverse (\a => do s <- cftySpec fc (snd a)
                                        pure (a, s)) args
         retType <- cftySpec fc ret
         let cbind = "(define-" ++ libn ++ " " ++ cfn ++
                     " (_fun " ++ showSep " " (map snd argTypes) ++ " -> " ++
                         retType ++ "))\n"
         let call = "(" ++ cfn ++ " " ++
                    showSep " " !(traverse useArg argTypes) ++ ")"

         pure (lib ++ cbind, case ret of
                                  CFIORes rt => handleRet rt call
                                  _ => call)
  where
    mkNs : Int -> List CFType -> List (Maybe (String, CFType))
    mkNs i [] = []
    mkNs i (CFWorld :: xs) = Nothing :: mkNs i xs
    mkNs i (x :: xs) = Just ("cb" ++ show i, x) :: mkNs (i + 1) xs

    applyLams : String -> List (Maybe (String, CFType)) -> String
    applyLams n [] = n
    applyLams n (Nothing :: as) = applyLams ("(" ++ n ++ " #f)") as
    applyLams n (Just (a, ty) :: as)
        = applyLams ("(" ++ n ++ " " ++ cToRkt ty a ++ ")") as

    mkFun : List CFType -> CFType -> String -> String
    mkFun args ret n
        = let argns = mkNs 0 args in
              "(lambda (" ++ showSep " " (map fst (mapMaybe id argns)) ++ ") " ++
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
             pure $ mkFun args retty n

    useArg : ((Name, CFType), String) -> Core String
    useArg ((n, CFFun s t), _) = callback (schName n) [s] t
    useArg ((n, ty), _)
        = pure $ rktToC ty (schName n)

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
                    pure $ concat defs ++ "(define-cstruct _" ++ n ++ " ("
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
         pure (concat argStrs ++ retStr ++ load,
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

compileToRKT : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core ()
compileToRKT c tm outfile
    = do cdata <- getCompileData tm
         let ns = allNames cdata
         let tags = nameTags cdata
         let ctm = forget (mainExpr cdata)

         defs <- get Ctxt
         l <- newRef {t = List String} Loaded []
         s <- newRef {t = List String} Structs []
         fgndefs <- traverse getFgnCall ns
         compdefs <- traverse (getScheme racketPrim racketString defs) ns
         let code = fastAppend (map snd fgndefs ++ compdefs)
         main <- schExp racketPrim racketString 0 ctm
         support <- readDataFile "racket/support.rkt"
         let scm = schHeader (concat (map fst fgndefs)) ++
                   support ++ code ++
                   "(void " ++ main ++ ")\n" ++
                   schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

compileExpr : Ref Ctxt Defs -> (execDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c execDir tm outfile
    = do let outSs = execDir ++ dirSep ++ outfile ++ ".rkt"
         let outBin = execDir ++ dirSep ++ outfile
         compileToRKT c tm outSs
         raco <- coreLift findRacoExe
         ok <- coreLift $ system (raco ++ " -o " ++ outBin ++ " " ++ outSs)
         if ok == 0
            then pure (Just outfile)
            else pure Nothing

executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c execDir tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".rkt"
         compileToRKT c tm outn
         racket <- coreLift findRacket
         coreLift $ system (racket ++ " " ++ outn)
         pure ()

export
codegenRacket : Codegen
codegenRacket = MkCG compileExpr executeExpr

