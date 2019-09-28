module Compiler.Scheme.Racket

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.Common

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
findRacket = pure "/usr/bin/env racket"

findRacoExe : IO String
findRacoExe = pure "raco exe"

schHeader : String -> String
schHeader libs
  = "#lang racket/base\n" ++
    "(require racket/promise)\n" ++ -- for force/delay
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
  racketPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  racketPrim i vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Racket yet"))
  racketPrim i vs prim args 
      = schExtCommon racketPrim racketString i vs prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

cftySpec : FC -> CFType -> Core String
cftySpec fc CFUnit = pure "_void"
cftySpec fc CFInt = pure "_int"
cftySpec fc CFString = pure "_string/utf-8"
cftySpec fc CFDouble = pure "_double"
cftySpec fc CFChar = pure "_int8"
cftySpec fc CFPtr = pure "_pointer"
cftySpec fc (CFIORes t) = cftySpec fc t
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

useArg : (Name, CFType) -> String
useArg (n, ty)
    = rktToC ty (schName n)

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
                           pure (loadlib libn vers)

         argTypes <- traverse (\a => do s <- cftySpec fc (snd a)
                                        pure (a, s)) args
         retType <- cftySpec fc ret
         let cbind = "(define-" ++ libn ++ " " ++ cfn ++ 
                     " (_fun " ++ showSep " " (map snd argTypes) ++ " -> " ++ 
                         retType ++ "))\n"
         let call = "(" ++ cfn ++ " " ++
                    showSep " " (map (useArg . fst) argTypes) ++ ")"

         pure (lib ++ cbind, case ret of
                                  CFIORes rt => handleRet rt call
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

compileToRKT : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core ()
compileToRKT c tm outfile
    = do (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         l <- newRef {t = List String} Loaded []
         fgndefs <- traverse getFgnCall ns
         compdefs <- traverse (getScheme racketPrim racketString defs) ns
         let code = concat (map snd fgndefs) ++ concat compdefs
         main <- schExp racketPrim racketString 0 [] !(compileExp tags tm)
         support <- readDataFile "racket/support.rkt"
         let scm = schHeader (concat (map fst fgndefs)) ++ 
                   support ++ code ++ 
                   "(void " ++ main ++ ")\n" ++ 
                   schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tm outfile
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".rkt"
         compileToRKT c tm outn
         raco <- coreLift findRacoExe
         ok <- coreLift $ system (raco ++ " -o " ++ outfile ++ " " ++ outn)
         if ok == 0
            then pure (Just outfile)
            else pure Nothing

executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core ()
executeExpr c tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".rkt"
         compileToRKT c tm outn
         racket <- coreLift findRacket
         coreLift $ system (racket ++ " " ++ outn)
         pure ()

export
codegenRacket : Codegen
codegenRacket = MkCG compileExpr executeExpr

