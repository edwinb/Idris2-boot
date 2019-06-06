module Compiler.Scheme.Racket

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.TT

import Data.NameMap
import Data.Vect
import System
import System.Info

%default covering

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

findRacket : IO String
findRacket = pure "/usr/bin/env racket"

findRacoExe : IO String
findRacoExe = pure "raco exe"

schHeader : String
schHeader
  = "#lang racket/base\n" ++
    "(require racket/promise)\n" ++ -- for force/delay
    "(let ()\n"

schFooter : String
schFooter = ")"

mutual
  racketPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  racketPrim i vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Racket yet"))
  racketPrim i vs prim args 
      = schExtCommon racketPrim i vs prim args

compileToRKT : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core ()
compileToRKT c tm outfile
    = do (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getScheme racketPrim defs) ns
         let code = concat compdefs
         main <- schExp racketPrim 0 [] !(compileExp tags tm)
         support <- readDataFile "racket/support.rkt"
         let scm = schHeader ++ support ++ code ++ "(void " ++ main ++ ")\n" ++ schFooter
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

