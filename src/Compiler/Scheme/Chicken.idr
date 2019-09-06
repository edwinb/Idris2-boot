module Compiler.Scheme.Chicken

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

findCSI : IO String
findCSI =
  do env <- getEnv "CHICKEN_CSI"
     pure $ fromMaybe "/usr/bin/env -S csi" env

findCSC : IO String
findCSC =
  do env <- getEnv "CHICKEN_CSC"
     pure $ fromMaybe "/usr/bin/env -S csc" env

schHeader : List String -> String
schHeader ds
  = "(use numbers)\n" ++ unlines ds ++ "\n" ++
    "(let ()\n"

schFooter : String
schFooter = ")"

showChickenChar : Char -> String -> String
showChickenChar '\\' = ("\\\\" ++)
showChickenChar c
   = if c < chr 32 || c > chr 126
        then (("\\u" ++ pad (asHex (cast c))) ++)
        else strCons c
  where
    pad : String -> String
    pad str
        = case isLTE (length str) 4 of
               Yes _ => cast (List.replicate (4 - length str) '0') ++ str
               No _ => str

showChickenString : List Char -> String -> String
showChickenString [] = id
showChickenString ('"'::cs) = ("\\\"" ++) . showChickenString cs
showChickenString (c ::cs) = (showChickenChar c) . showChickenString cs

chickenString : String -> String
chickenString cs = strCons '"' (showChickenString (unpack cs) "\"")

mutual
  chickenPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  chickenPrim i vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Chicken Scheme yet"))
  chickenPrim i vs prim args 
      = schExtCommon chickenPrim chickenString i vs prim args

compileToSCM : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core ()
compileToSCM c tm outfile
    = do ds <- getDirectives Chicken
         (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getScheme chickenPrim chickenString defs) ns
         let code = concat compdefs
         main <- schExp chickenPrim chickenString 0 [] !(compileExp tags tm)
         support <- readDataFile "chicken/support.scm"
         let scm = schHeader ds ++ support ++ code ++ main ++ schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tm outfile
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".scm"
         compileToSCM c tm outn
         csc <- coreLift findCSC
         ok <- coreLift $ system (csc ++ " " ++ outn ++ " -o " ++ outfile)
         if ok == 0
            then pure (Just outfile)
            else pure Nothing

executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core ()
executeExpr c tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".scm"
         compileToSCM c tm outn
         csi <- coreLift findCSI
         coreLift $ system (csi ++ " -s " ++ outn)
         pure ()

export
codegenChicken : Codegen
codegenChicken = MkCG compileExpr executeExpr


