module Compiler.Scheme.Gambit

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

findGSI : IO String
findGSI =
  do env <- getEnv "GAMBIT_GSI"
     pure $ fromMaybe "/usr/bin/env -S gsi-script" env

findGSC : IO String
findGSC =
  do env <- getEnv "GAMBIT_GSC"
     pure $ fromMaybe "/usr/bin/env -S gsc-script" env

schHeader : String
schHeader = "(declare (block)
         (standard-bindings)
         (extended-bindings)
         (not safe))\n\n"

schFooter : String
schFooter = "\n"

-- XXX
showGambitChar : Char -> String -> String
showGambitChar '\\' = ("\\\\" ++)
showGambitChar c = strCons c

showGambitString : List Char -> String -> String
showGambitString [] = id
showGambitString ('"'::cs) = ("\\\"" ++) . showGambitString cs
showGambitString (c::cs) = (showGambitChar c) . showGambitString cs

gambitString : String -> String
gambitString cs = strCons '"' (showGambitString (unpack cs) "\"")

mutual
  gambitPrim : Int -> ExtPrim -> List NamedCExp -> Core String
  gambitPrim i CCall [ret, NmPrimVal fc (Str fn), fargs, world]
      = throw (InternalError ("Can't compile C FFI calls to Gambit yet")) -- TODO
  gambitPrim i CCall [ret, fn, args, world]
      = pure "(error \"bad ffi call\")"
  gambitPrim i GetStr [world]
      = pure $ mkWorld "(read-line (current-input-port))"
  gambitPrim i GetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _]
      = do structsc <- schExp gambitPrim gambitString 0 struct
           pure $ "(" ++ s ++ "-" ++ fld ++ " " ++ structsc ++ ")" -- XXX
  gambitPrim i GetField [_,_,_,_,_,_]
      = pure "(error \"bad getField\")"
  gambitPrim i SetField [NmPrimVal _ (Str s), _, _, struct,
                         NmPrimVal _ (Str fld), _, val, world]
      = do structsc <- schExp gambitPrim gambitString 0 struct
           valsc <- schExp gambitPrim gambitString 0 val
           pure $ mkWorld $
                "(" ++ s ++ "-" ++ fld ++ "-set! " ++ structsc ++ " " ++ valsc ++ ")" -- XXX
  gambitPrim i SetField [_,_,_,_,_,_,_,_]
      = pure "(error \"bad setField\")"
  gambitPrim i SysCodegen []
      = pure $ "\"gambit\""
  gambitPrim i prim args
      = schExtCommon gambitPrim gambitString i prim args

-- Reference label for keeping track of loaded external libraries
data Loaded : Type where

-- Label for noting which struct types are declared
data Structs : Type where

-- TODO Support C FFI and libraries

compileToSCM : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core ()
compileToSCM c tm outfile
    = do -- XXX
         -- ds <- getDirectives Gambit
         -- libs <- findLibs ds
         -- traverse_ copyLib libs
         cdata <- getCompileData tm
         let ns = allNames cdata
         let tags = nameTags cdata
         let ctm = forget (mainExpr cdata)

         defs <- get Ctxt
         l <- newRef {t = List String} Loaded [] -- XXX ["libc", "libc 6"]
         s <- newRef {t = List String} Structs []
         -- fgndefs <- traverse getFgnCall ns
         compdefs <- traverse (getScheme gambitPrim gambitString defs) ns
         let code = concat compdefs -- XXX
         -- let code = fastAppend (map snd fgndefs ++ compdefs)
         main <- schExp gambitPrim gambitString 0 ctm
         support <- readDataFile "gambit/support.scm"
         let scm = schHeader ++ support ++ code ++ main ++ schFooter -- XXX
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

-- TODO Allow specifying if we want a dynamic obj file or an executable binary
-- Look at what is done in Chez Scheme
compileExpr : Ref Ctxt Defs -> (execDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c execDir tm outfile
    = do let outn = execDir ++ dirSep ++ outfile ++ ".scm"
         compileToSCM c tm outn
         gsc <- coreLift findGSC
         ok <- coreLift $ system (gsc ++ " -exe " ++ outn)
         if ok == 0
            then pure (Just outfile)
            else pure Nothing

executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c execDir tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".scm"
         compileToSCM c tm outn
         gsi <- coreLift findGSI
         coreLift $ system (gsi ++ " " ++ outn)
         pure ()

export
codegenGambit : Codegen
codegenGambit = MkCG compileExpr executeExpr
