module Compiler.Coredris

import Compiler.Common
import Compiler.CompileExpr
import Compiler.LambdaLift
import Compiler.Inline
import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT
import Data.List
import Data.NameMap
import Data.Vect
import System
import System.Info
import Utils.Hex

showCoredrisChar : Char -> String -> String
showCoredrisChar '\\' = ("bkslash" ++)
showCoredrisChar c
   = if c < chr 32 || c > chr 126
        then (("\\u" ++ pad (asHex (cast c))) ++)
        else strCons c
  where
    pad : String -> String
    pad str
        = case isLTE (length str) 4 of
               Yes _ => cast (List.replicate (4 - length str) '0') ++ str
               No _ => str

showCoredrisString : List Char -> String -> String
showCoredrisString [] = id
showCoredrisString ('"'::cs) = ("\\\"" ++) . showCoredrisString cs
showCoredrisString (c ::cs) = (showCoredrisChar c) . showCoredrisString cs

coredrisStringQuoted : String -> String
coredrisStringQuoted cs = strCons '"' (showCoredrisString (unpack cs) "\"")

showCoredrisIdentChar : Char -> String -> String
showCoredrisIdentChar '+' = ("_pl" ++)
showCoredrisIdentChar '-' = ("__" ++)
showCoredrisIdentChar '*' = ("_st" ++)
showCoredrisIdentChar '/' = ("_fs" ++)
showCoredrisIdentChar '\\' = ("_bs" ++)
showCoredrisIdentChar '<' = ("_lt" ++)
showCoredrisIdentChar '>' = ("_gt" ++)
showCoredrisIdentChar '=' = ("_eq" ++)
showCoredrisIdentChar '&' = ("_nd" ++)
showCoredrisIdentChar '\'' = ("_sq" ++)
showCoredrisIdentChar '"' = ("_dq" ++)
showCoredrisIdentChar '(' = ("_po" ++)
showCoredrisIdentChar ')' = ("_pc" ++)
showCoredrisIdentChar '{' = ("_bo" ++)
showCoredrisIdentChar '}' = ("_bc" ++)
showCoredrisIdentChar ' ' = ("_" ++)
showCoredrisIdentChar ':' = ("_co" ++)
showCoredrisIdentChar '.' = ("_dt" ++)
showCoredrisIdentChar c
   = if c < chr 32 || c > chr 126
        then (("u" ++ pad (asHex (cast c))) ++)
        else strCons c
  where
    pad : String -> String
    pad str
        = case isLTE (length str) 4 of
               Yes _ => cast (List.replicate (4 - length str) '0') ++ str
               No _ => str

showCoredrisIdent : List Char -> String -> String
showCoredrisIdent [] = id
showCoredrisIdent (c ::cs) = (showCoredrisIdentChar c) . showCoredrisIdent cs

coredrisIdent : String -> String
coredrisIdent cs = showCoredrisIdent (unpack cs) ""

export
coredrisName : Name -> String
coredrisName (NS ns n) = showSep "_" (map coredrisIdent ns) ++ "_" ++ coredrisName n
coredrisName (UN n) = coredrisIdent n
coredrisName (MN n i) = coredrisIdent n ++ "_" ++ coredrisIdent (show i)
coredrisName (PV n d) = "pat__" ++ coredrisName n
coredrisName (DN _ n) = coredrisName n
coredrisName (Nested i n) = "n__" ++ coredrisIdent (show i) ++ "_" ++ coredrisName n
coredrisName (CaseBlock x y) = "case__" ++ coredrisIdent (show x) ++ "_" ++ coredrisIdent (show y)
coredrisName (WithBlock x y) = "with__" ++ coredrisIdent (show x) ++ "_" ++ coredrisIdent (show y)
coredrisName (Resolved i) = "fn__" ++ coredrisIdent (show i)

data SVars : List Name -> Type where
     Nil : SVars []
     (::) : (svar : String) -> SVars ns -> SVars (n :: ns)

extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
  where
    extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
    extSVars' i [] vs = vs
    extSVars' i (x :: xs) vs = coredrisName (MN "v" i) :: extSVars' (i + 1) xs vs

initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : {idx : Nat} -> .(IsVar n idx xs) -> SVars xs -> String
lookupSVar First (n :: ns) = n
lookupSVar (Later p) (n :: ns) = lookupSVar p ns

coredrisArglist : SVars ns -> String
coredrisArglist [] = ""
coredrisArglist [x] = x
coredrisArglist (x :: xs) = x ++ " " ++ coredrisArglist xs

export
coredrisConstructor : Int -> List String -> String
coredrisConstructor t args = "(con #:tag " ++ show t ++ " #:args [" ++ showSep " " args ++ "])"

||| Generate scheme for a plain function.
op : String -> List String -> String
op o args = "(prim-app #:op " ++ o ++ " #:args [" ++ showSep " " args ++ "])"

||| Extended primitives for the scheme backend, outside the standard set of primFn
public export
data ExtPrim = PutStr | GetStr | PutChar | GetChar
             -- | CCall
             -- | FileOpen | FileClose | FileReadLine | FileWriteLine
             -- | FileEOF | FileModifiedTime
             -- | NewIORef | ReadIORef | WriteIORef
             -- | NewArray | ArrayGet | ArraySet
             -- | GetField | SetField
             -- | Stdin | Stdout | Stderr
             -- | VoidElim
             -- | SysOS | SysCodegen
             | Unknown Name

export
Show ExtPrim where
  -- show CCall = "CCall"
  show PutStr = "put-str"
  show GetStr = "get-str"
  show PutChar = "put-char"
  show GetChar = "get-char"
  -- show FileOpen = "FileOpen"
  -- show FileClose = "FileClose"
  -- show FileReadLine = "FileReadLine"
  -- show FileWriteLine = "FileWriteLine"
  -- show FileEOF = "FileEOF"
  -- show FileModifiedTime = "FileModifiedTime"
  -- show NewIORef = "NewIORef"
  -- show ReadIORef = "ReadIORef"
  -- show WriteIORef = "WriteIORef"
  -- show NewArray = "NewArray"
  -- show ArrayGet = "ArrayGet"
  -- show ArraySet = "ArraySet"
  -- show GetField = "GetField"
  -- show SetField = "SetField"
  -- show Stdin = "Stdin"
  -- show Stdout = "Stdout"
  -- show Stderr = "Stderr"
  -- show VoidElim = "VoidElim"
  -- show SysOS = "SysOS"
  -- show SysCodegen = "SysCodegen"
  show (Unknown n) = "unknown-" ++ show n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [-- (n == UN "prim__cCall", CCall),
            (n == UN "prim__putStr", PutStr),
            (n == UN "prim__getStr", GetStr),
            (n == UN "prim__putChar", PutChar),
            (n == UN "prim__getChar", GetChar)
            -- (n == UN "prim__open", FileOpen),
            -- (n == UN "prim__close", FileClose),
            -- (n == UN "prim__readLine", FileReadLine),
            -- (n == UN "prim__writeLine", FileWriteLine),
            -- (n == UN "prim__eof", FileEOF),
            -- (n == UN "prim__fileModifiedTime", FileModifiedTime),
            -- (n == UN "prim__newIORef", NewIORef),
            -- (n == UN "prim__readIORef", ReadIORef),
            -- (n == UN "prim__writeIORef", WriteIORef),
            -- (n == UN "prim__newArray", NewArray),
            -- (n == UN "prim__arrayGet", ArrayGet),
            -- (n == UN "prim__arraySet", ArraySet),
            -- (n == UN "prim__getField", GetField),
            -- (n == UN "prim__setField", SetField),
            -- (n == UN "prim__stdin", Stdin),
            -- (n == UN "prim__stdout", Stdout),
            -- (n == UN "prim__stderr", Stderr),
            -- (n == UN "void", VoidElim),
            -- (n == UN "prim__os", SysOS),
            -- (n == UN "prim__codegen", SysCodegen)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : String -> String
mkWorld res = "'mk-world"

coredrisConstant : Constant -> String
coredrisConstant (I x) = "(constant #:type 'i32 #:val " ++ show x ++ ")"
coredrisConstant (BI x) = "(constant #:type 'i64 #:val " ++ show x ++ ")"
coredrisConstant (Db x) = "(constant #:type 'double #:val " ++ show x ++ ")"
coredrisConstant (Ch x) = "(constant #:type 'char #:val '" ++ cast x ++ "')"
coredrisConstant (Str x) 
  = "(constant #:type 'string #:val " ++ coredrisStringQuoted x ++ ")"
coredrisConstant WorldVal = "'world"
coredrisConstant IntType = "'i32"
coredrisConstant IntegerType = "'i64"
coredrisConstant StringType = "'string"
coredrisConstant CharType = "'char"
coredrisConstant DoubleType = "'f64"
coredrisConstant WorldType = "'f32"

unop : String -> Constant -> String -> String
unop name ty x = 
  op ("(primop #:arity 1 #:op '" ++ name 
     ++ " #:type " ++ coredrisConstant ty ++ ")") [x]

binop : String -> Constant -> String -> String -> String
binop name ty x y = 
  op ("(primop #:arity 2 #:op '" ++ name 
     ++ " #:type " ++ coredrisConstant ty ++ ")") [x, y]

||| Generate scheme for a primitive function.
coredrisOp : PrimFn arity -> Vect arity String -> String
coredrisOp (Add ty) [x, y] = binop "add" ty x y
coredrisOp (Sub ty) [x, y] = binop "sub" ty x y
coredrisOp (Mul ty) [x, y] = binop "mul" ty x y
coredrisOp (Div ty) [x, y] = binop "div" ty x y
coredrisOp (Mod ty) [x, y] = binop "mod" ty x y
coredrisOp (Neg ty) [x] = unop "neg" ty x
coredrisOp (LT ty) [x, y] = binop "lt" ty x y
coredrisOp (GT ty) [x, y] = binop "gt" ty x y
coredrisOp (EQ ty) [x, y] = binop "eq" ty x y
coredrisOp (LTE ty) [x, y] = binop "lte" ty x y
coredrisOp (GTE ty) [x, y] = binop "gte" ty x y
coredrisOp StrLength [x] = unop "length" StringType x
coredrisOp StrHead [x] = unop "head" StringType x
coredrisOp StrTail [x] = unop "tail" StringType x
coredrisOp StrIndex [x, i] = unop "index" StringType x
coredrisOp StrCons [x, y] = unop "cons" StringType x
coredrisOp StrAppend [x, y] = binop "append" StringType x y
coredrisOp StrReverse [x] = unop "reverse" StringType x
coredrisOp (Cast i o) [x] = unop ("to-" ++ coredrisConstant o) i x
-- coredrisOp StrSubstr [x, y, z] = op "string-substring" [x, y, z]
coredrisOp fn args = op (show fn) (toList args)

coredrisCaseDef : Maybe String -> String
coredrisCaseDef Nothing = ""
coredrisCaseDef (Just tm) = " #:default " ++ tm

coredrisIfDef : Maybe String -> String
coredrisIfDef Nothing = ""
coredrisIfDef (Just tm) = " #:default " ++ tm

mutual
  coredrisConAlt : Int -> SVars vars -> String -> LiftedConAlt vars -> Core String
  coredrisConAlt i vs tgt (MkLConAlt n tag args sc)
      = do let vs' = extendSVars args vs
           pure $ "(con-alt" ++ " #:match " ++ tgt ++ " #:tag " ++ show tag ++ " #:body "
                            ++ bindArgs 1 args vs' !(coredrisExp i vs' sc) ++ ")"
    where
      bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
      bindArgs i [] vs body = body
      bindArgs i (n :: ns) (v :: vs) body
          = "(let-field #:bind-var " ++ v ++ " #:bind-body " ++ tgt ++ " #:bind-field " ++ show i ++ " " 
            ++ "#:body " ++ bindArgs (i + 1) ns vs body ++ ")"

  coredrisConstAlt : Int -> SVars vars -> String -> LiftedConstAlt vars -> Core String
  coredrisConstAlt i vs tgt (MkLConstAlt c exp)
      = pure $ "(const-alt"
                ++ " #:match " ++ tgt
                ++ " #:const " ++ coredrisConstant c ++ " #:body " 
                ++ !(coredrisExp i vs exp) ++ ")"

  coredrisArgs : Int -> SVars vars -> List (Lifted vars) -> Core (List String)
  coredrisArgs i vs [] = pure []
  coredrisArgs i vs (arg :: args) 
    = pure $ !(coredrisExp i vs arg) :: !(coredrisArgs i vs args)

  coredrisArgsVect : Int -> SVars vars -> Vect n (Lifted vars) -> Core (Vect n String)
  coredrisArgsVect i vs [] = pure []
  coredrisArgsVect i vs (arg :: args) 
    = pure $ !(coredrisExp i vs arg) :: !(coredrisArgsVect i vs args)

  coredrisExp : Int -> SVars vars -> Lifted vars -> Core String
  coredrisExp i vs (LLocal fc n) = pure $ lookupSVar n vs
  coredrisExp i vs (LLet fc x val sc)
     = do let vs' = extendSVars [x] vs
          val' <- coredrisExp i vs val
          sc' <- coredrisExp i vs' sc
          pure $ "(let #:var " ++ lookupSVar First vs' ++ " #:val " 
                  ++ val' ++ " #:body " ++ sc' ++ ")"
  coredrisExp i vs (LAppName fc n args)
      = pure $ "(app #:fn " ++ coredrisName n ++ " #:args [" ++ showSep " " !(coredrisArgs i vs args) ++ "])"
  coredrisExp i vs (LUnderApp fc n missing args)
      = pure $ "(mk-clos #:fn " ++ coredrisName n 
                ++ " #:missing " ++ show missing
                ++ " #:args [" ++ showSep " " !(coredrisArgs i vs args)
                ++ "])"
  coredrisExp i vs (LApp fc clos arg)
      = pure $ "(app-clos #:clos " ++ !(coredrisExp i vs clos) ++ " #:arg "
               ++ !(coredrisExp i vs arg) ++ ")"
  coredrisExp i vs (LCon fc n tag args)
      = pure $ "(con #:name " ++ coredrisName n ++ " #:tag " ++ show tag
                ++ " #:args [" ++ showSep " " !(coredrisArgs i vs args) ++ "])"
  coredrisExp i vs (LOp fc op args)
      = pure $ coredrisOp op !(coredrisArgsVect i vs args)
  coredrisExp i vs (LExtPrim fc p args)
      = coredrisExtCommon i vs (toPrim p) args
  coredrisExp i vs (LConCase fc sc alts def)
      = do tcode <- coredrisExp (i+1) vs sc
           defc <- maybe (pure Nothing) (\v => pure (Just !(coredrisExp i vs v))) def
           let n = "sc" ++ show i
           pure $ "(con-case #:bind-var " ++ n ++ " #:bind-body " 
                   ++ tcode ++ " #:cases [" 
                   ++ showSep " " !(traverse (coredrisConAlt (i+1) vs n) alts) ++ "]"
                   ++ coredrisCaseDef defc ++ ")"
  coredrisExp i vs (LConstCase fc sc alts def)
      = do tcode <- coredrisExp (i+1) vs sc
           defc <- maybe (pure Nothing) (\v => pure (Just !(coredrisExp i vs v))) def
           let n = "sc" ++ show i
           pure $ "(const-case #:bind-var " ++ n ++ " #:bind-body " ++ tcode 
                   ++ " #:conds ["
                   ++ showSep " " !(traverse (coredrisConstAlt (i+1) vs n) alts) 
                   ++ "]" ++ coredrisIfDef defc ++ ")"
  coredrisExp i vs (LPrimVal fc c) = pure $ coredrisConstant c
  coredrisExp i vs (LErased fc) = pure "'erased"
  coredrisExp i vs (LCrash fc msg) = pure $ "(crash " ++ show msg ++ ")"

  coredrisExtCommon : Int -> SVars vars -> ExtPrim -> List (Lifted vars) -> Core String
  coredrisExtCommon i vs prim args
      = pure $ "(ext-prim-app #:name '" ++ coredrisIdent (show prim) ++ " #:args [" 
                ++ showSep " " !(traverse (coredrisExp i vs) args) ++ "])"

coredrisDef : {auto c : Ref Ctxt Defs} ->
         Name -> LiftedDef -> Core String
coredrisDef n (MkLFun args scope exp) = do
  let vargs = initSVars (scope ++ args)
  let out = "(fn" ++ "\n  #:name " ++ coredrisName !(getFullName n) 
               ++ "\n  #:args [" ++ coredrisArglist vargs ++ "]"
               ++ "\n  #:body " ++ !(coredrisExp 0 vargs exp) ++ ")\n"
  pure out
coredrisDef n (MkLCon _tag _arity _) = pure "" -- Nothing to compile here
coredrisDef n (MkLForeign _ _ _) = pure "" -- compiled by specific back end
coredrisDef n (MkLError exp) 
   = pure $ "(def (" ++ coredrisName !(getFullName n) ++ " . 'any-args) " 
            ++ !(coredrisExp 0 [] exp) ++ ")\n"

-- coredrisTm : Term args -> String
-- coredrisTm (Erased _ _) = "'erased"
-- coredrisTm (Ref _ _ n) = coredrisName n
-- coredrisTm (App _ fn args) = "(app #:fn " ++ coredrisTm fn ++ " #:args [" ++ coredrisTm args ++ "])"

compileToCoredris : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core ()
compileToCoredris c tm outfile = do
  cdata <- getCompileData tm
  let ns = allNames cdata
  defs <- concat <$> traverse lambdaLift ns
  out <- traverse (\(n, d) => coredrisDef n d) defs
  coreLift (writeFile outfile (concat out))
  pure ()

||| Coredris implementation of the `executeExpr` interface.
executeExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> Core ()
executeExpr c _ tm
    = do coreLift $ system "false"
         pure ()

||| Coredris implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs -> (execDir : String) -> ClosedTerm -> 
              (outfile : String) -> Core (Maybe String)
compileExpr c _ tm outfile = do 
  let outn = outfile ++ ".lisp"
  compileToCoredris c tm outn
  pure (Just outfile)

||| Codegen wrapper for Coredris implementation.
export
codegenCoredris : Codegen
codegenCoredris = MkCG compileExpr executeExpr
