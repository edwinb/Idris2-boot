module Compiler.Scheme.Common

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

schString : String -> String
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

schName : Name -> String
schName (NS ns n) = showSep "-" ns ++ "-" ++ schName n
schName (UN n) = schString n
schName (MN n i) = schString n ++ "-" ++ show i
schName (PV n d) = "pat--" ++ schName n
schName (DN _ n) = schName n
schName (Nested i n) = "n--" ++ show i ++ "-" ++ schName n
schName (CaseBlock x y) = "case--" ++ show x ++ "-" ++ show y
schName (WithBlock x y) = "with--" ++ show x ++ "-" ++ show y
schName (Resolved i) = "fn--" ++ show i

-- local variable names as scheme names - we need to invent new names for the locals
-- because there might be shadows in the original expression which can't be resolved
-- by the same scoping rules. (e.g. something that computes \x, x => x + x where the
-- names are the same but refer to different bindings in the scope)
public export
data SVars : List Name -> Type where
     Nil : SVars []
     (::) : (svar : String) -> SVars ns -> SVars (n :: ns)

extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
  where 
    extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
    extSVars' i [] vs = vs
    extSVars' i (x :: xs) vs = schName (MN "v" i) :: extSVars' (i + 1) xs vs

initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : {idx : Nat} -> .(IsVar n idx xs) -> SVars xs -> String
lookupSVar First (n :: ns) = n
lookupSVar (Later p) (n :: ns) = lookupSVar p ns

export
schConstructor : Int -> List String -> String
schConstructor t args = "(vector " ++ show t ++ " " ++ showSep " " args ++ ")"

||| Generate scheme for a plain function.
op : String -> List String -> String
op o args = "(" ++ o ++ " " ++ showSep " " args ++ ")"

||| Generate scheme for a boolean operation.
boolop : String -> List String -> String
boolop o args = "(or (and " ++ op o args ++ " 1) 0)"

||| Generate scheme for a primitive function. 
schOp : PrimFn arity -> Vect arity String -> String
schOp (Add IntType) [x, y] = op "b+" [x, y, "63"]
schOp (Sub IntType) [x, y] = op "b-" [x, y, "63"]
schOp (Mul IntType) [x, y] = op "b*" [x, y, "63"]
schOp (Div IntType) [x, y] = op "b/" [x, y, "63"]
schOp (Add ty) [x, y] = op "+" [x, y]
schOp (Sub ty) [x, y] = op "-" [x, y]
schOp (Mul ty) [x, y] = op "*" [x, y]
schOp (Div ty) [x, y] = op "/" [x, y]
schOp (Mod ty) [x, y] = op "remainder" [x, y]
schOp (Neg ty) [x] = op "-" [x]
schOp (LT CharType) [x, y] = boolop "char<?" [x, y]
schOp (LTE CharType) [x, y] = boolop "char<=?" [x, y]
schOp (EQ CharType) [x, y] = boolop "char=?" [x, y]
schOp (GTE CharType) [x, y] = boolop "char>=?" [x, y]
schOp (GT CharType) [x, y] = boolop "char>?" [x, y]
schOp (LT StringType) [x, y] = boolop "string<?" [x, y]
schOp (LTE StringType) [x, y] = boolop "string<=?" [x, y]
schOp (EQ StringType) [x, y] = boolop "string=?" [x, y]
schOp (GTE StringType) [x, y] = boolop "string>=?" [x, y]
schOp (GT StringType) [x, y] = boolop "string>?" [x, y]
schOp (LT ty) [x, y] = boolop "<" [x, y]
schOp (LTE ty) [x, y] = boolop "<=" [x, y]
schOp (EQ ty) [x, y] = boolop "=" [x, y]
schOp (GTE ty) [x, y] = boolop ">=" [x, y]
schOp (GT ty) [x, y] = boolop ">" [x, y]
schOp StrLength [x] = op "string-length" [x]
schOp StrHead [x] = op "string-ref" [x, "0"]
schOp StrTail [x] = op "substring" [x, "1", op "string-length" [x]]
schOp StrIndex [x, i] = op "string-ref" [x, i]
schOp StrCons [x, y] = op "string-cons" [x, y]
schOp StrAppend [x, y] = op "string-append" [x, y]
schOp StrReverse [x] = op "string-reverse" [x]
schOp StrSubstr [x, y, z] = op "string-substr" [x, y, z]

schOp DoubleExp [x] = op "exp" [x]
schOp DoubleLog [x] = op "log" [x]
schOp DoubleSin [x] = op "sin" [x]
schOp DoubleCos [x] = op "cos" [x]
schOp DoubleTan [x] = op "tan" [x]
schOp DoubleASin [x] = op "asin" [x]
schOp DoubleACos [x] = op "asin" [x]
schOp DoubleATan [x] = op "atan" [x]
schOp DoubleSqrt [x] = op "sqrt" [x]
schOp DoubleFloor [x] = op "floor" [x]
schOp DoubleCeiling [x] = op "ceiling" [x]

schOp (Cast IntType StringType) [x] = op "number->string" [x]
schOp (Cast IntegerType StringType) [x] = op "number->string" [x]
schOp (Cast DoubleType StringType) [x] = op "number->string" [x]
schOp (Cast CharType StringType) [x] = op "string" [x]

schOp (Cast IntType IntegerType) [x] = x
schOp (Cast DoubleType IntegerType) [x] = op "floor" [x]
schOp (Cast CharType IntegerType) [x] = op "char->integer" [x]
schOp (Cast StringType IntegerType) [x] = op "cast-string-int" [x]

schOp (Cast IntegerType IntType) [x] = x
schOp (Cast DoubleType IntType) [x] = op "floor" [x]
schOp (Cast StringType IntType) [x] = op "cast-string-int" [x]
schOp (Cast CharType IntType) [x] = op "char->integer" [x]

schOp (Cast IntegerType DoubleType) [x] = op "exact->inexact" [x]
schOp (Cast IntType DoubleType) [x] = op "exact->inexact" [x]
schOp (Cast StringType DoubleType) [x] = op "cast-string-double" [x]

schOp (Cast IntType CharType) [x] = op "integer->char" [x]

schOp (Cast from to) [x] = "(blodwen-error-quit \"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"

schOp BelieveMe [_,_,x] = x

||| Extended primitives for the scheme backend, outside the standard set of primFn
public export
data ExtPrim = CCall | SchemeCall | PutStr | GetStr 
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | Stdin | Stdout | Stderr
             | VoidElim | Unknown Name

export
Show ExtPrim where
  show CCall = "CCall"
  show SchemeCall = "SchemeCall"
  show PutStr = "PutStr"
  show GetStr = "GetStr"
  show FileOpen = "FileOpen"
  show FileClose = "FileClose"
  show FileReadLine = "FileReadLine"
  show FileWriteLine = "FileWriteLine"
  show FileEOF = "FileEOF"
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show Stdin = "Stdin"
  show Stdout = "Stdout"
  show Stderr = "Stderr"
  show VoidElim = "VoidElim"
  show (Unknown n) = "Unknown " ++ show n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n) 
    = cond [(n == UN "prim__schemeCall", SchemeCall),
            (n == UN "prim__cCall", CCall),
            (n == UN "prim__putStr", PutStr),
            (n == UN "prim__getStr", GetStr),
            (n == UN "prim__open", FileOpen),
            (n == UN "prim__close", FileClose),
            (n == UN "prim__readLine", FileReadLine),
            (n == UN "prim__writeLine", FileWriteLine),
            (n == UN "prim__eof", FileEOF),
            (n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef),
            (n == UN "prim__stdin", Stdin),
            (n == UN "prim__stdout", Stdout),
            (n == UN "prim__stderr", Stderr),
            (n == UN "void", VoidElim)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : String -> String
mkWorld res = schConstructor 0 ["#f", res, "#f"] -- MkIORes

schConstant : Constant -> String
schConstant (I x) = show x
schConstant (BI x) = show x
schConstant (Str x) = show x
schConstant (Ch x) = "#\\" ++ cast x
schConstant (Db x) = show x
schConstant WorldVal = "#f"
schConstant IntType = "#t"
schConstant IntegerType = "#t"
schConstant StringType = "#t"
schConstant CharType = "#t"
schConstant DoubleType = "#t"
schConstant WorldType = "#t"

schCaseDef : Maybe String -> String
schCaseDef Nothing = ""
schCaseDef (Just tm) = "(else " ++ tm ++ ")"

parameters (schExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String)
  mutual
    schConAlt : Int -> SVars vars -> String -> CConAlt vars -> Core String
    schConAlt {vars} i vs target (MkConAlt n tag args sc)
        = let vs' = extendSVars args vs in
              pure $ "((" ++ show tag ++ ") "
                          ++ bindArgs 1 args vs' !(schExp i vs' sc) ++ ")"
      where
        bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
        bindArgs i [] vs body = body
        bindArgs i (n :: ns) (v :: vs) body 
            = "(let ((" ++ v ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) ns vs body ++ ")"

    schConstAlt : Int -> SVars vars -> String -> CConstAlt vars -> Core String
    schConstAlt i vs target (MkConstAlt c exp)
        = pure $ "((equal? " ++ target ++ " " ++ schConstant c ++ ") " ++ !(schExp i vs exp) ++ ")"
      
    -- oops, no traverse for Vect in Core
    schArgs : Int -> SVars vars -> Vect n (CExp vars) -> Core (Vect n String)
    schArgs i vs [] = pure []
    schArgs i vs (arg :: args) = pure $ !(schExp i vs arg) :: !(schArgs i vs args)

    export
    schExp : Int -> SVars vars -> CExp vars -> Core String
    schExp i vs (CLocal fc el) = pure $ lookupSVar el vs
    schExp i vs (CRef fc n) = pure $ schName n
    schExp i vs (CLam fc x sc) 
       = do let vs' = extendSVars [x] vs 
            sc' <- schExp i vs' sc
            pure $ "(lambda (" ++ lookupSVar First vs' ++ ") " ++ sc' ++ ")"
    schExp i vs (CLet fc x val sc) 
       = do let vs' = extendSVars [x] vs
            val' <- schExp i vs val
            sc' <- schExp i vs' sc
            pure $ "(let ((" ++ lookupSVar First vs' ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
    schExp i vs (CApp fc x []) 
        = pure $ "(" ++ !(schExp i vs x) ++ ")"
    schExp i vs (CApp fc x args) 
        = pure $ "(" ++ !(schExp i vs x) ++ " " ++ showSep " " !(traverse (schExp i vs) args) ++ ")"
    schExp i vs (CCon fc x tag args) 
        = pure $ schConstructor tag !(traverse (schExp i vs) args)
    schExp i vs (COp fc op args) 
        = pure $ schOp op !(schArgs i vs args)
    schExp i vs (CExtPrim fc p args) 
        = schExtPrim i vs (toPrim p) args
    schExp i vs (CForce fc t) = pure $ "(force " ++ !(schExp i vs t) ++ ")"
    schExp i vs (CDelay fc t) = pure $ "(delay " ++ !(schExp i vs t) ++ ")"
    schExp i vs (CConCase fc sc alts def) 
        = do tcode <- schExp (i+1) vs sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i vs v))) def
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (get-tag " ++ n ++ ") "
                     ++ showSep " " !(traverse (schConAlt (i+1) vs n) alts)
                     ++ schCaseDef defc ++ "))"
    schExp i vs (CConstCase fc sc alts def) 
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i vs v))) def
             tcode <- schExp (i+1) vs sc
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                      ++ showSep " " !(traverse (schConstAlt (i+1) vs n) alts)
                      ++ schCaseDef defc ++ "))"
    schExp i vs (CPrimVal fc c) = pure $ schConstant c
    schExp i vs (CErased fc) = pure "'()"
    schExp i vs (CCrash fc msg) = pure $ "(blodwen-error-quit " ++ show msg ++ ")"

  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : Int -> SVars vars -> CExp vars -> Core String
  readArgs i vs tm = pure $ "(blodwen-read-args " ++ !(schExp i vs tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  schExtCommon i vs SchemeCall [ret, CPrimVal fc (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs i vs args) ++ ")")
  schExtCommon i vs SchemeCall [ret, fn, args, world]
       = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(schExp i vs fn) ++")) "
                    ++ !(readArgs i vs args) ++ ")")
  schExtCommon i vs PutStr [arg, world] 
      = pure $ "(display " ++ !(schExp i vs arg) ++ ") " ++ mkWorld (schConstructor 0 []) -- code for MkUnit
  schExtCommon i vs GetStr [world] 
      = pure $ mkWorld "(blodwen-get-line (current-input-port))"
  schExtCommon i vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-open " 
                                      ++ !(schExp i vs file) ++ " "
                                      ++ !(schExp i vs mode) ++ " "
                                      ++ !(schExp i vs bin) ++ ")"
  schExtCommon i vs FileClose [file, world]
      = pure $ "(blodwen-close-port " ++ !(schExp i vs file) ++ ") " ++ mkWorld (schConstructor 0 [])
  schExtCommon i vs FileReadLine [file, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-get-line " ++ !(schExp i vs file) ++ ")"
  schExtCommon i vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-putstring " 
                                        ++ !(schExp i vs file) ++ " "
                                        ++ !(schExp i vs str) ++ ")"
  schExtCommon i vs FileEOF [file, world]
      = pure $ mkWorld $ "(blodwen-eof " ++ !(schExp i vs file) ++ ")"
  schExtCommon i vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(schExp i vs ref) ++ ")"
  schExtCommon i vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! " 
                           ++ !(schExp i vs ref) ++ " " 
                           ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs VoidElim [_, _]
      = pure "(display \"Error: Executed 'void'\")"
  schExtCommon i vs (Unknown n) args 
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon i vs Stdin [] = pure "(current-input-port)"
  schExtCommon i vs Stdout [] = pure "(current-output-port)"
  schExtCommon i vs Stderr [] = pure "(current-error-port)"
  schExtCommon i vs prim args 
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  schArglist : SVars ns -> String
  schArglist [] = ""
  schArglist [x] = x
  schArglist (x :: xs) = x ++ " " ++ schArglist xs

  schDef : {auto c : Ref Ctxt Defs} ->
           Name -> CDef -> Core String
  schDef n (MkFun args exp)
     = let vs = initSVars args in
           pure $ "(define " ++ schName !(getFullName n) ++ " (lambda (" ++ schArglist vs ++ ") "
                      ++ !(schExp 0 vs exp) ++ "))\n"
  schDef n (MkError exp)
     = pure $ "(define (" ++ schName !(getFullName n) ++ " . any-args) " ++ !(schExp 0 [] exp) ++ ")\n"
  schDef n (MkCon t a) = pure "" -- Nothing to compile here
  
-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getScheme : {auto c : Ref Ctxt Defs} ->
            (schExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String) ->
            Defs -> Name -> Core String
getScheme schExtPrim defs n
    = case !(lookupCtxtExact n (gamma defs)) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => schDef schExtPrim n d
