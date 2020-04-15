module Compiler.Coredris

import Compiler.Common
import Compiler.CompileExpr
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
showCoredrisIdentChar '+' = ("plus" ++)
showCoredrisIdentChar '-' = ("minus" ++)
showCoredrisIdentChar '*' = ("asterisk" ++)
showCoredrisIdentChar '/' = ("fwdslash" ++)
showCoredrisIdentChar '<' = ("lt" ++)
showCoredrisIdentChar '>' = ("gt" ++)
showCoredrisIdentChar '=' = ("eq" ++)
showCoredrisIdentChar '\\' = ("bkslash" ++)
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
showCoredrisIdent ('"'::cs) = ("dblquote" ++) . showCoredrisIdent cs
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
    extSVars' i (x :: xs) vs = coredrisName (MN "v" i) :: extSVars' (i + 1) xs vs

export
initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : {idx : Nat} -> .(IsVar n idx xs) -> SVars xs -> String
lookupSVar First (n :: ns) = n
lookupSVar (Later p) (n :: ns) = lookupSVar p ns

export
coredrisConstructor : Int -> List String -> String
coredrisConstructor t args = "(^con :tag " ++ show t ++ " :args [" ++ showSep " " args ++ "])"

||| Generate scheme for a plain function.
op : String -> List String -> String
op o args = "(^prim-app :op " ++ o ++ " :args [" ++ showSep " " args ++ "])"

||| Generate scheme for a primitive function.
coredrisOp : PrimFn arity -> Vect arity String -> String
coredrisOp fn args = op (show fn) (toList args)

||| Extended primitives for the scheme backend, outside the standard set of primFn
public export
data ExtPrim = PutStr | GetStr | PutChar | GetChar
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | NewArray | ArrayGet | ArraySet
             | GetField | SetField
             | Stdin | Stdout | Stderr
             | VoidElim
             | SysOS | SysCodegen
             | Unknown Name

export
Show ExtPrim where
  show PutStr = "PutStr"
  show GetStr = "GetStr"
  show PutChar = "PutChar"
  show GetChar = "GetChar"
  show FileOpen = "FileOpen"
  show FileClose = "FileClose"
  show FileReadLine = "FileReadLine"
  show FileWriteLine = "FileWriteLine"
  show FileEOF = "FileEOF"
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show NewArray = "NewArray"
  show ArrayGet = "ArrayGet"
  show ArraySet = "ArraySet"
  show GetField = "GetField"
  show SetField = "SetField"
  show Stdin = "Stdin"
  show Stdout = "Stdout"
  show Stderr = "Stderr"
  show VoidElim = "VoidElim"
  show SysOS = "SysOS"
  show SysCodegen = "SysCodegen"
  show (Unknown n) = "Unknown " ++ show n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN "prim__putStr", PutStr),
            (n == UN "prim__getStr", GetStr),
            (n == UN "prim__putChar", PutChar),
            (n == UN "prim__getChar", GetChar),
            (n == UN "prim__open", FileOpen),
            (n == UN "prim__close", FileClose),
            (n == UN "prim__readLine", FileReadLine),
            (n == UN "prim__writeLine", FileWriteLine),
            (n == UN "prim__eof", FileEOF),
            (n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef),
            (n == UN "prim__newArray", NewArray),
            (n == UN "prim__arrayGet", ArrayGet),
            (n == UN "prim__arraySet", ArraySet),
            (n == UN "prim__getField", GetField),
            (n == UN "prim__setField", SetField),
            (n == UN "prim__stdin", Stdin),
            (n == UN "prim__stdout", Stdout),
            (n == UN "prim__stderr", Stderr),
            (n == UN "void", VoidElim),
            (n == UN "prim__os", SysOS),
            (n == UN "prim__codegen", SysCodegen)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : String -> String
mkWorld res = "'mk-world"

coredrisConstant : (String -> String) -> Constant -> String
coredrisConstant _ (I x) = "(^constant :type 'int :val " ++ show x ++ ")"
coredrisConstant _ (BI x) = "(^constant :type 'big-int :val " ++ show x ++ ")"
coredrisConstant _ (Db x) = "(^constant :type 'double :val " ++ show x ++ ")"
coredrisConstant _ (Ch x) = "(^constant :type 'char :val '" ++ cast x ++ "')"
coredrisConstant coredrisStringQuoted (Str x) = coredrisStringQuoted x
coredrisConstant _ WorldVal = "@world"
coredrisConstant _ IntType = "@i32"
coredrisConstant _ IntegerType = "@i64"
coredrisConstant _ StringType = "@string"
coredrisConstant _ CharType = "@char"
coredrisConstant _ DoubleType = "@f64"
coredrisConstant _ WorldType = "@f32"

coredrisCaseDef : Maybe String -> String
coredrisCaseDef Nothing = ""
coredrisCaseDef (Just tm) = "(^case-default " ++ tm ++ ")"

coredrisIfDef : Maybe String -> String
coredrisIfDef Nothing = ""
coredrisIfDef (Just tm) = "(^if-default " ++ tm ++ ")"

coredrisType' : {auto c: Ref Ctxt Defs} -> List String -> Term args 
          -> Core (String, List String)
coredrisType' acc (Local {name} _ _ _ _) = do
  let rname = "T" ++ coredrisName !(getFullName name)
  -- let rname = "Box<&dyn Any>"
  pure (rname, rname :: acc)
coredrisType' acc (Ref _ _ name) = pure (coredrisName !(getFullName name), acc)
coredrisType' acc (Erased _ _) = pure ("^erased", acc)
coredrisType' acc (App _ x y) = do
  (xty, acc') <- coredrisType' acc x
  (yty, acc'') <- coredrisType' acc' y
  -- pure (xty ++ "<" ++ yty ++ ">", acc'')
  pure (xty, acc'')
coredrisType' acc (Bind _ _ (Pi _ _ x) sc) = do
  (retty, acc') <- coredrisType' acc sc
  (xty, acc'') <- coredrisType' acc' x
  pure ("(^arrow :from " ++ xty ++ " :to " ++ retty ++ ")", acc'')
coredrisType' acc ty = pure (show ty, acc)

coredrisType : {auto c: Ref Ctxt Defs} -> Term args -> Core (String, List String)
coredrisType tm = coredrisType' [] tm

export
coredrisArglist : {auto c: Ref Ctxt Defs} -> SVars ns -> Term args -> Core (List String, String, List String)
coredrisArglist [] ty = do
  (rty, univs) <- coredrisType ty
  pure ([], rty, univs)
coredrisArglist (x :: xs) (Bind _ _ (Pi _ _ (Ref _ _ name)) sc) = do
  (rest, retty, univs) <- coredrisArglist xs sc
  pure (("(^arg :name " ++ x ++ " :ty " ++ coredrisName !(getFullName name) ++ ")") :: rest, retty, univs)
coredrisArglist (x :: xs) (Bind _ _ (Pi _ _ ty) sc) = do 
  (rest, retty, univs) <- coredrisArglist xs sc
  (ty_, univs') <- coredrisType ty
  pure (("(^arg :name " ++ x ++ " :ty " ++ ty_ ++ ")") :: rest, retty, reverse univs {- ++ univs' -})
coredrisArglist (x :: xs) ty = pure (["error: broken arglist"], show ty, [])

mutual
  coredrisConAlt : Int -> SVars vars -> String -> CConAlt vars -> Core String
  coredrisConAlt {vars} i vs target (MkConAlt n tag args sc)
      = let vs' = extendSVars args vs in
            pure $ "(^con-alt :tag " ++ show tag ++ " :rhs "
                        ++ bindArgs 1 args vs' !(coredrisExp i vs' sc) ++ ")"
    where
      bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
      bindArgs i [] vs body = body
      bindArgs i (n :: ns) (v :: vs) body
          = "(^let-field :var " ++ v ++ " :val " ++ target ++ " :field-ix " ++ show i ++ " " 
          ++ ":body " ++ bindArgs (i + 1) ns vs body ++ ")"

  coredrisConstAlt : Int -> SVars vars -> String -> CConstAlt vars -> Core String
  coredrisConstAlt i vs target (MkConstAlt c exp)
      = pure $ "(^const-alt :var " ++ target ++ " :const " ++ coredrisConstant coredrisStringQuoted c ++ " :body " 
                ++ !(coredrisExp i vs exp) ++ ")"

  -- oops, no traverse for Vect in Core
  coredrisArgs : Int -> SVars vars -> Vect n (CExp vars) -> Core (Vect n String)
  coredrisArgs i vs [] = pure []
  coredrisArgs i vs (arg :: args) = pure $ !(coredrisExp i vs arg) :: !(coredrisArgs i vs args)

  export
  coredrisExp : Int -> SVars vars -> CExp vars -> Core String
  coredrisExp i vs (CLocal fc el) = pure $ lookupSVar el vs
  coredrisExp i vs (CRef fc n) = pure $ coredrisName n
  coredrisExp i vs (CLam fc x sc)
     = do let vs' = extendSVars [x] vs
          sc' <- coredrisExp i vs' sc
          pure $ "(^lam :var " ++ lookupSVar First vs' ++ " :body " ++ sc' 
                          ++ ")"
  coredrisExp i vs (CLet fc x val sc)
     = do let vs' = extendSVars [x] vs
          val' <- coredrisExp i vs val
          sc' <- coredrisExp i vs' sc
          pure $ "(^let :var " ++ lookupSVar First vs' ++ " " ++ val' ++ " :body " ++ 
                                                          sc' ++ ")"
  coredrisExp i vs (CApp fc x [])
      = pure $ "(^call " ++ !(coredrisExp i vs x) ++ ")"
  coredrisExp i vs (CApp fc x args)
      = pure $ "(^app :fn " ++ !(coredrisExp i vs x) ++ " :args [" ++ showSep " " !(traverse (coredrisExp i
                vs) args) ++ "])"
  coredrisExp i vs (CCon fc x tag args)
      = pure $ coredrisConstructor tag !(traverse (coredrisExp i vs) args)
  coredrisExp i vs (COp fc op args)
      = pure $ coredrisOp op !(coredrisArgs i vs args)
  coredrisExp i vs (CExtPrim fc p args)
      = coredrisExtCommon i vs (toPrim p) args
  coredrisExp i vs (CForce fc t) = pure $ "(^force " ++ !(coredrisExp i vs t) ++ ")"
  coredrisExp i vs (CDelay fc t) = pure $ "(^delay " ++ !(coredrisExp i vs t) ++ ")"
  coredrisExp i vs (CConCase fc sc alts def)
      = do tcode <- coredrisExp (i+1) vs sc
           defc <- maybe (pure Nothing) (\v => pure (Just !(coredrisExp i vs v))) def
           let n = "sc" ++ show i
           pure $ "(^con-case :bind-var " ++ n ++ " :bind-body " ++ tcode ++ " :tag-of " ++ n
                   ++ " :cases [" ++ showSep " " !(traverse (coredrisConAlt (i+1) vs n) alts)
                   ++ coredrisCaseDef defc ++ "])"
  coredrisExp i vs (CConstCase fc sc alts def)
      = do defc <- maybe (pure Nothing) (\v => pure (Just !(coredrisExp i vs v))) def
           tcode <- coredrisExp (i+1) vs sc
           let n = "sc" ++ show i
           pure $ "(^const-case :bind-var " ++ n ++ " :bind-body " ++ tcode ++ " :conds ["
                    ++ showSep " " !(traverse (coredrisConstAlt (i+1) vs n) alts) 
                    ++ "]"
                    ++ coredrisIfDef defc ++ ")"
  coredrisExp i vs (CPrimVal fc c) = pure $ coredrisConstant coredrisStringQuoted c
  coredrisExp i vs (CErased fc) = pure "'erased"
  coredrisExp i vs (CCrash fc msg) = pure $ "(^crash " ++ show msg ++ ")"

  coredrisExtCommon : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  coredrisExtCommon i vs PutStr [arg, world]
      = pure $ "('print " ++ !(coredrisExp i vs arg) ++ ") " ++ mkWorld (coredrisConstructor 0 [])
  coredrisExtCommon i vs GetStr [world]
      = pure $ mkWorld "('get-line (current-input-port))"
  coredrisExtCommon i vs PutChar [arg, world]
      = pure $ "('display " ++ !(coredrisExp i vs arg) ++ ") " ++ mkWorld (coredrisConstructor 0 [])
  coredrisExtCommon i vs GetChar [world]
      = pure $ mkWorld "('get-char (current-input-port))"
  coredrisExtCommon i vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ fileOp $ "('file-open "
                                      ++ !(coredrisExp i vs file) ++ " "
                                      ++ !(coredrisExp i vs mode) ++ " "
                                      ++ !(coredrisExp i vs bin) ++ ")"
  coredrisExtCommon i vs FileClose [file, world]
      = pure $ "(blodwen-close-port " ++ !(coredrisExp i vs file) ++ ") " ++ mkWorld (coredrisConstructor 0 [])
  coredrisExtCommon i vs FileReadLine [file, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-get-line " ++ !(coredrisExp i vs file) ++ ")"
  coredrisExtCommon i vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-putstring "
                                        ++ !(coredrisExp i vs file) ++ " "
                                        ++ !(coredrisExp i vs str) ++ ")"
  coredrisExtCommon i vs FileEOF [file, world]
      = pure $ mkWorld $ "(blodwen-eof " ++ !(coredrisExp i vs file) ++ ")"
  coredrisExtCommon i vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(coredrisExp i vs val) ++ ")"
  coredrisExtCommon i vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(coredrisExp i vs ref) ++ ")"
  coredrisExtCommon i vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! "
                           ++ !(coredrisExp i vs ref) ++ " "
                           ++ !(coredrisExp i vs val) ++ ")"
  coredrisExtCommon i vs NewArray [_, size, val, world]
      = pure $ mkWorld $ "(make-vector " ++ !(coredrisExp i vs size) ++ " "
                                         ++ !(coredrisExp i vs val) ++ ")"
  coredrisExtCommon i vs ArrayGet [_, arr, pos, world]
      = pure $ mkWorld $ "(vector-ref " ++ !(coredrisExp i vs arr) ++ " "
                                        ++ !(coredrisExp i vs pos) ++ ")"
  coredrisExtCommon i vs ArraySet [_, arr, pos, val, world]
      = pure $ mkWorld $ "(vector-set! " ++ !(coredrisExp i vs arr) ++ " "
                                         ++ !(coredrisExp i vs pos) ++ " "
                                         ++ !(coredrisExp i vs val) ++ ")"
  coredrisExtCommon i vs VoidElim [_, _]
      = pure "(^err :type 'void-elim)"
  coredrisExtCommon i vs SysOS []
      = pure $ show os
  coredrisExtCommon i vs (Unknown n) args
      = pure $ "(^^" ++ show n ++ " [" ++ "????" ++ "])"
  coredrisExtCommon i vs Stdin [] = pure "(current-input-port)"
  coredrisExtCommon i vs Stdout [] = pure "(current-output-port)"
  coredrisExtCommon i vs Stderr [] = pure "(current-error-port)"
  coredrisExtCommon i vs prim args
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  readArgs : Int -> SVars vars -> CExp vars -> Core String
  readArgs i vs tm = pure $ "(blodwen-read-args " ++ !(coredrisExp i vs tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

-- External primitives which are common to the scheme codegens (they can be
-- overridden)
--
coredrisDef : {auto c : Ref Ctxt Defs} ->
         Name -> CDef -> ClosedTerm -> List String -> Core String
coredrisDef n (MkFun args exp) ty univs = do
  let vs = initSVars args
  (arglist, retty, univList) <- coredrisArglist vs ty
  let univs = "" -- if univList == [] then "" else "<" ++ showSep ", " univList ++ ">"
  let out = "(^fn" ++ -- univs ++
            "\n  :name " ++ coredrisName !(getFullName n) ++ "\n  :args\n  [" ++ concat (intersperse " " arglist)
                             ++ "]\n  :ret " ++ retty ++ "\n  :body " ++ !(coredrisExp 0 vs exp) ++ ")\n"
  pure out
coredrisDef n (MkError exp) _ _
   = pure $ "(define (" ++ coredrisName !(getFullName n) ++ " . any-args) " 
            ++ !(coredrisExp 0 [] exp) ++ ")\n"
coredrisDef n (MkForeign _ _ _) _ _ = pure "" -- compiled by specific back end
coredrisDef n (MkCon t a _) _ _ = pure "" -- Nothing to compile here

debugName 
  : {auto c : Ref Ctxt Defs} -> Context -> String -> Name
  -> Core String
debugName ctxt outfile n = do
  def <- lookupCtxtExact n ctxt
  full <- getFullName n
  case def of
    Nothing => pure $ "(" ++ "undefined name " ++ show n ++ ")"
    Just d => case compexpr d of
      Nothing => pure $ "(" ++ "no compd expr " ++ show n ++ ")"
      Just comp => do
        let ty = type d
        (rty, univs) <- coredrisType ty
        -- coreLift $ do
        --   putStr "// erased args: "
        --   print (eraseArgs d)
        --   putStrLn ""
        --   putStr "// type: "
        --   print rty
        --   putStrLn ""
        --   putStr "// compiled code: "
        --   print comp
        --   putStrLn ""
        --   putStr "// decl name: "
        --   print full
        --   putStrLn "\n"
        genDef <- coredrisDef n comp ty univs
        pure (genDef ++ "\n")

compileToCoredris : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core ()
compileToCoredris c tm outfile = do
  (ns, tags) <- findUsedNames tm
  defs <- get Ctxt
  let g = gamma defs
  out <- traverse (debugName g outfile) ns
  coreLift (writeFile outfile (concat out))
  -- !! coreLift (print tm)
  -- traverse (\n => do
  --   def <- lookupCtxtExact n (gamma defs) 
  --   coreLift $ case def of
  --        Nothing => putStrLn "undefined name"
  --        Just d => case compexpr d of 
  --                       Nothing => putStrLn "no compiled definition"
  --                       Just d' => print d') ns
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
