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
showCoredrisIdent ('"'::cs) = ("-zdq" ++) . showCoredrisIdent cs
showCoredrisIdent ('('::cs) = ("-zop" ++) . showCoredrisIdent cs
showCoredrisIdent (')'::cs) = ("-zcp" ++) . showCoredrisIdent cs
showCoredrisIdent (' '::cs) = ("-zsp" ++) . showCoredrisIdent cs
showCoredrisIdent ('\''::cs) = ("-zpr" ++) . showCoredrisIdent cs
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
data ExtPrim = SomeExtPrim Name

export
Show ExtPrim where
  show (SomeExtPrim n) = "SomeExtPrim " ++ coredrisName n

||| Match on a user given name to get the scheme primitive
toPrim : Name -> ExtPrim
toPrim pn = SomeExtPrim pn

export
mkWorld : String -> String
mkWorld res = "'mk-world"

coredrisConstant : (String -> String) -> Constant -> String
coredrisConstant _ (I x) = "(^constant :type 'int :val " ++ show x ++ ")"
coredrisConstant _ (BI x) = "(^constant :type 'big-int :val " ++ show x ++ ")"
coredrisConstant _ (Db x) = "(^constant :type 'double :val " ++ show x ++ ")"
coredrisConstant _ (Ch x) = "(^constant :type 'char :val '" ++ cast x ++ "')"
coredrisConstant coredrisStringQuoted (Str x) = "(^constant :type 'string :val " ++ coredrisStringQuoted x ++ ")"
coredrisConstant _ WorldVal = "'world"
coredrisConstant _ IntType = "'i32"
coredrisConstant _ IntegerType = "'i64"
coredrisConstant _ StringType = "'string"
coredrisConstant _ CharType = "'char"
coredrisConstant _ DoubleType = "'f64"
coredrisConstant _ WorldType = "'f32"

coredrisCaseDef : Maybe String -> String
coredrisCaseDef Nothing = ""
coredrisCaseDef (Just tm) = " :default " ++ tm

coredrisIfDef : Maybe String -> String
coredrisIfDef Nothing = ""
coredrisIfDef (Just tm) = " :default " ++ tm

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

coredrisType 
  : {auto c: Ref Ctxt Defs} -> Term args 
  -> Core (String, List String)
coredrisType tm = coredrisType' [] tm

export
coredrisArglist 
  : {auto c: Ref Ctxt Defs} -> List Name -> Term args 
  -> Core (List String, String, List String)
coredrisArglist nms ty = do
  (rty, univs) <- coredrisType ty
  pure ([], rty, univs)
coredrisArglist (n :: ns) (Bind _ _ (Pi _ _ (Ref _ _ name)) sc) = do
  (rest, retty, univs) <- coredrisArglist ns sc
  pure (("(^arg :name " ++ coredrisName n ++ " :ty " ++ coredrisName !(getFullName name) ++ ")") :: rest, retty, univs)
coredrisArglist (n :: ns) (Bind _ _ (Pi _ _ ty) sc) = do 
  (rest, retty, univs) <- coredrisArglist ns sc
  (ty_, univs') <- coredrisType ty
  pure (("(^arg :name " ++ coredrisName n ++ " :ty " ++ ty_ ++ ")") :: rest, retty, reverse univs {- ++ univs' -})
coredrisArglist _ ty = pure (["error: broken arglist"], show ty, [])

mutual
  coredrisConAlt : Int -> String -> NamedConAlt -> Core String
  coredrisConAlt i target (MkNConAlt n tag args sc)
      = pure $ "(^con-alt :tag " ++ show tag ++ " :rhs "
                        ++ bindArgs 1 args !(coredrisExp i sc) ++ ")"
    where
      bindArgs : Int -> List Name -> String -> String
      bindArgs i [] body = body
      bindArgs i (n :: ns) body
          = "(^let-field :var " ++ coredrisName n ++ " :val " ++ target ++ " :field-ix " ++ show i ++ " " 
          ++ ":body " ++ bindArgs (i + 1) ns body ++ ")"

  coredrisConstAlt : Int -> String -> NamedConstAlt -> Core String
  coredrisConstAlt i target (MkNConstAlt c exp)
      = pure $ "(^const-alt :var " ++ target ++ " :const " ++ coredrisConstant coredrisStringQuoted c ++ " :body " 
                ++ !(coredrisExp i exp) ++ ")"

  -- oops, no traverse for Vect in Core
  coredrisArgs : Int -> Vect n NamedCExp -> Core (Vect n String)
  coredrisArgs i [] = pure []
  coredrisArgs i (arg :: args) = pure $ !(coredrisExp i arg) :: !(coredrisArgs i args)

  export
  coredrisExp : Int -> NamedCExp -> Core String
  coredrisExp i (NmLocal fc n) = pure $ coredrisName n
  coredrisExp i (NmRef fc n) = pure $ coredrisName n
  coredrisExp i (NmLam fc x sc)
     = do sc' <- coredrisExp i sc
          pure $ "(^lam :var " ++ coredrisName x ++ " :body " ++ sc' ++ ")"
  coredrisExp i (NmLet fc x val sc)
     = do val' <- coredrisExp i val
          sc' <- coredrisExp i sc
          pure $ "(^let :var " ++ coredrisName x ++ " :val " 
                  ++ val' ++ " :body " ++ sc' ++ ")"
  coredrisExp i (NmApp fc x [])
      = pure $ "(^call " ++ !(coredrisExp i x) ++ ")"
  coredrisExp i (NmApp fc x args)
      = pure $ "(^app :fn " ++ !(coredrisExp i x) ++ " :args [" 
                ++ showSep " " !(traverse (coredrisExp i) args) ++ "])"
  coredrisExp i (NmCon fc x tag args)
      = pure $ coredrisConstructor tag !(traverse (coredrisExp i) args)
  coredrisExp i (NmOp fc op args)
      = pure $ coredrisOp op !(coredrisArgs i args)
  coredrisExp i (NmExtPrim fc p args)
      = coredrisExtCommon i (toPrim p) args
  coredrisExp i (NmForce fc t) = pure $ "(^force " ++ !(coredrisExp i t) ++ ")"
  coredrisExp i (NmDelay fc t) = pure $ "(^delay " ++ !(coredrisExp i t) ++ ")"
  coredrisExp i (NmConCase fc sc alts def)
      = do tcode <- coredrisExp (i+1) sc
           defc <- maybe (pure Nothing) (\v => pure (Just !(coredrisExp i v))) def
           let n = "sc" ++ show i
           pure $ "(^con-case :bind-var " ++ n ++ " :bind-body " 
                   ++ tcode ++ " :tag-of " ++ n ++ " :cases [" 
                   ++ showSep " " !(traverse (coredrisConAlt (i+1) n) alts) ++ "]"
                   ++ coredrisCaseDef defc ++ ")"
  coredrisExp i (NmConstCase fc sc alts def)
      = do tcode <- coredrisExp (i+1) sc
           defc <- maybe (pure Nothing) (\v => pure (Just !(coredrisExp i v))) def
           let n = "sc" ++ show i
           pure $ "(^const-case :bind-var " ++ n ++ " :bind-body " ++ tcode 
                   ++ " :conds ["
                   ++ showSep " " !(traverse (coredrisConstAlt (i+1) n) alts) 
                   ++ "]" ++ coredrisIfDef defc ++ ")"
  coredrisExp i (NmPrimVal fc c) = pure $ coredrisConstant coredrisStringQuoted c
  coredrisExp i (NmErased fc) = pure "'erased"
  coredrisExp i (NmCrash fc msg) = pure $ "(^crash " ++ show msg ++ ")"

  coredrisExtCommon : Int -> ExtPrim -> List NamedCExp -> Core String
  coredrisExtCommon i (SomeExtPrim n) args
      = pure $ "(^ext-prim-app :name " ++ coredrisName n ++ " :args [" 
                ++ showSep " " !(traverse (coredrisExp i) args) ++ "])"

  readArgs : Int -> NamedCExp -> Core String
  readArgs i tm = pure $ "(blodwen-read-args " ++ !(coredrisExp i tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

-- External primitives which are common to the scheme codegens (they can be
-- overridden)
--
coredrisDef : {auto c : Ref Ctxt Defs} ->
         Name -> NamedDef -> ClosedTerm -> List String -> Core String
coredrisDef n (MkNmFun args exp) ty univs = do
  (arglist, retty, univList) <- coredrisArglist args ty
  let univs = "" -- if univList == [] then "" else "<" ++ showSep ", " univList ++ ">"
  let out = "(^fn" ++ "\n  :name " ++ coredrisName !(getFullName n) 
               ++ "\n  :args  [" ++ showSep " " (map coredrisName args) ++ "]"
               -- ++ "\n  :ret " ++ retty ++ "\n" ++
               ++ "\n  :body " ++ !(coredrisExp 0 exp) ++ ")\n"
  pure out
coredrisDef n (MkNmError exp) _ _
   = pure $ "(^def (" ++ coredrisName !(getFullName n) ++ " . 'any-args) " 
            ++ !(coredrisExp 0 exp) ++ ")\n"
coredrisDef n (MkNmForeign _ _ _) _ _ = pure "" -- compiled by specific back end
coredrisDef n (MkNmCon t a _) _ _ = pure "" -- Nothing to compile here

debugName 
  : {auto c : Ref Ctxt Defs} -> Context -> String -> Name
  -> Core String
debugName ctxt outfile n = do
  def <- lookupCtxtExact n ctxt
  full <- getFullName n
  case def of
    Nothing => pure $ "(" ++ "undefined name " ++ show n ++ ")"
    Just d => case namedcompexpr d of
      Nothing => pure $ "(" ++ "no compd expr " ++ show n ++ ")"
      Just ncomp => do
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
        genDef <- coredrisDef n ncomp ty univs
        pure (genDef ++ "\n")

coredrisTm : Term args -> String
coredrisTm (Erased _ _) = "'erased"
coredrisTm (Ref _ _ n) = coredrisName n
coredrisTm (App _ fn args) = "(^app :fn " ++ coredrisTm fn ++ " :args [" ++ coredrisTm args ++ "])"
coredrisTm x = "(^error " ++ show x ++ ")"

compileToCoredris : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core ()
compileToCoredris c tm outfile = do
  (ns, tags) <- findUsedNames tm
  defs <- get Ctxt
  let g = gamma defs
  out <- traverse (debugName g outfile) ns
  coreLift (writeFile outfile (concat out ++ "\n" ++ coredrisTm tm))
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
