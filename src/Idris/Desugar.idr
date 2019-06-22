module Idris.Desugar

import Core.Binary
import Core.Context
import Core.Core
import Core.Env
import Core.Metadata
import Core.Options
import Core.TT
import Core.Unify

import Data.StringMap
import Data.ANameMap

import Idris.Syntax

import Idris.Elab.Implementation
import Idris.Elab.Interface

import Parser.Lexer

import TTImp.BindImplicits
import TTImp.Parser
import TTImp.TTImp
import TTImp.Utils

import Utils.Shunting

import Control.Monad.State

-- Convert high level Idris declarations (PDecl from Idris.Syntax) into
-- TTImp, recording any high level syntax info on the way (e.g. infix
-- operators)

-- Desugaring from high level Idris syntax to TTImp involves:

-- Done:
-- * Shunting infix operators into function applications according to precedence
-- * Replacing 'do' notating with applications of (>>=)
-- * Replacing pattern matching binds with 'case'
-- * Changing tuples to 'Pair/MkPair'
-- * List notation

-- Still TODO:
-- * Replacing !-notation
-- * Dependent pair notation
-- * Idiom brackets

%default covering

public export
data Side = LHS | AnyExpr

export
extendAs : {auto s : Ref Syn SyntaxInfo} ->
           List String -> List String -> SyntaxInfo -> Core ()
extendAs old as newsyn
    = do syn <- get Syn
         put Syn (record { infixes $= mergeLeft (infixes newsyn),
                           prefixes $= mergeLeft (prefixes newsyn),
                           ifaces $= mergeAs old as (ifaces newsyn),
                           bracketholes $= ((bracketholes newsyn) ++) } 
                  syn)

mkPrec : Fixity -> Nat -> OpPrec
mkPrec InfixL p = AssocL p
mkPrec InfixR p = AssocR p
mkPrec Infix p = NonAssoc p
mkPrec Prefix p = Prefix p

toTokList : {auto s : Ref Syn SyntaxInfo} ->
            PTerm -> Core (List (Tok OpStr PTerm))
toTokList (POp fc opn l r)
    = do syn <- get Syn
         let op = nameRoot opn
         case lookup op (infixes syn) of
              Nothing => 
                let ops = unpack opChars in
                    if any (\x => x `elem` ops) (unpack op)
                       then throw (GenericMsg fc $ "Unknown operator '" ++ op ++ "'")
                       else do rtoks <- toTokList r
                               pure (Expr l :: Op fc opn backtickPrec :: rtoks)
              Just (Prefix, _) =>
                      throw (GenericMsg fc $ "'" ++ op ++ "' is a prefix operator")
              Just (fix, prec) =>
                   do rtoks <- toTokList r
                      pure (Expr l :: Op fc opn (mkPrec fix prec) :: rtoks)
  where
    backtickPrec : OpPrec
    backtickPrec = NonAssoc 10
toTokList (PPrefixOp fc opn arg)
    = do syn <- get Syn
         let op = nameRoot opn
         case lookup op (prefixes syn) of
              Nothing =>
                   throw (GenericMsg fc $ "'" ++ op ++ "' is not a prefix operator")
              Just prec =>
                   do rtoks <- toTokList arg
                      pure (Op fc opn (Prefix prec) :: rtoks)
toTokList t = pure [Expr t]

mutual
  export
  desugar : {auto s : Ref Syn SyntaxInfo} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto m : Ref MD Metadata} ->
            Side -> List Name -> PTerm -> Core RawImp
  desugar side ps (PRef fc x) = pure $ IVar fc x
  desugar side ps (PPi fc rig p mn argTy retTy) 
      = let ps' = maybe ps (:: ps) mn in
            pure $ IPi fc rig p mn !(desugar side ps argTy) 
                                   !(desugar side ps' retTy)
  desugar side ps (PLam fc rig p n argTy scope) 
      = pure $ ILam fc rig p (Just n) !(desugar side ps argTy) 
                                      !(desugar side (n :: ps) scope)
  desugar side ps (PLet fc rig (PRef _ n) nTy nVal scope [])
      = pure $ ILet fc rig n !(desugar side ps nTy) !(desugar side ps nVal) 
                             !(desugar side (n :: ps) scope)
  desugar side ps (PLet fc rig pat nTy nVal scope alts) 
      = pure $ ICase fc !(desugar side ps nVal) !(desugar side ps nTy)
                        !(traverse (desugarClause ps True) 
                            (MkPatClause fc pat scope [] :: alts))
  desugar side ps (PCase fc x xs) 
      = pure $ ICase fc !(desugar side ps x) 
                        (Implicit fc False)
                        !(traverse (desugarClause ps True) xs)
  desugar side ps (PLocal fc xs scope) 
      = pure $ ILocal fc (concat !(traverse (desugarDecl ps) xs)) 
                         !(desugar side (definedIn xs ++ ps) scope)
  desugar side ps (PApp pfc (PUpdate fc fs) rec)
      = pure $ IUpdate pfc !(traverse (desugarUpdate side ps) fs)
                           !(desugar side ps rec)
  desugar side ps (PUpdate fc fs)
      = desugar side ps (PLam fc RigW Explicit (MN "rec" 0) (PImplicit fc)
                            (PApp fc (PUpdate fc fs) (PRef fc (MN "rec" 0))))
  desugar side ps (PApp fc x y) 
      = pure $ IApp fc !(desugar side ps x) !(desugar side ps y)
  desugar side ps (PImplicitApp fc x argn y) 
      = pure $ IImplicitApp fc !(desugar side ps x) argn !(desugar side ps y)
  desugar side ps (PDelayed fc r ty)
      = pure $ IDelayed fc r !(desugar side ps ty)
  desugar side ps (PDelay fc tm)
      = pure $ IDelay fc !(desugar side ps tm)
  desugar side ps (PForce fc tm)
      = pure $ IForce fc !(desugar side ps tm)
  desugar side ps (PEq fc l r)
      = do l' <- desugar side ps l
           r' <- desugar side ps r
           pure $ apply (IVar fc (UN "Equal")) [l', r']
  desugar side ps (PBracketed fc e) = desugar side ps e
  desugar side ps (POp fc op l r) 
      = do ts <- toTokList (POp fc op l r)
           desugarTree side ps !(parseOps ts)
  desugar side ps (PPrefixOp fc op arg) 
      = do ts <- toTokList (PPrefixOp fc op arg)
           desugarTree side ps !(parseOps ts)
  desugar side ps (PSectionL fc op arg) 
      = do syn <- get Syn
           -- It might actually be a prefix argument rather than a section
           -- so check that first, otherwise desugar as a lambda
           case lookup (nameRoot op) (prefixes syn) of
                Nothing => 
                   desugar side ps (PLam fc RigW Explicit (MN "arg" 0) (PImplicit fc)
                               (POp fc op (PRef fc (MN "arg" 0)) arg))
                Just prec => desugar side ps (PPrefixOp fc op arg)
  desugar side ps (PSectionR fc arg op)
      = desugar side ps (PLam fc RigW Explicit (MN "arg" 0) (PImplicit fc)
                 (POp fc op arg (PRef fc (MN "arg" 0))))
  desugar side ps (PSearch fc depth) = pure $ ISearch fc depth
  desugar side ps (PPrimVal fc (BI x))
      = case !fromIntegerName of
             Nothing =>
                pure $ IAlternative fc (UniqueDefault (IPrimVal fc (BI x)))
                                [IPrimVal fc (BI x),
                                 IPrimVal fc (I (fromInteger x))]
             Just fi => pure $ IApp fc (IVar fc fi) 
                                       (IPrimVal fc (BI x))
  desugar side ps (PPrimVal fc (Str x))
      = case !fromStringName of
             Nothing =>
                pure $ IPrimVal fc (Str x)
             Just f => pure $ IApp fc (IVar fc f) 
                                      (IPrimVal fc (Str x))
  desugar side ps (PPrimVal fc (Ch x))
      = case !fromCharName of
             Nothing =>
                pure $ IPrimVal fc (Ch x)
             Just f => pure $ IApp fc (IVar fc f) 
                                      (IPrimVal fc (Ch x))
  desugar side ps (PPrimVal fc x) = pure $ IPrimVal fc x
  desugar side ps (PQuote fc x) 
      = throw (GenericMsg fc "Reflection not implemeted yet")
--       = pure $ IQuote fc !(desugar side ps x)
  desugar side ps (PUnquote fc x) 
      = throw (GenericMsg fc "Reflection not implemeted yet")
--       = pure $ IUnquote fc !(desugar side ps x)
  desugar side ps (PHole fc br holename) 
      = do when br $
              do syn <- get Syn
                 put Syn (record { bracketholes $= ((UN holename) ::) } syn)
           pure $ IHole fc holename
  desugar side ps (PType fc) = pure $ IType fc
  desugar side ps (PAs fc vname pattern) 
      = pure $ IAs fc UseRight vname !(desugar side ps pattern)
  desugar side ps (PDotted fc x) 
      = pure $ IMustUnify fc "User dotted" !(desugar side ps x)
  desugar side ps (PImplicit fc) = pure $ Implicit fc True
  desugar side ps (PInfer fc) = pure $ Implicit fc False
  desugar side ps (PDoBlock fc block)
      = expandDo side ps fc block
  desugar side ps (PList fc args)
      = expandList side ps fc args
  desugar side ps (PPair fc l r) 
      = do l' <- desugar side ps l
           r' <- desugar side ps r
           let pval = apply (IVar fc (UN "MkPair")) [l', r']
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar fc (UN "Pair")) [l', r'], pval]
  desugar side ps (PDPair fc (PRef nfc (UN n)) (PImplicit _) r) 
      = do r' <- desugar side ps r
           let pval = apply (IVar fc (UN "MkDPair")) [IVar nfc (UN n), r']
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar fc (UN "DPair")) 
                      [Implicit nfc False, 
                       ILam nfc RigW Explicit (Just (UN n)) (Implicit nfc False) r'],
                   pval]
  desugar side ps (PDPair fc (PRef nfc (UN n)) ty r) 
      = do ty' <- desugar side ps ty
           r' <- desugar side ps r
           pure $ apply (IVar fc (UN "DPair"))
                        [ty', 
                         ILam nfc RigW Explicit (Just (UN n)) ty' r']
  desugar side ps (PDPair fc l (PImplicit _) r) 
      = do l' <- desugar side ps l
           r' <- desugar side ps r
           pure $ apply (IVar fc (UN "MkDPair")) [l', r']
  desugar side ps (PDPair fc l ty r) 
      = throw (GenericMsg fc "Invalid dependent pair type")
  desugar side ps (PUnit fc) 
      = pure $ IAlternative fc (UniqueDefault (IVar fc (UN "MkUnit")))
               [IVar fc (UN "Unit"), 
                IVar fc (UN "MkUnit")]
  desugar side ps (PIfThenElse fc x t e)
      = pure $ ICase fc !(desugar side ps x) (Implicit fc False)
                   [PatClause fc (IVar fc (UN "True")) !(desugar side ps t),
                    PatClause fc (IVar fc (UN "False")) !(desugar side ps e)]
  desugar side ps (PComprehension fc ret conds)
      = desugar side ps (PDoBlock fc (map guard conds ++ [toPure ret]))
    where
      guard : PDo -> PDo
      guard (DoExp fc tm) = DoExp fc (PApp fc (PRef fc (UN "guard")) tm)
      guard d = d

      toPure : PTerm -> PDo
      toPure tm = DoExp fc (PApp fc (PRef fc (UN "pure")) tm)
  desugar side ps (PRewrite fc rule tm)
      = pure $ IRewrite fc !(desugar side ps rule) !(desugar side ps tm)

  desugarUpdate : {auto s : Ref Syn SyntaxInfo} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto m : Ref MD Metadata} ->
                  Side -> List Name -> PFieldUpdate -> Core IFieldUpdate
  desugarUpdate side ps (PSetField p v)
      = pure (ISetField p !(desugar side ps v))
  desugarUpdate side ps (PSetFieldApp p v)
      = pure (ISetFieldApp p !(desugar side ps v))

  expandList : {auto s : Ref Syn SyntaxInfo} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto m : Ref MD Metadata} ->
               Side -> List Name -> FC -> List PTerm -> Core RawImp
  expandList side ps fc [] = pure (IVar fc (UN "Nil"))
  expandList side ps fc (x :: xs)
      = pure $ apply (IVar fc (UN "::")) 
                [!(desugar side ps x), !(expandList side ps fc xs)]

  expandDo : {auto s : Ref Syn SyntaxInfo} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto m : Ref MD Metadata} ->
             Side -> List Name -> FC -> List PDo -> Core RawImp
  expandDo side ps fc [] = throw (GenericMsg fc "Do block cannot be empty")
  expandDo side ps _ [DoExp fc tm] = desugar side ps tm
  expandDo side ps fc [e] 
      = throw (GenericMsg (getLoc e) 
                  "Last statement in do block must be an expression") 
  expandDo side ps topfc (DoExp fc tm :: rest)
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc rest
           gam <- get Ctxt
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                          (ILam fc RigW Explicit Nothing 
                                (Implicit fc False) rest')
  expandDo side ps topfc (DoBind fc n tm :: rest)
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                     (ILam fc RigW Explicit (Just n) 
                           (Implicit fc False) rest')
  expandDo side ps topfc (DoBindPat fc pat exp alts :: rest)
      = do pat' <- desugar LHS ps pat
           (newps, bpat) <- bindNames False pat'
           exp' <- desugar side ps exp
           alts' <- traverse (desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) exp')
                    (ILam fc RigW Explicit (Just (MN "_" 0)) 
                          (Implicit fc False)
                          (ICase fc (IVar fc (MN "_" 0))
                               (Implicit fc False)
                               (PatClause fc bpat rest' 
                                  :: alts')))
  expandDo side ps topfc (DoLet fc n rig tm :: rest) 
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc rest
           pure $ ILet fc rig n (Implicit fc False) tm' rest'
  expandDo side ps topfc (DoLetPat fc pat tm alts :: rest) 
      = do pat' <- desugar LHS ps pat
           (newps, bpat) <- bindNames False pat'
           tm' <- desugar side ps tm
           alts' <- traverse (desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc rest
           pure $ ICase fc tm' (Implicit fc False) 
                       (PatClause fc bpat rest'
                                  :: alts')
  expandDo side ps topfc (DoLetLocal fc decls :: rest)
      = do rest' <- expandDo side ps topfc rest
           decls' <- traverse (desugarDecl ps) decls
           pure $ ILocal fc (concat decls') rest'
  expandDo side ps topfc (DoRewrite fc rule :: rest)
      = do rest' <- expandDo side ps topfc rest
           rule' <- desugar side ps rule
           pure $ IRewrite fc rule' rest'

  desugarTree : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                Side -> List Name -> Tree OpStr PTerm -> Core RawImp
  desugarTree side ps (Inf loc (UN "=") l r) -- special case since '=' is special syntax
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IApp loc (IApp loc (IVar loc (UN "Equal")) l') r')
  desugarTree side ps (Inf loc (UN "$") l r) -- special case since '$' is special syntax
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IApp loc l' r')
  desugarTree side ps (Inf loc op l r)
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IApp loc (IApp loc (IVar loc op) l') r')
  -- negation is a special case, since we can't have an operator with
  -- two meanings otherwise
  desugarTree side ps (Pre loc (UN "-") arg)
      = do arg' <- desugarTree side ps arg
           pure (IApp loc (IVar loc (UN "negate")) arg')
  desugarTree side ps (Pre loc op arg)
      = do arg' <- desugarTree side ps arg
           pure (IApp loc (IVar loc op) arg')
  desugarTree side ps (Leaf t) = desugar side ps t

  desugarType : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                List Name -> PTypeDecl -> Core ImpTy
  desugarType ps (MkPTy fc n ty) 
      = pure $ MkImpTy fc n !(bindTypeNames ps !(desugar AnyExpr ps ty))

  desugarClause : {auto s : Ref Syn SyntaxInfo} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto m : Ref MD Metadata} ->
                  List Name -> Bool -> PClause -> Core ImpClause
  desugarClause ps arg (MkPatClause fc lhs rhs wheres)
      = do ws <- traverse (desugarDecl ps) wheres
           (bound, blhs) <- bindNames arg !(desugar LHS ps lhs)
           rhs' <- desugar AnyExpr (bound ++ ps) rhs
           pure $ PatClause fc blhs 
                     (case ws of
                           [] => rhs'
                           _ => ILocal fc (concat ws) rhs')
  desugarClause ps arg (MkWithClause fc lhs wval cs)
      = do cs' <- traverse (desugarClause ps arg) cs
           (bound, blhs) <- bindNames arg !(desugar LHS ps lhs)
           wval' <- desugar AnyExpr (bound ++ ps) wval
           pure $ WithClause fc blhs wval' cs'
  desugarClause ps arg (MkImpossible fc lhs)
      = do dlhs <- desugar LHS ps lhs
           pure $ ImpossibleClause fc (snd !(bindNames arg dlhs))

  desugarData : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                List Name -> PDataDecl -> Core ImpData
  desugarData ps (MkPData fc n tycon opts datacons) 
      = pure $ MkImpData fc n !(bindTypeNames ps !(desugar AnyExpr ps tycon))
                              opts
                              !(traverse (desugarType ps) datacons)
  desugarData ps (MkPLater fc n tycon) 
      = pure $ MkImpLater fc n !(bindTypeNames ps !(desugar AnyExpr ps tycon))

  desugarField : {auto s : Ref Syn SyntaxInfo} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {auto m : Ref MD Metadata} ->
                 List Name -> PField -> 
                 Core IField
  desugarField ps (MkField fc rig p n ty)
      = pure (MkIField fc rig p n !(bindTypeNames ps !(desugar AnyExpr ps ty)))

  -- Get the declaration to process on each pass of a mutual block
  -- Essentially: types on the first pass 
  --    i.e. type constructors of data declarations
  --         function types
  --         interfaces (in full, since it includes function types)
  --         records (in full, similarly)
  --         implementation headers (i.e. note their existence, but not the bodies)
  -- Everything else on the second pass
  getDecl : Pass -> PDecl -> Maybe PDecl
  getDecl p (PImplementation fc vis _ cons n ps iname ds)
      = Just (PImplementation fc vis p cons n ps iname ds)

  getDecl p (PNamespace fc ns ds)
      = Just (PNamespace fc ns (mapMaybe (getDecl p) ds))

  getDecl AsType d@(PClaim _ _ _ _) = Just d
  getDecl AsType (PData fc vis (MkPData dfc tyn tyc opts cons))
      = Just (PData fc vis (MkPLater dfc tyn tyc))
  getDecl AsType d@(PInterface fc vis cons n ps det cname ds) = Just d
  getDecl AsType d@(PRecord fc vis n ps con fs) = Just d
  getDecl AsType d@(PFixity _ _ _ _) = Just d
  getDecl AsType d@(PDirective _ _) = Just d
  getDecl AsType d = Nothing

  getDecl AsDef (PClaim _ _ _ _) = Nothing
  getDecl AsDef (PData fc vis (MkPLater dfc tyn tyc)) = Nothing
  getDecl AsDef (PInterface fc vis cons n ps det cname ds) = Nothing
  getDecl AsDef (PRecord fc vis n ps con fs) = Nothing
  getDecl AsDef (PFixity _ _ _ _) = Nothing
  getDecl AsDef (PDirective _ _) = Nothing
  getDecl AsDef d = Just d
  
  getDecl p (PParameters fc ps pds) 
      = Just (PParameters fc ps (mapMaybe (getDecl p) pds))

  getDecl Single d = Just d

  -- Given a high level declaration, return a list of TTImp declarations
  -- which process it, and update any necessary state on the way.
  export
  desugarDecl : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                List Name -> PDecl -> Core (List ImpDecl)
  desugarDecl ps (PClaim fc vis opts ty) 
      = pure [IClaim fc RigW vis opts !(desugarType ps ty)]
  desugarDecl ps (PDef fc clauses) 
  -- The clauses won't necessarily all be from the same function, so split
  -- after desugaring, by function name, using collectDefs from RawImp
      = do cs <- traverse (desugarClause ps False) clauses
           defs <- traverse toIDef cs
           pure (collectDefs defs) 
    where
      getFn : RawImp -> Core Name
      getFn (IVar _ n) = pure n
      getFn (IApp _ f a) = getFn f
      getFn (IImplicitApp _ f _ a) = getFn f
      getFn tm = throw (InternalError (show tm ++ " is not a function application"))

      toIDef : ImpClause -> Core ImpDecl
      toIDef (PatClause fc lhs rhs) 
          = pure $ IDef fc !(getFn lhs) [PatClause fc lhs rhs]
      toIDef (WithClause fc lhs rhs cs) 
          = pure $ IDef fc !(getFn lhs) [WithClause fc lhs rhs cs]
      toIDef (ImpossibleClause fc lhs) 
          = pure $ IDef fc !(getFn lhs) [ImpossibleClause fc lhs]

  desugarDecl ps (PData fc vis ddecl) 
      = pure [IData fc vis !(desugarData ps ddecl)]
  desugarDecl ps (PParameters fc params pds)
      = do pds' <- traverse (desugarDecl (ps ++ map fst params)) pds
           params' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                            pure (fst ntm, tm')) params
           -- Look for implicitly bindable names in the parameters
           let pnames = concatMap (findBindableNames True
                                    (ps ++ map fst params) [])
                                    (map snd params')
           let paramsb = map (\ (n, tm) => (n, doBind pnames tm)) params'
           pure [IParameters fc paramsb (concat pds')]
  desugarDecl ps (PReflect fc tm)
      = throw (GenericMsg fc "Reflection not implemented yet")
--       pure [IReflect fc !(desugar AnyExpr ps tm)]
  desugarDecl ps (PInterface fc vis cons tn params det conname body)
      = do cons' <- traverse (\ ntm => do tm' <- desugar AnyExpr (ps ++ map fst params)
                                                         (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                            pure (fst ntm, tm')) params
           -- Look for bindable names in all the constraints and parameters
           let mnames = map dropNS (definedIn body)
           let bnames = concatMap (findBindableNames True 
                                      (ps ++ mnames ++ map fst params) []) 
                                  (map snd cons') ++
                        concatMap (findBindableNames True 
                                      (ps ++ mnames ++ map fst params) []) 
                                  (map snd params')
           let paramsb = map (\ (n, tm) => (n, doBind bnames tm)) params'
           let consb = map (\ (n, tm) => (n, doBind bnames tm)) cons'

           body' <- traverse (desugarDecl (ps ++ mnames ++ map fst params)) body
           pure [IPragma (\c, nest, env => 
                             elabInterface fc vis env nest consb
                                           tn paramsb det conname 
                                           (concat body'))]
  desugarDecl ps (PImplementation fc vis pass cons tn params impname body)
      = do cons' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- traverse (desugar AnyExpr ps) params
           -- Look for bindable names in all the constraints and parameters
           let bnames = concatMap (findBindableNames True ps []) (map snd cons') ++
                        concatMap (findBindableNames True ps []) params'
           let paramsb = map (doBind bnames) params'
           let consb = map (\ (n, tm) => (n, doBind bnames tm)) cons'

           body' <- maybe (pure Nothing)
                          (\b => do b' <- traverse (desugarDecl ps) b
                                    pure (Just (concat b'))) body
           pure [IPragma (\c, nest, env =>
                             elabImplementation fc vis pass env nest consb
                                                tn paramsb impname 
                                                body')]
  desugarDecl ps (PRecord fc vis tn params conname fields)
      = do params' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                            pure (fst ntm, tm')) params
           let fnames = map fname fields
           -- Look for bindable names in the parameters
           let bnames = concatMap (findBindableNames True 
                                      (ps ++ fnames ++ map fst params) []) 
                                  (map snd params')
           fields' <- traverse (desugarField (ps ++ fnames ++ map fst params))
                               fields
           let paramsb = map (\ (n, tm) => (n, doBind bnames tm)) params'
           fields' <- traverse (desugarField (ps ++ map fname fields ++
                                              map fst params)) fields
           pure [IRecord fc vis (MkImpRecord fc tn paramsb conname fields')]
    where
      fname : PField -> Name
      fname (MkField _ _ _ n _) = n
  desugarDecl ps (PFixity fc Prefix prec (UN n)) 
      = do syn <- get Syn
           put Syn (record { prefixes $= insert n prec } syn)
           pure []
  desugarDecl ps (PFixity fc fix prec (UN n)) 
      = do syn <- get Syn
           put Syn (record { infixes $= insert n (fix, prec) } syn)
           pure []
  desugarDecl ps (PFixity fc _ _ _)
      = throw (GenericMsg fc "Fixity declarations must be for unqualified names")
  desugarDecl ps (PMutual fc ds)
      = do let mds = mapMaybe (getDecl AsType) ds ++ mapMaybe (getDecl AsDef) ds
           mds' <- traverse (desugarDecl ps) mds
           pure (concat mds')
  desugarDecl ps (PNamespace fc ns decls)
      = do ds <- traverse (desugarDecl ps) decls
           pure [INamespace fc ns (concat ds)]
  desugarDecl ps (PDirective fc d) 
      = case d of
             Hide n => pure [IPragma (\c, nest, env => hide fc n)]
             Logging i => pure [ILog i]
             LazyOn a => pure [IPragma (\c, nest, env => lazyActive a)]
             PairNames ty f s => pure [IPragma (\c, nest, env => setPair fc ty f s)]
             RewriteName eq rw => pure [IPragma (\c, nest, env => setRewrite fc eq rw)]
             PrimInteger n => pure [IPragma (\c, nest, env => setFromInteger n)]
             PrimString n => pure [IPragma (\c, nest, env => setFromString n)]
             PrimChar n => pure [IPragma (\c, nest, env => setFromChar n)]
             CGAction cg dir => pure [IPragma (\c, nest, env => addDirective cg dir)]
             Names n ns => pure [IPragma (\c, nest, env => addNameDirective fc n ns)]
             StartExpr tm => pure [IPragma (\c, nest, env => throw (InternalError "%start not implemented"))] -- TODO!
             Overloadable n => pure [IPragma (\c, nest, env => setNameFlag fc n Overloadable)]
             Extension e => pure [IPragma (\c, nest, env => setExtension e)]

