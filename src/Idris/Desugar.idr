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

-- * Shunting infix operators into function applications according to precedence
-- * Replacing 'do' notating with applications of (>>=)
-- * Replacing pattern matching binds with 'case'
-- * Changing tuples to 'Pair/MkPair'
-- * List notation
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
                  if any isOpChar (unpack op)
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
    backtickPrec = NonAssoc 1
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

record BangData where
  constructor MkBangData
  nextName : Int
  bangNames : List (Name, FC, RawImp)

initBangs : BangData
initBangs = MkBangData 0 []

bindBangs : List (Name, FC, RawImp) -> RawImp -> RawImp
bindBangs [] tm = tm
bindBangs ((n, fc, btm) :: bs) tm
    = bindBangs bs $ IApp fc (IApp fc (IVar fc (UN ">>=")) btm)
                          (ILam fc top Explicit (Just n)
                                (Implicit fc False) tm)

idiomise : FC -> RawImp -> RawImp
idiomise fc (IApp afc f a)
    = IApp fc (IApp fc (IVar fc (UN "<*>"))
                    (idiomise afc f))
                    a
idiomise fc fn = IApp fc (IVar fc (UN "pure")) fn

pairname : Name
pairname = NS ["Builtin"] (UN "Pair")

mkpairname : Name
mkpairname = NS ["Builtin"] (UN "MkPair")

dpairname : Name
dpairname = NS ["DPair", "Builtin"] (UN "DPair")

mkdpairname : Name
mkdpairname = NS ["DPair", "Builtin"] (UN "MkDPair")

data Bang : Type where

mutual
  desugarB : {auto s : Ref Syn SyntaxInfo} ->
             {auto b : Ref Bang BangData} ->
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref MD Metadata} ->
             {auto u : Ref UST UState} ->
             Side -> List Name -> PTerm -> Core RawImp
  desugarB side ps (PRef fc x) = pure $ IVar fc x
  desugarB side ps (PPi fc rig p mn argTy retTy)
      = let ps' = maybe ps (:: ps) mn in
            pure $ IPi fc rig !(traverse (desugar side ps') p)
                              mn !(desugarB side ps argTy)
                                 !(desugarB side ps' retTy)
  desugarB side ps (PLam fc rig p (PRef _ n@(UN _)) argTy scope)
      = pure $ ILam fc rig !(traverse (desugar side ps) p)
                           (Just n) !(desugarB side ps argTy)
                                    !(desugar side (n :: ps) scope)
  desugarB side ps (PLam fc rig p (PRef _ n@(MN _ _)) argTy scope)
      = pure $ ILam fc rig !(traverse (desugar side ps) p)
                           (Just n) !(desugarB side ps argTy)
                                    !(desugar side (n :: ps) scope)
  desugarB side ps (PLam fc rig p (PImplicit _) argTy scope)
      = pure $ ILam fc rig !(traverse (desugar side ps) p)
                           Nothing !(desugarB side ps argTy)
                                   !(desugar side ps scope)
  desugarB side ps (PLam fc rig p pat argTy scope)
      = pure $ ILam fc rig !(traverse (desugar side ps) p)
                   (Just (MN "lamc" 0)) !(desugarB side ps argTy) $
                 ICase fc (IVar fc (MN "lamc" 0)) (Implicit fc False)
                     [!(desugarClause ps True (MkPatClause fc pat scope []))]
  desugarB side ps (PLet fc rig (PRef _ n) nTy nVal scope [])
      = pure $ ILet fc rig n !(desugarB side ps nTy) !(desugarB side ps nVal)
                             !(desugar side (n :: ps) scope)
  desugarB side ps (PLet fc rig pat nTy nVal scope alts)
      = pure $ ICase fc !(desugarB side ps nVal) !(desugarB side ps nTy)
                        !(traverse (desugarClause ps True)
                            (MkPatClause fc pat scope [] :: alts))
  desugarB side ps (PCase fc x xs)
      = pure $ ICase fc !(desugarB side ps x)
                        (Implicit fc False)
                        !(traverse (desugarClause ps True) xs)
  desugarB side ps (PLocal fc xs scope)
      = let ps' = definedIn xs ++ ps in
            pure $ ILocal fc (concat !(traverse (desugarDecl ps') xs))
                             !(desugar side ps' scope)
  desugarB side ps (PApp pfc (PUpdate fc fs) rec)
      = pure $ IUpdate pfc !(traverse (desugarUpdate side ps) fs)
                           !(desugarB side ps rec)
  desugarB side ps (PUpdate fc fs)
      = desugarB side ps (PLam fc top Explicit (PRef fc (MN "rec" 0)) (PImplicit fc)
                            (PApp fc (PUpdate fc fs) (PRef fc (MN "rec" 0))))
  desugarB side ps (PApp fc x y)
      = pure $ IApp fc !(desugarB side ps x) !(desugarB side ps y)
  desugarB side ps (PWithApp fc x y)
      = pure $ IWithApp fc !(desugarB side ps x) !(desugarB side ps y)
  desugarB side ps (PImplicitApp fc x argn y)
      = pure $ IImplicitApp fc !(desugarB side ps x) argn !(desugarB side ps y)
  desugarB side ps (PDelayed fc r ty)
      = pure $ IDelayed fc r !(desugarB side ps ty)
  desugarB side ps (PDelay fc tm)
      = pure $ IDelay fc !(desugarB side ps tm)
  desugarB side ps (PForce fc tm)
      = pure $ IForce fc !(desugarB side ps tm)
  desugarB side ps (PEq fc l r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           pure $ IAlternative fc FirstSuccess
                     [apply (IVar fc (UN "===")) [l', r'],
                      apply (IVar fc (UN "~=~")) [l', r']]
  desugarB side ps (PBracketed fc e) = desugarB side ps e
  desugarB side ps (POp fc op l r)
      = do ts <- toTokList (POp fc op l r)
           desugarTree side ps !(parseOps ts)
  desugarB side ps (PPrefixOp fc op arg)
      = do ts <- toTokList (PPrefixOp fc op arg)
           desugarTree side ps !(parseOps ts)
  desugarB side ps (PSectionL fc op arg)
      = do syn <- get Syn
           -- It might actually be a prefix argument rather than a section
           -- so check that first, otherwise desugar as a lambda
           case lookup (nameRoot op) (prefixes syn) of
                Nothing =>
                   desugarB side ps (PLam fc top Explicit (PRef fc (MN "arg" 0)) (PImplicit fc)
                               (POp fc op (PRef fc (MN "arg" 0)) arg))
                Just prec => desugarB side ps (PPrefixOp fc op arg)
  desugarB side ps (PSectionR fc arg op)
      = desugarB side ps (PLam fc top Explicit (PRef fc (MN "arg" 0)) (PImplicit fc)
                 (POp fc op arg (PRef fc (MN "arg" 0))))
  desugarB side ps (PSearch fc depth) = pure $ ISearch fc depth
  desugarB side ps (PPrimVal fc (BI x))
      = case !fromIntegerName of
             Nothing =>
                pure $ IAlternative fc (UniqueDefault (IPrimVal fc (BI x)))
                                [IPrimVal fc (BI x),
                                 IPrimVal fc (I (fromInteger x))]
             Just fi => pure $ IApp fc (IVar fc fi)
                                       (IPrimVal fc (BI x))
  desugarB side ps (PPrimVal fc (Str x))
      = case !fromStringName of
             Nothing =>
                pure $ IPrimVal fc (Str x)
             Just f => pure $ IApp fc (IVar fc f)
                                      (IPrimVal fc (Str x))
  desugarB side ps (PPrimVal fc (Ch x))
      = case !fromCharName of
             Nothing =>
                pure $ IPrimVal fc (Ch x)
             Just f => pure $ IApp fc (IVar fc f)
                                      (IPrimVal fc (Ch x))
  desugarB side ps (PPrimVal fc x) = pure $ IPrimVal fc x
  desugarB side ps (PQuote fc tm)
      = pure $ IQuote fc !(desugarB side ps tm)
  desugarB side ps (PQuoteDecl fc x)
      = do [x'] <- desugarDecl ps x
              | _ => throw (GenericMsg fc "Can't quote this declaration")
           pure $ IQuoteDecl fc x'
  desugarB side ps (PUnquote fc tm)
      = pure $ IUnquote fc !(desugarB side ps tm)
  desugarB side ps (PRunElab fc tm)
      = pure $ IRunElab fc !(desugarB side ps tm)
  desugarB side ps (PHole fc br holename)
      = do when br $
              do syn <- get Syn
                 put Syn (record { bracketholes $= ((UN holename) ::) } syn)
           pure $ IHole fc holename
  desugarB side ps (PType fc) = pure $ IType fc
  desugarB side ps (PAs fc vname pattern)
      = pure $ IAs fc UseRight vname !(desugarB side ps pattern)
  desugarB side ps (PDotted fc x)
      = pure $ IMustUnify fc UserDotted !(desugarB side ps x)
  desugarB side ps (PImplicit fc) = pure $ Implicit fc True
  desugarB side ps (PInfer fc) = pure $ Implicit fc False
  desugarB side ps (PDoBlock fc block)
      = expandDo side ps fc block
  desugarB side ps (PBang fc term)
      = do itm <- desugarB side ps term
           bs <- get Bang
           let bn = MN "bind" (nextName bs)
           put Bang (record { nextName $= (+1),
                              bangNames $= ((bn, fc, itm) ::)
                            } bs)
           pure (IVar fc bn)
  desugarB side ps (PIdiom fc term)
      = do itm <- desugarB side ps term
           pure (idiomise fc itm)
  desugarB side ps (PList fc args)
      = expandList side ps fc args
  desugarB side ps (PPair fc l r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           let pval = apply (IVar fc mkpairname) [l', r']
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar fc pairname) [l', r'], pval]
  desugarB side ps (PDPair fc (PRef nfc (UN n)) (PImplicit _) r)
      = do r' <- desugarB side ps r
           let pval = apply (IVar fc mkdpairname) [IVar nfc (UN n), r']
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar fc dpairname)
                      [Implicit nfc False,
                       ILam nfc top Explicit (Just (UN n)) (Implicit nfc False) r'],
                   pval]
  desugarB side ps (PDPair fc (PRef nfc (UN n)) ty r)
      = do ty' <- desugarB side ps ty
           r' <- desugarB side ps r
           pure $ apply (IVar fc dpairname)
                        [ty',
                         ILam nfc top Explicit (Just (UN n)) ty' r']
  desugarB side ps (PDPair fc l (PImplicit _) r)
      = do l' <- desugarB side ps l
           r' <- desugarB side ps r
           pure $ apply (IVar fc mkdpairname) [l', r']
  desugarB side ps (PDPair fc l ty r)
      = throw (GenericMsg fc "Invalid dependent pair type")
  desugarB side ps (PUnit fc)
      = pure $ IAlternative fc (UniqueDefault (IVar fc (UN "MkUnit")))
               [IVar fc (UN "Unit"),
                IVar fc (UN "MkUnit")]
  desugarB side ps (PIfThenElse fc x t e)
      = pure $ ICase fc !(desugarB side ps x) (IVar fc (UN "Bool"))
                   [PatClause fc (IVar fc (UN "True")) !(desugar side ps t),
                    PatClause fc (IVar fc (UN "False")) !(desugar side ps e)]
  desugarB side ps (PComprehension fc ret conds)
      = desugarB side ps (PDoBlock fc (map guard conds ++ [toPure ret]))
    where
      guard : PDo -> PDo
      guard (DoExp fc tm) = DoExp fc (PApp fc (PRef fc (UN "guard")) tm)
      guard d = d

      toPure : PTerm -> PDo
      toPure tm = DoExp fc (PApp fc (PRef fc (UN "pure")) tm)
  desugarB side ps (PRewrite fc rule tm)
      = pure $ IRewrite fc !(desugarB side ps rule) !(desugarB side ps tm)
  desugarB side ps (PRange fc start next end)
      = case next of
             Nothing =>
                desugarB side ps (PApp fc
                                    (PApp fc (PRef fc (UN "rangeFromTo"))
                                          start) end)
             Just n =>
                desugarB side ps (PApp fc
                                    (PApp fc
                                        (PApp fc (PRef fc (UN "rangeFromThenTo"))
                                              start) n) end)
  desugarB side ps (PRangeStream fc start next)
      = case next of
             Nothing =>
                desugarB side ps (PApp fc (PRef fc (UN "rangeFrom")) start)
             Just n =>
                desugarB side ps (PApp fc (PApp fc (PRef fc (UN "rangeFromThen")) start) n)
  desugarB side ps (PUnifyLog fc lvl tm)
      = pure $ IUnifyLog fc lvl !(desugarB side ps tm)
  desugarB side ps (PRecordFieldAccess fc rec fields)
      = desugarB side ps $ foldl (\r, f => PApp fc (PRef fc f) r) rec fields
  desugarB side ps (PRecordProjection fc fields)
      = desugarB side ps $
          PLam fc top Explicit (PRef fc (MN "rec" 0)) (PImplicit fc) $
            foldl (\r, f => PApp fc (PRef fc f) r) (PRef fc (MN "rec" 0)) fields

  desugarUpdate : {auto s : Ref Syn SyntaxInfo} ->
                  {auto b : Ref Bang BangData} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto m : Ref MD Metadata} ->
                  Side -> List Name -> PFieldUpdate -> Core IFieldUpdate
  desugarUpdate side ps (PSetField p v)
      = pure (ISetField p !(desugarB side ps v))
  desugarUpdate side ps (PSetFieldApp p v)
      = pure (ISetFieldApp p !(desugarB side ps v))

  expandList : {auto s : Ref Syn SyntaxInfo} ->
               {auto b : Ref Bang BangData} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {auto m : Ref MD Metadata} ->
               Side -> List Name -> FC -> List PTerm -> Core RawImp
  expandList side ps fc [] = pure (IVar fc (UN "Nil"))
  expandList side ps fc (x :: xs)
      = pure $ apply (IVar fc (UN "::"))
                [!(desugarB side ps x), !(expandList side ps fc xs)]

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
                          (ILam fc top Explicit Nothing
                                (Implicit fc False) rest')
  expandDo side ps topfc (DoBind fc n tm :: rest)
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                     (ILam fc top Explicit (Just n)
                           (Implicit fc False) rest')
  expandDo side ps topfc (DoBindPat fc pat exp alts :: rest)
      = do pat' <- desugar LHS ps pat
           (newps, bpat) <- bindNames False pat'
           exp' <- desugar side ps exp
           alts' <- traverse (desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) exp')
                    (ILam fc top Explicit (Just (MN "_" 0))
                          (Implicit fc False)
                          (ICase fc (IVar fc (MN "_" 0))
                               (Implicit fc False)
                               (PatClause fc bpat rest'
                                  :: alts')))
  expandDo side ps topfc (DoLet fc n rig ty tm :: rest)
      = do b <- newRef Bang initBangs
           tm' <- desugarB side ps tm
           ty' <- desugar side ps ty
           rest' <- expandDo side ps topfc rest
           let bind = ILet fc rig n ty' tm' rest'
           bd <- get Bang
           pure $ bindBangs (bangNames bd) bind
  expandDo side ps topfc (DoLetPat fc pat ty tm alts :: rest)
      = do b <- newRef Bang initBangs
           pat' <- desugar LHS ps pat
           ty' <- desugar side ps ty
           (newps, bpat) <- bindNames False pat'
           tm' <- desugarB side ps tm
           alts' <- traverse (desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc rest
           bd <- get Bang
           pure $ bindBangs (bangNames bd) $
                    ICase fc tm' ty'
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
                {auto b : Ref Bang BangData} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                Side -> List Name -> Tree OpStr PTerm -> Core RawImp
  desugarTree side ps (Inf loc (UN "=") l r) -- special case since '=' is special syntax
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IAlternative loc FirstSuccess
                     [apply (IVar loc (UN "===")) [l', r'],
                      apply (IVar loc (UN "~=~")) [l', r']])
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
  desugarTree side ps (Leaf t) = desugarB side ps t

  desugarType : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                List Name -> PTypeDecl -> Core ImpTy
  desugarType ps (MkPTy fc n ty)
      = do syn <- get Syn
           pure $ MkImpTy fc n !(bindTypeNames (usingImpl syn)
                                               ps !(desugar AnyExpr ps ty))

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
      = do syn <- get Syn
           pure $ MkImpData fc n
                              !(bindTypeNames (usingImpl syn)
                                              ps !(desugar AnyExpr ps tycon))
                              opts
                              !(traverse (desugarType ps) datacons)
  desugarData ps (MkPLater fc n tycon)
      = do syn <- get Syn
           pure $ MkImpLater fc n !(bindTypeNames (usingImpl syn)
                                                  ps !(desugar AnyExpr ps tycon))

  desugarField : {auto s : Ref Syn SyntaxInfo} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {auto m : Ref MD Metadata} ->
                 List Name -> PField ->
                 Core IField
  desugarField ps (MkField fc rig p n ty)
      = do syn <- get Syn
           pure (MkIField fc rig !(traverse (desugar AnyExpr ps) p )
                          n !(bindTypeNames (usingImpl syn)
                          ps !(desugar AnyExpr ps ty)))

  -- Get the declaration to process on each pass of a mutual block
  -- Essentially: types on the first pass
  --    i.e. type constructors of data declarations
  --         function types
  --         interfaces (in full, since it includes function types)
  --         records (just the generated type constructor)
  --         implementation headers (i.e. note their existence, but not the bodies)
  -- Everything else on the second pass
  getDecl : Pass -> PDecl -> Maybe PDecl
  getDecl p (PImplementation fc vis opts _ is cons n ps iname nusing ds)
      = Just (PImplementation fc vis opts p is cons n ps iname nusing ds)

  getDecl p (PNamespace fc ns ds)
      = Just (PNamespace fc ns (mapMaybe (getDecl p) ds))

  getDecl AsType d@(PClaim _ _ _ _ _) = Just d
  getDecl AsType (PData fc vis (MkPData dfc tyn tyc _ _))
      = Just (PData fc vis (MkPLater dfc tyn tyc))
  getDecl AsType d@(PInterface _ _ _ _ _ _ _ _) = Just d
  getDecl AsType d@(PRecord fc vis n ps _ _)
      = Just (PData fc vis (MkPLater fc n (mkRecType ps)))
    where
      mkRecType : List (Name, RigCount, PiInfo PTerm, PTerm) -> PTerm
      mkRecType [] = PType fc
      mkRecType ((n, c, p, t) :: ts) = PPi fc c p (Just n) t (mkRecType ts)
  getDecl AsType d@(PFixity _ _ _ _) = Just d
  getDecl AsType d@(PDirective _ _) = Just d
  getDecl AsType d = Nothing

  getDecl AsDef (PClaim _ _ _ _ _) = Nothing
  getDecl AsDef d@(PData _ _ (MkPLater _ _ _)) = Just d
  getDecl AsDef (PInterface _ _ _ _ _ _ _ _) = Nothing
  getDecl AsDef d@(PRecord _ _ _ _ _ _) = Just d
  getDecl AsDef (PFixity _ _ _ _) = Nothing
  getDecl AsDef (PDirective _ _) = Nothing
  getDecl AsDef d = Just d

  getDecl p (PParameters fc ps pds)
      = Just (PParameters fc ps (mapMaybe (getDecl p) pds))
  getDecl p (PUsing fc ps pds)
      = Just (PUsing fc ps (mapMaybe (getDecl p) pds))

  getDecl Single d = Just d

  export
  desugarFnOpt : {auto s : Ref Syn SyntaxInfo} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {auto m : Ref MD Metadata} ->
                 List Name -> PFnOpt -> Core FnOpt
  desugarFnOpt ps (IFnOpt f) = pure f
  desugarFnOpt ps (PForeign tms)
      = do tms' <- traverse (desugar AnyExpr ps) tms
           pure (ForeignFn tms')

  -- Given a high level declaration, return a list of TTImp declarations
  -- which process it, and update any necessary state on the way.
  export
  desugarDecl : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto m : Ref MD Metadata} ->
                List Name -> PDecl -> Core (List ImpDecl)
  desugarDecl ps (PClaim fc rig vis fnopts ty)
      = do opts <- traverse (desugarFnOpt ps) fnopts
           opts <- if (isTotalityOption `any` opts)
                   then pure opts
                   else do PartialOK <- getDefaultTotalityOption
                           | tot => pure (Totality tot :: opts)
                           -- We assume PartialOK by default internally
                           pure opts
           pure [IClaim fc rig vis opts !(desugarType ps ty)]
        where
          isTotalityOption : FnOpt -> Bool
          isTotalityOption (Totality _) = True
          isTotalityOption _            = False

  desugarDecl ps (PDef fc clauses)
  -- The clauses won't necessarily all be from the same function, so split
  -- after desugaring, by function name, using collectDefs from RawImp
      = do cs <- traverse (desugarClause ps False) clauses
           defs <- traverse toIDef cs
           pure (collectDefs defs)
    where
      getFn : RawImp -> Core Name
      getFn (IVar _ n) = pure n
      getFn (IApp _ f _) = getFn f
      getFn (IImplicitApp _ f _ _) = getFn f
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
           let pnames = if !isUnboundImplicits
                        then concatMap (findBindableNames True
                                         (ps ++ map fst params) [])
                                       (map snd params')
                        else []
           let paramsb = map (\ (n, tm) => (n, doBind pnames tm)) params'
           pure [IParameters fc paramsb (concat pds')]
  desugarDecl ps (PUsing fc uimpls uds)
      = do syn <- get Syn
           let oldu = usingImpl syn
           uimpls' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                            btm <- bindTypeNames oldu ps tm'
                                            pure (fst ntm, btm)) uimpls
           put Syn (record { usingImpl = uimpls' ++ oldu } syn)
           uds' <- traverse (desugarDecl ps) uds
           syn <- get Syn
           put Syn (record { usingImpl = oldu } syn)
           pure (concat uds')
  desugarDecl ps (PReflect fc tm)
      = throw (GenericMsg fc "Reflection not implemented yet")
--       pure [IReflect fc !(desugar AnyExpr ps tm)]
  desugarDecl ps (PInterface fc vis cons_in tn params det conname body)
      = do let cons = concatMap expandConstraint cons_in
           cons' <- traverse (\ ntm => do tm' <- desugar AnyExpr (ps ++ map fst params)
                                                         (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                            pure (fst ntm, tm')) params
           -- Look for bindable names in all the constraints and parameters
           let mnames = map dropNS (definedIn body)
           let bnames = if !isUnboundImplicits
                        then
                        concatMap (findBindableNames True
                                      (ps ++ mnames ++ map fst params) [])
                                  (map snd cons') ++
                        concatMap (findBindableNames True
                                      (ps ++ mnames ++ map fst params) [])
                                  (map snd params')
                        else []
           let paramsb = map (\ (n, tm) => (n, doBind bnames tm)) params'
           let consb = map (\ (n, tm) => (n, doBind bnames tm)) cons'

           body' <- traverse (desugarDecl (ps ++ mnames ++ map fst params)) body
           pure [IPragma (\c, nest, env =>
                             elabInterface fc vis env nest consb
                                           tn paramsb det conname
                                           (concat body'))]
    where
      -- Turns pairs in the constraints to individual constraints. This
      -- is a bit of a hack, but it's necessary to build parent constraint
      -- chasing functions correctly
      pairToCons : PTerm -> List PTerm
      pairToCons (PPair _ l r) = pairToCons l ++ pairToCons r
      pairToCons t = [t]

      expandConstraint : (Maybe Name, PTerm) -> List (Maybe Name, PTerm)
      expandConstraint (Just n, t) = [(Just n, t)]
      expandConstraint (Nothing, p)
          = map (\x => (Nothing, x)) (pairToCons p)

  desugarDecl ps (PImplementation fc vis fnopts pass is cons tn params impname nusing body)
      = do opts <- traverse (desugarFnOpt ps) fnopts
           is' <- traverse (\ (n,c,tm) => do tm' <- desugar AnyExpr ps tm
                                             pure (n, c, tm')) is
           let _ = the (List (Name, RigCount, RawImp)) is'
           cons' <- traverse (\ (n, tm) => do tm' <- desugar AnyExpr ps tm
                                              pure (n, tm')) cons
           let _ = the (List (Maybe Name, RawImp)) cons'
           params' <- traverse (desugar AnyExpr ps) params
           let _ = the (List RawImp) params'
           -- Look for bindable names in all the constraints and parameters
           let bnames = if !isUnboundImplicits
                        then
                        concatMap (findBindableNames True ps []) (map snd cons') ++
                        concatMap (findBindableNames True ps []) params'
                        else []

           let paramsb = map (doBind bnames) params'
           let isb = map (\ (n, r, tm) => (n, r, doBind bnames tm)) is'
           let _ = the (List (Name, RigCount, RawImp)) isb
           let consb = map (\(n, tm) => (n, doBind bnames tm)) cons'
           let _ = the (List (Maybe Name, RawImp)) consb

           body' <- maybe (pure Nothing)
                          (\b => do b' <- traverse (desugarDecl ps) b
                                    pure (Just (concat b'))) body
           pure [IPragma (\c, nest, env =>
                             elabImplementation fc vis opts pass env nest isb consb
                                                tn paramsb impname nusing
                                                body')]

  desugarDecl ps (PRecord fc vis tn params conname_in fields)
      = do params' <- traverse (\ (n,c,p,tm) =>
                          do tm' <- desugar AnyExpr ps tm
                             p'  <- mapDesugarPiInfo ps p
                             pure (n, c, p', tm'))
                        params
           let _ = the (List (Name, RigCount, PiInfo RawImp, RawImp)) params'
           let fnames = map fname fields
           let _ = the (List Name) fnames
           -- Look for bindable names in the parameters

           let bnames = if !isUnboundImplicits
                        then concatMap (findBindableNames True
                                         (ps ++ fnames ++ map fst params) [])
                                       (map (\(_,_,_,d) => d) params')
                        else []
           let _ = the (List (String, String)) bnames

           let paramsb = map (\ (n, c, p, tm) => (n, c, p, doBind bnames tm)) params'
           let _ = the (List (Name, RigCount, PiInfo RawImp, RawImp)) paramsb
           fields' <- traverse (desugarField (ps ++ map fname fields ++
                                              map fst params)) fields
           let _ = the (List IField) fields'
           let conname = maybe (mkConName tn) id conname_in
           let _ = the Name conname
           -- True flag set so that the parent namespace can look inside the
           -- record definition
           pure [IRecord fc (Just (nameRoot tn))
                         vis (MkImpRecord fc tn paramsb conname fields')]
    where
      fname : PField -> Name
      fname (MkField _ _ _ n _) = n

      mkConName : Name -> Name
      mkConName (NS ns (UN n)) = NS ns (DN n (MN ("__mk" ++ n) 0))
      mkConName n = DN (show n) (MN ("__mk" ++ show n) 0)

      mapDesugarPiInfo : {auto s : Ref Syn SyntaxInfo} -> {auto c : Ref Ctxt Defs}
                  -> {auto u : Ref UST UState} -> {auto m : Ref MD Metadata}
                  -> List Name -> PiInfo PTerm -> Core (PiInfo RawImp)
      mapDesugarPiInfo ps Implicit         = pure   Implicit
      mapDesugarPiInfo ps Explicit         = pure   Explicit
      mapDesugarPiInfo ps AutoImplicit     = pure   AutoImplicit
      mapDesugarPiInfo ps (DefImplicit tm) = pure $ DefImplicit
                                                  !(desugar AnyExpr ps tm)


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
  desugarDecl ps (PTransform fc lhs rhs)
      = do (bound, blhs) <- bindNames False !(desugar LHS ps lhs)
           rhs' <- desugar AnyExpr (bound ++ ps) rhs
           pure [ITransform fc blhs rhs']
  desugarDecl ps (PDirective fc d)
      = case d of
             Hide n => pure [IPragma (\c, nest, env => hide fc n)]
             Logging i => pure [ILog i]
             LazyOn a => pure [IPragma (\c, nest, env => lazyActive a)]
             UnboundImplicits a => do
               setUnboundImplicits a
               pure [IPragma (\c, nest, env => setUnboundImplicits a)]
             UndottedRecordProjections b => do
               pure [IPragma (\c, nest, env => setUndottedRecordProjections b)]
             AmbigDepth n => pure [IPragma (\c, nest, env => setAmbigLimit n)]
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
             DefaultTotality tot => do setDefaultTotalityOption tot
                                       pure []

  export
  desugar : {auto s : Ref Syn SyntaxInfo} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            Side -> List Name -> PTerm -> Core RawImp
  desugar s ps tm
      = do b <- newRef Bang initBangs
           tm' <- desugarB s ps tm
           bd <- get Bang
           pure $ bindBangs (bangNames bd) tm'

