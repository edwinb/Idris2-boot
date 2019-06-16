module Core.TTC

import Core.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Core
import Core.Env
import Core.FC
import Core.Name
import Core.Options
import Core.TT

import Data.NameMap
import Data.Vect

import Utils.Binary

%default covering

export
TTC FC where
  toBuf b (MkFC file startPos endPos) 
      = do toBuf b file; toBuf b startPos; toBuf b endPos
  fromBuf r b
      = do f <- fromBuf r b; 
           s <- fromBuf r b; e <- fromBuf r b
           pure (MkFC f s e)

export
TTC Name where
  toBuf b (NS xs x) = do tag 0; toBuf b xs; toBuf b x
  toBuf b (UN x) = do tag 1; toBuf b x
  toBuf b (MN x y) = do tag 2; toBuf b x; toBuf b y
  toBuf b (PV x y) = do tag 3; toBuf b x; toBuf b y
  toBuf b (DN x y) = do tag 4; toBuf b x; toBuf b y
  toBuf b (Nested x y) = do tag 5; toBuf b x; toBuf b y
  toBuf b (CaseBlock x y) = do tag 6; toBuf b x; toBuf b y
  toBuf b (WithBlock x y) = do tag 7; toBuf b x; toBuf b y
  toBuf b (Resolved x) = do tag 8; toBuf b x

  fromBuf r b
      = case !getTag of
             0 => do xs <- fromBuf r b
                     x <- fromBuf r b
                     pure (NS xs x)
             1 => do x <- fromBuf r b
                     pure (UN x)
             2 => do x <- fromBuf r b
                     y <- fromBuf r b
                     pure (MN x y)
             3 => do x <- fromBuf r b
                     y <- fromBuf r b
                     pure (PV x y)
             4 => do x <- fromBuf r b
                     y <- fromBuf r b
                     pure (DN x y)
             5 => do x <- fromBuf r b
                     y <- fromBuf r b
                     pure (Nested x y)
             6 => do x <- fromBuf r b
                     y <- fromBuf r b
                     pure (CaseBlock x y)
             7 => do x <- fromBuf r b
                     y <- fromBuf r b
                     pure (WithBlock x y)
             8 => do x <- fromBuf r b
                     Just (n, Just idx) <- coreLift $ readArray r x
                          | Just (n, Nothing) => pure n
                          | Nothing => if x < 70 -- ^ must be primitive
                                          then pure (Resolved x)
                                          else corrupt ("Name index " ++ show x)
                     pure (Resolved idx)
             _ => corrupt "Name"
            
export 
TTC RigCount where
  toBuf b Rig0 = tag 0
  toBuf b Rig1 = tag 1
  toBuf b RigW = tag 2

  fromBuf r b
      = case !getTag of
             0 => pure Rig0
             1 => pure Rig1
             2 => pure RigW
             _ => corrupt "RigCount"

export
TTC PiInfo where
  toBuf b Implicit = tag 0
  toBuf b Explicit = tag 1
  toBuf b AutoImplicit = tag 2

  fromBuf r b
      = case !getTag of
             0 => pure Implicit
             1 => pure Explicit
             2 => pure AutoImplicit
             _ => corrupt "PiInfo"

export
TTC Constant where
  toBuf b (I x) = do tag 0; toBuf b x
  toBuf b (BI x) = do tag 1; toBuf b x
  toBuf b (Str x) = do tag 2; toBuf b x
  toBuf b (Ch x) = do tag 3; toBuf b x
  toBuf b (Db x) = do tag 4; toBuf b x
  
  toBuf b WorldVal = tag 5
  toBuf b IntType = tag 6
  toBuf b IntegerType = tag 7 
  toBuf b StringType = tag 8
  toBuf b CharType = tag 9
  toBuf b DoubleType = tag 10
  toBuf b WorldType = tag 11

  fromBuf r b
      = case !getTag of
             0 => do x <- fromBuf r b; pure (I x)
             1 => do x <- fromBuf r b; pure (BI x)
             2 => do x <- fromBuf r b; pure (Str x)
             3 => do x <- fromBuf r b; pure (Ch x)
             4 => do x <- fromBuf r b; pure (Db x)
             5 => pure WorldVal
             6 => pure IntType
             7 => pure IntegerType
             8 => pure StringType
             9 => pure CharType
             10 => pure DoubleType
             11 => pure WorldType
             _ => corrupt "Constant"

export
TTC LazyReason where
  toBuf b LInf = tag 0
  toBuf b LLazy = tag 1
  toBuf b LUnknown = tag 2

  fromBuf r b
      = case !getTag of
             0 => pure LInf
             1 => pure LLazy
             2 => pure LUnknown
             _ => corrupt "LazyReason"

export
TTC NameType where
  toBuf b Bound = tag 0
  toBuf b Func = tag 1
  toBuf b (DataCon t arity) = do tag 2; toBuf b t; toBuf b arity
  toBuf b (TyCon t arity) = do tag 3; toBuf b t; toBuf b arity

  fromBuf r b
      = case !getTag of
             0 => pure Bound
             1 => pure Func
             2 => do x <- fromBuf r b; y <- fromBuf r b; pure (DataCon x y)
             3 => do x <- fromBuf r b; y <- fromBuf r b; pure (TyCon x y)
             _ => corrupt "NameType"

-- Assumption is that it was type safe when we wrote it out, so believe_me
-- to rebuild proofs is fine.
-- We're just making up the implicit arguments - this is only fine at run
-- time because those arguments get erased!
-- (Indeed, we're expecting the whole IsVar proof to be erased because
-- we have the idx...)
mkPrf : (idx : Nat) -> IsVar n idx ns
mkPrf {n} {ns} Z = believe_me (First {n} {ns = n :: ns})
mkPrf {n} {ns} (S k) = believe_me (Later {m=n} (mkPrf {n} {ns} k))

export
TTC (Var vars) where
  toBuf b (MkVar {i} {n} v) = do toBuf b n; toBuf b i
  fromBuf r b
      = do n <- fromBuf r b
           i <- fromBuf r b
           pure (MkVar {n} (mkPrf i))

mutual
  export
  TTC (Binder (Term vars)) where
    toBuf b (Lam c x ty) = do tag 0; toBuf b c; toBuf b x; -- toBuf b ty
    toBuf b (Let c val ty) = do tag 1; toBuf b c; toBuf b val -- ; toBuf b ty
    toBuf b (Pi c x ty) = do tag 2; toBuf b c; toBuf b x; toBuf b ty
    toBuf b (PVar c ty) = do tag 3; toBuf b c; toBuf b ty
    toBuf b (PLet c val ty) = do tag 4; toBuf b c; toBuf b val -- ; toBuf b ty
    toBuf b (PVTy c ty) = do tag 5; toBuf b c -- ; toBuf b ty

    fromBuf r b
        = case !getTag of
               0 => do c <- fromBuf r b; x <- fromBuf r b; pure (Lam c x (Erased emptyFC))
               1 => do c <- fromBuf r b; x <- fromBuf r b; pure (Let c x (Erased emptyFC))
               2 => do c <- fromBuf r b; x <- fromBuf r b; y <- fromBuf r b; pure (Pi c x y)
               3 => do c <- fromBuf r b; ty <- fromBuf r b; pure (PVar c ty)
               4 => do c <- fromBuf r b; x <- fromBuf r b; pure (PLet c x (Erased emptyFC))
               5 => do c <- fromBuf r b; pure (PVTy c (Erased emptyFC))
               _ => corrupt "Binder"


  export
  TTC (Term vars) where
    toBuf b (Local {name} fc c idx y) 
        = if idx < 244
             then do toBuf b (prim__truncBigInt_B8 (12 + cast idx))
                     toBuf b name
             else do tag 0
                     toBuf b name
                     toBuf b idx
    toBuf b (Ref fc nt name) 
        = do tag 1;
             toBuf b nt; toBuf b name
    toBuf b (Meta fc n i xs) 
        = do tag 2;
             -- Name no longer needed
             toBuf b i; toBuf b xs
    toBuf b (Bind fc x bnd scope) 
        = do tag 3;
             toBuf b x; 
             toBuf b bnd; toBuf b scope
    toBuf b (App fc fn arg) 
        = do tag 4;
             toBuf b fn; toBuf b arg
--              let (fn, args) = getFnArgs (App fc fn arg)
--              toBuf b fn; -- toBuf b p; 
--              toBuf b args
    toBuf b (As fc as tm)
        = do tag 5;
             toBuf b as; toBuf b tm
    toBuf b (TDelayed fc r tm) 
        = do tag 6;
             toBuf b r; toBuf b tm
    toBuf b (TDelay fc r ty tm)
        = do tag 7;
             toBuf b r; toBuf b ty; toBuf b tm
    toBuf b (TForce fc tm)
        = do tag 8;
             toBuf b tm
    toBuf b (PrimVal fc c) 
        = do tag 9;
             toBuf b c
    toBuf b (Erased fc) 
        = tag 10
    toBuf b (TType fc)
        = tag 11

    fromBuf r b 
        = case !getTag of
               0 => do name <- fromBuf r b
                       idx <- fromBuf r b
                       pure (Local {name} emptyFC Nothing idx (mkPrf idx))
               1 => do nt <- fromBuf r b; name <- fromBuf r b
                       pure (Ref emptyFC nt name)
               2 => do x <- fromBuf r b
                       Just (n, Just idx) <- coreLift $ readArray r x
                          | Just (n, Nothing) => 
                                corrupt ("Metavar name index not updated " ++ show x)
                          | Nothing => corrupt ("Metavar name index " ++ show x ++ " (not in array)")
                       xs <- fromBuf r b
                       pure (Meta emptyFC (UN "metavar") idx xs)
               3 => do x <- fromBuf r b
                       bnd <- fromBuf r b; scope <- fromBuf r b
                       pure (Bind emptyFC x bnd scope)
               4 => do fn <- fromBuf r b
                       arg <- fromBuf r b
                       pure (App emptyFC fn arg)
               5 => do as <- fromBuf r b; tm <- fromBuf r b
                       pure (As emptyFC as tm)
               6 => do lr <- fromBuf r b; tm <- fromBuf r b
                       pure (TDelayed emptyFC lr tm)
               7 => do lr <- fromBuf r b; 
                       ty <- fromBuf r b; tm <- fromBuf r b
                       pure (TDelay emptyFC lr ty tm)
               8 => do tm <- fromBuf r b
                       pure (TForce emptyFC tm)
               9 => do c <- fromBuf r b
                       pure (PrimVal emptyFC c)
               10 => pure (Erased emptyFC)
               11 => pure (TType emptyFC)
               idxp => do name <- fromBuf r b
                          let idx = fromInteger (prim__sextB8_BigInt idxp - 12)
                          pure (Local {name} emptyFC Nothing idx (mkPrf idx))

export
TTC Pat where
  toBuf b (PAs fc x y) 
      = do tag 0; toBuf b fc; toBuf b x; toBuf b y
  toBuf b (PCon fc x t arity xs) 
      = do tag 1; toBuf b fc; toBuf b x; toBuf b t; toBuf b arity; toBuf b xs
  toBuf b (PTyCon fc x arity xs) 
      = do tag 2; toBuf b fc; toBuf b x; toBuf b arity; toBuf b xs
  toBuf b (PConst fc c)
      = do tag 3; toBuf b fc; toBuf b c
  toBuf b (PArrow fc x s t)
      = do tag 4; toBuf b fc; toBuf b x; toBuf b s; toBuf b t
  toBuf b (PDelay fc x t y) 
      = do tag 5; toBuf b fc; toBuf b x; toBuf b t; toBuf b y
  toBuf b (PLoc fc x) 
      = do tag 6; toBuf b fc; toBuf b x
  toBuf b (PUnmatchable fc x) 
      = do tag 7; toBuf b fc; toBuf b x

  fromBuf r b 
      = case !getTag of
             0 => do fc <- fromBuf r b; x <- fromBuf r b;
                     y <- fromBuf r b
                     pure (PAs fc x y)
             1 => do fc <- fromBuf r b; x <- fromBuf r b
                     t <- fromBuf r b; arity <- fromBuf r b
                     xs <- fromBuf r b
                     pure (PCon fc x t arity xs)
             2 => do fc <- fromBuf r b; x <- fromBuf r b
                     arity <- fromBuf r b
                     xs <- fromBuf r b
                     pure (PTyCon fc x arity xs)
             3 => do fc <- fromBuf r b; c <- fromBuf r b
                     pure (PConst fc c)
             4 => do fc <- fromBuf r b; x <- fromBuf r b
                     s <- fromBuf r b; t <- fromBuf r b
                     pure (PArrow fc x s t)
             5 => do fc <- fromBuf r b; x <- fromBuf r b;
                     t <- fromBuf r b; y <- fromBuf r b
                     pure (PDelay fc x t y)
             6 => do fc <- fromBuf r b; x <- fromBuf r b
                     pure (PLoc fc x)
             7 => do fc <- fromBuf r b; x <- fromBuf r b
                     pure (PUnmatchable fc x)
             _ => corrupt "Pat"

mutual
  export
  TTC (CaseTree vars) where
    toBuf b (Case {name} idx x scTy xs) 
        = do tag 0; toBuf b name; toBuf b idx; toBuf b scTy; toBuf b xs
    toBuf b (STerm x) 
        = do tag 1; toBuf b x
    toBuf b (Unmatched msg) 
        = do tag 2; toBuf b msg
    toBuf b Impossible = tag 3

    fromBuf r b 
        = case !getTag of
               0 => do name <- fromBuf r b; idx <- fromBuf r b
                       scTy <- fromBuf r b; xs <- fromBuf r b
                       pure (Case {name} idx (mkPrf idx) scTy xs)
               1 => do x <- fromBuf r b
                       pure (STerm x)
               2 => do msg <- fromBuf r b
                       pure (Unmatched msg)
               3 => pure Impossible
               _ => corrupt "CaseTree"

  export
  TTC (CaseAlt vars) where
    toBuf b (ConCase x t args y) 
        = do tag 0; toBuf b x; toBuf b t; toBuf b args; toBuf b y
    toBuf b (DelayCase ty arg y) 
        = do tag 1; toBuf b ty; toBuf b arg; toBuf b y
    toBuf b (ConstCase x y)
        = do tag 2; toBuf b x; toBuf b y
    toBuf b (DefaultCase x)
        = do tag 3; toBuf b x

    fromBuf r b 
        = case !getTag of
               0 => do x <- fromBuf r b; t <- fromBuf r b
                       args <- fromBuf r b; y <- fromBuf r b
                       pure (ConCase x t args y)
               1 => do ty <- fromBuf r b; arg <- fromBuf r b; y <- fromBuf r b
                       pure (DelayCase ty arg y)
               2 => do x <- fromBuf r b; y <- fromBuf r b
                       pure (ConstCase x y)
               3 => do x <- fromBuf r b
                       pure (DefaultCase x)
               _ => corrupt "CaseAlt"

export
TTC (Env Term vars) where
  toBuf b [] = pure ()
  toBuf b ((::) bnd env) 
      = do toBuf b bnd; toBuf b env

  -- Length has to correspond to length of 'vars'
  fromBuf s {vars = []} b = pure Nil
  fromBuf s {vars = x :: xs} b
      = do bnd <- fromBuf s b
           env <- fromBuf s b
           pure (bnd :: env)

export
TTC Visibility where
  toBuf b Private = tag 0
  toBuf b Export = tag 1
  toBuf b Public = tag 2

  fromBuf s b 
      = case !getTag of
             0 => pure Private
             1 => pure Export
             2 => pure Public
             _ => corrupt "Visibility"

export
TTC PartialReason where
  toBuf b NotStrictlyPositive = tag 0
  toBuf b (BadCall xs) = do tag 1; toBuf b xs
  toBuf b (RecPath xs) = do tag 2; toBuf b xs

  fromBuf s b 
      = case !getTag of
             0 => pure NotStrictlyPositive
             1 => do xs <- fromBuf s b
                     pure (BadCall xs)
             2 => do xs <- fromBuf s b
                     pure (RecPath xs)
             _ => corrupt "PartialReason"

export
TTC Terminating where
  toBuf b Unchecked = tag 0
  toBuf b IsTerminating = tag 1
  toBuf b (NotTerminating p) = do tag 2; toBuf b p

  fromBuf s b
      = case !getTag of
             0 => pure Unchecked
             1 => pure IsTerminating
             2 => do p <- fromBuf s b
                     pure (NotTerminating p)
             _ => corrupt "Terminating"

export
TTC Covering where
  toBuf b IsCovering = tag 0
  toBuf b (MissingCases ms) 
      = do tag 1
           toBuf b ms
  toBuf b (NonCoveringCall ns) 
      = do tag 2
           toBuf b ns

  fromBuf s b 
      = case !getTag of
             0 => pure IsCovering
             1 => do ms <- fromBuf s b
                     pure (MissingCases ms)
             2 => do ns <- fromBuf s b
                     pure (NonCoveringCall ns)
             _ => corrupt "Covering"

export
TTC Totality where
  toBuf b (MkTotality term cov) = do toBuf b term; toBuf b cov

  fromBuf s b
      = do term <- fromBuf s b
           cov <- fromBuf s b
           pure (MkTotality term cov)

export
TTC (PrimFn n) where
  toBuf b (Add ty) = do tag 0; toBuf b ty
  toBuf b (Sub ty) = do tag 1; toBuf b ty
  toBuf b (Mul ty) = do tag 2; toBuf b ty
  toBuf b (Div ty) = do tag 3; toBuf b ty
  toBuf b (Mod ty) = do tag 4; toBuf b ty
  toBuf b (Neg ty) = do tag 5; toBuf b ty
  toBuf b (LT ty) = do tag 6; toBuf b ty
  toBuf b (LTE ty) = do tag 7; toBuf b ty
  toBuf b (EQ ty) = do tag 8; toBuf b ty
  toBuf b (GTE ty) = do tag 9; toBuf b ty
  toBuf b (GT ty) = do tag 10; toBuf b ty
  toBuf b StrLength = tag 11
  toBuf b StrHead = tag 12
  toBuf b StrTail = tag 13
  toBuf b StrIndex = tag 14
  toBuf b StrCons = tag 15
  toBuf b StrAppend = tag 16
  toBuf b StrReverse = tag 17
  toBuf b StrSubstr = tag 18
  toBuf b (Cast x y) = do tag 19; toBuf b x; toBuf b y
  toBuf b BelieveMe = tag 20

  fromBuf {n} s b
      = case n of
             S Z => fromBuf1 s b
             S (S Z) => fromBuf2 s b
             S (S (S Z)) => fromBuf3 s b
             _ => corrupt "PrimFn"
    where
      fromBuf1 : NameRefs -> Ref Bin Binary ->
                 Core (PrimFn 1)
      fromBuf1 s b
          = case !getTag of
                 5 => do ty <- fromBuf s b; pure (Neg ty)
                 11 => pure StrLength
                 12 => pure StrHead
                 13 => pure StrTail
                 17 => pure StrReverse
                 19 => do x <- fromBuf s b; y <- fromBuf s b; pure (Cast x y)
                 _ => corrupt "PrimFn 1"

      fromBuf2 : NameRefs -> Ref Bin Binary ->
                 Core (PrimFn 2)
      fromBuf2 s b
          = case !getTag of
                 0 => do ty <- fromBuf s b; pure (Add ty)
                 1 => do ty <- fromBuf s b; pure (Sub ty)
                 2 => do ty <- fromBuf s b; pure (Mul ty)
                 3 => do ty <- fromBuf s b; pure (Div ty)
                 4 => do ty <- fromBuf s b; pure (Mod ty)
                 6 => do ty <- fromBuf s b; pure (LT ty)
                 7 => do ty <- fromBuf s b; pure (LTE ty)
                 8 => do ty <- fromBuf s b; pure (EQ ty)
                 9 => do ty <- fromBuf s b; pure (GTE ty)
                 10 => do ty <- fromBuf s b; pure (GT ty)
                 14 => pure StrIndex
                 15 => pure StrCons
                 16 => pure StrAppend
                 _ => corrupt "PrimFn 2"
      
      fromBuf3 : NameRefs -> Ref Bin Binary ->
                 Core (PrimFn 3)
      fromBuf3 s b
          = case !getTag of
                 18 => pure StrSubstr
                 20 => pure BelieveMe
                 _ => corrupt "PrimFn 3"
             
mutual
  export
  TTC (CExp vars) where
    toBuf b (CLocal fc {x} {idx} h) = do tag 0; toBuf b fc; toBuf b x; toBuf b idx
    toBuf b (CRef fc n) = do tag 1; toBuf b fc; toBuf b n
    toBuf b (CLam fc x sc) = do tag 2; toBuf b fc; toBuf b x; toBuf b sc
    toBuf b (CLet fc x val sc) = do tag 3; toBuf b fc; toBuf b x; toBuf b val; toBuf b sc
    toBuf b (CApp fc f as) = assert_total $ do tag 4; toBuf b fc; toBuf b f; toBuf b as
    toBuf b (CCon fc t n as) = assert_total $ do tag 5; toBuf b fc; toBuf b t; toBuf b n; toBuf b as
    toBuf b (COp {arity} fc op as) = assert_total $ do tag 6; toBuf b fc; toBuf b arity; toBuf b op; toBuf b as
    toBuf b (CExtPrim fc f as) = assert_total $ do tag 7; toBuf b fc; toBuf b f; toBuf b as
    toBuf b (CForce fc x) = assert_total $ do tag 8; toBuf b fc; toBuf b x
    toBuf b (CDelay fc x) = assert_total $ do tag 9; toBuf b fc; toBuf b x
    toBuf b (CConCase fc sc alts def) = assert_total $ do tag 10; toBuf b fc; toBuf b sc; toBuf b alts; toBuf b def
    toBuf b (CConstCase fc sc alts def) = assert_total $ do tag 11; toBuf b fc; toBuf b sc; toBuf b alts; toBuf b def
    toBuf b (CPrimVal fc c) = do tag 12; toBuf b fc; toBuf b c
    toBuf b (CErased fc) = do tag 13; toBuf b fc
    toBuf b (CCrash fc msg) = do tag 14; toBuf b fc; toBuf b msg

    fromBuf s b
        = assert_total $ case !getTag of
               0 => do fc <- fromBuf s b
                       x <- fromBuf s b; idx <- fromBuf s b
                       pure (CLocal {x} fc (mkPrf idx))
               1 => do fc <- fromBuf s b
                       n <- fromBuf s b
                       pure (CRef fc n)
               2 => do fc <- fromBuf s b
                       x <- fromBuf s b; sc <- fromBuf s b
                       pure (CLam fc x sc)
               3 => do fc <- fromBuf s b
                       x <- fromBuf s b; val <- fromBuf s b; sc <- fromBuf s b
                       pure (CLet fc x val sc)
               4 => do fc <- fromBuf s b
                       f <- fromBuf s b; as <- fromBuf s b
                       pure (CApp fc f as)
               5 => do fc <- fromBuf s b
                       t <- fromBuf s b; n <- fromBuf s b; as <- fromBuf s b
                       pure (CCon fc t n as)
               6 => do fc <- fromBuf s b
                       arity <- fromBuf s b; op <- fromBuf s b; args <- fromBuf s b
                       pure (COp {arity} fc op args)
               7 => do fc <- fromBuf s b
                       p <- fromBuf s b; as <- fromBuf s b
                       pure (CExtPrim fc p as)
               8 => do fc <- fromBuf s b
                       x <- fromBuf s b
                       pure (CForce fc x)
               9 => do fc <- fromBuf s b
                       x <- fromBuf s b
                       pure (CDelay fc x)
               10 => do fc <- fromBuf s b
                        sc <- fromBuf s b; alts <- fromBuf s b; def <- fromBuf s b
                        pure (CConCase fc sc alts def)
               11 => do fc <- fromBuf s b
                        sc <- fromBuf s b; alts <- fromBuf s b; def <- fromBuf s b
                        pure (CConstCase fc sc alts def)
               12 => do fc <- fromBuf s b
                        c <- fromBuf s b
                        pure (CPrimVal fc c)
               13 => do fc <- fromBuf s b
                        pure (CErased fc)
               14 => do fc <- fromBuf s b
                        msg <- fromBuf s b
                        pure (CCrash fc msg)
               _ => corrupt "CExp"

  export
  TTC (CConAlt vars) where
    toBuf b (MkConAlt n t as sc) = do toBuf b n; toBuf b t; toBuf b as; toBuf b sc

    fromBuf s b
        = do n <- fromBuf s b; t <- fromBuf s b
             as <- fromBuf s b; sc <- fromBuf s b
             pure (MkConAlt n t as sc)

  export
  TTC (CConstAlt vars) where
    toBuf b (MkConstAlt c sc) = do toBuf b c; toBuf b sc

    fromBuf s b
        = do c <- fromBuf s b; sc <- fromBuf s b
             pure (MkConstAlt c sc)

export
  TTC CDef where
    toBuf b (MkFun args cexpr) = do tag 0; toBuf b args; toBuf b cexpr
    toBuf b (MkCon t arity) = do tag 1; toBuf b t; toBuf b arity
    toBuf b (MkError cexpr) = do tag 2; toBuf b cexpr

    fromBuf s b 
        = case !getTag of
               0 => do args <- fromBuf s b; cexpr <- fromBuf s b
                       pure (MkFun args cexpr)
               1 => do t <- fromBuf s b; arity <- fromBuf s b
                       pure (MkCon t arity)
               2 => do cexpr <- fromBuf s b
                       pure (MkError cexpr)
               _ => corrupt "CDef"

export
TTC CG where
  toBuf b Chez = tag 0
  toBuf b Chicken = tag 1
  toBuf b Racket = tag 2

  fromBuf r b
      = case !getTag of
             0 => pure Chez
             1 => pure Chicken
             2 => pure Racket
             _ => corrupt "CG"

export
TTC PairNames where
  toBuf b l
      = do toBuf b (pairType l)
           toBuf b (fstName l)
           toBuf b (sndName l)
  fromBuf r b
      = do ty <- fromBuf r b
           d <- fromBuf r b
           f <- fromBuf r b
           pure (MkPairNs ty d f)

export
TTC RewriteNames where
  toBuf b l
      = do toBuf b (equalType l)
           toBuf b (rewriteName l)
  fromBuf r b
      = do ty <- fromBuf r b
           l <- fromBuf r b
           pure (MkRewriteNs ty l)

export
TTC PrimNames where
  toBuf b l
      = do toBuf b (fromIntegerName l)
           toBuf b (fromStringName l)
           toBuf b (fromCharName l)
  fromBuf r b
      = do i <- fromBuf r b
           str <- fromBuf r b
           c <- fromBuf r b
           pure (MkPrimNs i str c)


export
TTC Def where
  toBuf b None = tag 0
  toBuf b (PMDef args ct rt pats) 
      = do tag 1; toBuf b args; toBuf b ct; toBuf b rt; -- toBuf b pats
  toBuf b (ExternDef a)
      = do tag 2; toBuf b a
  toBuf b (Builtin a)
      = throw (InternalError "Trying to serialise a Builtin")
  toBuf b (DCon t arity) = do tag 3; toBuf b t; toBuf b arity
  toBuf b (TCon t arity parampos detpos ms datacons) 
      = do tag 4; toBuf b t; toBuf b arity; toBuf b parampos
           toBuf b detpos; toBuf b ms; toBuf b datacons
  toBuf b (Hole locs invertible) = do tag 5; toBuf b locs; toBuf b invertible
  toBuf b (BySearch c depth def) 
      = do tag 6; toBuf b c; toBuf b depth; toBuf b def
  toBuf b (Guess guess constraints) = do tag 7; toBuf b guess; toBuf b constraints
  toBuf b ImpBind = tag 8
  toBuf b Delayed = tag 9

  fromBuf r b 
      = case !getTag of
             0 => pure None
             1 => do args <- fromBuf r b 
                     ct <- fromBuf r b
                     rt <- fromBuf r b
--                      pats <- fromBuf r b
                     pure (PMDef args ct rt []) -- pats)
             2 => do a <- fromBuf r b
                     pure (ExternDef a)
             3 => do t <- fromBuf r b; a <- fromBuf r b
                     pure (DCon t a)
             4 => do t <- fromBuf r b; a <- fromBuf r b
                     ps <- fromBuf r b; dets <- fromBuf r b; 
                     ms <- fromBuf r b; cs <- fromBuf r b
                     pure (TCon t a ps dets ms cs)
             5 => do l <- fromBuf r b
                     i <- fromBuf r b
                     pure (Hole l i)
             6 => do c <- fromBuf r b; depth <- fromBuf r b
                     def <- fromBuf r b
                     pure (BySearch c depth def)
             7 => do g <- fromBuf r b; cs <- fromBuf r b
                     pure (Guess g cs)
             8 => pure ImpBind
             9 => pure Context.Delayed
             _ => corrupt "Def"

TTC TotalReq where
  toBuf b Total = tag 0
  toBuf b CoveringOnly = tag 1
  toBuf b PartialOK = tag 2

  fromBuf s b
      = case !getTag of
             0 => pure Total
             1 => pure CoveringOnly
             2 => pure PartialOK
             _ => corrupt "TotalReq"

TTC DefFlag where
  toBuf b Inline = tag 2
  toBuf b Invertible = tag 3
  toBuf b Overloadable = tag 4
  toBuf b TCInline = tag 5
  toBuf b (SetTotal x) = do tag 6; toBuf b x

  fromBuf s b
      = case !getTag of
             2 => pure Inline
             3 => pure Invertible
             4 => pure Overloadable
             5 => pure TCInline
             6 => do x <- fromBuf s b; pure (SetTotal x)
             _ => corrupt "DefFlag"

export
TTC SizeChange where
  toBuf b Smaller = tag 0
  toBuf b Same = tag 1
  toBuf b Unknown = tag 2

  fromBuf s b
      = case !getTag of
             0 => pure Smaller
             1 => pure Same
             2 => pure Unknown
             _ => corrupt "SizeChange"

export
TTC SCCall where
  toBuf b c = do toBuf b (fnCall c); toBuf b (fnArgs c)
  fromBuf s b
      = do fn <- fromBuf s b
           args <- fromBuf s b
           pure (MkSCCall fn args)

export
TTC GlobalDef where
  toBuf b gdef 
      = -- Only write full details for user specified names. The others will
        -- be holes where all we will ever need after loading is the definition
        do toBuf b (fullname gdef)
           toBuf b (definition gdef)
           toBuf b (compexpr gdef)
           when (isUserName (fullname gdef)) $
              do toBuf b (location gdef)
                 toBuf b (type gdef)
                 toBuf b (multiplicity gdef)
                 toBuf b (vars gdef)
                 toBuf b (visibility gdef)
                 toBuf b (totality gdef)
                 toBuf b (flags gdef)
                 toBuf b (map fst (toList (refersTo gdef)))
                 toBuf b (noCycles gdef)
                 toBuf b (sizeChange gdef)

  fromBuf r b 
      = do name <- fromBuf r b
           def <- fromBuf r b
           cdef <- fromBuf r b
           if isUserName name
              then do loc <- fromBuf r b; 
                      ty <- fromBuf r b; mul <- fromBuf r b
                      vars <- fromBuf r b
                      vis <- fromBuf r b; tot <- fromBuf r b
                      fl <- fromBuf r b
                      refsList <- fromBuf r b; 
                      let refs = fromList (map (\x => (x, ())) refsList)
                      c <- fromBuf r b
                      sc <- fromBuf r b
                      pure (MkGlobalDef loc name ty mul vars vis 
                                        tot fl refs c True def cdef sc)
              else do let fc = emptyFC
                      pure (MkGlobalDef fc name (Erased fc)
                                        RigW [] Public unchecked [] empty
                                        False True def cdef [])


