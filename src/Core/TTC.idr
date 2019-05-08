module Core.TTC

import Core.CaseTree
import Core.Core
import Core.Env
import Core.FC
import Core.TT

import Utils.Binary

%default covering

export
TTC FC where
  toBuf b (MkFC file startPos endPos) 
      = pure () -- do toBuf b file; toBuf b startPos; toBuf b endPos
  fromBuf r b
      = pure emptyFC
--       do f <- fromBuf r b; 
--            s <- fromBuf r b; e <- fromBuf r b
--            pure (MkFC f s e)

export
TTC Name where
  toBuf b (NS xs x) = do tag 0; toBuf b xs; toBuf b x
  toBuf b (UN x) = do tag 1; toBuf b x
  toBuf b (MN x y) = do tag 2; toBuf b x; toBuf b y
  toBuf b (PV x y) = do tag 3; toBuf b x; toBuf b y
  toBuf b (Nested x y) = do tag 4; toBuf b x; toBuf b y
  toBuf b (CaseBlock x y) = do tag 5; toBuf b x; toBuf b y
  toBuf b (WithBlock x y) = do tag 6; toBuf b x; toBuf b y
  toBuf b (Resolved x) = do tag 7; toBuf b x

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
                     pure (Nested x y)
             5 => do x <- fromBuf r b
                     y <- fromBuf r b
                     pure (CaseBlock x y)
             6 => do x <- fromBuf r b
                     y <- fromBuf r b
                     pure (WithBlock x y)
             7 => do x <- fromBuf r b
                     Just (n, Just idx) <- coreLift $ readArray r x
                          | Just (n, Nothing) => pure n
                          | Nothing => corrupt "Name index"
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

  fromBuf r b
      = case !getTag of
             0 => pure LInf
             1 => pure LLazy
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

export
TTC AppInfo where
  toBuf b (MkAppInfo an p)
      = do toBuf b an; toBuf b p
  fromBuf r b
      = do an <- fromBuf r b; p <- fromBuf r b
           pure (MkAppInfo an p)

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
    toBuf b (PVar c ty) = do tag 3; toBuf b c -- ; toBuf b ty
    toBuf b (PLet c val ty) = do tag 4; toBuf b c; toBuf b val -- ; toBuf b ty
    toBuf b (PVTy c ty) = do tag 5; toBuf b c -- ; toBuf b ty

    fromBuf r b
        = case !getTag of
               0 => do c <- fromBuf r b; x <- fromBuf r b; pure (Lam c x (Erased emptyFC))
               1 => do c <- fromBuf r b; x <- fromBuf r b; pure (Let c x (Erased emptyFC))
               2 => do c <- fromBuf r b; x <- fromBuf r b; y <- fromBuf r b; pure (Pi c x y)
               3 => do c <- fromBuf r b; pure (PVar c (Erased emptyFC))
               4 => do c <- fromBuf r b; x <- fromBuf r b; pure (PLet c x (Erased emptyFC))
               5 => do c <- fromBuf r b; pure (PVTy c (Erased emptyFC))
               _ => corrupt "Binder"


  export
  TTC (Term vars) where
    toBuf b (Local {name} fc c idx y) 
        = if idx < 244
             then toBuf b (prim__truncBigInt_B8 (12 + cast idx))
             else do tag 0;
                     toBuf b fc -- toBuf b name
                     toBuf b idx
    toBuf b (Ref fc nt name) 
        = do tag 1;
             toBuf b fc; toBuf b nt; toBuf b name
    toBuf b (Meta fc n i xs) 
        = do tag 2;
             toBuf b fc -- Name no longer needed -- toBuf b n; 
             toBuf b i; toBuf b xs
    toBuf b (Bind fc x bnd scope) 
        = do tag 3;
             toBuf b fc; toBuf b x; 
             toBuf b bnd; toBuf b scope
    toBuf b (App fc fn p arg) 
        = do tag 4;
             let (fn, args) = getFnArgs (App fc fn p arg)
             toBuf b fc; toBuf b fn; -- toBuf b p; 
             toBuf b (map snd args)
    toBuf b (As fc as tm)
        = do tag 5;
             toBuf b fc; toBuf b as; toBuf b tm
    toBuf b (TDelayed fc r tm) 
        = do tag 6;
             toBuf b fc; toBuf b r; toBuf b tm
    toBuf b (TDelay fc r tm)
        = do tag 7;
             toBuf b fc; toBuf b r; toBuf b tm
    toBuf b (TForce fc tm)
        = do tag 8;
             toBuf b fc; toBuf b tm
    toBuf b (PrimVal fc c) 
        = do tag 9;
             toBuf b fc; toBuf b c
    toBuf b (Erased fc) 
        = do tag 10;
             toBuf b fc
    toBuf b (TType fc)
        = do tag 11;
             toBuf b fc

    fromBuf r b 
        = case !getTag of
               0 => do fc <- fromBuf r b; -- name <- fromBuf r b
                       idx <- fromBuf r b
                       pure (Local {name=UN "_"} fc Nothing idx (mkPrf idx))
               1 => do fc <- fromBuf r b; nt <- fromBuf r b; name <- fromBuf r b
                       pure (Ref fc nt name)
               2 => do fc <- fromBuf r b; -- n <- fromBuf r b
                       i <- fromBuf r b
                       xs <- fromBuf r b
                       pure (Meta fc (UN "metavar") i xs)
               3 => do fc <- fromBuf r b; x <- fromBuf r b
                       bnd <- fromBuf r b; scope <- fromBuf r b
                       pure (Bind fc x bnd scope)
               4 => do fc <- fromBuf r b; fn <- fromBuf r b
  --                      p <- fromBuf r b; 
                       args <- fromBuf r b
                       pure (apply fc (explApp Nothing) fn args)
               5 => do fc <- fromBuf r b
                       as <- fromBuf r b; tm <- fromBuf r b
                       pure (As fc as tm)
               6 => do fc <- fromBuf r b; lr <- fromBuf r b; tm <- fromBuf r b
                       pure (TDelayed fc lr tm)
               7 => do fc <- fromBuf r b; lr <- fromBuf r b; tm <- fromBuf r b
                       pure (TDelay fc lr tm)
               8 => do fc <- fromBuf r b; tm <- fromBuf r b
                       pure (TForce fc tm)
               9 => do fc <- fromBuf r b; c <- fromBuf r b
                       pure (PrimVal fc c)
               10 => do fc <- fromBuf r b; pure (Erased fc)
               11 => do fc <- fromBuf r b; pure (TType fc)
               idxp => do -- fc <- fromBuf r b; -- name <- fromBuf r b
                          let idx = fromInteger (prim__sextB8_BigInt idxp - 12)
                          pure (Local {name=UN "_"} 
                                      emptyFC Nothing idx (mkPrf idx))

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
  toBuf b (PLoc fc x) 
      = do tag 5; toBuf b fc; toBuf b x
  toBuf b (PUnmatchable fc x) 
      = do tag 6; toBuf b fc; toBuf b x

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
             5 => do fc <- fromBuf r b; x <- fromBuf r b
                     pure (PLoc fc x)
             6 => do fc <- fromBuf r b; x <- fromBuf r b
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
    toBuf b (ConstCase x y)
        = do tag 1; toBuf b x; toBuf b y
    toBuf b (DefaultCase x)
        = do tag 2; toBuf b x

    fromBuf r b 
        = case !getTag of
               0 => do x <- fromBuf r b; t <- fromBuf r b
                       args <- fromBuf r b; y <- fromBuf r b
                       pure (ConCase x t args y)
               1 => do x <- fromBuf r b; y <- fromBuf r b
                       pure (ConstCase x y)
               2 => do x <- fromBuf r b
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
             

