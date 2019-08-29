module Core.Reflect

import Core.Context
import Core.Env
import Core.Normalise
import Core.Value
import Core.TT

%default covering

public export
interface Reify a where
  reify : Defs -> NF vars -> Core a

public export
interface Reflect a where
  reflect : FC -> Defs -> Env Term vars -> a -> Core (Term vars)

export
getCon : FC -> Defs -> Name -> Core (Term vars)
getCon fc defs n
    = case !(lookupDefExact n (gamma defs)) of
           Just (DCon t a) => resolved (gamma defs) (Ref fc (DataCon t a) n)
           Just (TCon t a _ _ _ _) => resolved (gamma defs) (Ref fc (TyCon t a) n)
           Just _ => resolved (gamma defs) (Ref fc Func n)
           _ => throw (UndefinedName fc n)

export
appCon : FC -> Defs -> Name -> List (Term vars) -> Core (Term vars)
appCon fc defs n args
    = do fn <- getCon fc defs n
         resolved (gamma defs) (apply fc fn args)

export
prelude : String -> Name
prelude n = NS ["Prelude"] (UN n)

export
builtin : String -> Name
builtin n = NS ["Builtin"] (UN n)

export
primio : String -> Name
primio n = NS ["PrimIO"] (UN n)

export
reflection : String -> Name
reflection n = NS ["Reflection", "Language"] (UN n)

export
cantReify : NF vars -> String -> Core a
cantReify val ty 
    = throw (GenericMsg (getLoc val) ("Can't reify as " ++ ty))

export
cantReflect : FC -> String -> Core a
cantReflect fc ty 
    = throw (GenericMsg fc ("Can't reflect as " ++ ty))

export
Reify () where
  reify defs _ = pure ()

export
Reflect () where
  reflect fc defs env _ = getCon fc defs (builtin "MkUnit")

export
Reify String where
  reify defs (NPrimVal _ (Str str)) = pure str
  reify defs val = cantReify val "String"

export
Reflect String where
  reflect fc defs env x = pure (PrimVal fc (Str x))

export
Reify Int where
  reify defs (NPrimVal _ (I v)) = pure v
  reify defs val = cantReify val "Int"

export
Reflect Int where
  reflect fc defs env x = pure (PrimVal fc (I x))

export
Reify Integer where
  reify defs (NPrimVal _ (BI v)) = pure v
  reify defs val = cantReify val "Integer"

export
Reflect Integer where
  reflect fc defs env x = pure (PrimVal fc (BI x))

export
Reify Char where
  reify defs (NPrimVal _ (Ch v)) = pure v
  reify defs val = cantReify val "Char"

export
Reflect Char where
  reflect fc defs env x = pure (PrimVal fc (Ch x))

export
Reify Double where
  reify defs (NPrimVal _ (Db v)) = pure v
  reify defs val = cantReify val "Double"

export
Reflect Double where
  reflect fc defs env x = pure (PrimVal fc (Db x))

export
Reify Bool where
  reify defs (NDCon _ (NS _ (UN "True")) _ _ _) = pure True
  reify defs (NDCon _ (NS _ (UN "False")) _ _ _) = pure False
  reify defs val = cantReify val "Bool"

export
Reflect Bool where
  reflect fc defs env True = getCon fc defs (prelude "True")
  reflect fc defs env False = getCon fc defs (prelude "False")

export
Reify Nat where
  reify defs (NDCon _ (NS _ (UN "Z")) _ _ _)
      = pure Z
  reify defs (NDCon _ (NS _ (UN "S")) _ _ [k])
      = do k' <- reify defs !(evalClosure defs k)
           pure (S k')
  reify defs val = cantReify val "Nat"

export
Reflect Nat where
  reflect fc defs env Z = getCon fc defs (prelude "Z")
  reflect fc defs env (S k)
      = do k' <- reflect fc defs env k
           appCon fc defs (prelude "S") [k']

export
Reify a => Reify (List a) where
  reify defs (NDCon _ (NS _ (UN "Nil")) _ _ _)
      = pure []
  reify defs (NDCon _ (NS _ (UN "::")) _ _ [_, x, xs])
      = do x' <- reify defs !(evalClosure defs x)
           xs' <- reify defs !(evalClosure defs xs)
           pure (x' :: xs')
  reify defs val = cantReify val "List"

export
Reflect a => Reflect (List a) where
  reflect fc defs env [] = appCon fc defs (prelude "Nil") [Erased fc]
  reflect fc defs env (x :: xs)
      = do x' <- reflect fc defs env x
           xs' <- reflect fc defs env xs
           appCon fc defs (prelude "::") [Erased fc, x', xs']

export
(Reify a, Reify b) => Reify (a, b) where
  reify defs (NDCon _ (NS _ (UN "MkPair")) _ _ [_, _, x, y])
      = do x' <- reify defs !(evalClosure defs x)
           y' <- reify defs !(evalClosure defs y)
           pure (x', y')
  reify defs val = cantReify val "Pair"

export
(Reflect a, Reflect b) => Reflect (a, b) where
  reflect fc defs env (x, y)
      = do x' <- reflect fc defs env x
           y' <- reflect fc defs env y
           appCon fc defs (builtin "MkPair") [Erased fc, Erased fc, x', y']

export
Reify Name where
  reify defs (NDCon _ (NS _ (UN "UN")) _ _ [str])
      = do str' <- reify defs !(evalClosure defs str)
           pure (UN str')
  reify defs (NDCon _ (NS _ (UN "MN")) _ _ [str, i])
      = do str' <- reify defs !(evalClosure defs str)
           i' <- reify defs !(evalClosure defs i)
           pure (MN str' i')
  reify defs (NDCon _ (NS _ (UN "NS")) _ _ [ns, n])
      = do ns' <- reify defs !(evalClosure defs ns)
           n' <- reify defs !(evalClosure defs n)
           pure (NS ns' n')
  reify defs val = cantReify val "Name"

export
Reflect Name where
  reflect fc defs env (UN x) 
      = do x' <- reflect fc defs env x
           appCon fc defs (reflection "UN") [x']
  reflect fc defs env (MN x i) 
      = do x' <- reflect fc defs env x
           i' <- reflect fc defs env i
           appCon fc defs (reflection "MN") [x', i']
  reflect fc defs env (NS ns n) 
      = do ns' <- reflect fc defs env ns
           n' <- reflect fc defs env n
           appCon fc defs (reflection "NS") [ns', n']
  reflect fc defs env val = cantReflect fc "Name"

export
Reify NameType where
  reify defs (NDCon _ (NS _ (UN "Bound")) _ _ _)
      = pure Bound
  reify defs (NDCon _ (NS _ (UN "Func")) _ _ _)
      = pure Func
  reify defs (NDCon _ (NS _ (UN "DataCon")) _ _ [t,i])
      = do t' <- reify defs !(evalClosure defs t)
           i' <- reify defs !(evalClosure defs i)
           pure (DataCon t' i')
  reify defs (NDCon _ (NS _ (UN "TyCon")) _ _ [t,i])
      = do t' <- reify defs !(evalClosure defs t)
           i' <- reify defs !(evalClosure defs i)
           pure (TyCon t' i')
  reify defs val = cantReify val "NameType"

export
Reflect NameType where
  reflect fc defs env Bound = getCon fc defs (reflection "Bound")
  reflect fc defs env Func = getCon fc defs (reflection "Func")
  reflect fc defs env (DataCon t i)
      = do t' <- reflect fc defs env t
           i' <- reflect fc defs env i
           appCon fc defs (reflection "DataCon") [t', i']
  reflect fc defs env (TyCon t i)
      = do t' <- reflect fc defs env t
           i' <- reflect fc defs env i
           appCon fc defs (reflection "TyCon") [t', i']

export
Reify Constant where
  reify defs (NDCon _ (NS _ (UN "I")) _ _ [x])
      = do x' <- reify defs !(evalClosure defs x)
           pure (I x')
  reify defs (NDCon _ (NS _ (UN "BI")) _ _ [x])
      = do x' <- reify defs !(evalClosure defs x)
           pure (BI x')
  reify defs (NDCon _ (NS _ (UN "Str")) _ _ [x])
      = do x' <- reify defs !(evalClosure defs x)
           pure (Str x')
  reify defs (NDCon _ (NS _ (UN "Ch")) _ _ [x])
      = do x' <- reify defs !(evalClosure defs x)
           pure (Ch x')
  reify defs (NDCon _ (NS _ (UN "Db")) _ _ [x])
      = do x' <- reify defs !(evalClosure defs x)
           pure (Db x')
  reify defs (NDCon _ (NS _ (UN "WorldVal")) _ _ [])
      = pure WorldVal
  reify defs (NDCon _ (NS _ (UN "IntType")) _ _ [])
      = pure IntType
  reify defs (NDCon _ (NS _ (UN "IntegerType")) _ _ [])
      = pure IntegerType
  reify defs (NDCon _ (NS _ (UN "StringType")) _ _ [])
      = pure StringType
  reify defs (NDCon _ (NS _ (UN "CharType")) _ _ [])
      = pure CharType
  reify defs (NDCon _ (NS _ (UN "DoubleType")) _ _ [])
      = pure DoubleType
  reify defs (NDCon _ (NS _ (UN "WorldType")) _ _ [])
      = pure WorldType
  reify defs val = cantReify val "Constant"

export
Reflect Constant where
  reflect fc defs env (I x)
      = do x' <- reflect fc defs env x
           appCon fc defs (reflection "I") [x']
  reflect fc defs env (BI x)
      = do x' <- reflect fc defs env x
           appCon fc defs (reflection "BI") [x']
  reflect fc defs env (Str x)
      = do x' <- reflect fc defs env x
           appCon fc defs (reflection "Str") [x']
  reflect fc defs env (Ch x)
      = do x' <- reflect fc defs env x
           appCon fc defs (reflection "Ch") [x']
  reflect fc defs env (Db x)
      = do x' <- reflect fc defs env x
           appCon fc defs (reflection "Db") [x']
  reflect fc defs env WorldVal
      = getCon fc defs (reflection "WorldVal")
  reflect fc defs env IntType
      = getCon fc defs (reflection "IntTyoe")
  reflect fc defs env IntegerType
      = getCon fc defs (reflection "IntegerType")
  reflect fc defs env StringType
      = getCon fc defs (reflection "StringType")
  reflect fc defs env CharType
      = getCon fc defs (reflection "CharType")
  reflect fc defs env DoubleType
      = getCon fc defs (reflection "DoubleTyoe")
  reflect fc defs env WorldType
      = getCon fc defs (reflection "WorldType")

export
Reify Visibility where
  reify defs (NDCon _ (NS _ (UN "Private")) _ _ [])
      = pure Private
  reify defs (NDCon _ (NS _ (UN "Export")) _ _ [])
      = pure Export
  reify defs (NDCon _ (NS _ (UN "Public")) _ _ [])
      = pure Public
  reify defs val = cantReify val "Visibility"

export
Reflect Visibility where
  reflect fc defs env Private = getCon fc defs (reflection "Private")
  reflect fc defs env Export = getCon fc defs (reflection "Export")
  reflect fc defs env Public = getCon fc defs (reflection "Public")

export
Reify RigCount where
  reify defs (NDCon _ (NS _ (UN "M0")) _ _ [])
      = pure Rig0
  reify defs (NDCon _ (NS _ (UN "M1")) _ _ [])
      = pure Rig1
  reify defs (NDCon _ (NS _ (UN "MW")) _ _ [])
      = pure RigW
  reify defs val = cantReify val "Count"

export
Reflect RigCount where
  reflect fc defs env Rig0 = getCon fc defs (reflection "M0")
  reflect fc defs env Rig1 = getCon fc defs (reflection "M1")
  reflect fc defs env RigW = getCon fc defs (reflection "MW")

export
Reify PiInfo where
  reify defs (NDCon _ (NS _ (UN "ImplicitArg")) _ _ [])
      = pure Implicit
  reify defs (NDCon _ (NS _ (UN "ExplicitArg")) _ _ [])
      = pure Explicit
  reify defs (NDCon _ (NS _ (UN "AutoImplicit")) _ _ [])
      = pure AutoImplicit
  reify defs val = cantReify val "PiInfo"

export
Reflect PiInfo where
  reflect fc defs env Implicit = getCon fc defs (reflection "ImplicitArg")
  reflect fc defs env Explicit = getCon fc defs (reflection "ExplicitArg")
  reflect fc defs env AutoImplicit = getCon fc defs (reflection "AutoImplicit")

export
Reify LazyReason where
  reify defs (NDCon _ (NS _ (UN "LInf")) _ _ [])
      = pure LInf
  reify defs (NDCon _ (NS _ (UN "LLazy")) _ _ [])
      = pure LLazy
  reify defs (NDCon _ (NS _ (UN "LUnknown")) _ _ [])
      = pure LUnknown
  reify defs val = cantReify val "LazyReason"

export
Reflect LazyReason where
  reflect fc defs env LInf = getCon fc defs (reflection "LInf")
  reflect fc defs env LLazy = getCon fc defs (reflection "LLazy")
  reflect fc defs env LUnknown = getCon fc defs (reflection "LUnknown")

export
Reify FC where
  reify defs (NDCon _ (NS _ (UN "MkFC")) _ _ [fn, start, end])
      = do fn' <- reify defs !(evalClosure defs fn)
           start' <- reify defs !(evalClosure defs start)
           end' <- reify defs !(evalClosure defs start)
           pure (MkFC fn' start' end')
  reify defs (NDCon _ (NS _ (UN "EmptyFC")) _ _ [])
      = pure EmptyFC
  reify defs val = cantReify val "FC"

export
Reflect FC where
  reflect fc defs env (MkFC fn start end)
      = do fn' <- reflect fc defs env fn
           start' <- reflect fc defs env start
           end' <- reflect fc defs env end
           appCon fc defs (reflection "MkFC") [fn', start', end']
  reflect fc defs env EmptyFC = getCon fc defs (reflection "EmptyFC")

-- Reflection of well typed terms: We don't reify terms because that involves
-- type checking, but we can reflect them

export
Reflect (IsVar name idx vs) where
  reflect fc defs env First
      = appCon fc defs (reflection "First") [Erased fc, Erased fc]
  reflect fc defs env (Later p) 
      = do p' <- reflect fc defs env p
           appCon fc defs (reflection "Later") 
                  [Erased fc, Erased fc, Erased fc, Erased fc, p']

-- Assume terms are normalised so there's not Let bindings in particular
export
Reflect (Term vs) where
  reflect fc defs env (Local {name} lfc _ idx prf)
      = do name' <- reflect fc defs env name
           lfc' <- reflect fc defs env lfc
           idx' <- reflect fc defs env idx
           prf' <- reflect fc defs env prf
           appCon fc defs (reflection "Local")
                  [Erased fc, Erased fc, lfc', idx', prf']
  reflect fc defs env (Ref rfc nt n)
      = do rfc' <- reflect fc defs env rfc
           nt' <- reflect fc defs env nt
           n' <- reflect fc defs env n
           appCon fc defs (reflection "Ref")
                  [Erased fc, rfc', nt', n']
  reflect fc defs env (Bind bfc x (Pi c p ty) sc)
      = do bfc' <- reflect fc defs env bfc
           x' <- reflect fc defs env x
           c' <- reflect fc defs env c
           p' <- reflect fc defs env p
           ty' <- reflect fc defs env ty
           sc' <- reflect fc defs env sc
           appCon fc defs (reflection "Pi")
                  [Erased fc, bfc', c', p', x', ty', sc']
  reflect fc defs env (Bind bfc x (Lam c p ty) sc)
      = do bfc' <- reflect fc defs env bfc
           x' <- reflect fc defs env x
           c' <- reflect fc defs env c
           p' <- reflect fc defs env p
           ty' <- reflect fc defs env ty
           sc' <- reflect fc defs env sc
           appCon fc defs (reflection "Lam")
                  [Erased fc, bfc', c', p', x', ty', sc']
  reflect fc defs env (App afc fn arg)
      = do afc' <- reflect fc defs env afc
           fn' <- reflect fc defs env fn
           arg' <- reflect fc defs env arg
           appCon fc defs (reflection "App")
                  [Erased fc, afc', fn', arg']
  reflect fc defs env (TDelayed dfc r tm)
      = do dfc' <- reflect fc defs env dfc
           r' <- reflect fc defs env r
           tm' <- reflect fc defs env tm
           appCon fc defs (reflection "TDelayed")
                  [Erased fc, dfc', r', tm']
  reflect fc defs env (TDelay dfc r ty tm)
      = do dfc' <- reflect fc defs env dfc
           r' <- reflect fc defs env r
           ty' <- reflect fc defs env ty
           tm' <- reflect fc defs env tm
           appCon fc defs (reflection "TDelay")
                  [Erased fc, dfc', r', ty', tm']
  reflect fc defs env (TForce dfc tm)
      = do dfc' <- reflect fc defs env dfc
           tm' <- reflect fc defs env tm
           appCon fc defs (reflection "TForce")
                  [Erased fc, dfc', tm']
  reflect fc defs env (PrimVal pfc c)
      = do pfc' <- reflect fc defs env pfc
           c' <- reflect fc defs env c
           appCon fc defs (reflection "PrimVal")
                  [Erased fc, pfc', c']
  reflect fc defs env (Erased efc)
      = do efc' <- reflect fc defs env efc
           appCon fc defs (reflection "Erased")
                  [Erased fc, efc']
  reflect fc defs env (TType tfc)
      = do tfc' <- reflect fc defs env tfc
           appCon fc defs (reflection "TType")
                  [Erased fc, tfc']
  reflect fc defs env val = cantReflect fc "Term"

