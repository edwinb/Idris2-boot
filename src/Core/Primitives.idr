module Core.Primitives

import Core.Core
import Core.Context
import Core.TT
import Core.Value
import Utils.String

import Data.Vect

%default covering

public export
record Prim where
  constructor MkPrim
  fn : PrimFn arity
  type : ClosedTerm
  totality : Totality

binOp : (Constant -> Constant -> Maybe Constant) ->
        {vars : _} -> Vect 2 (NF vars) -> Maybe (NF vars)
binOp fn [NPrimVal fc x, NPrimVal _ y]
    = map (NPrimVal fc) (fn x y)
binOp _ _ = Nothing

unaryOp : (Constant -> Maybe Constant) ->
          {vars : _} -> Vect 1 (NF vars) -> Maybe (NF vars)
unaryOp fn [NPrimVal fc x]
    = map (NPrimVal fc) (fn x)
unaryOp _ _ = Nothing

castString : Vect 1 (NF vars) -> Maybe (NF vars)
castString [NPrimVal fc (I i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (BI i)] = Just (NPrimVal fc (Str (show i)))
castString [NPrimVal fc (Ch i)] = Just (NPrimVal fc (Str (stripQuotes (show i))))
castString [NPrimVal fc (Db i)] = Just (NPrimVal fc (Str (show i)))
castString _ = Nothing

castInteger : Vect 1 (NF vars) -> Maybe (NF vars)
castInteger [NPrimVal fc (I i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (Ch i)] = Just (NPrimVal fc (BI (cast (cast {to=Int} i))))
castInteger [NPrimVal fc (Db i)] = Just (NPrimVal fc (BI (cast i)))
castInteger [NPrimVal fc (Str i)] = Just (NPrimVal fc (BI (cast i)))
castInteger _ = Nothing

castInt : Vect 1 (NF vars) -> Maybe (NF vars)
castInt [NPrimVal fc (BI i)] = Just (NPrimVal fc (I (fromInteger i)))
castInt [NPrimVal fc (Db i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (Ch i)] = Just (NPrimVal fc (I (cast i)))
castInt [NPrimVal fc (Str i)] = Just (NPrimVal fc (I (cast i)))
castInt _ = Nothing

castDouble : Vect 1 (NF vars) -> Maybe (NF vars)
castDouble [NPrimVal fc (I i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (BI i)] = Just (NPrimVal fc (Db (cast i)))
castDouble [NPrimVal fc (Str i)] = Just (NPrimVal fc (Db (cast i)))
castDouble _ = Nothing

castChar : Vect 1 (NF vars) -> Maybe (NF vars)
castChar [NPrimVal fc (I i)] = Just (NPrimVal fc (Ch (cast i)))
castChar _ = Nothing

strLength : Vect 1 (NF vars) -> Maybe (NF vars)
strLength [NPrimVal fc (Str s)] = Just (NPrimVal fc (I (cast (length s))))
strLength _ = Nothing

strHead : Vect 1 (NF vars) -> Maybe (NF vars)
strHead [NPrimVal fc (Str "")] = Nothing
strHead [NPrimVal fc (Str str)]
    = Just (NPrimVal fc (Ch (assert_total (strHead str))))
strHead _ = Nothing

strTail : Vect 1 (NF vars) -> Maybe (NF vars)
strTail [NPrimVal fc (Str "")] = Nothing
strTail [NPrimVal fc (Str str)]
    = Just (NPrimVal fc (Str (assert_total (strTail str))))
strTail _ = Nothing

strIndex : Vect 2 (NF vars) -> Maybe (NF vars)
strIndex [NPrimVal fc (Str str), NPrimVal _ (I i)]
    = if i >= 0 && cast i < length str
         then Just (NPrimVal fc (Ch (assert_total (prim__strIndex str i))))
         else Nothing
strIndex _ = Nothing

strCons : Vect 2 (NF vars) -> Maybe (NF vars)
strCons [NPrimVal fc (Ch x), NPrimVal _ (Str y)]
    = Just (NPrimVal fc (Str (strCons x y)))
strCons _ = Nothing

strAppend : Vect 2 (NF vars) -> Maybe (NF vars)
strAppend [NPrimVal fc (Str x), NPrimVal _ (Str y)]
    = Just (NPrimVal fc (Str (x ++ y)))
strAppend _ = Nothing

strReverse : Vect 1 (NF vars) -> Maybe (NF vars)
strReverse [NPrimVal fc (Str x)]
    = Just (NPrimVal fc (Str (reverse x)))
strReverse _ = Nothing

strSubstr : Vect 3 (NF vars) -> Maybe (NF vars)
strSubstr [NPrimVal fc (I start), NPrimVal _ (I len), NPrimVal _ (Str str)]
    = Just (NPrimVal fc (Str (prim__strSubstr start len str)))
strSubstr _ = Nothing

add : Constant -> Constant -> Maybe Constant
add (BI x) (BI y) = pure $ BI (x + y)
add (I x) (I y) = pure $ I (x + y)
add (Ch x) (Ch y) = pure $ Ch (cast (cast {to=Int} x + cast y))
add (Db x) (Db y) = pure $ Db (x + y)
add _ _ = Nothing

sub : Constant -> Constant -> Maybe Constant
sub (BI x) (BI y) = pure $ BI (x - y)
sub (I x) (I y) = pure $ I (x - y)
sub (Ch x) (Ch y) = pure $ Ch (cast (cast {to=Int} x - cast y))
sub (Db x) (Db y) = pure $ Db (x - y)
sub _ _ = Nothing

mul : Constant -> Constant -> Maybe Constant
mul (BI x) (BI y) = pure $ BI (x * y)
mul (I x) (I y) = pure $ I (x * y)
mul (Db x) (Db y) = pure $ Db (x * y)
mul _ _ = Nothing

div : Constant -> Constant -> Maybe Constant
div (BI x) (BI 0) = Nothing
div (BI x) (BI y) = pure $ BI (assert_total (x `div` y))
div (I x) (I 0) = Nothing
div (I x) (I y) = pure $ I (assert_total (x `div` y))
div (Db x) (Db y) = pure $ Db (x / y)
div _ _ = Nothing

mod : Constant -> Constant -> Maybe Constant
mod (BI x) (BI 0) = Nothing
mod (BI x) (BI y) = pure $ BI (assert_total (x `mod` y))
mod (I x) (I 0) = Nothing
mod (I x) (I y) = pure $ I (assert_total (x `mod` y))
mod _ _ = Nothing

shiftl : Constant -> Constant -> Maybe Constant
shiftl (I x) (I y) = pure $ I (shiftL x y)
shiftl (BI x) (BI y) = pure $ BI (prim__shlBigInt x y)
shiftl _ _ = Nothing

shiftr : Constant -> Constant -> Maybe Constant
shiftr (I x) (I y) = pure $ I (shiftR x y)
shiftr (BI x) (BI y) = pure $ BI (prim__ashrBigInt x y)
shiftr _ _ = Nothing

band : Constant -> Constant -> Maybe Constant
band (I x) (I y) = pure $ I (prim__andInt x y)
band (BI x) (BI y) = pure $ BI (prim__andBigInt x y)
band _ _ = Nothing

bor : Constant -> Constant -> Maybe Constant
bor (I x) (I y) = pure $ I (prim__orInt x y)
bor (BI x) (BI y) = pure $ BI (prim__orBigInt x y)
bor _ _ = Nothing

bxor : Constant -> Constant -> Maybe Constant
bxor (I x) (I y) = pure $ I (prim__xorInt x y)
bxor _ _ = Nothing

neg : Constant -> Maybe Constant
neg (BI x) = pure $ BI (-x)
neg (I x) = pure $ I (-x)
neg (Db x) = pure $ Db (-x)
neg _ = Nothing

toInt : Bool -> Constant
toInt True = I 1
toInt False = I 0

lt : Constant -> Constant -> Maybe Constant
lt (I x) (I y) = pure $ toInt (x < y)
lt (BI x) (BI y) = pure $ toInt (x < y)
lt (Str x) (Str y) = pure $ toInt (x < y)
lt (Ch x) (Ch y) = pure $ toInt (x < y)
lt (Db x) (Db y) = pure $ toInt (x < y)
lt _ _ = Nothing

lte : Constant -> Constant -> Maybe Constant
lte (I x) (I y) = pure $ toInt (x <= y)
lte (BI x) (BI y) = pure $ toInt (x <= y)
lte (Str x) (Str y) = pure $ toInt (x <= y)
lte (Ch x) (Ch y) = pure $ toInt (x <= y)
lte (Db x) (Db y) = pure $ toInt (x <= y)
lte _ _ = Nothing

eq : Constant -> Constant -> Maybe Constant
eq (I x) (I y) = pure $ toInt (x == y)
eq (BI x) (BI y) = pure $ toInt (x == y)
eq (Str x) (Str y) = pure $ toInt (x == y)
eq (Ch x) (Ch y) = pure $ toInt (x == y)
eq (Db x) (Db y) = pure $ toInt (x == y)
eq _ _ = Nothing

gte : Constant -> Constant -> Maybe Constant
gte (I x) (I y) = pure $ toInt (x >= y)
gte (BI x) (BI y) = pure $ toInt (x >= y)
gte (Str x) (Str y) = pure $ toInt (x >= y)
gte (Ch x) (Ch y) = pure $ toInt (x >= y)
gte (Db x) (Db y) = pure $ toInt (x >= y)
gte _ _ = Nothing

gt : Constant -> Constant -> Maybe Constant
gt (I x) (I y) = pure $ toInt (x > y)
gt (BI x) (BI y) = pure $ toInt (x > y)
gt (Str x) (Str y) = pure $ toInt (x > y)
gt (Ch x) (Ch y) = pure $ toInt (x > y)
gt (Db x) (Db y) = pure $ toInt (x > y)
gt _ _ = Nothing

doubleOp : (Double -> Double) -> Vect 1 (NF vars) -> Maybe (NF vars)
doubleOp f [NPrimVal fc (Db x)] = Just (NPrimVal fc (Db (f x)))
doubleOp f _ = Nothing

doubleExp : Vect 1 (NF vars) -> Maybe (NF vars)
doubleExp = doubleOp exp

doubleLog : Vect 1 (NF vars) -> Maybe (NF vars)
doubleLog = doubleOp log

doubleSin : Vect 1 (NF vars) -> Maybe (NF vars)
doubleSin = doubleOp sin

doubleCos : Vect 1 (NF vars) -> Maybe (NF vars)
doubleCos = doubleOp cos

doubleTan : Vect 1 (NF vars) -> Maybe (NF vars)
doubleTan = doubleOp tan

doubleASin : Vect 1 (NF vars) -> Maybe (NF vars)
doubleASin = doubleOp asin

doubleACos : Vect 1 (NF vars) -> Maybe (NF vars)
doubleACos = doubleOp acos

doubleATan : Vect 1 (NF vars) -> Maybe (NF vars)
doubleATan = doubleOp atan

doubleSqrt : Vect 1 (NF vars) -> Maybe (NF vars)
doubleSqrt = doubleOp sqrt

doubleFloor : Vect 1 (NF vars) -> Maybe (NF vars)
doubleFloor = doubleOp floor

doubleCeiling : Vect 1 (NF vars) -> Maybe (NF vars)
doubleCeiling = doubleOp ceiling

-- Only reduce for concrete values
believeMe : Vect 3 (NF vars) -> Maybe (NF vars)
believeMe [_, _, val@(NDCon _ _ _ _ _)] = Just val
believeMe [_, _, val@(NTCon _ _ _ _ _)] = Just val
believeMe [_, _, val@(NPrimVal _ _)] = Just val
believeMe [_, _, NType fc] = Just (NType fc)
believeMe [_, _, val] = Nothing

constTy : Constant -> Constant -> Constant -> ClosedTerm
constTy a b c
    = PrimVal emptyFC a `linFnType`
         (PrimVal emptyFC b `linFnType` PrimVal emptyFC c)

constTy3 : Constant -> Constant -> Constant -> Constant -> ClosedTerm
constTy3 a b c d
    = PrimVal emptyFC a `linFnType`
         (PrimVal emptyFC b `linFnType`
             (PrimVal emptyFC c `linFnType` PrimVal emptyFC d))

predTy : Constant -> Constant -> ClosedTerm
predTy a b = PrimVal emptyFC a `linFnType` PrimVal emptyFC b

arithTy : Constant -> ClosedTerm
arithTy t = constTy t t t

cmpTy : Constant -> ClosedTerm
cmpTy t = constTy t t IntType

doubleTy : ClosedTerm
doubleTy = predTy DoubleType DoubleType

believeMeTy : ClosedTerm
believeMeTy
    = Bind emptyFC (UN "a") (Pi erased Explicit (TType emptyFC)) $
      Bind emptyFC (UN "b") (Pi erased Explicit (TType emptyFC)) $
      Bind emptyFC (UN "x") (Pi top Explicit (Local emptyFC Nothing _ (Later First))) $
      Local emptyFC Nothing _ (Later First)

crashTy : ClosedTerm
crashTy
    = Bind emptyFC (UN "a") (Pi erased Explicit (TType emptyFC)) $
      Bind emptyFC (UN "msg") (Pi top Explicit (PrimVal emptyFC StringType)) $
      Local emptyFC Nothing _ (Later First)

castTo : Constant -> Vect 1 (NF vars) -> Maybe (NF vars)
castTo IntType = castInt
castTo IntegerType = castInteger
castTo StringType = castString
castTo CharType = castChar
castTo DoubleType = castDouble
castTo _ = const Nothing

export
getOp : PrimFn arity ->
        {vars : List Name} -> Vect arity (NF vars) -> Maybe (NF vars)
getOp (Add ty) = binOp add
getOp (Sub ty) = binOp sub
getOp (Mul ty) = binOp mul
getOp (Div ty) = binOp div
getOp (Mod ty) = binOp mod
getOp (Neg ty) = unaryOp neg
getOp (ShiftL ty) = binOp shiftl
getOp (ShiftR ty) = binOp shiftr

getOp (BAnd ty) = binOp band
getOp (BOr ty) = binOp bor
getOp (BXOr ty) = binOp bxor

getOp (LT ty) = binOp lt
getOp (LTE ty) = binOp lte
getOp (EQ ty) = binOp eq
getOp (GTE ty) = binOp gte
getOp (GT ty) = binOp gt

getOp StrLength = strLength
getOp StrHead = strHead
getOp StrTail = strTail
getOp StrIndex = strIndex
getOp StrCons = strCons
getOp StrAppend = strAppend
getOp StrReverse = strReverse
getOp StrSubstr = strSubstr

getOp DoubleExp = doubleExp
getOp DoubleLog = doubleLog
getOp DoubleSin = doubleSin
getOp DoubleCos = doubleCos
getOp DoubleTan = doubleTan
getOp DoubleASin = doubleASin
getOp DoubleACos = doubleACos
getOp DoubleATan = doubleATan
getOp DoubleSqrt = doubleSqrt
getOp DoubleFloor = doubleFloor
getOp DoubleCeiling = doubleCeiling

getOp (Cast _ y) = castTo y
getOp BelieveMe = believeMe

getOp _ = const Nothing

prim : String -> Name
prim str = UN $ "prim__" ++ str

export
opName : PrimFn arity -> Name
opName (Add ty) = prim $ "add_" ++ show ty
opName (Sub ty) = prim $ "sub_" ++ show ty
opName (Mul ty) = prim $ "mul_" ++ show ty
opName (Div ty) = prim $ "div_" ++ show ty
opName (Mod ty) = prim $ "mod_" ++ show ty
opName (Neg ty) = prim $ "negate_" ++ show ty
opName (ShiftL ty) = prim $ "shl_" ++ show ty
opName (ShiftR ty) = prim $ "shr_" ++ show ty
opName (BAnd ty) = prim $ "and_" ++ show ty
opName (BOr ty) = prim $ "or_" ++ show ty
opName (BXOr ty) = prim $ "xor_" ++ show ty
opName (LT ty) = prim $ "lt_" ++ show ty
opName (LTE ty) = prim $ "lte_" ++ show ty
opName (EQ ty) = prim $ "eq_" ++ show ty
opName (GTE ty) = prim $ "gte_" ++ show ty
opName (GT ty) = prim $ "gt_" ++ show ty
opName StrLength = prim "strLength"
opName StrHead = prim "strHead"
opName StrTail = prim "strTail"
opName StrIndex = prim "strIndex"
opName StrCons = prim "strCons"
opName StrAppend = prim "strAppend"
opName StrReverse = prim "strReverse"
opName StrSubstr = prim "strSubstr"
opName DoubleExp = prim "doubleExp"
opName DoubleLog = prim "doubleLog"
opName DoubleSin = prim "doubleSin"
opName DoubleCos = prim "doubleCos"
opName DoubleTan = prim "doubleTan"
opName DoubleASin = prim "doubleASin"
opName DoubleACos = prim "doubleACos"
opName DoubleATan = prim "doubleATan"
opName DoubleSqrt = prim "doubleSqrt"
opName DoubleFloor = prim "doubleFloor"
opName DoubleCeiling = prim "doubleCeiling"
opName (Cast x y) = prim $ "cast_" ++ show x ++ show y
opName BelieveMe = prim $ "believe_me"
opName Crash = prim $ "crash"

export
allPrimitives : List Prim
allPrimitives =
    map (\t => MkPrim (Add t) (arithTy t) isTotal) [IntType, IntegerType, CharType, DoubleType] ++
    map (\t => MkPrim (Sub t) (arithTy t) isTotal) [IntType, IntegerType, CharType, DoubleType] ++
    map (\t => MkPrim (Mul t) (arithTy t) isTotal) [IntType, IntegerType, DoubleType] ++
    map (\t => MkPrim (Div t) (arithTy t) notCovering) [IntType, IntegerType, DoubleType] ++
    map (\t => MkPrim (Mod t) (arithTy t) notCovering) [IntType, IntegerType] ++
    map (\t => MkPrim (Neg t) (predTy t t) isTotal) [IntType, IntegerType, DoubleType] ++
    map (\t => MkPrim (ShiftL t) (arithTy t) notCovering) [IntType, IntegerType] ++
    map (\t => MkPrim (ShiftR t) (arithTy t) notCovering) [IntType, IntegerType] ++

    map (\t => MkPrim (BAnd t) (arithTy t) notCovering) [IntType, IntegerType] ++
    map (\t => MkPrim (BOr t) (arithTy t) notCovering) [IntType, IntegerType] ++
    map (\t => MkPrim (BXOr t) (arithTy t) notCovering) [IntType] ++

    map (\t => MkPrim (LT t) (cmpTy t) isTotal) [IntType, IntegerType, CharType, DoubleType, StringType] ++
    map (\t => MkPrim (LTE t) (cmpTy t) isTotal) [IntType, IntegerType, CharType, DoubleType, StringType] ++
    map (\t => MkPrim (EQ t) (cmpTy t) isTotal) [IntType, IntegerType, CharType, DoubleType, StringType] ++
    map (\t => MkPrim (GTE t) (cmpTy t) isTotal) [IntType, IntegerType, CharType, DoubleType, StringType] ++
    map (\t => MkPrim (GT t) (cmpTy t) isTotal) [IntType, IntegerType, CharType, DoubleType, StringType] ++

    [MkPrim StrLength (predTy StringType IntType) isTotal,
     MkPrim StrHead (predTy StringType CharType) notCovering,
     MkPrim StrTail (predTy StringType StringType) notCovering,
     MkPrim StrIndex (constTy StringType IntType CharType) notCovering,
     MkPrim StrCons (constTy CharType StringType StringType) isTotal,
     MkPrim StrAppend (arithTy StringType) isTotal,
     MkPrim StrReverse (predTy StringType StringType) isTotal,
     MkPrim StrSubstr (constTy3 IntType IntType StringType StringType) isTotal,
     MkPrim BelieveMe believeMeTy isTotal,
     MkPrim Crash crashTy notCovering] ++

    [MkPrim DoubleExp doubleTy isTotal,
     MkPrim DoubleLog doubleTy isTotal,
     MkPrim DoubleSin doubleTy isTotal,
     MkPrim DoubleCos doubleTy isTotal,
     MkPrim DoubleTan doubleTy isTotal,
     MkPrim DoubleASin doubleTy isTotal,
     MkPrim DoubleACos doubleTy isTotal,
     MkPrim DoubleATan doubleTy isTotal,
     MkPrim DoubleSqrt doubleTy isTotal,
     MkPrim DoubleFloor doubleTy isTotal,
     MkPrim DoubleCeiling doubleTy isTotal] ++

    map (\t => MkPrim (Cast t StringType) (predTy t StringType) isTotal) [IntType, IntegerType, CharType, DoubleType] ++
    map (\t => MkPrim (Cast t IntegerType) (predTy t IntegerType) isTotal) [StringType, IntType, CharType, DoubleType] ++
    map (\t => MkPrim (Cast t IntType) (predTy t IntType) isTotal) [StringType, IntegerType, CharType, DoubleType] ++
    map (\t => MkPrim (Cast t DoubleType) (predTy t DoubleType) isTotal) [StringType, IntType, IntegerType] ++
    map (\t => MkPrim (Cast t CharType) (predTy t CharType) isTotal) [StringType, IntType]
