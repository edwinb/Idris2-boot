module Idris.Syntax

import public Core.Binary
import public Core.Context
import public Core.Core
import public Core.FC
import public Core.Normalise
import public Core.Options
import public Core.TTC
import public Core.TT

import TTImp.TTImp

import Data.ANameMap
import Data.StringMap

%default covering

%hide Elab.Fixity

public export
data Fixity = InfixL | InfixR | Infix | Prefix

public export
OpStr : Type
OpStr = Name

mutual
  -- The full high level source language
  -- This gets desugared to RawImp (TTImp.TTImp), then elaborated to
  -- Term (Core.TT)
  public export
  data PTerm : Type where
       -- Direct (more or less) translations to RawImp

       PRef : FC -> Name -> PTerm
       PPi : FC -> RigCount -> PiInfo -> Maybe Name ->
             (argTy : PTerm) -> (retTy : PTerm) -> PTerm
       PLam : FC -> RigCount -> PiInfo -> PTerm ->
              (argTy : PTerm) -> (scope : PTerm) -> PTerm
       PLet : FC -> RigCount -> (pat : PTerm) ->
              (nTy : PTerm) -> (nVal : PTerm) -> (scope : PTerm) ->
              (alts : List PClause) -> PTerm
       PCase : FC -> PTerm -> List PClause -> PTerm
       PLocal : FC -> List PDecl -> (scope : PTerm) -> PTerm
       PUpdate : FC -> List PFieldUpdate -> PTerm
       PApp : FC -> PTerm -> PTerm -> PTerm
       PWithApp : FC -> PTerm -> PTerm -> PTerm
       PImplicitApp : FC -> PTerm -> (argn : Maybe Name) -> PTerm -> PTerm

       PDelayed : FC -> LazyReason -> PTerm -> PTerm
       PDelay : FC -> PTerm -> PTerm
       PForce : FC -> PTerm -> PTerm

       PSearch : FC -> (depth : Nat) -> PTerm
       PPrimVal : FC -> Constant -> PTerm
       PQuote : FC -> PTerm -> PTerm
       PQuoteDecl : FC -> PDecl -> PTerm
       PUnquote : FC -> PTerm -> PTerm
       PRunElab : FC -> PTerm -> PTerm
       PHole : FC -> (bracket : Bool) -> (holename : String) -> PTerm
       PType : FC -> PTerm
       PAs : FC -> Name -> (pattern : PTerm) -> PTerm
       PDotted : FC -> PTerm -> PTerm
       PImplicit : FC -> PTerm
       PInfer : FC -> PTerm

       -- Operators

       POp : FC -> OpStr -> PTerm -> PTerm -> PTerm
       PPrefixOp : FC -> OpStr -> PTerm -> PTerm
       PSectionL : FC -> OpStr -> PTerm -> PTerm
       PSectionR : FC -> PTerm -> OpStr -> PTerm
       PEq : FC -> PTerm -> PTerm -> PTerm
       PBracketed : FC -> PTerm -> PTerm

       -- Syntactic sugar

       PDoBlock : FC -> List PDo -> PTerm
       PBang : FC -> PTerm -> PTerm
       PIdiom : FC -> PTerm -> PTerm
       PList : FC -> List PTerm -> PTerm
       PPair : FC -> PTerm -> PTerm -> PTerm
       PDPair : FC -> PTerm -> PTerm -> PTerm -> PTerm
       PUnit : FC -> PTerm
       PIfThenElse : FC -> PTerm -> PTerm -> PTerm -> PTerm
       PComprehension : FC -> PTerm -> List PDo -> PTerm
       PRewrite : FC -> PTerm -> PTerm -> PTerm
       -- A list range  [x,y..z]
       PRange : FC -> PTerm -> Maybe PTerm -> PTerm -> PTerm
       -- A stream range [x,y..]
       PRangeStream : FC -> PTerm -> Maybe PTerm -> PTerm

       -- Debugging
       PUnifyLog : FC -> PTerm -> PTerm

       -- TODO: 'with' disambiguation

  public export
  data PFieldUpdate : Type where
       PSetField : (path : List String) -> PTerm -> PFieldUpdate
       PSetFieldApp : (path : List String) -> PTerm -> PFieldUpdate

  public export
  data PDo : Type where
       DoExp : FC -> PTerm -> PDo
       DoBind : FC -> Name -> PTerm -> PDo
       DoBindPat : FC -> PTerm -> PTerm -> List PClause -> PDo
       DoLet : FC -> Name -> RigCount -> PTerm -> PDo
       DoLetPat : FC -> PTerm -> PTerm -> List PClause -> PDo
       DoLetLocal : FC -> List PDecl -> PDo
       DoRewrite : FC -> PTerm -> PDo

  export
  getLoc : PDo -> FC
  getLoc (DoExp fc _) = fc
  getLoc (DoBind fc _ _) = fc
  getLoc (DoBindPat fc _ _ _) = fc
  getLoc (DoLet fc _ _ _) = fc
  getLoc (DoLetPat fc _ _ _) = fc
  getLoc (DoLetLocal fc _) = fc
  getLoc (DoRewrite fc _) = fc

  export
  papply : FC -> PTerm -> List PTerm -> PTerm
  papply fc f [] = f
  papply fc f (a :: as) = papply fc (PApp fc f a) as

  public export
  data PTypeDecl : Type where
       MkPTy : FC -> (n : Name) -> (type : PTerm) -> PTypeDecl

  public export
  data PDataDecl : Type where
       MkPData : FC -> (tyname : Name) -> (tycon : PTerm) ->
                 (opts : List DataOpt) ->
                 (datacons : List PTypeDecl) -> PDataDecl
       MkPLater : FC -> (tyname : Name) -> (tycon : PTerm) -> PDataDecl

  public export
  data PClause : Type where
       MkPatClause : FC -> (lhs : PTerm) -> (rhs : PTerm) ->
                     (whereblock : List PDecl) -> PClause
       MkWithClause : FC -> (lhs : PTerm) -> (wval : PTerm) ->
                        List PClause -> PClause
       MkImpossible : FC -> (lhs : PTerm) -> PClause

  public export
  data Directive : Type where
       Hide : Name -> Directive
       Logging : Nat -> Directive
       LazyOn : Bool -> Directive
       UnboundImplicits : Bool -> Directive
       PairNames : Name -> Name -> Name -> Directive
       RewriteName : Name -> Name -> Directive
       PrimInteger : Name -> Directive
       PrimString : Name -> Directive
       PrimChar : Name -> Directive
       CGAction : String -> String -> Directive
       Names : Name -> List String -> Directive
       StartExpr : PTerm -> Directive
       Overloadable : Name -> Directive
       Extension : LangExt -> Directive

  public export
  data PField : Type where
       MkField : FC -> RigCount -> PiInfo -> Name -> (ty : PTerm) -> PField

  -- For noting the pass we're in when desugaring a mutual block
  -- TODO: Decide whether we want mutual blocks!
  public export
  data Pass = Single | AsType | AsDef

  export
  Eq Pass where
    Single == Single = True
    AsType == AsType = True
    AsDef == AsDef = True
    _ == _ = False

  export
  typePass : Pass -> Bool
  typePass p = p == Single || p == AsType

  export
  defPass : Pass -> Bool
  defPass p = p == Single || p == AsDef

  public export
  data PFnOpt : Type where
       IFnOpt : FnOpt -> PFnOpt
       PForeign : List PTerm -> PFnOpt

  public export
  data PDecl : Type where
       PClaim : FC -> RigCount -> Visibility -> List PFnOpt -> PTypeDecl -> PDecl
       PDef : FC -> List PClause -> PDecl
       PData : FC -> Visibility -> PDataDecl -> PDecl
       PParameters : FC -> List (Name, PTerm) -> List PDecl -> PDecl
       PUsing : FC -> List (Maybe Name, PTerm) -> List PDecl -> PDecl
       PReflect : FC -> PTerm -> PDecl
       PInterface : FC ->
                    Visibility ->
                    (constraints : List (Maybe Name, PTerm)) ->
                    Name ->
                    (params : List (Name, PTerm)) ->
                    (det : List Name) ->
                    (conName : Maybe Name) ->
                    List PDecl ->
                    PDecl
       PImplementation : FC ->
                         Visibility -> Pass ->
                         (implicits : List (Name, RigCount, PTerm)) ->
                         (constraints : List (Maybe Name, PTerm)) ->
                         Name ->
                         (params : List PTerm) ->
                         (implName : Maybe Name) ->
                         Maybe (List PDecl) ->
                         PDecl
       PRecord : FC ->
                 Visibility ->
                 Name ->
                 (params : List (Name, PTerm)) ->
                 (conName : Maybe Name) ->
                 List PField ->
                 PDecl

       -- TODO: PPostulate
       -- TODO: POpen (for opening named interfaces)
       PMutual : FC -> List PDecl -> PDecl
       PFixity : FC -> Fixity -> Nat -> OpStr -> PDecl
       PNamespace : FC -> List String -> List PDecl -> PDecl
       PTransform : FC -> PTerm -> PTerm -> PDecl
       PDirective : FC -> Directive -> PDecl

definedInData : PDataDecl -> List Name
definedInData (MkPData _ n _ _ cons) = n :: map getName cons
  where
    getName : PTypeDecl -> Name
    getName (MkPTy _ n _) = n
definedInData (MkPLater _ n _) = [n]

export
definedIn : List PDecl -> List Name
definedIn [] = []
definedIn (PClaim _ _ _ _ (MkPTy _ n _) :: ds) = n :: definedIn ds
definedIn (PData _ _ d :: ds) = definedInData d ++ definedIn ds
definedIn (PParameters _ _ pds :: ds) = definedIn pds ++ definedIn ds
definedIn (PUsing _ _ pds :: ds) = definedIn pds ++ definedIn ds
definedIn (PNamespace _ _ ns :: ds) = definedIn ns ++ definedIn ds
definedIn (_ :: ds) = definedIn ds

public export
data REPLEval : Type where
     EvalTC : REPLEval -- Evaluate as if part of the typechecker
     NormaliseAll : REPLEval -- Normalise everything (default)
     Execute : REPLEval -- Evaluate then pass to an executer

export
Show REPLEval where
  show EvalTC = "typecheck"
  show NormaliseAll = "normalise"
  show Execute = "execute"

public export
data REPLOpt : Type where
     ShowImplicits : Bool -> REPLOpt
     ShowNamespace : Bool -> REPLOpt
     ShowTypes : Bool -> REPLOpt
     EvalMode : REPLEval -> REPLOpt
     Editor : String -> REPLOpt
     CG : String -> REPLOpt

export
Show REPLOpt where
  show (ShowImplicits impl) = "showimplicits = " ++ show impl
  show (ShowNamespace ns) = "shownamespace = " ++ show ns
  show (ShowTypes typs) = "showtypes = " ++ show typs
  show (EvalMode mod) = "eval = " ++ show mod
  show (Editor editor) = "editor = " ++ show editor
  show (CG str) = "cg = " ++ str


public export
data EditCmd : Type where
     TypeAt : Int -> Int -> Name -> EditCmd
     CaseSplit : Int -> Int -> Name -> EditCmd
     AddClause : Int -> Name -> EditCmd
     ExprSearch : Int -> Name -> List Name -> Bool -> EditCmd
     GenerateDef : Int -> Name -> EditCmd
     MakeLemma : Int -> Name -> EditCmd
     MakeCase : Int -> Name -> EditCmd
     MakeWith : Int -> Name -> EditCmd

public export
data REPLCmd : Type where
     Eval : PTerm -> REPLCmd
     Check : PTerm -> REPLCmd
     PrintDef : Name -> REPLCmd
     Reload : REPLCmd
     Load : String -> REPLCmd
     Edit : REPLCmd
     Compile : PTerm -> String -> REPLCmd
     Exec : PTerm -> REPLCmd
     ProofSearch : Name -> REPLCmd
     DebugInfo : Name -> REPLCmd
     SetOpt : REPLOpt -> REPLCmd
     GetOpts : REPLCmd
     CD : String -> REPLCmd
     Missing : Name -> REPLCmd
     Total : Name -> REPLCmd
     SetLog : Nat -> REPLCmd
     Metavars : REPLCmd
     Editing : EditCmd -> REPLCmd
     ShowVersion : REPLCmd
     Quit : REPLCmd
     NOP : REPLCmd

public export
record Import where
  constructor MkImport
  loc : FC
  reexport : Bool
  path : List String
  nameAs : List String

public export
record Module where
  constructor MkModule
  headerloc : FC
  moduleNS : List String
  imports : List Import
  decls : List PDecl

showCount : RigCount -> String
showCount Rig0 = "0 "
showCount Rig1 = "1 "
showCount RigW = ""

mutual
  showAlt : PClause -> String
  showAlt (MkPatClause _ lhs rhs _) = " | " ++ show lhs ++ " => " ++ show rhs ++ ";"
  showAlt (MkWithClause _ lhs wval cs) = " | <<with alts not possible>>;"
  showAlt (MkImpossible _ lhs) = " | " ++ show lhs ++ " impossible;"

  showDo : PDo -> String
  showDo (DoExp _ tm) = show tm
  showDo (DoBind _ n tm) = show n ++ " <- " ++ show tm
  showDo (DoBindPat _ l tm alts)
      = show l ++ " <- " ++ show tm ++ concatMap showAlt alts
  showDo (DoLet _ l rig tm) = "let " ++ show l ++ " = " ++ show tm
  showDo (DoLetPat _ l tm alts)
      = "let " ++ show l ++ " = " ++ show tm ++ concatMap showAlt alts
  showDo (DoLetLocal _ ds)
      -- We'll never see this when displaying a normal form...
      = "let { << definitions >>  }"
  showDo (DoRewrite _ rule)
      = "rewrite " ++ show rule

  showUpdate : PFieldUpdate -> String
  showUpdate (PSetField p v) = showSep "->" p ++ " = " ++ show v
  showUpdate (PSetFieldApp p v) = showSep "->" p ++ " $= " ++ show v

  export
  Show PTerm where
    showPrec d (PRef _ n) = showPrec d n
    showPrec d (PPi _ rig Explicit Nothing arg ret)
        = showPrec d arg ++ " -> " ++ showPrec d ret
    showPrec d (PPi _ rig Explicit (Just n) arg ret)
        = "(" ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d arg ++ ") -> " ++ showPrec d ret
    showPrec d (PPi _ rig Implicit Nothing arg ret) -- shouldn't happen
        = "{" ++ showCount rig ++ "_ : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PPi _ rig Implicit (Just n) arg ret)
        = "{" ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PPi _ RigW AutoImplicit Nothing arg ret)
        = showPrec d arg ++ " => " ++ showPrec d ret
    showPrec d (PPi _ rig AutoImplicit Nothing arg ret) -- shouldn't happen
        = "{auto " ++ showCount rig ++ "_ : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PPi _ rig AutoImplicit (Just n) arg ret)
        = "{auto " ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d arg ++ "} -> " ++ showPrec d ret
    showPrec d (PLam _ rig _ n (PImplicit _) sc)
        = "\\" ++ showCount rig ++ showPrec d n ++ " => " ++ showPrec d sc
    showPrec d (PLam _ rig _ n ty sc)
        = "\\" ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d ty ++ " => " ++ showPrec d sc
    showPrec d (PLet _ rig n (PImplicit _) val sc alts)
        = "let " ++ showCount rig ++ showPrec d n ++ " = " ++ showPrec d val ++ " in " ++ showPrec d sc
    showPrec d (PLet _ rig n ty val sc alts)
        = "let " ++ showCount rig ++ showPrec d n ++ " : " ++ showPrec d ty ++ " = "
                 ++ showPrec d val ++ concatMap showAlt alts ++
                 " in " ++ showPrec d sc
      where
        showAlt : PClause -> String
        showAlt (MkPatClause _ lhs rhs _) = " | " ++ show lhs ++ " => " ++ show rhs ++ ";"
        showAlt (MkWithClause _ lhs rhs _) = " | <<with alts not possible>>"
        showAlt (MkImpossible _ lhs) = " | " ++ show lhs ++ " impossible;"
    showPrec _ (PCase _ tm cs)
        = "case " ++ show tm ++ " of { " ++
            showSep " ; " (map showCase cs) ++ " }"
      where
        showCase : PClause -> String
        showCase (MkPatClause _ lhs rhs _) = show lhs ++ " => " ++ show rhs
        showCase (MkWithClause _ lhs rhs _) = " | <<with alts not possible>>"
        showCase (MkImpossible _ lhs) = show lhs ++ " impossible"
    showPrec d (PLocal _ ds sc) -- We'll never see this when displaying a normal form...
        = "let { << definitions >>  } in " ++ showPrec d sc
    showPrec d (PUpdate _ fs)
        = "record { " ++ showSep ", " (map showUpdate fs) ++ " }"
    showPrec d (PApp _ f a) = showPrec App f ++ " " ++ showPrec App a
    showPrec d (PWithApp _ f a) = showPrec d f ++ " | " ++ showPrec d a
    showPrec d (PImplicitApp _ f Nothing a)
        = showPrec d f ++ " @{" ++ showPrec d a ++ "}"
    showPrec d (PDelayed _ LInf ty)
        = showCon d "Inf" $ showArg ty
    showPrec d (PDelayed _ _ ty)
        = showCon d "Lazy" $ showArg ty
    showPrec d (PDelay _ tm)
        = showCon d "Delay" $ showArg tm
    showPrec d (PForce _ tm)
        = showCon d "Force" $ showArg tm
    showPrec d (PImplicitApp _ f (Just n) (PRef _ a))
        = if n == a
             then showPrec d f ++ " {" ++ showPrec d n ++ "}"
             else showPrec d f ++ " {" ++ showPrec d n ++ " = " ++ showPrec d a ++ "}"
    showPrec d (PImplicitApp _ f (Just n) a)
        = showPrec d f ++ " {" ++ showPrec d n ++ " = " ++ showPrec d a ++ "}"
    showPrec _ (PSearch _ _) = "%search"
    showPrec d (PQuote _ tm) = "`(" ++ showPrec d tm ++ ")"
    showPrec d (PQuoteDecl _ tm) = "`( <<declaration>> )"
    showPrec d (PUnquote _ tm) = "~(" ++ showPrec d tm ++ ")"
    showPrec d (PRunElab _ tm) = "%runElab " ++ showPrec d tm
    showPrec d (PPrimVal _ c) = showPrec d c
    showPrec _ (PHole _ _ n) = "?" ++ n
    showPrec _ (PType _) = "Type"
    showPrec d (PAs _ n p) = showPrec d n ++ "@" ++ showPrec d p
    showPrec d (PDotted _ p) = "." ++ showPrec d p
    showPrec _ (PImplicit _) = "_"
    showPrec _ (PInfer _) = "?"
    showPrec d (POp _ op x y) = showPrec d x ++ " " ++ showPrec d op ++ " " ++ showPrec d y
    showPrec d (PPrefixOp _ op x) = showPrec d op ++ showPrec d x
    showPrec d (PSectionL _ op x) = "(" ++ showPrec d op ++ " " ++ showPrec d x ++ ")"
    showPrec d (PSectionR _ x op) = "(" ++ showPrec d x ++ " " ++ showPrec d op ++ ")"
    showPrec d (PEq fc l r) = showPrec d l ++ " = " ++ showPrec d r
    showPrec d (PBracketed _ tm) = "(" ++ showPrec d tm ++ ")"
    showPrec d (PDoBlock _ ds)
        = "do " ++ showSep " ; " (map showDo ds)
    showPrec d (PBang _ tm) = "!" ++ showPrec d tm
    showPrec d (PIdiom _ tm) = "[|" ++ showPrec d tm ++ "|]"
    showPrec d (PList _ xs)
        = "[" ++ showSep ", " (map (showPrec d) xs) ++ "]"
    showPrec d (PPair _ l r) = "(" ++ showPrec d l ++ ", " ++ showPrec d r ++ ")"
    showPrec d (PDPair _ l (PImplicit _) r) = "(" ++ showPrec d l ++ " ** " ++ showPrec d r ++ ")"
    showPrec d (PDPair _ l ty r) = "(" ++ showPrec d l ++ " : " ++ showPrec d ty ++
                                 " ** " ++ showPrec d r ++ ")"
    showPrec _ (PUnit _) = "()"
    showPrec d (PIfThenElse _ x t e) = "if " ++ showPrec d x ++ " then " ++ showPrec d t ++
                                 " else " ++ showPrec d e
    showPrec d (PComprehension _ ret es)
        = "[" ++ showPrec d (dePure ret) ++ " | " ++
                 showSep ", " (map (showDo . deGuard) es) ++ "]"
      where
        dePure : PTerm -> PTerm
        dePure tm@(PApp _ (PRef _ n) arg)
            = if dropNS n == UN "pure" then arg else tm
        dePure tm = tm

        deGuard : PDo -> PDo
        deGuard tm@(DoExp fc (PApp _ (PRef _ n) arg))
            = if dropNS n == UN "guard" then DoExp fc arg else tm
        deGuard tm = tm
    showPrec d (PRewrite _ rule tm)
        = "rewrite " ++ showPrec d rule ++ " in " ++ showPrec d tm
    showPrec d (PRange _ start Nothing end)
        = "[" ++ showPrec d start ++ " .. " ++ showPrec d end ++ "]"
    showPrec d (PRange _ start (Just next) end)
        = "[" ++ showPrec d start ++ ", " ++ showPrec d next ++ " .. " ++ showPrec d end ++ "]"
    showPrec d (PRangeStream _ start Nothing)
        = "[" ++ showPrec d start ++ " .. ]"
    showPrec d (PRangeStream _ start (Just next))
        = "[" ++ showPrec d start ++ ", " ++ showPrec d next ++ " .. ]"
    showPrec d (PUnifyLog _ tm) = showPrec d tm

public export
record IFaceInfo where
  constructor MkIFaceInfo
  iconstructor : Name
  params : List Name
  parents : List RawImp
  methods : List (Name, RigCount, Bool, RawImp)
     -- ^ name, whether a data method, and desugared type (without constraint)
  defaults : List (Name, List ImpClause)

export
TTC IFaceInfo where
  toBuf b (MkIFaceInfo ic ps cs ms ds)
      = do toBuf b ic
           toBuf b ps
           toBuf b cs
           toBuf b ms
           toBuf b ds

  fromBuf b
      = do ic <- fromBuf b
           ps <- fromBuf b
           cs <- fromBuf b
           ms <- fromBuf b
           ds <- fromBuf b
           pure (MkIFaceInfo ic ps cs ms ds)

-- If you update this, update 'extendAs' in Desugar to keep it up to date
-- when reading imports
public export
record SyntaxInfo where
  constructor MkSyntax
  -- Keep infix/prefix, then we can define operators which are both
  -- (most obviously, -)
  infixes : StringMap (Fixity, Nat)
  prefixes : StringMap Nat
  ifaces : ANameMap IFaceInfo
  bracketholes : List Name -- hole names in argument position (so need
                           -- to be bracketed when solved)
  usingImpl : List (Maybe Name, RawImp)
  startExpr : RawImp

export
TTC Fixity where
  toBuf b InfixL = tag 0
  toBuf b InfixR = tag 1
  toBuf b Infix = tag 2
  toBuf b Prefix = tag 3

  fromBuf b
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

export
TTC SyntaxInfo where
  toBuf b syn
      = do toBuf b (toList (infixes syn))
           toBuf b (toList (prefixes syn))
           toBuf b (toList (ifaces syn))
           toBuf b (bracketholes syn)
           toBuf b (startExpr syn)

  fromBuf b
      = do inf <- fromBuf b
           pre <- fromBuf b
           ifs <- fromBuf b
           bhs <- fromBuf b
           start <- fromBuf b
           pure (MkSyntax (fromList inf) (fromList pre) (fromList ifs)
                          bhs [] start)

HasNames IFaceInfo where
  full gam iface
      = do -- coreLift $ printLn (iconstructor iface)
           -- coreLift $ printLn (methods iface)
           pure iface

  resolved gam iface = pure iface

HasNames a => HasNames (ANameMap a) where
  full gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : ANameMap a -> List (Name, a) -> Core (ANameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (addName !(full gam k) !(full gam v) ms) ns

  resolved gam nmap
      = insertAll empty (toList nmap)
    where
      insertAll : ANameMap a -> List (Name, a) -> Core (ANameMap a)
      insertAll ms [] = pure ms
      insertAll ms ((k, v) :: ns)
          = insertAll (addName !(resolved gam k) !(resolved gam v) ms) ns

export
HasNames SyntaxInfo where
  full gam syn
      = pure $ record { ifaces = !(full gam (ifaces syn)),
                        bracketholes = !(traverse (full gam) (bracketholes syn))
                      } syn
  resolved gam syn
      = pure $ record { ifaces = !(resolved gam (ifaces syn)),
                        bracketholes = !(traverse (resolved gam) (bracketholes syn))
                      } syn

export
initSyntax : SyntaxInfo
initSyntax
    = MkSyntax (insert "=" (Infix, 0) empty)
               (insert "-" 10 empty)
               empty
               []
               []
               (IVar (MkFC "(default)" (0, 0) (0, 0)) (UN "main"))

-- A label for Syntax info in the global state
export
data Syn : Type where
