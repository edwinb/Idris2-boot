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
       PLam : FC -> RigCount -> PiInfo -> Name ->
              (argTy : PTerm) -> (scope : PTerm) -> PTerm
       PLet : FC -> RigCount -> (pat : PTerm) -> 
              (nTy : PTerm) -> (nVal : PTerm) -> (scope : PTerm) -> 
              (alts : List PClause) -> PTerm
       PCase : FC -> PTerm -> List PClause -> PTerm
       PLocal : FC -> List PDecl -> (scope : PTerm) -> PTerm
       PUpdate : FC -> List PFieldUpdate -> PTerm
       PApp : FC -> PTerm -> PTerm -> PTerm
       PImplicitApp : FC -> PTerm -> (argn : Maybe Name) -> PTerm -> PTerm
       PSearch : FC -> (depth : Nat) -> PTerm
       PPrimVal : FC -> Constant -> PTerm
       PQuote : FC -> PTerm -> PTerm
       PUnquote : FC -> PTerm -> PTerm
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
       PList : FC -> List PTerm -> PTerm
       PPair : FC -> PTerm -> PTerm -> PTerm
       PDPair : FC -> PTerm -> PTerm -> PTerm -> PTerm
       PUnit : FC -> PTerm
       PIfThenElse : FC -> PTerm -> PTerm -> PTerm -> PTerm
       PComprehension : FC -> PTerm -> List PDo -> PTerm
       PRewrite : FC -> PTerm -> PTerm -> PTerm

       -- TODO: Ranges, idiom brackets (?), 
       -- 'with' disambiguation

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
       Hide : Bool -> Name -> Directive
       Logging : Nat -> Directive
       LazyNames : Name -> Name -> Name -> Name -> Directive
       LazyOn : Bool -> Directive
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
  data PDecl : Type where
       PClaim : FC -> Visibility -> List FnOpt -> PTypeDecl -> PDecl
       PDef : FC -> List PClause -> PDecl
       PData : FC -> Visibility -> PDataDecl -> PDecl
       PParameters : FC -> List (Name, PTerm) -> List PDecl -> PDecl
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
definedIn (PClaim _ _ _ (MkPTy _ n _) :: ds) = n :: definedIn ds
definedIn (PData _ _ d :: ds) = definedInData d ++ definedIn ds
definedIn (PParameters _ _ pds :: ds) = definedIn pds ++ definedIn ds
definedIn (PNamespace _ _ ns :: ds) = definedIn ns ++ definedIn ds
definedIn (_ :: ds) = definedIn ds

public export
data REPLEval : Type where
     EvalTC : REPLEval -- Evaluate as if part of the typechecker
     NormaliseAll : REPLEval -- Normalise everything (default)
     Execute : REPLEval -- Evaluate then pass to an executer

public export
data REPLOpt : Type where
     ShowImplicits : Bool -> REPLOpt
     ShowNamespace : Bool -> REPLOpt
     ShowTypes : Bool -> REPLOpt
     EvalMode : REPLEval -> REPLOpt
     Editor : String -> REPLOpt
     CG : String -> REPLOpt

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
     CD : String -> REPLCmd
     Missing : Name -> REPLCmd
     Total : Name -> REPLCmd
     Editing : EditCmd -> REPLCmd
     Quit : REPLCmd

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
    show (PRef _ n) = show n
    show (PPi _ rig Explicit Nothing arg ret)
        = show arg ++ " -> " ++ show ret
    show (PPi _ rig Explicit (Just n) arg ret)
        = "(" ++ showCount rig ++ show n ++ " : " ++ show arg ++ ") -> " ++ show ret
    show (PPi _ rig Implicit Nothing arg ret) -- shouldn't happen
        = "{" ++ showCount rig ++ "_ : " ++ show arg ++ "} -> " ++ show ret
    show (PPi _ rig Implicit (Just n) arg ret)
        = "{" ++ showCount rig ++ show n ++ " : " ++ show arg ++ "} -> " ++ show ret
    show (PPi _ RigW AutoImplicit Nothing arg ret)
        = show arg ++ " => " ++ show ret
    show (PPi _ rig AutoImplicit Nothing arg ret) -- shouldn't happen
        = "{auto " ++ showCount rig ++ "_ : " ++ show arg ++ "} -> " ++ show ret
    show (PPi _ rig AutoImplicit (Just n) arg ret)
        = "{auto " ++ showCount rig ++ show n ++ " : " ++ show arg ++ "} -> " ++ show ret
    show (PLam _ rig _ n (PImplicit _) sc)
        = "\\" ++ showCount rig ++ show n ++ " => " ++ show sc
    show (PLam _ rig _ n ty sc)
        = "\\" ++ showCount rig ++ show n ++ " : " ++ show ty ++ " => " ++ show sc
    show (PLet _ rig n (PImplicit _) val sc alts)
        = "let " ++ showCount rig ++ show n ++ " = " ++ show val ++ " in " ++ show sc
    show (PLet _ rig n ty val sc alts)
        = "let " ++ showCount rig ++ show n ++ " : " ++ show ty ++ " = " 
                 ++ show val ++ concatMap showAlt alts ++
                 " in " ++ show sc
      where
        showAlt : PClause -> String
        showAlt (MkPatClause _ lhs rhs _) = " | " ++ show lhs ++ " => " ++ show rhs ++ ";"
        showAlt (MkWithClause _ lhs rhs _) = " | <<with alts not possible>>"
        showAlt (MkImpossible _ lhs) = " | " ++ show lhs ++ " impossible;"
    show (PCase _ tm cs) 
        = "case " ++ show tm ++ " of { " ++ 
            showSep " ; " (map showCase cs) ++ " }"
      where
        showCase : PClause -> String
        showCase (MkPatClause _ lhs rhs _) = show lhs ++ " => " ++ show rhs
        showCase (MkWithClause _ lhs rhs _) = " | <<with alts not possible>>"
        showCase (MkImpossible _ lhs) = show lhs ++ " impossible"
    show (PLocal _ ds sc) -- We'll never see this when displaying a normal form...
        = "let { << definitions >>  } in " ++ show sc
    show (PUpdate _ fs)
        = "record { " ++ showSep ", " (map showUpdate fs) ++ " }"
    show (PApp _ f a) = show f ++ " " ++ show a
    show (PImplicitApp _ f Nothing a) 
        = show f ++ " @{" ++ show a ++ "}"
    show (PImplicitApp _ f (Just n) (PRef _ a)) 
        = if n == a
             then show f ++ " {" ++ show n ++ "}"
             else show f ++ " {" ++ show n ++ " = " ++ show a ++ "}"
    show (PImplicitApp _ f (Just n) a) 
        = show f ++ " {" ++ show n ++ " = " ++ show a ++ "}"
    show (PSearch _ d) = "%search"
    show (PQuote _ tm) = "`(" ++ show tm ++ ")"
    show (PUnquote _ tm) = "~(" ++ show tm ++ ")"
    show (PPrimVal _ c) = show c
    show (PHole _ _ n) = "?" ++ n
    show (PType _) = "Type"
    show (PAs _ n p) = show n ++ "@" ++ show p
    show (PDotted _ p) = "." ++ show p
    show (PImplicit _) = "_"
    show (PInfer _) = "?"
    show (POp _ op x y) = show x ++ " " ++ show op ++ " " ++ show y
    show (PPrefixOp _ op x) = show op ++ show x
    show (PSectionL _ op x) = "(" ++ show op ++ " " ++ show x ++ ")"
    show (PSectionR _ x op) = "(" ++ show x ++ " " ++ show op ++ ")"
    show (PEq fc l r) = show l ++ " = " ++ show r
    show (PBracketed _ tm) = "(" ++ show tm ++ ")"
    show (PDoBlock _ ds) 
        = "do " ++ showSep " ; " (map showDo ds)
    show (PList _ xs)
        = "[" ++ showSep ", " (map show xs) ++ "]"
    show (PPair _ l r) = "(" ++ show l ++ ", " ++ show r ++ ")"
    show (PDPair _ l (PImplicit _) r) = "(" ++ show l ++ " ** " ++ show r ++ ")"
    show (PDPair _ l ty r) = "(" ++ show l ++ " : " ++ show ty ++ 
                                 " ** " ++ show r ++ ")"
    show (PUnit _) = "()"
    show (PIfThenElse _ x t e) = "if " ++ show x ++ " then " ++ show t ++
                                 " else " ++ show e
    show (PComprehension _ ret es)
        = "[" ++ show (dePure ret) ++ " | " ++
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
    show (PRewrite _ rule tm)
        = "rewrite " ++ show rule ++ " in " ++ show tm

public export
record IFaceInfo where
  constructor MkIFaceInfo
  iconstructor : Name
  params : List Name
  parents : List RawImp
  methods : List (Name, Bool, RawImp) 
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

  fromBuf s b
      = do ic <- fromBuf s b
           ps <- fromBuf s b
           cs <- fromBuf s b
           ms <- fromBuf s b
           ds <- fromBuf s b
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
  ifaceNames : List Name -- list of interface names, which we use for
                         -- writing to TTC
  ifaces : Context IFaceInfo
  bracketholes : List Name -- hole names in argument position (so need
                           -- to be bracketed when solved)
  startExpr : RawImp

export
TTC Fixity where
  toBuf b InfixL = tag 0
  toBuf b InfixR = tag 1
  toBuf b Infix = tag 2
  toBuf b Prefix = tag 3

  fromBuf r b 
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

getSaveIFaces : Context IFaceInfo ->
                List Name -> Core (List (Name, IFaceInfo))
getSaveIFaces ctxt [] = pure []
getSaveIFaces ctxt (n :: ns)
    = do Just i <- lookupCtxtExact n ctxt
              | Nothing => throw (InternalError ("Unknown interface " ++ show n))
         is <- getSaveIFaces ctxt ns
         pure ((n, i) :: is)

addSavedIFaces : Context IFaceInfo -> List (Name, IFaceInfo) ->
                 Core (Context IFaceInfo)
addSavedIFaces ctxt [] = pure ctxt
addSavedIFaces ctxt ((n, i) :: ns)
    = do (_, ctxt') <- addCtxt n i ctxt
         addSavedIFaces ctxt' ns

export
TTC SyntaxInfo where
  toBuf b syn 
      = do toBuf b (toList (infixes syn))
           toBuf b (toList (prefixes syn))
           ilist <- getSaveIFaces (ifaces syn) (ifaceNames syn)
           toBuf b ilist
           toBuf b (bracketholes syn)
           toBuf b (startExpr syn)

  fromBuf r b 
      = do inf <- fromBuf r b
           pre <- fromBuf r b
           ilist <- fromBuf r b
           ifctx <- initCtxt
           ifctx <- addSavedIFaces ifctx ilist
           bhs <- fromBuf r b
           start <- fromBuf r b
           pure (MkSyntax (fromList inf) (fromList pre) [] ifctx bhs start)

export
initSyntax : Core SyntaxInfo
initSyntax
    = do ifctx <- initCtxt
         pure $ MkSyntax 
                  (insert "=" (Infix, 0) empty) 
                  (insert "-" 10 empty)
                  []
                  ifctx
                  []
                  (IVar (MkFC "(default)" (0, 0) (0, 0)) (UN "main"))

-- A label for Syntax info in the global state
export
data Syn : Type where


