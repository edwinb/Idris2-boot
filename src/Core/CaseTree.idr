module Core.CaseTree

import Core.TT

%default covering

mutual
  public export
  data CaseTree : List Name -> Type where
       Case : {name : _} ->
              (idx : Nat) -> 
              IsVar name idx vars ->
              (scTy : Term vars) -> List (CaseAlt vars) ->
              CaseTree vars
       STerm : Term vars -> CaseTree vars
       Unmatched : (msg : String) -> CaseTree vars
       Impossible : CaseTree vars

  public export
  data CaseAlt : List Name -> Type where
       ConCase : Name -> (tag : Int) -> (args : List Name) ->
                 CaseTree (args ++ vars) -> CaseAlt vars
       DelayCase : (ty : Name) -> (arg : Name) -> 
                   CaseTree (ty :: arg :: vars) -> CaseAlt vars
       ConstCase : Constant -> CaseTree vars -> CaseAlt vars
       DefaultCase : CaseTree vars -> CaseAlt vars

public export
data Pat : Type where
     PAs : FC -> Name -> Pat -> Pat
     PCon : FC -> Name -> (tag : Int) -> (arity : Nat) ->
            List Pat -> Pat
     PTyCon : FC -> Name -> (arity : Nat) -> List Pat -> Pat
     PConst : FC -> (c : Constant) -> Pat
     PArrow : FC -> (x : Name) -> Pat -> Pat -> Pat
     PDelay : FC -> LazyReason -> Pat -> Pat -> Pat
     -- TODO: Matching on lazy types
     PLoc : FC -> Name -> Pat
     PUnmatchable : FC -> Term [] -> Pat

mutual
  export
  Show (CaseTree vars) where
    show (Case {name} idx prf ty alts)
        = "case " ++ show name ++ " : " ++ show ty ++ " of { " ++
                showSep " | " (assert_total (map show alts)) ++ " }"
    show (STerm tm) = show tm
    show (Unmatched msg) = "Error: " ++ show msg
    show Impossible = "Impossible"

  export
  Show (CaseAlt vars) where
    show (ConCase n tag args sc)
        = show n ++ " " ++ showSep " " (map show args) ++ " => " ++
          show sc
    show (DelayCase _ arg sc)
        = "Delay " ++ show arg ++ " => " ++ show sc
    show (ConstCase c sc)
        = show c ++ " => " ++ show sc
    show (DefaultCase sc)
        = "_ => " ++ show sc

export
Show Pat where
  show (PAs _ n p) = show n ++ "@(" ++ show p ++ ")"
  show (PCon _ n i _ args) = show n ++ " " ++ show i ++ " " ++ assert_total (show args)
  show (PTyCon _ n _ args) = "<TyCon>" ++ show n ++ " " ++ assert_total (show args)
  show (PConst _ c) = show c
  show (PArrow _ x s t) = "(" ++ show s ++ " -> " ++ show t ++ ")"
  show (PDelay _ _ _ p) = "(Delay " ++ show p ++ ")"
  show (PLoc _ n) = show n
  show (PUnmatchable _ tm) = ".(" ++ show tm ++ ")"

mutual
  insertCaseNames : (ns : List Name) -> CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames {inner} {outer} ns (Case idx prf scTy alts) 
      = let MkVar prf' = insertVarNames {outer} {inner} {ns} _ prf in
            Case _ prf' (insertNames {outer} ns scTy)
                (map (insertCaseAltNames {outer} {inner} ns) alts)
  insertCaseNames {outer} ns (STerm x) = STerm (insertNames {outer} ns x)
  insertCaseNames ns (Unmatched msg) = Unmatched msg
  insertCaseNames ns Impossible = Impossible

  insertCaseAltNames : (ns : List Name) -> 
                       CaseAlt (outer ++ inner) -> 
                       CaseAlt (outer ++ (ns ++ inner))
  insertCaseAltNames {outer} {inner} ns (ConCase x tag args ct) 
      = ConCase x tag args 
           (rewrite appendAssociative args outer (ns ++ inner) in
                    insertCaseNames {outer = args ++ outer} {inner} ns
                        (rewrite sym (appendAssociative args outer inner) in
                                 ct))
  insertCaseAltNames {outer} {inner} ns (DelayCase tyn valn ct)
      = DelayCase tyn valn 
                  (insertCaseNames {outer = tyn :: valn :: outer} {inner} ns ct)
  insertCaseAltNames ns (ConstCase x ct) 
      = ConstCase x (insertCaseNames ns ct)
  insertCaseAltNames ns (DefaultCase ct) 
      = DefaultCase (insertCaseNames ns ct)
  
export
thinTree : (n : Name) -> CaseTree (outer ++ inner) -> CaseTree (outer ++ n :: inner)
thinTree n (Case idx prf scTy alts) 
    = let MkVar prf' = insertVar {n} _ prf in
          Case _ prf' (thin n scTy) (map (insertCaseAltNames [n]) alts)
thinTree n (STerm tm) = STerm (thin n tm)
thinTree n (Unmatched msg) = Unmatched msg
thinTree n Impossible = Impossible

export
Weaken CaseTree where
  weakenNs ns t = insertCaseNames {outer = []} ns t 

export
mkPat' : List Pat -> ClosedTerm -> ClosedTerm -> Pat
mkPat' args orig (Ref fc Bound n) = PLoc fc n
mkPat' args orig (Ref fc (DataCon t a) n) = PCon fc n t a args
mkPat' args orig (Ref fc (TyCon t a) n) = PTyCon fc n a args
mkPat' args orig (Bind fc x (Pi _ _ s) t)
    = let t' = subst (Erased fc) t in
          PArrow fc x (mkPat' [] s s) (mkPat' [] t' t')
mkPat' args orig (App fc fn p arg) 
    = let parg = mkPat' [] arg arg in
                 mkPat' (parg :: args) orig fn
mkPat' args orig (As fc (Ref _ Bound n) ptm) 
    = PAs fc n (mkPat' [] ptm ptm)
mkPat' args orig (TDelay fc r ty p) 
    = PDelay fc r (mkPat' [] orig ty) (mkPat' [] orig p)
mkPat' args orig (PrimVal fc c) = PConst fc c
mkPat' args orig tm = PUnmatchable (getLoc orig) orig

export
argToPat : ClosedTerm -> Pat
argToPat tm 
    = mkPat' [] tm tm

export
mkTerm : (vars : List Name) -> Pat -> Term vars
mkTerm vars (PAs fc x y) = mkTerm vars y
mkTerm vars (PCon fc x tag arity xs) 
    = apply fc (explApp Nothing) (Ref fc (DataCon tag arity) x)
               (map (mkTerm vars) xs)
mkTerm vars (PTyCon fc x arity xs) 
    = apply fc (explApp Nothing) (Ref fc (TyCon 0 arity) x)
               (map (mkTerm vars) xs)
mkTerm vars (PConst fc c) = PrimVal fc c
mkTerm vars (PArrow fc x s t) 
    = Bind fc x (Pi RigW Explicit (mkTerm vars s)) (mkTerm (x :: vars) t)
mkTerm vars (PDelay fc r ty p)
    = TDelay fc r (mkTerm vars ty) (mkTerm vars p)
mkTerm vars (PLoc fc n) 
    = case isVar n vars of
           Just (MkVar prf) => Local fc Nothing _ prf
           _ => Ref fc Bound n
mkTerm vars (PUnmatchable fc tm) = embed tm


