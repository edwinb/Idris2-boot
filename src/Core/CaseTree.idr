module Core.CaseTree

import Core.TT

mutual
  public export
  data CaseTree : List Name -> Type where
       Case : {name : _} ->
              (idx : Nat) -> IsVar name idx vars ->
              (scTy : Term vars) -> List (CaseAlt vars) ->
              CaseTree vars
       STerm : Term vars -> CaseTree vars
       Unmatched : (msg : String) -> CaseTree vars
       Impossible : CaseTree vars

  public export
  data CaseAlt : List Name -> Type where
       ConCase : Name -> (tag : Int) -> (args : List Name) ->
                 CaseTree (args ++ vars) -> CaseAlt vars
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
    show (ConstCase c sc)
        = show c ++ " => " ++ show sc
    show (DefaultCase sc)
        = "_ => " ++ show sc

mkPat' : List Pat -> Term [] -> Term [] -> Pat
mkPat' [] orig (Ref fc Bound n) = PLoc fc n
mkPat' args orig (Ref fc (DataCon t a) n) = PCon fc n t a args
mkPat' args orig (Ref fc (TyCon t a) n) = PTyCon fc n a args
mkPat' [] orig (Bind fc x (Pi _ _ s) t)
    = let t' = subst (Erased fc) t in
          PArrow fc x (mkPat' [] s s) (mkPat' [] t' t')
mkPat' args orig (App fc fn p arg) 
    = let parg = mkPat' [] arg arg in
          mkPat' (parg :: args) orig fn
mkPat' [] orig (As fc (Ref _ Bound n) ptm) 
    = PAs fc n (mkPat' [] ptm ptm)
mkPat' [] orig (PrimVal fc c) = PConst fc c
mkPat' args orig tm = PUnmatchable (getLoc orig) orig

export
mkPat : Term [] -> Pat
mkPat tm = mkPat' [] tm tm

mutual
  insertCaseNames : (ns : List Name) -> CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames {inner} {outer} ns (Case idx prf scTy alts) 
      = let (_ ** prf') = insertVarNames {outer} {inner} {ns} _ prf in
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
  insertCaseAltNames ns (ConstCase x ct) 
      = ConstCase x (insertCaseNames ns ct)
  insertCaseAltNames ns (DefaultCase ct) 
      = DefaultCase (insertCaseNames ns ct)
  
export
thinTree : (n : Name) -> CaseTree (outer ++ inner) -> CaseTree (outer ++ n :: inner)
thinTree n (Case idx prf scTy alts) 
    = let (_ ** prf') = insertVar {n} _ prf in
          Case _ prf' (thin n scTy) (map (insertCaseAltNames [n]) alts)
thinTree n (STerm tm) = STerm (thin n tm)
thinTree n (Unmatched msg) = Unmatched msg
thinTree n Impossible = Impossible


