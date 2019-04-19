module Core.CaseTree

import Core.TT

mutual
  public export
  data CaseTree : List Name -> Type where
       Switch : {name : _} ->
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
data Pat : List Name -> Type where
     PAs : {name : _} ->
           FC -> (idx : Nat) -> IsVar name idx vars -> Pat vars -> Pat vars
     PCon : FC -> Name -> (tag : Int) -> (arity : Nat) ->
            List (Pat vars) -> Pat vars
     PTyCon : FC -> Name -> (arity : Nat) ->
              List (Pat vars) -> Pat vars
     PConst : FC -> (c : Constant) -> Pat vars
     PArrow : FC -> (x : Name) -> Pat vars -> Pat (x :: vars) -> Pat vars
     PLoc : {name : _} ->
            FC -> (idx : Nat) -> IsVar name idx vars -> Pat vars
     PUnmatchable : FC -> Term vars -> Pat vars

mkPat' : List (Pat vars) -> Term vars -> Term vars -> Pat vars
mkPat' [] orig (Local fc c idx p) = PLoc fc idx p
mkPat' args orig (Ref fc (DataCon t a) n) = PCon fc n t a args
mkPat' args orig (Ref fc (TyCon t a) n) = PTyCon fc n a args
mkPat' [] orig (Bind fc x (Pi _ _ s) t)
    = PArrow fc x (mkPat' [] s s) (mkPat' [] t t)
mkPat' args orig (App fc fn p arg) 
    = let parg = mkPat' [] arg arg in
          mkPat' (parg :: args) orig fn
mkPat' args orig (As fc idx p ptm) 
    = let pat = mkPat' args orig ptm in
          PAs fc idx p pat
mkPat' [] orig (PrimVal fc c) = PConst fc c
mkPat' args orig tm = PUnmatchable (getLoc orig) orig

export
mkPat : Term vars -> Pat vars
mkPat tm = mkPat' [] tm tm

mutual
  insertCaseNames : (ns : List Name) -> CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames {inner} {outer} ns (Switch idx prf scTy alts) 
      = let (_ ** prf') = insertVarNames {outer} {inner} {ns} _ prf in
            Switch _ prf' (insertNames {outer} ns scTy)
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
thinTree n (Switch idx prf scTy alts) 
    = let (_ ** prf') = insertVar {n} _ prf in
          Switch _ prf' (thin n scTy) (map (insertCaseAltNames [n]) alts)
thinTree n (STerm tm) = STerm (thin n tm)
thinTree n (Unmatched msg) = Unmatched msg
thinTree n Impossible = Impossible


