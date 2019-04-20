module TTImp.ProcessData

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.UnifyState
import Core.Value

import TTImp.Elab.Check
import TTImp.Elab
import TTImp.TTImp

checkRetType : Env Term vars -> NF vars -> 
               (NF vars -> Core ()) -> Core ()
checkRetType env (NBind fc x (Pi _ _ ty) sc) chk
    = checkRetType env !(sc (toClosure defaultOpts env (Erased fc))) chk
checkRetType env nf chk = chk nf

checkIsType : FC -> Name -> Env Term vars -> NF vars -> Core ()
checkIsType loc n env nf
    = checkRetType env nf 
         (\nf => case nf of 
                      NType _ => pure ()
                      _ => throw (BadTypeConType loc n))

checkFamily : FC -> Name -> Name -> Env Term vars -> NF vars -> Core ()
checkFamily loc cn tn env nf
    = checkRetType env nf 
         (\nf => case nf of 
                      NType _ => throw (BadDataConType loc cn tn)
                      NTCon _ n' _ _ _ => 
                            if tn == n'
                               then pure ()
                               else throw (BadDataConType loc cn tn)
                      _ => throw (BadDataConType loc cn tn))

checkCon : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Env Term vars -> Visibility -> Name ->
           ImpTy -> Core Constructor
checkCon env vis tn (MkImpTy fc cn_in ty_raw)
    = do cn <- inCurrentNS cn_in
         defs <- get Ctxt
         -- Check 'cn' is undefined
         Nothing <- lookupCtxtExact cn (gamma defs)
             | Just gdef => throw (AlreadyDefined fc cn)
         (ty, _) <- elabTerm cn InType env (IBindHere fc (PI Rig0) ty_raw)
                         (Just (gType fc))

         -- Check 'ty' returns something in the right family
         checkFamily fc cn tn env !(nf defs env ty)
         let fullty = abstractEnvType fc env ty
         logTermNF 5 (show cn) [] fullty
         -- TODO: Interface hash

         pure (MkCon fc cn !(getArity defs [] fullty) fullty)

export
processData : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Env Term vars -> FC -> Visibility ->
              ImpData -> Core ()
processData env fc vis (MkImpLater dfc n_in ty_raw) 
    = do n <- inCurrentNS n_in
         defs <- get Ctxt
         -- Check 'n' is undefined
         Nothing <- lookupCtxtExact n (gamma defs)
             | Just gdef => throw (AlreadyDefined fc n)
         
         (ty, _) <- elabTerm n InType env (IBindHere fc (PI Rig0) ty_raw)
                                 (Just (gType dfc))
         let fullty = abstractEnvType dfc env ty
         logTermNF 5 ("data " ++ show n) [] fullty

         checkIsType fc n env !(nf defs env ty)
         arity <- getArity defs [] fullty

         -- Add the type constructor as a placeholder while checking
         -- data constructors
         tidx <- addDef n (newDef fc n Rig1 fullty vis
                          (TCon 0 arity [] [] []))
         pure ()
processData env fc vis (MkImpData dfc n_in ty_raw opts cons_raw)
    = do n <- inCurrentNS n_in
         defs <- get Ctxt
         (ty, _) <- elabTerm n InType env (IBindHere fc (PI Rig0) ty_raw)
                                 (Just (gType dfc))
         let fullty = abstractEnvType dfc env ty

         -- If n exists, check it's the same type as we have here, and is
         -- a data constructor.
         ndefm <- lookupCtxtExact n (gamma defs)
         case ndefm of
              Nothing => pure ()
              Just ndef =>
                case definition ndef of
                     TCon _ _ _ _ _ =>
                        do ok <- convert defs [] fullty (type ndef)
                           if ok then pure ()
                                 else throw (AlreadyDefined fc n)
                     _ => throw (AlreadyDefined fc n)

         logTermNF 5 ("data " ++ show n) [] fullty

         checkIsType fc n env !(nf defs env ty)
         arity <- getArity defs [] fullty

         -- Add the type constructor as a placeholder while checking
         -- data constructors
         tidx <- addDef n (newDef fc n Rig1 fullty vis
                          (TCon 0 arity [] [] []))

         -- Constructors are private if the data type as a whole is
         -- export
         let cvis = if vis == Export then Private else vis
         cons <- traverse (checkCon env cvis (Resolved tidx)) cons_raw

         let ddef = MkData (MkCon dfc n arity fullty) cons
         addData vis ddef

         -- TODO: Interface hash, process options
         pure ()

