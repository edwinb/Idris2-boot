module Core.CaseBuilder

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Normalise
import Core.TT
import Core.Value

%default covering

public export
data Phase = CompileTime | RunTime

data ArgType : List Name -> Type where
     Known : RigCount -> (ty : Term vars) -> ArgType vars -- arg has type 'ty'
     Stuck : (fty : Term vars) -> ArgType vars 
         -- ^ arg will have argument type of 'fty' when we know enough to
         -- calculate it
     Unknown : ArgType vars
         -- arg's type is not yet known due to a previously stuck argument

Show (ArgType ns) where
  show (Known c t) = "Known " ++ show c ++ " " ++ show t
  show (Stuck t) = "Stuck " ++ show t
  show Unknown = "Unknown"

record PatInfo (pvar : Name) (vars : List Name) where
  constructor MkInfo
  pat : Pat
  loc : IsVar name idx vars
  argType : ArgType vars -- Type of the argument being inspected (i.e. 
                         -- *not* refined by this particular pattern)


