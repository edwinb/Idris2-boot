module Core.TTC

import Core.Core
import Core.FC
import Core.TT

import Utils.Binary

export
TTC FC where
  toBuf = ?tofc
  fromBuf = ?fromfc

export
TTC Name where
  toBuf = ?toName
  fromBuf = ?fromName

