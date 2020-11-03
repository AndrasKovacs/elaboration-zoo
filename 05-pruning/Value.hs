
module Value where

import Common
import Syntax

type Env     = [Val]
type Spine   = [(Val, Icit)]
data Closure = Closure Env Tm
type VTy     = Val

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl Spine
  | VLam Name Icit {-# unpack #-} Closure
  | VPi Name Icit ~VTy {-# unpack #-} Closure
  | VU

pattern VVar :: Lvl -> Val
pattern VVar x = VRigid x []

pattern VMeta :: MetaVar -> Val
pattern VMeta m = VFlex m []
