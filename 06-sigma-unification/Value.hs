
module Value where

import Common
import Syntax

data Spine
  = SNil
  | SApp Spine ~Val Icit
  | SProj1 Spine
  | SProj2 Spine
  | SProjField Spine Name Int

spineLen :: Spine -> Int
spineLen = go 0 where
  go acc SNil                = acc
  go acc (SApp sp _ _)       = go (acc + 1) sp
  go acc (SProj1 sp)         = go (acc + 1) sp
  go acc (SProj2 sp)         = go (acc + 1) sp
  go acc (SProjField sp _ _) = go (acc + 1) sp

type Env     = [Val]
data Closure = Closure Env Tm
type VTy     = Val

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl Spine
  | VLam Name Icit {-# unpack #-} Closure
  | VPi Name Icit ~VTy {-# unpack #-} Closure
  | VSg Name ~VTy {-# unpack #-} Closure
  | VPair ~Val ~Val
  | VU

pattern VVar :: Lvl -> Val
pattern VVar x = VRigid x SNil

pattern VMeta :: MetaVar -> Val
pattern VMeta m = VFlex m SNil
