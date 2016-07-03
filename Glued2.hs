
-- {-# language PatternSynonyms, BangPatterns, MagicHash, LambdaCase, ViewPatterns #-}
-- {-# language OverloadedStrings #-}
-- {-# options_ghc -fwarn-incomplete-patterns #-}

-- module Glued2 where

-- import Prelude hiding (pi)
-- import Data.String
-- import Control.Monad
-- import Control.Applicative
-- import Control.Monad.Except
-- import Data.Either
-- import GHC.Prim (reallyUnsafePtrEquality#)
-- import GHC.Types (isTrue#)

-- import Data.HashMap.Strict (HashMap, (!))
-- import qualified Data.HashMap.Strict as M

-- import Debug.Trace

-- {-
-- binder :
--   - type
--   - var
--   - instantiate
--   - body

-- current env in monad
-- enter closure
-- -}


-- ptrEq :: a -> a -> Bool
-- ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
-- {-# inline ptrEq #-}

-- -- Data
-- --------------------------------------------------------------------------------

-- type AlphaVar = Int
-- type Var = String

-- -- Concrete
-- type QType = QTerm
-- data QTerm
--   = QVar !Var
--   | QApp !QTerm !QTerm
--   | QPi !Var !QType !QTerm
--   | QLet !Var !QType !QTerm !QTerm
--   | QLam !Var !QTerm
--   | QStar

-- -- Abstract
-- type AType = ATerm
-- data ATerm
--   = AVar !Var
--   | AAlpha !AlphaVar
--   | AApp !ATerm !ATerm
--   | APiApp !ATerm {-# unpack #-} !Closure
--   | APi !Var !AType !AType
--   | ALam !Var !ATerm
--   | ALet !Var !AType !ATerm !ATerm
--   | AStar

-- -- Weak head normal
-- type WType = Whnf
-- data Whnf
--   = VVar !Var
--   | VAlpha !AlphaVar
--   | VApp !Whnf Whnf
--   | VPi  !Var !AType {-# unpack #-} !Closure
--   | VLam !Var {-# unpack #-} !Closure
--   | VStar

-- data Closure = C !Env !ATerm

-- _cenv  (C e _) = e
-- _cbody (C _ t) = t

-- type GType = Glued
-- data Glued = G {-# unpack #-} !Closure Whnf

-- _raw  (G u _) = u
-- _whnf (G _ v) = v

-- data Entry = E {-# unpack #-} !Glued {-# unpack #-} !GType

-- _term (E t _) = t
-- _type (E _ v) = v

-- type Env = HashMap Var Entry
-- type TM  = Either String

-- instance IsString ATerm where fromString = AVar
-- instance IsString Whnf  where fromString = VVar
-- instance IsString QTerm where fromString = QVar


-- reduction
--------------------------------------------------------------------------------

-- whnfApp :: Env -> ATerm -> (Whnf, WType)
-- whnfApp e = \case  
--   AVar v   -> let E t ty = e ! v in (_whnf t, _whnf ty)
--   AApp f x -> case whnfApp e f of
--     (VLam v (C elam t), VPi v' a (C epi b)) -> _
  
-- whnf :: Env -> ATerm -> Whnf
-- whnf e = \case
--   AApp f x -> fst $ whnfApp e (AApp f x) 


  
