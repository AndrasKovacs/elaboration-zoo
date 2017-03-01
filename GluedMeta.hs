{-# language Strict, OverloadedStrings #-}

{-
  Concept:
    - Metas + closures + gluing
    - Untyped evaluation, untyped eta for functions
    - Experiment with optimizations for meta solutions

  The essence of what we're trying to do here:
    - The only place where fundamental inefficieny comes in
      is metavariable solution, where we need occurs/scope check
      and variable renaming.

    - We may have to evaluate rhs to do occurs/scope check in any case,
      but we don't want to rename evaluated terms. We want to rename
      unreduced terms, because that's always going to be bounded by
      source size. From another perspective, unreduced terms have explicit
      sharing, while reduced terms only unobservable sharing, and renaming
      reduced terms eliminates all unobservable sharing.

    - Similary, when zonking an elaborated term, we want to instantiate
      metas with unreduced terms, and also preserve sharing in the
      metacontext. The latter can be done by lowering mcxt entries into
      the term as let bindings. The details of this should be worked out.
-}

module GluedMeta where

import Prelude hiding (pi)

import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict as IM
import qualified Data.ByteString.Short as B

import Control.Arrow
import Control.Exception
import Control.Monad
import Data.Function
import Data.IORef
import Data.List
import Data.String
import System.IO.Unsafe

type Name  = B.ShortByteString
type Meta  = Int
type Gen   = Int

type Ws    = [(Name, Whnf)]            -- whnf substitution
type Tms   = [(Name, CTm)]             -- unreduced term substitution
type Cxt   = [(Name, Either GTy GTy)]  -- type context (type of let or lam binding)
type MCxt  = IM.IntMap (GTy, Maybe GTm)
type M     = IO

type WTy = Whnf
type GTy = GTm
type Ty  = Tm

data CTm = C {
    _Tms :: Tms
  , _Tm  :: Tm}
  
data GTm = G {
    _CTm  :: {-# unpack #-} CTm
  , _Whnf :: ~Whnf}

data Raw
  = RVar Name
  | RApp Raw Raw
  | RStar
  | RLam Name Raw
  | RPi Name Raw Raw
  | RLet Name Raw Raw Raw

data Tm
  = Var Name
  | Gen Gen
  | App Tm Tm Name
  | Star
  | Lam Name Tm
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm

data WHead
  = WMeta Meta
  | WVar Name
  | WGen Gen  

data Whnf
  = WNe WHead Ws Tms
  | WLam Name Ws Tms Tm 
  | WPi  Name Ws Tms Ty ~WTy Ty
  | WStar

--------------------------------------------------------------------------------

{-# inline doIO #-}
doIO :: IO a -> a
doIO = unsafeDupablePerformIO

{-# noinline mcxt #-}
mcxt :: IORef MCxt
mcxt = doIO (newIORef mempty)

{-# noinline freshMeta #-}
freshMeta :: IORef Int
freshMeta = doIO (newIORef 0)

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef freshMeta 0

lookupMeta :: Meta -> (GTy, Maybe GTm)
lookupMeta m = doIO $ ((IM.! m) <$> readIORef mcxt)

-- Evaluation (modulo global mcxt)
--------------------------------------------------------------------------------

-- inst :: Meta -> Maybe Whnf
-- inst m = _Whnf <$> snd (lookupMeta m)

-- glue :: Ws -> Tms -> Tm -> GTm
-- glue ws ts t = G (C ts t) (whnf ws ts t)

-- whnf :: Ws -> Tms -> Tm -> Whnf
-- whnf ws ts = \case
--   Var n     -> maybe (WNe (WVar n) [] []) update (lookup n ws)
--   App f a n -> wapp (whnf ws ts f) (glue ws ts a) n

-- wapp :: Whnf -> GTm -> Name -> Whnf
-- wapp f (G a ~wa) n = case f of
--   WLam n' ws' ts' t' -> whnf ((n', wa):ws') ((n', a):ts') t'
--   WNe h ws' ts'      -> WNe h ((n , wa):ws') ((n, a):ts')
    
-- update :: Whnf -> Whnf
-- update = \case
--   WNe (WMeta m) ws ts | Just w <- inst m -> update (go ws ts w) where
--     go [] [] w = w
--     go ((n, w)
                        

                        --update (foldr (\(n, ~a) t -> wapp t a n) w ws)
--  w -> w
  


  -- Let v e' ty e -> whnf ((v, whnf vs e'):vs) e
  -- App f a v     -> vapp (whnf vs f) (whnf vs a) v
  -- Lam v t       -> VLam v $ \a -> whnf ((v, a):vs) t
  -- Pi v a b      -> VPi v (whnf vs a) $ \a -> whnf ((v, a):vs) b
  -- Star          -> VStar
  -- Meta i        -> maybe (VMeta i :$ []) refresh (inst i)                   
  -- Gen{}         -> error "whnf: impossible"
  

-- update :: Whnf -> Whnf
-- update = \case
--   WNe (WMeta m) ws | Just w <- inst m -> update (foldr (\(n, ~a) t -> wapp t a n) w ws)
--   w -> w

-- wapp :: Whnf -> Whnf -> Name -> Whnf
-- wapp f ~x n = case f of
--   WLam n e t -> whnf ((n, x):e) t
--   WNe h ws   -> WNe h ((n, x):ws)
  
