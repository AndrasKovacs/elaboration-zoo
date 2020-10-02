{-# options_ghc -Wno-unused-imports #-}

module Main where

import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.Morph
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Char
import Data.Bifunctor
import Data.Foldable
import Data.Maybe
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Data.Set                   as S
import qualified Data.IntMap.Strict         as M
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

main = undefined

type Name = String

-- | Elaboration input contains holes which are filled in the output.
data Raw
  = RVar Name
  | RLam Name Raw
  | RApp Raw Raw
  | RU
  | RPi Name Raw Raw
  | RLet Name Raw Raw Raw
  | RHole
  | RSrcPos SourcePos Raw
  deriving Show

type Meta = Int

-- | Metacontext. An unsolved meta is just a meta which isn't contained in
--   the metacontext.
type MCxt = M.IntMap Val

type Ty  = Tm
type VTy = Val

-- | Environment for values. A `Nothing` denotes a bound variable.
type Vals = [Maybe Val]

-- | Elaboration context. We distinguish types of bound and defined variables.
data TyEntry = Bound ~VTy | Def ~VTy

data Cxt = Cxt {
  _vals  :: Vals,
  _types :: [TyEntry],
  _names :: [Name]
  }

-- | De Bruijn indices.
newtype Ix  = Ix Int deriving (Eq, Ord, Show, Num)

-- | DeBruijn levels.
newtype Lvl = Lvl Int deriving (Eq, Ord, Show, Num)

data Tm
  = Var Ix
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta Meta

data Head = HMeta Meta | HVar Lvl deriving Eq

-- | We use a spine form for neutral values, i.e. we have the head variable and
--   all arguments in a list. We need convenient access to both head and spine
--   when unifying and solving metas.
data Val
  = VNe Head [Val]    -- ^ [Val] here is in reverse order, i. e. the first Val in
                      --   the list is applied last to the head.
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

pattern VVar :: Lvl -> Val
pattern VVar x = VNe (HVar x) []

pattern VMeta :: Meta -> Val
pattern VMeta m = VNe (HMeta m) []


-- | Evaluation is up to a metacontext, so whenever we inspect a value during
--   elaboration, we always have to force it first, i.e. unfold solved metas and
--   compute until we hit a rigid head.
force :: MCxt -> Val -> Val
force ms = \case
  VNe (HMeta m) sp | Just t <- M.lookup m ms ->
    force ms (foldr (flip vApp) t sp)
  v -> v

-- forceM :: Val -> M e Val
-- forceM v = gets (\(_, ms) -> force ms v)

vVar :: Vals -> Ix -> Val
vVar (mv:vs) 0 = maybe (VVar $ Lvl $ length vs) id mv
vVar (_ :vs) x = vVar vs (x - 1)
vVar _       _ = error "impossible"

vApp :: Val -> Val -> Val
vApp (VLam _ t) ~u = t u
vApp (VNe h sp) ~u = VNe h (u:sp)
vApp _           _ = error "impossible"

eval :: MCxt -> Vals -> Tm -> Val
eval ms = go where
  go vs = \case
    Var x       -> vVar vs x
    Meta m      -> maybe (VMeta m) id (M.lookup m ms)
    App t u     -> vApp (go vs t) (go vs u)
    Lam x t     -> VLam x (\u -> go (Just u:vs) t)
    Pi x a b    -> VPi x (go vs a) (\u -> go (Just u:vs) b)
    Let x _ t u -> go (Just (go vs t):vs) u
    U           -> VU

-- evalM :: Cxt -> Tm -> M e Val
-- evalM cxt t = gets (\(_, ms) -> eval ms (_vals cxt) t)

-- -- |  Quote into fully forced normal forms.
-- quote :: MCxt -> Vals -> Val -> Tm
-- quote ms = go where
--   go vs v = case force ms v of
--     VNe h sp -> foldr (\v acc -> App acc (go vs v))
--                       (case h of HMeta m -> Meta m; HVar x -> Var x)
--                       sp
--     VLam x t ->
--       Lam x (go ((x, Nothing):vs) (t (VVar x)))
--     VPi x a b ->
--       Pi x (go vs a) (go ((x, Nothing):vs) (b (VVar x)))
--     VU -> U

-- quoteM :: Vals -> Val -> M e Tm
-- quoteM vs v = gets $ \(_, ms) -> quote ms vs v

-- nf :: MCxt -> Vals -> Tm -> Tm
-- nf ms vs = quote ms vs . eval ms vs

-- nfM :: Vals -> Tm -> M e Tm
-- nfM vs t = gets $ \(_, ms) -> nf ms vs t
