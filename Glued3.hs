
{-# language
  PatternSynonyms, BangPatterns, MagicHash,
  DataKinds, LambdaCase, ViewPatterns #-}
{-# language TypeFamilies, GADTs, EmptyCase #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued3 where

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import GHC.Prim (reallyUnsafePtrEquality#)
import GHC.Types (isTrue#)

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M

ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)

type Var   = String
type Gen   = Int
type Depth = Int

data Sp
  = Var !Var
  | Gen !Gen {-# unpack #-} !GType -- present only during syntactic equality check
  | App !Sp !Term

data Term
  = Sp !Sp
  | Pi !Var !Type !Term
  | Let !Var !Term !Type !Term
  | Star
  | Lam !Var !Term

data WSp
  = WGen !Gen {-# unpack #-} !GType
  | WVar !Var {-# unpack #-} !GType -- present only during quoting
  | WApp !WSp {-# unpack #-} !GTerm

data WTerm
  = WSp !WSp
  | WPi  {-# unpack #-} !WPi_
  | WLam {-# unpack #-} !WLam_
  | WStar

type Type    = Term
type WType   = WTerm
data Closure = C !Env !Term
data GTerm   = G {-# unpack #-} !Closure WTerm
type GType   = GTerm
data Entry   = E {-# unpack #-} !GTerm {-# unpack #-} !GType
type Env     = HashMap Var Entry
data WPi_    = WPi_ !Env !Var !Type WType !Term
data WLam_   = WLam_ !Env !Var !Term
type M       = Either String

-- misc
--------------------------------------------------------------------------------

gen :: Gen -> GType -> GTerm
gen g gty = G (C mempty (Sp (Gen g gty))) (WSp (WGen g gty))

var :: Var -> GType -> GTerm
var v gty = G (C mempty (Sp (Var v))) (WSp (WVar v gty))

domG :: WPi_ -> GType
domG (WPi_ e v a wa b) = G (C e a) wa

domW :: WPi_ -> WType
domW (WPi_ _ _ _ wa _) = wa

piVar :: WPi_ -> Var
piVar (WPi_ _ v _ _ _) = v

domVar :: WPi_ -> GType
domVar pi = var (piVar pi) (domG pi)

domGen :: Gen -> WPi_ -> GType
domGen g pi = gen g (domG pi)

getW :: GTerm -> WTerm
getW (G _ wt) = wt

foldSp :: forall r. (Var -> Entry -> r) -> (Gen -> r) -> (WPi_ -> r -> GTerm -> r) -> Env -> Sp -> r
foldSp var gen app e = fst . go
  where
    go :: Sp -> (r, WType)
    go (Var v)     = let entry@(E _ gty) = e ! v in (var v entry, getW gty)
    go (Gen v gty) = (gen v, getW gty)
    go (App sp t)  = let gt = glue e t in case go sp of
      (sp', WPi pi) -> (app pi sp' gt, instPi pi gt)
      _             -> error "foldSp: non-Pi spine type"

-- Whnf
--------------------------------------------------------------------------------

wapp :: WPi_ -> WTerm -> GTerm -> WTerm
wapp pi (WLam lam) gt = instLam lam pi gt
wapp pi (WSp  sp ) gt = WSp (WApp sp gt)
wapp _  _          _  = error "wapp: impossible"

whnfSp :: Env -> Sp -> WTerm
whnfSp = foldSp (\_ (E gt _) -> getW gt) (\_ -> error "whnfSp: Gen in spine") wapp

glue :: Env -> Term -> GTerm
glue !e !t = G (C e t) (whnf e t)

whnf :: Env -> Term -> WTerm
whnf !e = \case
  Sp sp         -> whnfSp e sp
  Pi v a b      -> WPi (WPi_ e v a (whnf e a) b)
  Lam v t       -> WLam (WLam_ e v t)
  Let v t ty t' -> whnf (M.insert v (E (glue e t) (glue e ty)) e) t'
  Star          -> WStar

-- Going under binders
--------------------------------------------------------------------------------

instLam :: WLam_ -> WPi_ -> GTerm -> WTerm
instLam (WLam_ e v t) pi gt = whnf (M.insert v (E gt (domG pi)) e) t

instPi :: WPi_ -> GTerm -> WType
instPi pi@(WPi_ e v a wa b) gt = whnf (M.insert v (E gt (domG pi)) e) b

divePi :: Gen -> WPi_ -> WType
divePi g pi = instPi pi (domGen g pi)

quotePi :: WPi_ -> WType
quotePi pi = instPi pi (domVar pi)

-- Beta-eta conversion check
--------------------------------------------------------------------------------

conv :: Gen -> WType -> WTerm -> WTerm -> Bool
conv g ty WStar WStar = True

conv g ty (WPi pi) (WPi pi') =
  conv g (domW pi) (domW pi') WStar &&
  conv (g + 1) (divePi g pi) (divePi g pi') WStar

conv g (WPi pi) t t' =
  conv (g + 1) (divePi g pi)
    (wapp pi t  (gen g (domG pi)))
    (wapp pi t' (gen g (domG pi)))

conv g _ (WSp sp) (WSp sp') = convSp g sp sp'

conv _ _ _ _ = error "conv: impossible"

convSp :: Gen -> WSp -> WSp -> Bool
convSp g sp sp' = maybe False (\_ -> True) $ go g sp sp'
  where
    go :: Gen -> WSp -> WSp -> Maybe WType
    go g (WGen v gt)  (WGen v' _)    = getW gt <$ guard (v == v')
    go g (WApp sp gt) (WApp sp' gt') = do
      go g sp sp' >>= \case
        WPi pi -> do
          let wty = instPi pi gt
          wty <$ (guard $ conv g wty (getW gt) (getW gt'))
        _ -> error "convSp : impossible"
    go g _ _ = Nothing

-- Quoting to beta-eta normal form
--------------------------------------------------------------------------------

quote :: WTerm -> WType -> Term
quote WStar    _       = Star
quote (WPi pi) _       = Pi (piVar pi) (quote (domW pi) WStar) (quote (quotePi pi) WStar)
quote wt      (WPi pi) = Lam (piVar pi) (quote (wapp pi wt (domVar pi)) (quotePi pi))
quote (WSp sp) _       = Sp (quoteSp sp)
quote _        _       = error "quote: impossible"

quoteSp :: WSp -> Sp
quoteSp = snd . go where
  go (WVar v  gt) = (getW gt, Var v)
  go (WApp sp gt) = case go sp of
    (WPi pi, sp) -> (quotePi pi, App sp (quote (getW gt) (domW pi)))
    _            -> error "quoteSp: impossible"
  go WGen{} = error "quoteSp: WGen"

-- Equality with n-depth delta reduction (semidecision)
--------------------------------------------------------------------------------

-- varVar :: Gen -> Depth -> Env -> Env -> Var -> Var -> Maybe Bool
-- varVar !g !d !e !e' v v' = case (e ! v, e' ! v') of
--   (entry@(E (G (C e t) _) _), entry'@(E (G (C e' t') _) _))
--     | ptrEq entry entry' -> Just True
--     | d == 0             -> Nothing
--     | otherwise          -> deltaEqN g (d - 1) e e' t t'

-- varTerm :: Gen -> Depth -> Env -> Env -> Var -> Term -> WType -> Maybe Bool
-- varTerm !g !d !e !e' v t' ty'
--   | d == 0    = Nothing
--   | otherwise = case e ! v of
--       E (G (C e t) _) _ -> deltaEqN g (d - 1) e e' t t'

-- -- deltaEqNSp :: Gen -> Depth -> Env -> Env -> Sp -> Sp -> Maybe Bool
-- -- deltaEqNSp !g !d !e !e' sp sp' = case (sp, sp') of
-- --   (Gen v   , Gen v'    ) -> Just (v == v')
-- --   (Var v   , Var v'    ) -> varVar g d e e' v v'
-- --   (Var v   , sp'       ) -> varTerm g d e e' v (Sp sp')
-- --   (sp      , Var v'    ) -> varTerm g d e e' v' (Sp sp)
-- --   (App sp t, App sp' t') -> True <$ do
-- --                               guard =<< deltaEqNSp g d e e' sp sp'
-- --                               guard =<< deltaEqN g d e e' t t'
-- --   _                      -> Nothing

-- deltaEqN :: Gen -> Depth -> Env -> Env -> Term -> Term -> WType -> WType -> Maybe Bool
-- deltaEqN !g !d !e !e' t t' ty ty' = case (t, t') of
--   (Sp sp     , Sp sp'     ) -> undefined -- deltaEqNSp g d e e' sp sp'
--   (Sp (Var v), t'         ) -> varTerm g d e e' v t'
--   (t         , Sp (Var v')) -> varTerm g d e e' v' t
--   (Lam v t   , Lam v' t'  ) -> case (ty, ty') of
--     (WPi pi, WPi pi') -> _


--   (Pi v a b  , Pi v' a' b') -> do
--     aEq <- deltaEqN g d e e' a a' WStar WStar
--     if aEq then do
--       let entry = quoteGen g (glue e a)
--       deltaEqN (g + 1) d (M.insert v entry e) (M.insert v' entry e') b b' WStar WStar
--     else
--       pure False
--   (Star      , Star       ) -> Just True
--   _                         -> Just False

