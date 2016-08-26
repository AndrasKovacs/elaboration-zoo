
{-# language
  PatternSynonyms, BangPatterns, MagicHash,
  DataKinds, LambdaCase, ViewPatterns,
  TypeFamilies, GADTs, EmptyCase #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued3 where

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import Control.Monad.Except
import GHC.Prim (reallyUnsafePtrEquality#)
import GHC.Types (isTrue#)

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M

{-
Issue: when doing syn check we don't really need types, but must
fiddle with them currently
  - solution : Elaborate into unreduced Elab with annotated spines and all the pizazz
               Keep raw terms really raw.
-}

type Var   = String
type Gen   = Int
type Depth = Int

data Sp
  = Var !Var
  | Gen !Gen -- only for syntactic equality
  | App !Sp !Term

data Term
  = Sp !Sp
  | Pi !Var !Type !Term
  | Let !Var !Term !Type !Term
  | Star
  | Lam !Var !Term
  | PiApp !Term !Var {-# unpack #-} !Entry -- only in inferred types

data WSp
  = WGen !Gen
  | WVar !Var -- only for quoting
  | WApp !WSp WTerm WType

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

gen :: Gen -> GTerm
gen g = G (C mempty (Sp (Gen g))) (WSp (WGen g))

var :: Var -> GTerm
var v = G (C mempty (Sp (Var v))) (WSp (WVar v))

domG :: WPi_ -> GType
domG (WPi_ e v a wa b) = G (C e a) wa

domW :: WPi_ -> WType
domW (WPi_ _ _ _ wa _) = wa

domVar :: WPi_ -> Var
domVar (WPi_ _ v _ _ _) = v

getW :: GTerm -> WTerm
getW (G _ wt) = wt

gstar :: GType
gstar = G (C mempty Star) WStar

(<:) :: Env -> (Var, GTerm, GType) -> Env
e <: (v, gt, gty) = M.insert v (E gt gty) e

(<::) :: Env -> (Var, GType) -> Env
e <:: (v, gty) = e <: (v, var v, gty)

-- Whnf
--------------------------------------------------------------------------------

wapp :: WPi_ -> WTerm -> GTerm -> WTerm
wapp pi (WLam lam) gt = instLam lam pi gt
wapp pi (WSp  sp ) gt = WSp (WApp sp (getW gt) (domW pi))
wapp _  _          _  = error "wapp: impossible"

whnfSp :: Env -> Sp -> WTerm
whnfSp e = fst . go where
  go :: Sp -> (WTerm, WType)
  go (Var v)    = let E _ gty = e ! v in (WSp (WVar v), getW gty)
  go Gen{}      = error "whnfSp: Gen"
  go (App sp t) = let gt = glue e t in case go sp of
    (wt, WPi pi) -> (wapp pi wt gt, instPi pi gt)
    _            -> error "whnfSp: non-Pi spine type"

glue :: Env -> Term -> GTerm
glue e t = G (C e t) (whnf e t)

whnf :: Env -> Term -> WTerm
whnf !e = \case
  Sp sp         -> whnfSp e sp
  Pi v a b      -> WPi (WPi_ e v a (whnf e a) b)
  Lam v t       -> WLam (WLam_ e v t)
  Let v t ty t' -> whnf (e <: (v, glue e t, glue e ty)) t'
  Star          -> WStar
  PiApp{}       -> error "whnf: PiApp"

-- Going under binders
--------------------------------------------------------------------------------

instLam :: WLam_ -> WPi_ -> GTerm -> WTerm
instLam (WLam_ e v t) pi gt = whnf (e <: (v, gt, domG pi)) t

instPi :: WPi_ -> GTerm -> WType
instPi pi@(WPi_ e v a wa b) gt = whnf (e <: (v, gt, domG pi)) b

divePi :: Gen -> WPi_ -> WType
divePi g pi = instPi pi (gen g)

quotePi :: WPi_ -> WType
quotePi pi = instPi pi (var (domVar pi))

-- Beta-eta conversion check
--------------------------------------------------------------------------------

conv :: WType -> WType -> Bool
conv = go 0 WStar where

  go :: Gen -> WType -> WTerm -> WTerm -> Bool
  go !g ty WStar WStar = True

  go g ty (WPi pi) (WPi pi') =
    go g (domW pi) (domW pi') WStar && go (g + 1) (divePi g pi) (divePi g pi') WStar

  go g (WPi pi) t t' =
    go (g + 1) (divePi g pi) (wapp pi t (gen g)) (wapp pi t' (gen g))

  go g _ (WSp sp) (WSp sp') = goSp g sp sp'
  go _ _ _ _ = error "conv: impossible"

  goSp :: Gen -> WSp -> WSp -> Bool
  goSp !g (WGen v)         (WGen v')           = v == v'
  goSp  g (WApp sp wt wty) (WApp sp' wt' wty') = goSp g sp sp' && go g wty wt wt'
  goSp  _ WVar{}           _                   = error "convSp: WVar"
  goSp  _ _                WVar{}              = error "convSp: WVar"
  goSp  _ _                _                   = False

-- Quoting to beta-eta normal form
--------------------------------------------------------------------------------

quote :: WTerm -> WType -> Term
quote WStar    _       = Star
quote (WPi pi) _       = Pi (domVar pi) (quote (domW pi) WStar) (quote (quotePi pi) WStar)
quote wt      (WPi pi) = Lam (domVar pi) (quote (wapp pi wt (var (domVar pi))) (quotePi pi))
quote (WSp sp) _       = Sp (quoteSp sp)
quote _        _       = error "quote: impossible"

quoteSp :: WSp -> Sp
quoteSp (WVar v)         = Var v
quoteSp (WApp sp wt wty) = App (quoteSp sp) (quote wt wty)
quoteSp WGen{}           = error "quoteSp: WGen"

-- Check & infer
--------------------------------------------------------------------------------

check :: Env -> Term -> WType -> M ()
check !e t want = case (t, want) of
  (Lam v t, WPi pi) ->
    check (e <:: (v, domG pi)) t (instPi pi (var v))
  _ -> do
    has <- getW <$> infer e t
    unless (conv has want) $ throwError "type mismatch"

inferSp :: Env -> Sp -> M GType
inferSp e = \case
  Var v    -> let E _ gty = e ! v in pure gty
  App sp t -> do
    G (C e' spTy) wSpTy <- inferSp e sp
    case wSpTy of
      WPi pi -> do
        check e t (domW pi)
        let gt = glue e t
        pure (G (C e' (PiApp spTy (domVar pi) (E gt (domG pi)))) (instPi pi gt))
      _ -> throwError "can't apply non-function"
  Gen{} -> error "inferSp: Gen"

infer :: Env -> Term -> M GType
infer !e = \case
  Sp sp    -> inferSp e sp
  Star     -> pure gstar
  Lam{}    -> throwError "can't infer type for lambda"
  Pi v a b -> do
    check e a WStar
    check (e <:: (v, glue e a)) b WStar
    pure gstar
  Let v t ty t' -> do
    check e ty WStar
    let gty = glue e ty
    check e t (getW gty)
    infer (e <: (v, glue e t, gty)) t'
  PiApp{} -> error "infer: PiApp"










-- Syntactic equality (semidecision)
--------------------------------------------------------------------------------

ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)

varVar :: Gen -> Depth -> Env -> Env -> Var -> Var -> Maybe Bool
varVar !g !d !e !e' v v' = case (M.lookup v e, M.lookup v' e') of
  (Just entry@(E (G (C e t) _) gt), Just entry'@(E (G (C e' t') _) _))
    | ptrEq entry entry' -> Just True
    | d == 0             -> Nothing
    | otherwise          -> synEqN g (d - 1) e e' (getW gt) t t'
  _ -> Nothing

synEqNSp :: Gen -> Depth -> Env -> Env -> Sp -> Sp -> Maybe Bool
synEqNSp g d e e' sp sp' = fst <$> go sp sp' where
  go (Gen v) (Gen v') = undefined -- Just (v == v')

  -- (Var v, Var v') -> varVar g d e e' v v'
  -- (Var v, sp'   ) -> varTerm g d e e' v (Sp sp')
  -- (sp   , Var v') -> varTerm g d e e' v' (Sp sp)
  -- (App sp t, App sp' t') -> do
  --   guard =<< synEqNSp g d e e' sp sp'
  --   guard =<< synEq g d e e' t t'
  --   pure True
  -- _ -> Nothing

varTerm :: Gen -> Depth -> Env -> Env -> Var -> Term -> Maybe Bool
varTerm g d e e' v t' = do
  guard (d /= 0)
  E (G (C e t) _) gt <- M.lookup v e
  synEqN g (d - 1) e e' (getW gt) t t'

-- | Try to decide equality by doing PiApp elimination, n-depth delta-reduction,
--   and eta-expansion. Beta reduction is *not* performed.
--   A 'Nothing' result indicates that equality can't be decided this way.
synEqN :: Gen -> Depth -> Env -> Env -> WType -> Term -> Term -> Maybe Bool
synEqN g d e e' wty t t' = case (t, t') of

  (PiApp t v entry, t')   -> synEqN g d (M.insert v entry e) e' wty t t'
  (t, PiApp t' v' entry') -> synEqN g d e (M.insert v' entry' e') wty t t'
  (Sp sp, Sp sp')         -> synEqNSp g d e e' sp sp'
  (Sp (Var v), t')        -> varTerm g d e e' v t'
  (t, Sp (Var v'))        -> varTerm g d e e' v' t

  (Lam v t, Lam v' t')    -> case wty of
    WPi pi -> let gvar = gen g; ga = domG pi in
      synEqN (g + 1) d (e <: (v, gvar, ga)) (e' <: (v', gvar, ga)) (divePi g pi) t t'
    _ -> error "synEq: non-Pi type for Lam"

  (Pi v a b, Pi v' a' b') -> (&&) <$> synEqN g d e e' WStar a a' <*>
    (let gvar = gen g; ga = glue e a in
     synEqN (g + 1) d (e <: (v, gvar, ga)) (e' <: (v', gvar, ga)) WStar b b')

  (Star, Star) -> Just True
  _            -> Just False
