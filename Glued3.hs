
-- {-# language PatternSynonyms, BangPatterns, MagicHash, LambdaCase, ViewPatterns #-}
-- {-# language OverloadedStrings, TypeFamilies, GADTs, EmptyCase #-}
-- {-# options_ghc -fwarn-incomplete-patterns #-}

-- module Glued3 where

-- import Prelude hiding (pi)
-- import Data.String
-- import Control.Monad
-- import Control.Applicative
-- import Control.Monad.Except
-- import Data.Either
-- import GHC.Prim (reallyUnsafePtrEquality#)
-- import GHC.Types (isTrue#)

-- import Data.Text (Text)
-- import qualified Data.Text as T

-- import Data.HashMap.Strict (HashMap, (!))
-- import qualified Data.HashMap.Strict as M

-- ptrEq :: a -> a -> Bool
-- ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
-- {-# inline ptrEq #-}

-- type Gen = Int
-- type Var = Text

-- type Type = Term
-- data Term
--   = Var !Var
--   | Gen !Gen
--   | App !Term !Term
--   | PiApp !Term {-# unpack #-} !Closure
--   | Pi !Var !Type !Type
--   | Lam !Var !Term
--   | Let !Var !Type !Term !Term
--   | Star

-- -- whnf
-- type WType = WTerm
-- data WTerm
--   = WVar !Var
--   | WGen !Gen
--   | WApp !WTerm WTerm
--   | WPi {-# unpack #-} !PiBind
--   | WLam {-# unpack #-} !LamBind
--   | WStar

-- data GTerm   = G !Closure !WTerm
-- type GType   = GTerm
-- data Closure = C !Env !Term
-- data Entry   = E {-# unpack #-} !GTerm {-# unpack #-} !GType
-- data LamBind = LamBind !Env !Var !Term
-- data PiBind  = PiBind !Env !Var !Type WType !Term
-- type Env     = HashMap Var Entry
-- type M       = Either String

-- instance IsString Term  where fromString = Var . fromString
-- instance IsString WTerm where fromString = WVar . fromString

-- inst :: LamBind -> PiBind -> GTerm -> (WTerm, WType)
-- inst (LamBind e v t) (PiBind e' v' a wa b) x =
--   let ga = G (C e' a) wa in
--   (whnf (M.insert v (E x ga) e) t, whnf (M.insert v' (E x ga) e') b)

-- instPi :: PiBind -> GTerm -> WType
-- instPi (PiBind e v a wa b) t' = whnf (M.insert v (E t' (G (C e a) wa)) e) b

-- -- --------------------------------------------------------------------------------

-- glued :: Env -> Term -> GTerm
-- glued e t = G (C e t) (whnf e t)

-- whnfApp :: Env -> Term -> (WTerm, WType)
-- whnfApp e = \case
--   Var v -> let E (G _ t) (G _ ty) = e ! v in (t, ty)
--   App f x -> case whnfApp e f of
--     (WLam lam, WPi pi) -> inst lam pi (glued e x)
--     (f       , WPi pi) -> (WApp f (whnf e x), instPi pi (glued e x))
--     _                  -> error "whnfApp: impossible"
--   _ -> error "whnfApp: impossible"
    
-- whnf :: Env -> Term -> WTerm
-- whnf e = \case
--   Var v     -> let E (G _ t) _ = e ! v in t
--   App f x   -> fst $ whnfApp e (App f x)
--   Pi v a b  -> WPi (PiBind e v a (whnf e a) b)
--   Lam v t   -> WLam (LamBind e v t)
--   PiApp f (C e x) -> case whnf e f of
--     WPi pi -> instPi pi (glued e x)
--     _      -> error "whnf: impossible"
--   Star -> WStar
--   Let v t ty t' -> whnf (M.insert v (E (glued e t) (glued e ty)) e) t'
--   _ -> error "whnf: impossible"

-- quoteVar :: Env -> Var -> GType -> Entry
-- quoteVar e v ty = E (G (C e (Var v)) (WVar v)) ty

-- gen :: Int -> Env -> GType -> Entry
-- gen a e = E (G (C e (Gen a)) (WGen a))

-- nf :: Env -> Term -> Term
-- nf e = quote . whnf e

-- quote :: WTerm -> Term
-- quote = \case
--   WVar v            -> Var v
--   WApp f x          -> App (quote f) (quote x)
--   WPi (PiBind e v a wa b) ->
--     Pi v (quote wa) (nf (M.insert v (quoteVar e v (G (C e a) wa)) e) b)
--   WLam (LamBind e v t) -> _
  


    
--   -- WPi  pi           -> Pi  v (nf e ty) (nf (M.insert v (quoteVar e v (glued e ty)) e) t)
--   -- WLam lam          -> Lam v (nf e ty) (nf (M.insert v (quoteVar e v (glued e ty)) e) t)
--   WStar             -> Star
--   WGen{}            -> error "quote: Gen in WTerm"



-- --      PiBind !Env !Var !Type WType !Term 





