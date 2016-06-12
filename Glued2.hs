--
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

-- import Syntax (RawTerm)
-- import qualified Syntax as S

-- import Debug.Trace

-- {- Notes:

--   - add sigma & bottom
--   - add eta expansion for alpha
--   - elaborate values of bottom to common dummy value (eta rule for bottom)
--   - use phantom tags for scopes
--   - think about saner closure API
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
--   | QLam !Var !QTerm
--   | QLet !Var !QTerm !QTerm
--   | QStar
--   | QAnn !QTerm !QType
--   deriving (Eq)

-- -- Abstract
-- type AType = ATerm
-- data ATerm
--   = AVar !Var
--   | AAlpha !AlphaVar
--   | AApp !ATerm !ATerm
--   | APiApp !ATerm {-# unpack #-} !CTerm
--   | APi  !Var {-# unpack #-} !GType !ATerm
--   | ALam !Var {-# unpack #-} !GType !ATerm
--   | ALet !Var {-# unpack #-} !GType !ATerm !ATerm
--   | AStar
--   deriving (Eq)

-- -- Weak head normal
-- data Whnf
--   = VVar !Var
--   | VAlpha !AlphaVar
--   | VApp !Whnf Whnf
--   | VPi  !Var {-# unpack #-} !GType {-# unpack #-} !CTerm
--   | VLam !Var {-# unpack #-} !GType {-# unpack #-} !CTerm
--   | VStar
--   deriving (Eq, Show)

-- data Closure a = C !Env !a
--   deriving (Eq, Show, Functor)

-- type CTerm = Closure ATerm
-- type CType = Closure AType

-- _cenv (C e _) = e
-- _cterm (C _ t) = t

-- type GType = Glued
-- data Glued = G {-# unpack #-} !CTerm Whnf deriving (Eq)
-- instance Show Glued where show (G (C _ t) v) = show t

-- _pure (G u _) = u
-- _whnf (G _ v) = v

-- data Entry = E {-# unpack #-} !Glued {-# unpack #-} !GType deriving (Eq)
-- deriving instance Show Entry

-- _term (E t _) = t
-- _type (E _ v) = v

-- type Env = HashMap Var Entry
-- type TM  = Either String

-- instance IsString ATerm where fromString = AVar
-- instance IsString Whnf  where fromString = VVar
-- instance IsString QTerm where fromString = QVar

-- insert :: Var -> Entry -> Closure a -> Closure a
-- insert v x (C e t) = C (M.insert v x e) t

-- -- Reduction
-- --------------------------------------------------------------------------------

-- glued :: CTerm -> Glued
-- glued t = G t (whnf t)

-- whnf :: CTerm -> Whnf
-- whnf (C e t) = case t of
--   AApp f x -> case whnf (C e f) of
--     VLam v (G (C _ ty) _) t -> whnf (insert v (E (glued (C e x)) (glued (C e ty))) t)
--     f'          -> VApp f' (whnf (C e x))
--   APiApp f x -> case whnf (C e f) of
--     VPi  v (G (C _ ty) _) t -> whnf (insert v (E (glued x) (glued (C e ty))) t)
--     f'          -> error "whnf: APiApp"
--   AVar v         -> maybe (VVar v) (_whnf . _term) $ M.lookup v e
--   ALet v ty t t' -> whnf (insert v (E (glued (C e t)) ty) (C e t'))
--   APi  v (G (C _ ty) _) t -> VPi  v (glued (C e ty)) (C e t)
--   ALam v (G (C _ ty) _) t -> VLam v (glued (C e ty)) (C e t)
--   AStar          -> VStar
--   AAlpha{}       -> error "whnf: Alpha in ATerm"

-- isNeutral :: CTerm -> Bool
-- isNeutral (C e t) = case t of
--   AApp{}        -> True
--   AAlpha{}      -> True
--   AVar{}        -> True
--   APiApp{}      -> True
--   _             -> False

-- quoteVar :: Env -> Var -> GType -> Entry
-- quoteVar e v ty = E (G (C e (AVar v)) (VVar v)) ty

-- -- TODO: eta-expansion
-- alpha :: Int -> GType -> Entry
-- alpha a ty@(G (C e _) _) = E (G (C e (AAlpha a)) (VAlpha a)) ty

-- nf :: CTerm -> ATerm
-- nf = quote . whnf

-- quote :: Whnf -> ATerm
-- quote = \case
--   VVar v              -> AVar v
--   VApp f x            -> AApp (quote f) (quote x)
--   VPi  v ty t@(C e _) -> APi  v ty (nf (insert v (quoteVar e v ty) t))
--   VLam v ty t@(C e _) -> ALam v ty (nf (insert v (quoteVar e v ty) t))
--   VStar               -> AStar
--   VAlpha{}            -> error "quote: Alpha in Whnf"


-- -- Equality with n-depth delta reduction (but no beta)
-- --------------------------------------------------------------------------------

-- type Depth = Int

-- semiEqN :: Depth -> AlphaVar -> CTerm -> CTerm -> Maybe Bool
-- semiEqN !d !a c@(C e t) c'@(C e' t') = case (t, t') of
--   (AVar v, AVar v') ->
--     case (M.lookup v e, M.lookup v' e') of
--       (Just e1@(E (G t _) _), Just e2@(E (G t' _) _)) ->
--         if ptrEq e1 e2 then
--           Just True
--         else if d == 0 then
--           Nothing
--         else
--           semiEqN (d - 1) a t t'
--       _ -> Nothing

--   (AVar v, t') | d == 0    -> Nothing
--                | otherwise -> do
--                    E (G t _) _ <- M.lookup v e
--                    semiEqN (d - 1) a t c'
--   (t, AVar v') | d == 0    -> Nothing
--                | otherwise -> do
--                    E (G t' _) _ <- M.lookup v' e'
--                    semiEqN (d - 1) a c t'

--   (AApp f x, AApp f' x') ->
--     True <$ do {guard =<< semiEqN d a (C e f) (C e' f'); guard =<< semiEqN d a (C e x) (C e' x')}
--   (APiApp f x, APiApp f' x') ->
--     True <$ do {guard =<< semiEqN d a (C e f) (C e' f'); guard =<< semiEqN d a x x'}

--   (AApp{},   _) -> Nothing
--   (_,   AApp{}) -> Nothing
--   (APiApp{}, _) -> Nothing
--   (_, APiApp{}) -> Nothing

--   (ALam v ty t, ALam v' ty' t') -> (&&) <$> semiEqN d a (_pure ty) (_pure ty') <*>
--     (let al = alpha a ty in semiEqN d a (insert v al (C e t)) (insert v' al (C e' t')))
--   (APi  v ty t, APi  v' ty' t') -> (&&) <$> semiEqN d a (_pure ty) (_pure ty') <*>
--     (let al = alpha a ty in semiEqN d a (insert v al (C e t)) (insert v' al (C e' t')))

--   (AAlpha a, AAlpha a') -> Just (a == a')
--   (AStar,    AStar    ) -> Just True
--   _                     -> Just False

-- -- | Reduce top level Pi applications
-- reducePiApps :: CTerm -> CTerm
-- reducePiApps (C e t) = case t of
--   APiApp (APi v ty t) x -> C (M.insert v (E (glued x) ty) e) t
--   APiApp f x -> case reducePiApps (C e f) of
--     C e (APi v ty t) -> C (M.insert v (E (glued x) ty) e) t
--     _                -> C e (APiApp f x)
--   t -> C e t

-- depth :: Depth
-- depth = 1

-- semiEq_C :: CTerm -> CTerm -> Maybe Bool
-- semiEq_C t t' = semiEqN depth 0 (reducePiApps t) (reducePiApps t')

-- -- Equality with reduction
-- --------------------------------------------------------------------------------

-- whnfEq :: Int -> Whnf -> Whnf -> Bool
-- whnfEq !a t t' = case (t, t') of
--   (VVar v,   VVar v'   ) -> v == v'
--   (VApp f x, VApp f' x') -> whnfEq a f f' && whnfEq a x x'
--   (VLam v ty t, VLam v' ty' t') ->
--     termEq a (_pure ty) (_pure ty') &&
--     let al = alpha a ty
--     in termEq (a + 1) (insert v al t) (insert v' al t')
--   (VPi v ty t, VPi v' ty' t') ->
--     termEq a (_pure ty) (_pure ty') &&
--     let al = alpha a ty
--     in termEq (a + 1) (insert v al t) (insert v' al t')
--   (VStar,    VStar    ) -> True
--   (VAlpha a, VAlpha a') -> a == a'
--   _                     -> False

-- termEq :: Int -> CTerm -> CTerm -> Bool
-- termEq !b t t'
--   | isNeutral t || isNeutral t' = case semiEqN 0 b t t' of
--     Just True -> True
--     _ -> whnfEq b (whnf t) (whnf t')
--   | otherwise = whnfEq b (whnf t) (whnf t')

-- gluedEq :: Glued -> Glued -> Bool
-- gluedEq (G t v) (G t' v') =
--   maybe False id (semiEq_C t t') || whnfEq 0 v v'

-- -- Type checking / elaboration
-- --------------------------------------------------------------------------------

-- gstar :: GType
-- gstar = G (C mempty AStar) VStar

-- check :: Closure QTerm -> GType -> TM ATerm
-- check (C e t) want = traceShow ("check", (C e t), quote $ _whnf want) $ case (t, _whnf want) of
--   (QLam v t, VPi v' (G (C _ a) _) b) -> do
--     let a' = glued (C e a)
--     -- traceShowM (quote . _whnf $ glued (insert v' (quoteVar e v a) b))
--     t' <- check (insert v (quoteVar e v a') (C e t))
--                 (glued (insert v' (quoteVar e v a') b))
--     pure $ ALam v a' t'

--   _ -> do
--     (t', has) <- infer (C e t)
--     unless (gluedEq has want) $ Left "type mismatch"
--     pure t'

-- infer :: Closure QTerm -> TM (ATerm, Glued)
-- infer (C e t) = case t of
--   QVar v    -> pure (AVar v, _type $ e ! v)
--   QStar     -> pure (AStar, gstar)
--   QAnn t ty -> do
--     ty' <- glued . C e <$> check (C e ty) gstar
--     t'  <- check (C e t) ty'
--     pure (t', ty')
--   QLam{} -> Left "can't infer type for lambda"
--   QPi v ty t -> do
--     ty' <- glued . C e <$> check (C e ty) gstar
--     t'  <- check (insert v (quoteVar e v ty') (C e t)) gstar
--     pure (APi v ty' t', gstar)
--   QLet v t1 t2 -> do
--     (t1', t1t) <- infer (C e t1)
--     (t2', t2t) <- infer (insert v (E (glued (C e t1')) t1t) (C e t2))
--     pure (ALet v t1t t1' t2', t2t)
--   QApp f x -> do
--     (f', tf) <- infer (C e f)
--     case _whnf tf of
--       VPi v a (C e' b) -> do
--         x' <- check (C e x) a
--         pure (AApp f' x',
--               G (C (_cenv $ _pure tf) (APiApp (_cterm $ _pure tf) (C e x')))
--                 (whnf (insert v (E (glued (C e x')) a) (C e' b))))
--       _ -> Left "can't apply to non-function"

-- -- print
-- --------------------------------------------------------------------------------

-- instance Show QTerm where showsPrec = prettyQTerm


-- prettyQTerm :: Int -> QTerm -> ShowS
-- prettyQTerm prec = go (prec /= 0) where

--   unwords' :: [ShowS] -> ShowS
--   unwords' = foldr1 (\x acc -> x . (' ':) . acc)

--   spine :: QTerm -> QTerm -> [QTerm]
--   spine f x = go f [x] where
--     go (QApp f y) args = go f (y : args)
--     go t          args = t:args

--   go :: Bool -> QTerm -> ShowS
--   go p (QVar i)   = (i++)
--   go p (QApp f x) = showParen p (unwords' $ map (go True) (spine f x))
--   go p (QLam k t) = showParen p
--     (("λ "++) . (k++) . (". "++) . go False t)
--   go p (QPi k a b) = showParen p (arg . (" -> "++) . go False b)
--     where arg = if freeIn k b then showParen True ((k++) . (" : "++) . go False a)
--                               else go True a
--   go p QStar = ('*':)
--   go p (QAnn t ty) = showParen p (go False t . (" ∈ "++) . go False ty)
--   go p (QLet v t1 t2) =
--     showParen p (("let "++) . (v++) . (" = "++) . go False t1 . (" in \n"++) .
--                 go False t2)

--   freeIn :: Var -> QTerm -> Bool
--   freeIn k = go where
--     go (QVar i)      = i == k
--     go (QApp f x)    = go f || go x
--     go (QLam k' t)   = (k' /= k && go t)
--     go (QPi  k' a b) = go a || (k' /= k && go b)
--     go _             = False

-- prettyATerm :: Int -> ATerm -> ShowS
-- prettyATerm prec = go (prec /= 0) where

--   unwords' :: [ShowS] -> ShowS
--   unwords' = foldr1 (\x acc -> x . (' ':) . acc)

--   spine :: ATerm -> ATerm -> [ATerm]
--   spine f x = go f [x] where
--     go (AApp f y) args = go f (y : args)
--     go t          args = t:args

--   go :: Bool -> ATerm -> ShowS
--   go p (AVar i)     = (i++)
--   go p (AAlpha i)   = showParen p (("alpha " ++ show i)++)
--   go p (AApp f x)   = showParen p (unwords' $ map (go True) (spine f x))
--   go p (APiApp f (C _ x)) = showParen p (unwords' $ map (go True) (spine f x))
--   go p (ALam k a t) = showParen p
--     (("λ "++) . showParen True ((k++) . (" : "++) . go False (_cterm $ _pure a)) . (". "++) . go False t)
--   go p (APi k a b) = showParen p (arg . (" -> "++) . go False b)
--     where arg = if freeIn k b then showParen True ((k++) . (" : "++) . go False (_cterm $ _pure a))
--                               else go True (_cterm $ _pure a)
--   go p AStar = ('*':)
--   go p (ALet v ty t1 t2) =
--     showParen p (("let "++) . (v++) . (" = "++) .
--                  go False t1 . (" ∈ "++) . go False (_cterm $ _pure ty) .
--                  (" in \n"++) . go False t2)
--   freeIn :: String -> ATerm -> Bool
--   freeIn k = go where
--     go (AVar i)      = i == k
--     go (AApp f x)    = go f || go x
--     go (ALam k' a t) = go (_cterm $ _pure a) || (k' /= k && go t)
--     go (APi  k' a b) = go (_cterm $ _pure a) || (k' /= k && go b)
--     go _             = False

-- instance Show ATerm where
--   showsPrec = prettyATerm

-- -- tests
-- --------------------------------------------------------------------------------

-- nf0         = nf . C mempty
-- whnf0       = whnf . C mempty
-- infer0      = infer . C mempty
-- infer0'     = fmap (quote . _whnf . snd) . infer0

-- star    = QStar
-- ann     = flip QAnn
-- a ==> b = QPi "" a b
-- lam     = QLam
-- pi      = QPi
-- ($$)    = QApp
-- qlet    = QLet
-- infixl 8 $$
-- infixr 7 ==>


-- test =

--   -- qlet "nat"  (pi "r" star $ ("r" ==> "r") ==> "r" ==> "r") $

--   -- qlet "zero" (ann "nat" (lam "r" $ lam "s" $ lam "z" "z")) $

--   -- qlet "suc" (ann ("nat" ==> "nat")
--   -- (lam "a" $ lam "r" $ lam "s" $ lam "z" $ "s" $$ ("a" $$ "r" $$ "s" $$ "z"))) $

--   -- qlet "add" (ann ("nat" ==> "nat" ==> "nat")
--   -- (lam "a" $ lam "b" $ lam "r" $ lam "s" $ lam "z" $
--   --     "a" $$ "r" $$ "s" $$ ("b" $$ "r" $$ "s" $$ "z"))) $

--   -- qlet "mul" (ann ("nat" ==> "nat" ==> "nat")
--   -- (lam "a" $ lam "b" $ lam "r" $ lam "s" $ lam "z" $
--   --     "a" $$ "r" $$ ("b" $$ "r" $$ "s") $$ "z")) $

--   -- qlet "one"      ("suc" $$ "zero") $
--   -- qlet "two"      ("suc" $$ ("suc" $$ "zero")) $
--   -- qlet "five"     ("suc" $$ ("add" $$ "two" $$ "two")) $
--   -- qlet "ten"      ("add" $$ "five" $$ "five") $
--   -- qlet "hundred"  ("mul" $$ "ten" $$ "ten") $
--   -- qlet "thousand" ("mul" $$ "ten" $$ "hundred") $
--   -- qlet "tenK"     ("mul" $$ "hundred" $$ "hundred") $
--   -- qlet "hundredK" ("mul" $$ "hundred" $$ "thousand") $

--   qlet "id" (ann (pi "x" star $ "x" ==> "x")
--   (lam "a" $ lam "b" "b")) $

--   -- qlet "const" (ann (pi "a" star $ pi "b" star $ "a" ==> "b" ==> "a")
--   -- (lam "a" $ lam "b" $ lam "x" $ lam "y" "x")) $

--   -- qlet "list" (ann (star ==> star)
--   -- (lam "a" $ pi "r" star $ ("a" ==> "r" ==> "r") ==> "r" ==> "r")) $

--   -- qlet "nil" (ann (pi "a" star $ "list" $$ "a")
--   -- (lam "a" $ lam "r" $ lam "c" $ lam "n" $ "n")) $

--   -- qlet "cons" (ann (pi "a" star $ "a" ==> "list" $$ "a" ==> "list" $$ "a")
--   -- (lam "a" $ lam "x" $ lam "xs" $ lam "r" $ lam "c" $ lam "n" $
--   --  "c" $$ "x" $$ ("xs" $$ "r" $$ "c" $$ "n"))) $

--   -- qlet "listTest"
--   --   ("cons" $$ "nat" $$ "ten" $$ ("cons" $$ "nat" $$ "ten" $$ ("nil" $$ "nat"))) $

--   -- -- unreduced equalities
--   -- ------------------------------------------------------------
--   -- qlet "nfunTy" (ann ("nat" ==> star)
--   -- (lam "n" $ "n" $$ star $$ (lam "t" (star ==> "t")) $$ star)) $

--   -- -- simple unreduced eq (works)
--   -- qlet "unreduced1" (ann ("nfunTy" $$ "tenK" ==> "nfunTy" $$ "tenK")
--   -- (lam "f" $ "f")) $

--   -- -- unreduced eq under general function application (doesn't work)
--   -- -- qlet "unreduced2" (ann (
--   -- --       "const" $$ star $$ "nat" $$ ("nfunTy" $$ "tenK") $$ "zero"
--   -- --   ==> "const" $$ star $$ "nat" $$ ("nfunTy" $$ "tenK") $$ "one" )
--   -- -- (lam "f" "f")) $

--   -- -- unreduced eq under whnf (works)
--   -- qlet "unreduced3" (ann (
--   --       "const" $$ star $$ "nat" $$ (star ==> "nfunTy" $$ "tenK") $$ "zero"
--   --   ==> "const" $$ star $$ "nat" $$ (star ==> "nfunTy" $$ "tenK") $$ "one" )
--   -- (lam "f" "f")) $

--   -- -- unreduced eq from Pi applications (works)
--   -- qlet "unreduced4" (ann ("list" $$ ("nfunTy" $$ "tenK")) ("nil" $$ ("nfunTy" $$ "tenK"))) $

--   "id"

