{-# language BangPatterns, MagicHash, LambdaCase, Strict, CPP, TupleSections #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module MetavarLet where

import Prelude hiding (pi, lookup)
import Control.Applicative
import Control.Monad
import Data.Void
import Data.Functor.Identity
import Data.Hashable

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Data.List hiding (lookup)
import Data.String
import System.IO.Unsafe
import Data.IORef

import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char       as C

import Debug.Trace

-- Syntax
--------------------------------------------------------------------------------

type Name   = String
type Meta   = Int
type Gen    = Int
type Ty     = Val
type Sub a  = [(Name, a)]
type Vals   = Sub (Maybe Val)        -- Nothing: bound, Just: defined
type Tys    = Sub (Either Ty Ty)     -- Left: bound, Right: defined
type Metas  = IntMap Val
type Ren    = HashMap (Either Name Gen) Name
type Spine  = Sub (Val, Icit)

data Icit = Expl | Impl deriving (Eq, Show)

data MetaInsertion
  = MIYes
  | MINo
  | MIUntilName Name
  deriving (Eq, Show)

data Raw
  = RVar Name
  | RLet Name Raw Raw Raw
  | RApp Raw Raw (Either Name Icit)
  | RLam Name (Either Name Icit) Raw
  | RPi Name Icit Raw Raw
  | RU
  | RNoMI Raw
  | RHole

data Tm
  = Var Name
  | Gen Gen
  | Let Name Tm Tm Tm
  | App Tm Tm Name Icit
  | Lam Name Icit Tm
  | Pi Name Icit Tm Tm
  | U
  | Meta Meta

data Head
  = VMeta Meta
  | VVar Name
  | VGen Gen

data Val
  = Head :$ Spine
  | VLam Name Icit (Val -> Val)
  | VPi Name Icit Val (Val -> Val)
  | VU
infix 3 :$

-- Parser
--------------------------------------------------------------------------------

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme     = L.lexeme sc
symbol     = L.symbol sc
char c     = lexeme (C.char c)
parens p   = lexeme (char '(' *> p <* char ')')
brackets p = lexeme (char '{' *> p <* char '}')
keywords   = HS.fromList ["let", "in"] :: HS.HashSet String

pIdent = try $ lexeme $ do
  w <- some C.alphaNumChar
  if HS.member w keywords
    then empty
    else pure w

pBind    = pIdent <|> symbol "_"
pVar     = RVar <$> pIdent
pU       = RU <$ char '*'
pHole    = RHole <$ char '_'

pLamBinder :: Parser (Name, Either Name Icit)
pLamBinder =
      ((,Right Expl) <$> pBind)
  <|> try ((,Right Impl) <$> brackets pBind)
  <|> brackets ((\x y -> (y, Left x)) <$> (pIdent <* char '=') <*> pBind)

pLam :: Parser Raw
pLam = do
  char '\\'
  binders <- some pLamBinder
  char '.'
  t <- pRaw
  pure (foldr (\(x, i) u -> RLam x i u) t binders)

pArg :: Parser (Maybe (Raw, Either Name Icit))
pArg =
      (Just <$>
        (    try ((,Right Impl) <$> brackets pRaw)
         <|> brackets ((\x t -> (t, Left x)) <$> (pIdent <* char '=') <*> pRaw)
         <|> ((,Right Expl) <$> pAtom)))
  <|> (Nothing <$ char '!')

pSpine :: Parser Raw
pSpine = do
  head  <- pAtom
  spine <- many pArg
  pure (foldl' (\t -> maybe (RNoMI t) (\(u, i) -> RApp t u i)) head spine)

pPiBinder :: Parser ([Name], Raw, Icit)
pPiBinder =
      brackets ((,,Impl) <$> some pBind <*> ((char ':' *> pRaw) <|> pure RHole))
  <|> parens ((,,Expl) <$> some pBind <*> (char ':' *> pRaw))

pPiDomain :: Parser (Either Raw [([Name], Raw, Icit)])
pPiDomain =
      try (Right <$> some pPiBinder)
  <|> (Left <$> pSpine)

pPi :: Parser Raw
pPi = do
  dom <- pPiDomain
  symbol "->"
  b <- pRaw
  case dom of
    Right binders ->
      pure (foldr (\(xs, a, i) b -> foldr (\x -> RPi x i a) b xs) b binders)
    Left dom ->
      pure (RPi "_" Expl dom b)

pLet :: Parser Raw
pLet = do
  symbol "let"
  x <- pIdent
  char ':'
  a <- pRaw
  char '='
  t <- pRaw
  symbol "in"
  u <- pRaw
  pure (RLet x a t u)

pAtom :: Parser Raw
pAtom = pU <|> pVar <|> pHole <|> parens pRaw

pRaw :: Parser Raw
pRaw =
      pLam
  <|> pLet
  <|> try pPi
  <|> pSpine

pRaw' :: Parser Raw
pRaw' = sc *> pRaw <* eof


-- Global metacontext
--------------------------------------------------------------------------------

{-# noinline mcxt #-}
mcxt :: IORef Metas
mcxt = unsafeDupablePerformIO (newIORef mempty)

{-# noinline freshMeta #-}
freshMeta :: IORef Int
freshMeta = unsafeDupablePerformIO (newIORef 0)

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef freshMeta 0

inst :: Meta -> Maybe Val
inst m = unsafeDupablePerformIO (IM.lookup m <$> readIORef mcxt)


-- Evaluation (modulo global metacontext)
--------------------------------------------------------------------------------

lookup :: String -> Name -> Sub a -> a
lookup msg x ((x', a):as) = if x == x' then a else lookup msg x as
lookup msg x _            = error msg

vapp :: Val -> Val -> Name -> Icit -> Val
vapp t ~u x i = case t of
  VLam _ _ t -> t u
  h :$ sp    -> h :$ ((x, (u, i)) : sp)
  _          -> error "vapp: impossible"

eval :: Vals -> Tm -> Val
eval vs = \case
  Var x         -> maybe (VVar x :$ []) refresh (lookup "eval: impossible" x vs)
  Let x t a u   -> eval ((x, Just (eval vs t)):vs) u
  App t u x i   -> vapp (eval vs t) (eval vs u) x i
  Lam x i t     -> VLam x i $ \a -> eval ((x, Just a):vs) t
  Pi x i a b    -> VPi x i (eval vs a) $ \a -> eval ((x, Just a):vs) b
  Gen g         -> VGen g :$ []
  U             -> VU
  Meta i        -> maybe (VMeta i :$ []) refresh (inst i)

refresh :: Val -> Val
refresh = \case
  VMeta i :$ sp
    | Just t <- inst i ->
      refresh (foldr (\(x, (u, i)) t -> vapp t u x i) t sp)
  t -> t

quote :: Val -> Tm
quote = go where
  goHead = \case
    VMeta m -> Meta m
    VVar x  -> Var x
    VGen g  -> Gen g
  go t = case refresh t of
    h :$ sp     -> foldr (\(x, (a, i)) t -> App t (go a) x i) (goHead h) sp
    VLam x i t  -> Lam x i (go (t (VVar x :$ [])))
    VPi x i a b -> Pi x i (go a) (go (b (VVar x :$ [])))
    VU          -> U

-- Unification
--------------------------------------------------------------------------------

lams :: Spine -> Tm -> Tm
lams sp t = foldl' (\t (x, (u, i)) -> Lam x i t) t sp

invert :: Spine -> Ren
invert = foldl' go HM.empty where
  go r (x, (a, _)) =
    let var = case a of
          VVar x' :$ [] -> Left x'
          VGen i  :$ [] -> Right i
          _             -> error "Meta substitution is not a renaming"
    in HM.alter (maybe (Just x) (\_ -> Nothing)) var r

rename :: Meta -> Ren -> Tm -> Tm
rename occur = go where
  go r = \case
    Var x       -> maybe (error "scope error") Var (HM.lookup (Left x) r)
    Let x t a u -> Let x (go r t) (go r a) (go r u)
    App t u x i -> App (go r t) (go r u) x i
    Lam x i t   -> Lam x i (go (HM.insert (Left x) x r) t)
    Gen g       -> maybe (error "scope error") Var (HM.lookup (Right g) r)
    Pi x i a b  -> Pi x i (go r a) (go (HM.insert (Left x) x r) b)
    U           -> U
    Meta i | i == occur -> error "occurs check"
           | otherwise  -> Meta i

solve :: Meta -> Spine -> Val -> IO ()
solve m sp t = do
  let t' = lams sp (rename m (invert sp) (quote t))
  modifyIORef' mcxt $ IM.insert m (eval [] t')

gen :: Gen -> Val
gen g = VGen g :$ []

matchIcit :: Icit -> Icit -> IO ()
matchIcit i i' = if i == i'
  then pure ()
  else error "can't match explicit binder with implicit"

unify :: Val -> Val -> IO ()
unify t t' = go 0 t t' where

  go :: Gen -> Val -> Val -> IO ()
  go !g t t' = case (refresh t, refresh t') of
    (VU, VU) -> pure ()

    (VLam x i t, VLam x' i' t') -> go (g + 1) (t (gen g)) (t' (gen g))

    (VLam x i t, t')   -> go (g + 1) (t (gen g)) (vapp t' (gen g) x i)
    (t, VLam x' i' t') -> go (g + 1) (vapp t (gen g) x' i') (t' (gen g))

    (VPi x i a b, VPi x' i' a' b') -> do
      matchIcit i i'
      go g a a'
      go (g + 1) (b (gen g)) (b' (gen g))

    (VVar x  :$ sp, VVar x'  :$ sp') | x == x' -> goSpine g sp sp'
    (VGen i  :$ sp, VGen i'  :$ sp') | i == i' -> goSpine g sp sp'
    (VMeta m :$ sp, VMeta m' :$ sp') | m == m' -> goSpine g sp sp'
    (VMeta m :$ sp, t              ) -> solve m sp t
    (t,             VMeta m  :$ sp ) -> solve m sp t

    (t, t') ->
      error $ "can't unify\n" ++ show (quote t) ++ "\nwith\n" ++ show (quote t')

  goSpine :: Gen -> Spine -> Spine -> IO ()
  goSpine g sp sp' = case (sp, sp') of
    ((_, (a, _)):as, (_, (b, _)):bs)  -> goSpine g as bs >> go g a b
    ([]            , []            )  -> pure ()
    _                                 -> error "unify spine: impossible"


-- Elaboration
--------------------------------------------------------------------------------

hashNub :: (Eq a, Hashable a) => [a] -> [a]
hashNub = snd . foldr go (HS.empty, []) where
  go a (!seen, !as) | HS.member a seen = (seen, as)
  go a (seen, as) = (HS.insert a seen, a:as)

freeInRaw :: Name -> Raw -> Bool
freeInRaw x = \case
  RVar x'         -> x == x'
  RApp f a i      -> freeInRaw x f || freeInRaw x a
  RLam x' i t     -> if x == x' then False else freeInRaw x t
  RPi x' i a b    -> freeInRaw x a || if x == x' then False else freeInRaw x b
  RLet x' a t u   -> freeInRaw x a || freeInRaw x t ||
                     if x == x' then False else freeInRaw x u
  RNoMI t         -> freeInRaw x t
  RU              -> False
  RHole           -> False

newMeta :: Tys -> IO Tm
newMeta cxt = do
  m <- readIORef freshMeta
  writeIORef freshMeta (m + 1)
  let bvars = hashNub [x | (x, Left{}) <- cxt]
  pure $ foldr (\x t -> App t (Var x) x Expl) (Meta m) bvars

-- | Expects up-to-date Ty.
check :: Tys -> Vals -> Raw -> Ty -> IO Tm
check tys vs t want = case (t, want) of
  (RLam x i t, VPi x' i' a b) | either (==x') (==i') i ->
    Lam x i' <$> check ((x, Left a): tys) ((x, Nothing):vs) t (b (VVar x :$ []))

  (t, VPi x Impl a b) -> do
    let x' = if freeInRaw x t then x ++ show (length tys) else x
    t <- check ((x', Left a): tys) ((x', Nothing):vs) t (b (VVar x' :$ []))
    pure $ Lam x' Impl t

  (RLet x a' t' u', _) -> do
    a' <- check tys vs a' VU
    let ~va' = eval vs a'
    t' <- check tys vs t' va'
    let ~vt' = eval vs t'
    u' <- check ((x, Right va'): tys) ((x, Just vt'):vs) u' want
    pure (Let x t' a' u')

  (RHole, _) ->
    newMeta tys

  (t, _) -> do
    (t, has) <- infer MIYes tys vs t
    t <$ unify has want

-- | Expects up-to-date Ty
insertMetas :: MetaInsertion -> Tys -> Vals -> IO (Tm, Ty) -> IO (Tm, Ty)
insertMetas ins tys vs inp = case ins of
  MINo  -> inp
  MIYes -> uncurry go =<< inp where
    go t (VPi x Impl a b) = do
      m <- newMeta tys
      go (App t m x Impl) (b (eval vs m))
    go t a = pure (t, a)
  MIUntilName x -> uncurry go =<< inp where
    go t (VPi x' Impl a b)
      | x == x'   = pure (t, VPi x' Impl a b)
      | otherwise = do
          m <- newMeta tys
          go (App t m x Impl) (b (eval vs m))
    go t a = error "Expected named implicit argument"

-- | Returns up-to-date Ty
infer :: MetaInsertion -> Tys -> Vals -> Raw -> IO (Tm, Ty)
infer ins tys vs = \case
  RU      -> pure (U, VU)
  RNoMI t -> infer MINo tys vs t
  RVar x  -> insertMetas ins tys vs $ do
    let a = either id id $ lookup "variable not in scope" x tys
    pure (Var x, a)

  RApp t u i -> insertMetas ins tys vs $ do
    (t, a) <- infer
        (case i of Left x     -> MIUntilName x;
                   Right Impl -> MINo;
                   Right Expl -> MIYes)
        tys vs t
    case a of
      VPi x i' a b -> do
        traverse (matchIcit i') i
        u <- check tys vs u a
        pure (App t u x i', b (eval vs u))
      _ -> error "Expected a function in application"

  RPi x i a b -> do
    a <- check tys vs a VU
    b <- check ((x, Left (eval vs a)):tys) ((x, Nothing):vs) b VU
    pure (Pi x i a b, VU)

  RLet x a t u -> do
    a <- check tys vs a VU
    let ~va = eval vs a
    t <- check tys vs t va
    let ~vt = eval vs t
    (u, tu) <- infer ins ((x, Right va): tys) ((x, Just vt):vs) u
    pure (Let x t a u, tu)

  RLam x i t -> insertMetas ins tys vs $ do
    i <- case i of
      Left  x -> error "Can't use named argument for lambda expression with inferred type"
      Right i -> pure i
    a <- eval vs <$> newMeta tys
    let xa = "x" ++ show (length tys)
    b <- newMeta ((xa, Left a):tys)
    let ty = VPi xa i a (\v -> eval ((xa, Just v):vs) b)
    t <- check tys vs (RLam x (Right i) t) ty
    pure (t, ty)

  RHole -> do
    m1 <- newMeta tys
    m2 <- newMeta tys
    pure (m1, eval vs m2)


-- Replace metas by their solutions in normal forms.
--------------------------------------------------------------------------------

tmSpine :: Tm -> (Tm, Sub (Tm, Icit))
tmSpine = \case
  App f a x i -> ((x, (a, i)):) <$> tmSpine f
  t           -> (t, [])

zonkSp :: Vals -> Val -> Sub (Tm, Icit) -> Tm
zonkSp vs v sp = either id quote $
  foldr
    (\(x, (a, i)) -> either
      (\t -> Left (App t a x i))
      (\case VLam _ _ t -> Right (t (eval vs a))
             v          -> Left (App (quote v) a x i)))
    (Right v) sp

zonk :: Vals -> Tm -> Tm
zonk vs = \case
  Var x        -> Var x
  Meta m       -> maybe (Meta m) quote (inst m)
  U            -> U
  Pi x i a b   -> Pi x i (zonk vs a) (zonk ((x, Nothing):vs) b)
  App f a x i  -> let (h, sp) = tmSpine (App f a x i)
                  in case h of
                       Meta m | Just v <- inst m ->
                         zonkSp vs v sp
                       _ -> foldr (\(x, (t, i)) f -> App f (zonk vs t) x i) h sp
  Lam x i t    -> Lam x i (zonk ((x, Nothing): vs) t)
  Let x e t e' -> Let x (zonk vs e) (zonk vs t) (zonk ((x, Just (eval vs e)) : vs) e')
  Gen _        -> error "Impossible Gen"


--------------------------------------------------------------------------------

parseRaw :: String -> Raw
parseRaw s = case parse pRaw' "" s of
  Left e  -> error (show e)
  Right t -> t

infer0 :: String -> IO Tm
infer0 t = quote . snd <$> (reset *> infer MINo [] [] (parseRaw t))

elab0 :: String -> IO Tm
elab0 t = fst <$> (reset *> infer MINo [] [] (parseRaw t))

zonk0 :: String -> IO Tm
zonk0 t = zonk [] . fst <$> (reset *> infer MINo [] [] (parseRaw t))

nf0 :: String -> IO Tm
nf0 t = quote . eval [] . fst <$> (reset *> infer MINo [] [] (parseRaw t))


-- Printing
--------------------------------------------------------------------------------

freeIn :: Name -> Tm -> Bool
freeIn x = \case
  Var x'         -> x == x'
  App f a _ i    -> freeIn x f || freeIn x a
  Lam x' i t     -> if x == x' then False else freeIn x t
  Pi x' i a b    -> freeIn x a || if x == x' then False else freeIn x b
  Let x' t ty t' -> freeIn x t || freeIn x ty || if x == x' then False else freeIn x t'
  Gen _          -> error "Impossible Gen"
  Meta _         -> False
  U              -> False

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  lams :: (Name, Icit) -> Tm -> ([(Name, Icit)], Tm)
  lams xi t = go [xi] t where
    go xs (Lam x i t) = go ((x,i):xs) t
    go xs t           = (xs, t)

  bracket :: ShowS -> ShowS
  bracket s = ('{':).s.('}':)

  icit :: Icit -> a -> a -> a
  icit Impl i e = i
  icit Expl i e = e

  -- Note: printing is kinda slow (make tmSpine return in reverse, optimize App case)
  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x -> (x++)
    t@App{} -> let (h, sp) = tmSpine t
      in showParen p $
         unwords' $
         go True h :
         reverse (map (\(_, (t, i)) -> icit i (bracket (go False t)) (go True t)) sp)

    Lam x i t -> case lams (x, i) t of
      (xis, t) -> showParen p (("\\"++) . params . (". "++) . go False t)
        where params = unwords' $ reverse $ map (\(x, i) -> icit i bracket id (x++)) xis

    Pi x i a b -> showParen p (arg . (" -> "++) . go False b)
      where
        arg = if freeIn x b
                then (icit i bracket (showParen True)) ((x++) . (" : "++) . go False a)
                else go True a

    Let x t ty t' ->
      (x++) . (" : "++) . go False ty . ("\n"++) .
      (x++) . (" = "++) . go False t  . ("\n\n"++) .
      go False t'
    U      -> ('*':)
    Meta m -> (("?"++).(show m++))
    Gen _  -> error "Impossible Gen"

instance IsString Tm where fromString = Var
instance Show Tm where showsPrec = prettyTm
deriving instance Show Raw
instance IsString Raw where fromString = RVar

-------------------------------------------------------------------------------

test = "\
  let Nat : *\
      = (n : *) -> (n -> n) -> n -> n in\
  \
  let zero : Nat\
      = \\n s z. z in\
  \
  let suc : Nat -> Nat\
      = \\a n s z. s (a n s z) in\
  \
  let const : {a b} -> a -> b -> a\
      = \\x y. x in\
  \
  let five : Nat\
      = suc (suc (suc (suc (suc zero)))) in\
  \
  let Vec : Nat -> * -> *\
      = \\n A.\
        (P     : Nat -> *)\
        (pnil  : P zero)\
        (pcons : {n} -> A -> P n -> P (suc n))\
        -> P n in\
  \
  let nil : {A} -> Vec zero A\
      = \\P n c. n in\
  \
  let cons : {A n} -> A -> Vec n A -> Vec (suc n) A\
      = \\a as P n c. c a (as P n c) in\
  \
  let add : Nat -> Nat -> Nat\
      = \\a b n s z. a n s (b n s z) in\
  \
  let append : {A n m} -> Vec n A -> Vec m A -> Vec (add n m) A\
      = \\{A}{n}{m} as1 as2.\
          as1 (\\n. Vec (add n m) A) as2 _ in\
  nil"
