{-# OPTIONS_GHC -Wno-type-defaults -Wno-unused-imports #-}

module Main where

import Prelude hiding (lookup)
import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

-- import Debug.Trace

{-

Minimal bidirectional checking with coercive cumulative subtyping and explicit lifting.

I tried to eliminate as much as possible usage/storage of levels. Only U is
annotated with levels, and check/infer does not expect or return levels
either. As a result, conversion checking is a bit weirdly heterogeneous, as it's
possible to have U i and U i' types of sides with i /= i'. It seems correct though.

Although we use less levels, I don't think the core syntax is any smaller, because of
the explicit lifts.

Features:

- U i : U (i + 1)

- if (Γ ⊢ A : U i) and (Γ, x : A ⊢ B : U i) then Γ ⊢ (x : A) → B : U i
    (homogeneous levels in function type)

- if a : U i, then ^a : U (i + 1)
- if t : a,   then <t> : ^a
- if t : ^a,  then [t] : a

- ^((x : A) -> B x) = (x : ^A) -> ^(B [x])
- <[t]>             = t
- [<t>]             = t
- <λ x. t>          = λ x. <t[x]>
- [λ x. t]          = λ x. [t<x>]
- <t u>             = <t> <u>
- [<t> u]           = t [u]

Coercive cumulative subtyping:

  - whenever A ≤ B and t : A, then coe A B t : B
  - coe is not an internal function, it's used during elaboration
  - U i ≤ U j  if  i ≤ j
  - ((x : A) → B x) ≤ ((x : A') → B' x) if A' ≤ A and ∀ x. B (coe A' A x) ≤ B x
  - A ≤ ^A
  - ^A ≤ A

Non-dependent Pi inference:
  For (_ : A) → B, we independently infer levels for A and B, and
  If one level is smaller, we raise A/B to the higher level.
  This (partially) emulates the conventional maximum level rule.


-}

-- examples
--------------------------------------------------------------------------------


-- see also "elab-no-delift" option
ex0 = main' "elab" $ unlines [

  "let f : U 0 -> U 0 = \\A. A;",
  "let g : U 0 -> U 1 = f;",
  "let g : ^(U 0 -> U 0) = <f>;",
  "let g : ^(U 0 -> U 0) = f;",

  "let f : U 1 -> U 1 = \\A. A;",
  "let g : U 0 -> U 2 = f;",

  "let f : (A : U 0) -> A -> A = \\A x. x;",
  "let g : ^((A : U 0) -> A -> A) = f;",
  "let g : (A : ^(U 0)) -> ^(^[A]) -> ^(^[A]) = f;",

  "let IdTy1    : U 2 = (A : U 1) -> A -> A;",
  "let ConstTy0 : U 1 = (A B : U 0) -> A -> B -> A;",
  "let id1 : IdTy1 = \\A x. x;",
  "let const0 : ConstTy0 = \\A B x y. x;",

  "let foo : ^ConstTy0 = id1 ConstTy0 const0;",
  "let foo : ^ConstTy0 = id1 ConstTy0 <const0>;",
  "let foo : ConstTy0 = id1 ConstTy0 const0;",

  "let Nat  : U 1 = (N : U 0) -> (N -> N) -> N -> N ;",
  "let zero : Nat = λ N s z. z;",
  "let one  : Nat = λ N s z. s z;",
  "let five : Nat = \\N s z. s (s (s (s (s z)))) ;",
  "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z) ;",
  "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z ;",
  "let ten      : Nat = add five five ;",
  "let hundred  : Nat = mul ten ten ;",

  "let Eq1 : (A : U 1) → A → A → U 1",
  "    = λ A x y. (P : A → U 0) → P x → P y;",

  "let refl1 : (A : U 1)(x : A) → Eq1 A x x",
  "  = λ A x P px. px;",

  "let p1 : Eq1 Nat ten ten = refl1 Nat ten;",

  "id1 Nat hundred"

  ]


-- syntax
--------------------------------------------------------------------------------

-- | De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int


type Name = String

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU Int                 -- U i
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLet Name Raw Raw Raw  -- let x : A = t in u
  | RLift Raw
  | RUp Raw
  | RDown Raw
  | RSrcPos SourcePos Raw  -- source position for error reporting
  deriving Show

-- core syntax
------------------------------------------------------------

type Ty = Tm

data Tm
  = Var Ix
  | Lam Name Tm
  | App Tm Tm
  | U Int
  | Lift Tm
  | Up Tm
  | Down Tm
  | Pi Name Ty Ty
  | Let Name Ty Int Tm Tm
  | Wk Tm                  -- explicit weakening

-- values
------------------------------------------------------------

type Env = [Val]
type VTy = Val

data Val
  = VVar Lvl
  | VApp Val ~Val
  | VLift Val
  | VUp Val
  | VDown Val
  | VLam Name (Val -> Val)
  | VPi Name ~VTy (Val -> Val)
  | VU Int

--------------------------------------------------------------------------------

vLift :: Val -> Val
vLift = \case
  VPi x a b -> VPi x (vLift a) (vLift . b . vDown)
  a         -> VLift a

vUp :: Val -> Val
vUp = \case
  VDown a  -> a
  VLam x t -> VLam x (vUp . t . vDown)
  VApp t u -> VApp (vUp t) (vUp u)
  a        -> VUp a

vDown :: Val -> Val
vDown = \case
  VUp a          -> a
  VLam x t       -> VLam x (vDown . t . vUp)
  VApp (VUp t) u -> VApp t (vDown u)
  a              -> VDown a

eval :: Env -> Tm -> Val
eval env = \case
  Var (Ix x)    -> env !! x
  App t u       -> case (eval env t, eval env u) of
                     (VLam _ t, u) -> t u
                     (t       , u) -> VApp t u
  Lam x t       -> VLam x \v -> eval (v:env) t
  Pi x a b      -> VPi x (eval env a) \v -> eval (v:env) b
  Let x _ _ t u -> eval (eval env t : env) u
  U i           -> VU i
  Lift a        -> vLift (eval env a)
  Up t          -> vUp (eval env t)
  Down t        -> vDown (eval env t)
  Wk t          -> eval (tail env) t


lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quote :: Lvl -> Val -> Tm
quote l = \case
  VVar x     -> Var (lvl2Ix l x)
  VApp t u   -> App (quote l t) (quote l u)
  VLam x t   -> Lam x (quote (l + 1) (t (VVar l)))
  VPi  x a b -> Pi x (quote l a) (quote (l + 1) (b (VVar l)))
  VU i       -> U i
  VLift a    -> Lift (quote l a)
  VUp t      -> Up (quote l t)
  VDown t    -> Down (quote l t)

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)

nf0 :: Tm -> Tm
nf0 = nf []

nTimes :: Int -> (a -> a) -> (a -> a)
nTimes n f ~a | n <= 0 = a
nTimes n f ~a = nTimes (n - 1) f (f a)

-- Note: If sides are types, their levels may differ! If sides are not types,
-- then the types of the sides must be the same.
conv :: Lvl -> Val -> Val -> Bool
conv l t u = case (t, u) of
  (VU i, VU i') -> i == i'
  (VPi _ a b, VPi _ a' b') ->
       conv l a a'
    && conv (l + 1) (b (VVar l)) (b' (VVar l))

  (VLam _ t, VLam _ t') ->
    conv (l + 1) (t (VVar l)) (t' (VVar l))
  (VLam _ t, u) ->
    conv (l + 1) (t (VVar l)) (VApp u (VVar l))
  (u, VLam _ t) ->
    conv (l + 1) (VApp u (VVar l)) (t (VVar l))

  (VLift a, VLift a')    -> conv l a a'
  (VUp t, VUp t')        -> conv l t t'
  (VDown t, VDown t')    -> conv l t t'
  (VVar x  , VVar x'   ) -> x == x'
  (VApp t u, VApp t' u') -> conv l t t' && conv l u u'
  _ -> False



coe :: Cxt -> Val -> Val -> Tm -> M Tm
coe cxt a b t = maybe t id <$> go cxt a b t where

  -- -- just a cheap optimization, computes less than "delift"
  -- up :: Tm -> Tm
  -- up (Down t) = t
  -- up t        = Up t

  -- down :: Tm -> Tm
  -- down (Up t) = t
  -- down t      = Down t
  up = Up
  down = Down

  -- the Maybe Tm result is used to avoid unnecessary eta-expansion of functions
  -- by coercion. We return a Nothing if it turns out that coercion has the
  -- identity action.
  go :: Cxt -> Val -> Val -> Tm -> M (Maybe Tm)
  go cxt a b t = case (a, b) of
    (VU i, VU i') -> case compare i i' of
      EQ -> pure Nothing
      LT -> pure $! Just $! nTimes (i' - i) Lift t
      GT -> report cxt $ printf "expected type %s, inferred type %s for %s"
                (showVal cxt (VU i')) (showVal cxt (VU i))
                (showTm cxt t)

    (VLift a, VLift a') ->
      (up <$>) <$> go cxt a a' (down t)

    (VPi x a b, VPi x' a' b') -> do

      let x'' = case (x, x') of
            ("_", "_") -> "x"
            ("_", x  ) -> x
            (x  , _  ) -> x

      let cxt' = bind x' a' cxt
          v0   = VVar (lvl cxt)

      go cxt' a' a (Var 0) >>= \case
        Nothing -> do
          go cxt' (b v0) (b' v0) (App (Wk t) (Var 0)) >>= \case
            Nothing   -> pure Nothing
            Just body -> pure $ Just $ Lam x'' body
        Just coev0 -> do
          go cxt' (b (eval (env cxt') coev0)) (b' v0) (App (Wk t) coev0) >>= \case
            Nothing   -> pure $ Just $ Lam x'' $ App (Wk t) coev0
            Just body -> pure $ Just $ Lam x'' $ body

    (VLift a, a') -> Just <$> coe cxt a a' (down t)
    (a, VLift a') -> Just . up <$> coe cxt a a' t

    (a, a') -> do
      unless (conv (lvl cxt) a a') $
        report cxt
          (printf
              "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
              (showVal cxt a) (showVal cxt a'))
      pure Nothing


-- Elaboration
--------------------------------------------------------------------------------

-- type of every variable in scope
type Types = [(Name, VTy)]

-- | Elaboration context.
data Cxt = Cxt {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}
   -- "unzipped" Cxt definition, for performance reason (also for convenience)

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] [] 0

-- | Extend Cxt with a bound variable.
bind :: Name -> VTy -> Cxt -> Cxt
bind x ~a (Cxt env types l pos) =
  Cxt (VVar l:env) ((x, a):types) (l + 1) pos

-- | Extend Cxt with a definition.
define :: Name -> Val -> VTy -> Cxt -> Cxt
define x ~t ~a (Cxt env types l pos) =
  Cxt (t:env) ((x, a):types) (l + 1) pos

-- | Typechecking monad. We annotate the error with the current source position.
type M = Either (String, SourcePos)

report :: Cxt -> String -> M a
report cxt msg = Left (msg, pos cxt)

deriving instance Show Tm

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (map fst (types cxt)) t []
-- showTm cxt t = show t

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

showVal :: Cxt -> Val -> String
showVal cxt v = showTm cxt $ quote (lvl cxt) v

--------------------------------------------------------------------------------

inferU :: Cxt -> Raw -> M (Tm, Int)
inferU cxt t = do
  (t, a) <- infer cxt t
  case a of
    VU n -> pure (t, n)
    _    -> report cxt "expected a type"

checkU :: Cxt -> Raw -> Int -> M Tm
checkU cxt t i = check cxt t (VU i)

check :: Cxt -> Raw -> VTy -> M Tm
check cxt t a = case (t, a) of
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a

  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a cxt) t (b (VVar (lvl cxt)))

  (RPi x a b, VU i) -> do
    a <- checkU cxt a i
    b <- checkU (bind x (eval (env cxt) a) cxt) b i
    pure $ Pi x a b

  (RLift t, VU i) | i > 0 -> do
    Lift <$> checkU cxt t (i - 1)

  (RUp t, VLift a) -> do
    Up <$> check cxt t a

  (RLet x a t u, a') -> do
    (a, i) <- inferU cxt a
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    u <- check (define x vt va cxt) u a'
    pure (Let x a i t u)

  _ -> do
    (t, tty) <- infer cxt t
    coe cxt tty a t

infer :: Cxt -> Raw -> M (Tm, VTy)
infer cxt = \case
  RSrcPos pos t -> infer (cxt {pos = pos}) t

  RVar x -> do
    let go i [] = report cxt ("variable out of scope: " ++ x)
        go i ((x', a):tys)
          | x == x'   = pure (Var i, a)
          | otherwise = go (i + 1) tys
    go 0 (types cxt)

  RU i -> pure (U i, VU (i + 1))

  RApp t u -> do
    (t, tty) <- infer cxt t
    case tty of
      VPi _ a b -> do
        u <- check cxt u a
        pure (App t u, b (eval (env cxt) u))
      tty ->
        report cxt $ "Expected a function type, instead inferred:\n\n  " ++ showVal cxt tty

  RLam{} -> report cxt "Can't infer type for lambda expression"

  -- Trick for non-dependent functions: we lift the lower type to match the higher.
  RPi "_" a b -> do
    (a, i) <- inferU cxt a
    (b, j) <- inferU (bind "_" undefined cxt) b
    case compare i j of
      EQ -> pure (Pi "_" a b, VU i)
      LT -> do
        a <- coe cxt (VU i) (VU j) a
        pure (Pi "_" a b, VU j)
      GT -> do
        b <- coe cxt (VU j) (VU i) b
        pure (Pi "_" a b, VU i)

  RPi x a b -> do
    (a, i) <- inferU cxt a
    b <- checkU (bind x (eval (env cxt) a) cxt) b i
    pure (Pi x a b, VU i)

  RLet x a t u -> do
    (a, i) <- inferU cxt a
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    (u, uty) <- infer (define x vt va cxt) u
    pure (Let x a i t u, uty)

  RLift a -> do
    (a, i) <- inferU cxt a
    pure (Lift a, VU (i + 1))

  RUp t -> do
    (t, a) <- infer cxt t
    pure (Up t, vLift a)

  RDown t -> do
    (t, a) <- infer cxt t
    case a of
      VLift a -> pure (Down t, a)
      _       -> report cxt "Can't infer type for lowering"


-- Computing only lifts and Wk-s (to improve elab output)
--------------------------------------------------------------------------------

type Env' = [Val']

data Val'
  = VVar' Lvl
  | VApp' Val' Val'
  | VLift' Val'
  | VUp' Val'
  | VDown' Val'
  | VLam' Name (Val' -> Val')
  | VPi' Name Val' (Val' -> Val')
  | VLet' Name Val' Int Val' (Val' -> Val')
  | VU' Int

vLift' :: Val' -> Val'
vLift' = \case
  VPi' x a b -> VPi' x (vLift' a) (vLift' . b . vDown')
  a          -> VLift' a

vUp' :: Val' -> Val'
vUp' = \case
  VDown' a  -> a
  VLam' x t -> VLam' x (vUp' . t . vDown')
  VApp' t u -> VApp' (vUp' t) (vUp' u)
  a         -> VUp' a

vDown' :: Val' -> Val'
vDown' = \case
  VUp' a           -> a
  VLam' x t        -> VLam' x (vDown' . t . vUp')
  VApp' (VUp' t) u -> VApp' t (vDown' u)
  a                -> VDown' a

eval' :: Env' -> Tm -> Val'
eval' env = \case
  Var (Ix x)    -> env !! x
  Lam x t       -> VLam' x \v -> eval' (v:env) t
  App t u       -> VApp' (eval' env t) (eval' env u)
  U i           -> VU' i
  Lift t        -> vLift' (eval' env t)
  Up t          -> vUp' (eval' env t)
  Down t        -> vDown' (eval' env t)
  Pi x a b      -> VPi' x (eval' env a) \v -> eval' (v:env) b
  Let x a i t u -> VLet' x (eval' env a) i (eval' env t) \v -> eval' (v:env) u
  Wk t          -> eval' (tail env) t

quote' :: Lvl -> Val' -> Tm
quote' l = \case
  VVar' x         -> Var (lvl2Ix l x)
  VApp' t u       -> App (quote' l t) (quote' l u)
  VLam' x t       -> Lam x (quote' (l + 1) (t (VVar' l)))
  VPi'  x a b     -> Pi x (quote' l a) (quote' (l + 1) (b (VVar' l)))
  VU' i           -> U i
  VLift' a        -> Lift (quote' l a)
  VUp' t          -> Up (quote' l t)
  VDown' t        -> Down (quote' l t)
  VLet' x a i t u -> Let x (quote' l a) i (quote' l t) (quote' (l + 1) (u (VVar' l)))

delift :: Tm -> Tm
delift = quote' 0 . eval' []

-- printing
--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = go (1 :: Int) where
  go n | elem (x ++ show n) ns = go (n + 1)
       | otherwise             = x ++ show n
fresh ns x = x

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec where

  piBind ns x a =
    showParen True ((x++) . (" : "++) . go letp ns a)

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var (Ix x) ->
      case ns !! x of
        "_"   -> ("@"++).(show x++)
        n     -> (n++)

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    Lam (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
                                   goLam ns (Lam (fresh ns -> x) t) =
                                     (' ':) . (x++) . goLam (x:ns) t
                                   goLam ns t =
                                     (". "++) . go letp ns t

    U i                       -> par p appp $ ("U "++).(show i++)

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip ("_":ns) b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (x:ns) b where
                                   goPi ns (Pi "_" a b) = (" → "++) . go appp ns a
                                                          . (" → "++) . go pip ("_":ns) b
                                   goPi ns (Pi x a b)   = piBind ns x a . goPi (x:ns) b
                                   goPi ns b            = (" → "++) . go pip ns b

    Let (fresh ns -> x) a _ t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
      . ("\n    = "++) . go letp ns t . ("\n;\n"++) . go letp (x:ns) u

    Lift a -> par p appp $ ("^"++) . go atomp ns a
    Up t   -> ('<':).go letp ns t.('>':)
    Down t -> ('[':).go letp ns t.(']':)

    -- Wk t -> go p (tail ns) t
    Wk t   -> ("wk("++).go p (tail ns) t.(")"++)

-- instance Show Tm where showsPrec p = prettyTm p []

-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
pArrow   = symbol "→" <|> symbol "->"
decimal  = lexeme L.decimal

keyword :: String -> Bool
keyword x = x == "let" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Raw
pAtom =
      withPos (
          (RVar <$> pIdent)
      <|> (RU <$> (pKeyword "U" *> decimal)))
      <|> (char '[' *> (RDown <$> pRaw) <* char ']')
      <|> (char '<' *> (RUp <$> pRaw) <* char '>')
  <|> parens pRaw

pBinder = pIdent <|> symbol "_"


pSpine  =
      (RLift <$> (char '^' *> pAtom))
  <|> foldl1 RApp <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RLam t xs)

pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" sp <$> pRaw

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol "="
  t <- pRaw
  char ';'
  u <- pRaw
  pure $ RLet x a t u

pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)
pSrc = ws *> pRaw <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm   <- parseString file
  pure (tm, file)

-- main
--------------------------------------------------------------------------------

displayError :: String -> (String, SourcePos) -> IO ()
displayError file (msg, SourcePos path (unPos -> linum) (unPos -> colnum)) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg

helpMsg = unlines [
  "usage: elabzoo-univ-lifts [--help|nf|type]",
  "  --help         : display this message",
  "  nf             : read & elaborate expression from stdin, print its normal form and type",
  "  elab           : read & elaborate expression from stdin, print output",
  "  elab-no-delift : read & elaborate expression from stdin, print output",
  "                   without removing intermediate lifts and explicit weakenings",
  "  type           : read & elaborate expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err -> displayError file err
        Right (t, a) -> do
          putStrLn $ showTm0 $ nf0 t
          putStrLn "  :"
          putStrLn $ showTm0 $ quote 0 a
    ["elab"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> putStrLn $ showTm0 $ delift t
    ["elab-no-delift"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> putStrLn $ showTm0 $ t
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> putStrLn $ showTm0 $ quote 0 a
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
