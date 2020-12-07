
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

-- examples
--------------------------------------------------------------------------------

ex0 = main' "elab" $ unlines [

  "let f : U 1 -> U 1 = \\A. A;",
  "let g : U 0 -> U 2 = f;",
  "let f : (A : U 0) -> A -> A = \\A x. x;",

  "let IdTy1    : U 2 = (A : U 1) -> A -> A;",
  "let ConstTy0 : U 1 = (A B : U 0) -> A -> B -> A;",
  "let id1 : IdTy1 = \\A x. x;",
  "let const0 : ConstTy0 = \\A B x y. x;",
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
  | Pi Name Ty Ty
  | Let Name Ty Int Tm Tm
  deriving Show

-- values
------------------------------------------------------------

type Env = [Val]
type VTy = Val

data Val
  = VVar Lvl
  | VApp Val ~Val
  | VLam Name (Val -> Val)
  | VPi Name ~VTy (Val -> Val)
  | VU Int

--------------------------------------------------------------------------------

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

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quote :: Lvl -> Val -> Tm
quote l = \case
  VVar x     -> Var (lvl2Ix l x)
  VApp t u   -> App (quote l t) (quote l u)
  VLam x t   -> Lam x (quote (l + 1) (t (VVar l)))
  VPi  x a b -> Pi x (quote l a) (quote (l + 1) (b (VVar l)))
  VU i       -> U i

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)

nf0 :: Tm -> Tm
nf0 = nf []

-- Note: if sides are types, their levels may differ!
conv :: Lvl -> Val -> Val -> Bool
conv l t u = case (t, u) of
  (VU i      , VU i'       ) -> i == i'
  (VPi _ a b , VPi _ a' b' ) -> conv l a a' && conv (l + 1) (b (VVar l)) (b' (VVar l))
  (VLam _ t  , VLam _ t'   ) -> conv (l + 1) (t (VVar l)) (t' (VVar l))
  (VLam _ t  , u           ) -> conv (l + 1) (t (VVar l)) (VApp u (VVar l))
  (u         , VLam _ t    ) -> conv (l + 1) (VApp u (VVar l)) (t (VVar l))
  (VVar x    , VVar x'     ) -> x == x'
  (VApp t u  , VApp t' u'  ) -> conv l t t' && conv l u u'
  _                          -> False

subty :: Lvl -> Val -> Val -> Bool
subty l a a' = case (a, a') of
  (VU i      , VU j        ) -> i <= j
  (VPi _ a b , VPi _ a' b' ) -> subty l a' a && subty (l + 1) (b (VVar l)) (b' (VVar l))
  (a         , a'          ) -> conv l a a'

-- Elaboration
--------------------------------------------------------------------------------

type Types = [(Name, VTy)]

-- | Elaboration context.
data Cxt = Cxt {env :: Env, types :: Types, lvl :: Lvl, pos :: SourcePos}

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
    VU i -> pure (t, i)
    _    -> report cxt "expected a type"

checkU :: Cxt -> Raw -> Int -> M Tm
checkU cxt t i = check cxt t (VU i)

check :: Cxt -> Raw -> VTy -> M Tm
check cxt t a = case (t, a) of
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a

  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a cxt) t (b (VVar (lvl cxt)))

  (RLet x a t u, a') -> do
    (a, i) <- inferU cxt a
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    u <- check (define x vt va cxt) u a'
    pure (Let x a i t u)

  _ -> do
    (t, tty) <- infer cxt t
    unless (subty (lvl cxt) tty a) $
      report cxt
        (printf
            "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
            (showVal cxt tty) (showVal cxt a))
    pure t

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

  RPi x a b -> do
    (a, i) <- inferU cxt a
    (b, j) <- inferU (bind x (eval (env cxt) a) cxt) b
    pure (Pi x a b, VU (max i j))

  RLet x a t u -> do
    (a, i) <- inferU cxt a
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    (u, uty) <- infer (define x vt va cxt) u
    pure (Let x a i t u, uty)

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
  <|> parens pRaw

pBinder = pIdent <|> symbol "_"


pSpine  = foldl1 RApp <$> some pAtom

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
