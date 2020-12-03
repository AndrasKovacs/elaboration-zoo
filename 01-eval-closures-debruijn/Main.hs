
module Main where

import Prelude hiding (lookup, length)
import Control.Applicative hiding (many, some)
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Data.Char

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

-- | De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

data Tm
  = Var Ix
  | Lam Tm      -- lam (x.t)
  | App Tm Tm
  | Let Tm Tm   -- let t (x.u)

data Env
  = Nil
  | Define Env ~Val

data Closure
  = Closure Env Tm

data Val
  = VVar Lvl
  | VApp Val ~Val
  | VLam {-# unpack #-} Closure

--------------------------------------------------------------------------------

length :: Env -> Lvl
length = go 0 where
  go acc Nil            = acc
  go acc (Define env _) = go (acc + 1) env

lookup :: Env -> Ix -> Val
lookup (Define env v) 0 = v
lookup (Define env _) x = lookup env (x - 1)
lookup _              _ = error "index out of scope"

cApp :: Closure -> Val -> Val
cApp (Closure env t) ~u = eval (Define env u) t

eval :: Env -> Tm -> Val
eval env = \case
  Var x   -> lookup env x
  App t u -> case (eval env t, eval env u) of
               (VLam t, u) -> cApp t u
               (t     , u) -> VApp t u
  Lam t   -> VLam (Closure env t)
  Let t u -> eval (Define env (eval env t)) u

-- Normalization
--------------------------------------------------------------------------------

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quote :: Lvl -> Val -> Tm
quote l = \case
  VVar x   -> Var (lvl2Ix l x)
  VApp t u -> App (quote l t) (quote l u)
  VLam t   -> Lam (quote (l + 1) (cApp t (VVar l)))

nf :: Env -> Tm -> Tm
nf env t = quote (length env) (eval env t)

-- ("\\" works for lambda as well)
ex3 = main' "nf" $ unlines [
  "let λ λ 1 (1 (1 (1 (1 0)))) in",    -- five = λ s z. s (s (s (s (s z))))
  "let λ λ λ λ 3 1 (2 1 0) in",        -- add  = λ a b s z. a s (b s z)
  "let λ λ λ λ 3 (2 1) 0 in",          -- mul  = λ a b s z. a (b s) z
  "let 1 2 2 in",                      -- ten  = add five five
  "let 1 0 0 in",                      -- hundred = mul ten ten
  "let 2 1 0 in",                      -- thousand = mul ten hundred
  "0"                                  -- thousand
  ]

-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isDigit *> empty) <|> ws

pIx    = lexeme L.decimal
pAtom  = (Var <$> pIx) <|> parens pTm
pSpine = foldl1 App <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  Lam <$> pTm

pLet = do
  pKeyword "let"
  t <- pTm
  pKeyword "in"
  u <- pTm
  pure $ Let t u

pTm  = pLam <|> pLet <|> pSpine
pSrc = ws *> pTm <* eof

parseString :: String -> IO Tm
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO Tm
parseStdin = parseString =<< getContents

-- printing
--------------------------------------------------------------------------------

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where
  goArg = go True

  goLam (Lam t) = ("λ "++) . goLam t
  goLam t       = go False t

  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x            -> (show x++)
    App (App t u) u' -> showParen p (go False t . (' ':) . goArg u . (' ':) . goArg u')
    App t u          -> showParen p (go True t . (' ':) . goArg u)
    Lam t            -> showParen p (("λ "++) . goLam t)
    Let t u          -> ("let "++) . go False t . ("\nin\n"++) . go False u

instance Show Tm where showsPrec = prettyTm


-- main
--------------------------------------------------------------------------------

helpMsg = unlines [
  "usage: elabzoo-eval [--help|nf]",
  "  --help : display this message",
  "  nf     : read expression from stdin, print its normal form"]

mainWith :: IO [String] -> IO Tm -> IO ()
mainWith getOpt getTm = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]     -> print . nf Nil  =<< getTm
    _          -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) (parseString src)
