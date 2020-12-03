{-# language Strict, LambdaCase, ViewPatterns #-}

module Main where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Maybe
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L


-- examples
--------------------------------------------------------------------------------

ex1, ex2, ex3 :: IO ()
ex1 = main' "nf" "\\x.x"
ex2 = main' "nf" "(\\x.x) (\\x.x)"

-- Church-coded natural numbers, printing normal form of 1000
ex3 = main' "nf" $ unlines [
  "let five = \\s z. s (s (s (s (s z)))) in",
  "let add = \\a b s z. a s (b s z) in",
  "let mul = \\a b s z. a (b s) z in",
  "let ten = add five five in",
  "let hundred = mul ten ten in",
  "let thousand = mul ten hundred in",
  "thousand"
  ]

-- pre-define values, values can be optimized by GHC

vid :: Val
vid = VLam "x" $ \x -> x

-- compiled by GHC to code
vApplyTwice :: Val
vApplyTwice = VLam "f" $ \f -> VLam "x" $ \x -> f $$ (f $$ x)

-- data Closure = HOAS (Val -> Val) | FirstOrder Env Tm

-- Look at all 3 versions (HOAS + names, closure + names, deBruijn + closure)
--   (rewrite it from from memory (40 lines))
--    ( what is this enough for? many kinds of type theories (not for cubical) )
-- Next: bidirectional checking (involves conversion checking)

-- syntax
--------------------------------------------------------------------------------

type Name = String

data Tm
  = Var Name           -- x
  | Lam Name Tm        -- \x. t
  | App Tm Tm          -- t u
  | Let Name Tm Tm     -- let x = t in u


-- evaluation
--------------------------------------------------------------------------------

data Val
  = VVar Name
  | VApp Val ~Val
  | VLam Name (Val -> Val)

type Env = [(Name, Val)]

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x   = case elem x ns of
  True  -> fresh ns (x ++ "'")
  False -> x

infixl 2 $$
($$) :: Val -> Val -> Val
($$) (VLam _ t) ~u = t u
($$) t          ~u = VApp t u

eval :: Env -> Tm -> Val
eval env = \case
  Var x     -> fromJust $ lookup x env
  App t u   -> eval env t $$ eval env u
  Lam x t   -> VLam x (\u -> eval ((x, u):env) t)
  Let x t u -> eval ((x, eval env t):env) u

quote :: [Name] -> Val -> Tm
quote ns = \case
  VVar x                 -> Var x
  VApp t u               -> App (quote ns t) (quote ns u)
  VLam (fresh ns -> x) t -> Lam x (quote (x:ns) (t (VVar x)))

nf :: Env -> Tm -> Tm
nf env = quote (map fst env) . eval env

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------



-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'

keyword :: String -> Bool
keyword x = x == "λ" || x == "in" || x == "let"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pBind  = pIdent <|> symbol "_"
pAtom  = (Var <$> pIdent) <|> parens pTm
pSpine = foldl1 App <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBind
  char '.'
  t <- pTm
  pure (foldr Lam t xs)

pLet = do
  pKeyword "let"
  x <- pBind
  symbol "="
  t <- pTm
  pKeyword "in"
  u <- pTm
  pure $ Let x t u

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
  goArg t      = go True t
  goLamBind x  = (x++)

  goLam (Lam x t) = (' ':) . goLamBind x . goLam t
  goLam t         = (". "++) . go False t

  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x -> (x++)
    App (App t u) u' ->
      showParen p (go False t . (' ':) . goArg u . (' ':) . goArg u')
    App t u  -> showParen p (go True t . (' ':) . goArg u)
    Lam x t  -> showParen p (("λ "++) . goLamBind x . goLam t)
    Let x t u ->
      ("let "++) . (x++) . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False  u

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
    ["nf"]     -> print . nf []  =<< getTm
    _          -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) (parseString src)
