{-# options_ghc -fwarn-incomplete-patterns #-}

{-|
Minimal bidirectional dependent type checker with type-in-type. Based on Coquand's
algorithm.
-}

module Typecheck.Main (main, main') where

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

-- syntax
--------------------------------------------------------------------------------

type Name = String
type Ty   = Tm
type Raw  = Tm

data Tm
  = Var Name           -- x
  | Lam Name Tm        -- \x. t
  | App Tm Tm          -- t u
  | U                  -- U
  | Pi Name Ty Ty      -- (x : A) -> B
  | Let Name Ty Tm Tm  -- let x : A = t in u

-- type checking
--------------------------------------------------------------------------------

data Val
  = VVar Name
  | VApp Val Val
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

type Env = [(Name, Maybe Val)]

fresh :: Env -> Name -> Name
fresh env "_" = "_"
fresh env x   = case lookup x env of
  Just _  -> fresh env (x ++ "'")
  Nothing -> x

eval :: Env -> Tm -> Val
eval env = \case
  Var x       -> maybe (VVar x) id (fromJust $ lookup x env)
  App t u     -> case (eval env t, eval env u) of
                   (VLam _ t, u) -> t u
                   (t       , u) -> VApp t u
  Lam x t     -> VLam x (\u -> eval ((x, Just u):env) t)
  Pi x a b    -> VPi x (eval env a) (\u -> eval ((x, Just u):env) b)
  Let x _ t u -> eval ((x, Just (eval env t)):env) u
  U           -> VU

quote :: Env -> Val -> Tm
quote env = \case
  VVar x   -> Var x
  VApp t u -> App (quote env t) (quote env u)
  VLam (fresh env -> x) t -> Lam x (quote ((x, Nothing):env) (t (VVar x)))
  VPi  (fresh env -> x) a b ->
    Pi x (quote env a) (quote ((x, Nothing):env) (b (VVar x)))
  VU -> U

nf :: Env -> Tm -> Tm
nf env = quote env . eval env

nf0 :: Tm -> Tm
nf0 = nf []

-- | Beta-eta conversion checking
conv :: Env -> Val -> Val -> Bool
conv env t u = case (t, u) of
  (VU, VU) -> True

  (VPi (fresh env -> gx) a b, VPi x' a' b') ->
    conv env a a' && conv ((gx, Nothing):env) (b (VVar gx)) (b' (VVar gx))

  (VLam (fresh env -> gx) t, VLam x' t') ->
    conv ((gx, Nothing):env) (t (VVar gx)) (t' (VVar gx))

  -- checking eta conversion for Lam
  (VLam (fresh env -> gx) t, u) ->
    conv ((gx, Nothing):env) (t (VVar gx)) (VApp u (VVar gx))
  (u, VLam (fresh env -> gx) t) ->
    conv ((gx, Nothing):env) (VApp u (VVar gx)) (t (VVar gx))

  (VVar x  , VVar x'   ) -> x == x'
  (VApp t u, VApp t' u') -> conv env t t' && conv env u u'

  _ -> False

type VTy = Val
type Cxt = [(Name, VTy)]
type M   = Either String

check :: Env -> Cxt -> Raw -> VTy -> M ()
check env cxt t a = case (t, a) of
  (Lam x t, VPi (fresh env -> x') a b) ->
    check ((x, Just (VVar x')):env) ((x, a):cxt) t (b (VVar x'))

  (Let x a' t' u, _) -> do
    check env cxt a' VU
    let a'' = eval env a'
    check env cxt t' a''
    check ((x, Just (eval env t')):env) ((x, a''):cxt) u a

  _ -> do
    tty <- infer env cxt t
    unless (conv env tty a) $
      Left ("type mismatch:\nexpected:\n" ++ show (quote env a) ++
            "\ninferred:\n" ++ show (quote env tty))

infer :: Env -> Cxt -> Raw -> M VTy
infer env cxt = \case
  Var "_" -> Left "_ is not a valid name"
  Var x   -> maybe (Left ("name not in scope: " ++ x)) Right (lookup x cxt)
  U       -> pure VU

  App t u -> do
    tty <- infer env cxt t
    case tty of
      VPi _ a b -> do
        check env cxt u a
        pure (b (eval env u))
      _ -> Left "expected a function type"

  Lam{} -> Left "can't infer type for lambda"

  Pi x a b -> do
    check env cxt a VU
    check ((x, Nothing):env) ((x, eval env a):cxt) b VU
    pure VU

  Let x a t u -> do
    check env cxt a VU
    let a' = eval env a
    check env cxt t a'
    infer ((x, Just (eval env t)):env) ((x, a'):cxt) u



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- printing
--------------------------------------------------------------------------------

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where
  goArg t      = go True t
  goPiBind x a = showParen True ((x++) . (" : "++) . go False a)
  goLamBind x  = (x++)

  goLam (Lam x t) = (' ':) . goLamBind x . goLam t
  goLam t         = (". "++) . go False t

  goPi :: Bool -> Tm -> ShowS
  goPi p (Pi x a b)
    | x /= "_" = goPiBind x a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; _ -> True) a .
       (" → "++) . go False b
  goPi p t = (if p then (" -> "++) else id) . go False t

  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x -> (x++)
    App (App t u) u' ->
      showParen p (go False t . (' ':) . goArg u . (' ':) . goArg u')

    App t u  -> showParen p (go True t . (' ':) . goArg u)
    Lam x t  -> showParen p (("λ "++) . goLamBind x . goLam t)
    Pi x a b -> showParen p (goPi False (Pi x a b))

    Let x a t u ->
      ("let "++) . (x++) . (" : "++) . go False a . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False  u
    U -> ('U':)

instance Show Tm where showsPrec = prettyTm


-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'
pArrow     = symbol "→" <|> symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pAtom  = (Var <$> pIdent) <|> parens pTm <|> (U <$ symbol "U")
pSpine = foldl1 App <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pIdent
  char '.'
  t <- pTm
  pure (foldr Lam t xs)

pPi = do
  dom <- some (parens ((,) <$> some pIdent <*> (char ':' *> pTm)))
  pArrow
  cod <- pTm
  pure $ foldr (\(xs, a) t -> foldr (\x -> Pi x a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> Pi "_" sp <$> pTm

pLet = do
  symbol "let"
  x <- pIdent
  symbol ":"
  a <- pTm
  symbol "="
  t <- pTm
  symbol "in"
  u <- pTm
  pure $ Let x a t u

pTm  = pLam <|> pLet <|> try pPi <|> funOrSpine
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


-- main
--------------------------------------------------------------------------------

helpMsg = unlines [
  "usage: typecheck [--help|nf|type]",
  "  --help : display this message",
  "  nf     : read & typecheck expression from stdin, print its normal form",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO Tm -> IO ()
mainWith getOpt getTm = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      t <- getTm
      case infer [] [] t of
        Left err -> putStrLn err
        Right a  -> do
          print $ nf0 t
          putStrLn "  :"
          print $ quote [] a
    ["type"] -> do
      t <- getTm
      either putStrLn (print . quote []) $ infer [] [] t
    _          -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) (parseString src)
