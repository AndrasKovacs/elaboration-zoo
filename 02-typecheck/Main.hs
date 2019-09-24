{-# options_ghc -fwarn-incomplete-patterns #-}

module Main where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Maybe
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

-- examples
--------------------------------------------------------------------------------

ex0 = main' "nf" $ unlines [
  "let id : (A : U) -> A -> A",
  "     = \\A x. x in",
  "let foo : U = U in",
  "let bar : U = id id in",
  "id"
  ]

-- basic polymorphic functions
ex1 = main' "nf" $ unlines [
  "let id : (A : U) -> A -> A",
  "      = \\A x. x in",
  "let const : (A B : U) -> A -> B -> A",
  "      = \\A B x y. x in",
  "id ((A B : U) -> A -> B -> A) const"
  ]

-- Church-coded natural numbers
ex2 = main' "nf" $ unlines [
  "let Nat  : U = (N : U) -> (N -> N) -> N -> N in",
  "let five : Nat = \\N s z. s (s (s (s (s z)))) in",
  "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z) in",
  "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z in",
  "let ten      : Nat = add five five in",
  "let hundred  : Nat = mul ten ten in",
  "let thousand : Nat = mul ten hundred in",
  "thousand"
  ]

-- syntax
--------------------------------------------------------------------------------

type Name = String
type Ty   = Tm
type Raw  = Tm

data Tm
  = Var Name             -- x
  | Lam Name Tm          -- \x. t
  | App Tm Tm            -- t u
  | U                    -- U
  | Pi Name Ty Ty        -- (x : A) -> B
  | Let Name Ty Tm Tm    -- let x : A = t in u
  | SrcPos SourcePos Tm  -- source position for error reporting

-- type checking
--------------------------------------------------------------------------------

data Val
  = VVar Name
  | VApp Val ~Val
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
  SrcPos _ t  -> eval env t

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

-- | Typechecking monad. After we throw an error, we annotate it at the innermost
--   point in the syntax where source position information is available from
--   a 'SrcPos' 'Tm' constructor.
type M = Either (String, Maybe SourcePos)

report :: String -> M a
report str = Left (str, Nothing)

quoteShow :: Env -> Val -> String
quoteShow env = show . quote env

addPos :: SourcePos -> M a -> M a
addPos pos ma = case ma of
  Left (msg, Nothing) -> Left (msg, Just pos)
  x -> x

check :: Env -> Cxt -> Raw -> VTy -> M ()
check env cxt t a = case (t, a) of
  (SrcPos pos t, _) -> addPos pos (check env cxt t a)

  (Lam x t, VPi (fresh env -> x') a b) ->
    check ((x, Just (VVar x')):env) ((x, a):cxt) t (b (VVar x'))

  (Let x a' t' u, _) -> do
    check env cxt a' VU
    let ~a'' = eval env a'
    check env cxt t' a''
    check ((x, Just (eval env t')):env) ((x, a''):cxt) u a

  _ -> do
    tty <- infer env cxt t
    unless (conv env tty a) $
      report (printf
        "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
        (quoteShow env a) (quoteShow env tty))

infer :: Env -> Cxt -> Raw -> M VTy
infer env cxt = \case
  SrcPos pos t -> addPos pos (infer env cxt t)

  Var x -> case lookup x cxt of
             Nothing -> report $ "Name not in scope: " ++ x
             Just a  -> pure a

  U -> pure VU

  App t u -> do
    tty <- infer env cxt t
    case tty of
      VPi _ a b -> do
        check env cxt u a
        pure (b (eval env u))
      tty -> report $
        "Expected a function type, instead inferred:\n\n  "
        ++ quoteShow env tty

  Lam{} -> report "Can't infer type for lambda expresion"

  Pi x a b -> do
    check env cxt a VU
    check ((x, Nothing):env) ((x, eval env a):cxt) b VU
    pure VU

  Let x a t u -> do
    check env cxt a VU
    let ~a' = eval env a
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
    SrcPos _ t -> go p t

instance Show Tm where showsPrec = prettyTm


-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Tm -> Parser Tm
withPos p = SrcPos <$> getSourcePos <*> p

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
pArrow   = symbol "→" <|> symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pAtom =
      withPos ((Var <$> pIdent) <|> (U <$ symbol "U"))
  <|> parens pTm

pBinder = pIdent <|> symbol "_"
pSpine  = foldl1 App <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pTm
  pure (foldr Lam t xs)

pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pTm)))
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
  x <- pBinder
  symbol ":"
  a <- pTm
  symbol "="
  t <- pTm
  symbol "in"
  u <- pTm
  pure $ Let x a t u

pTm  = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)
pSrc = ws *> pTm <* eof

parseString :: String -> IO Tm
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (Tm, String)
parseStdin = do
  file <- getContents
  tm   <- parseString file
  pure (tm, file)

-- main
--------------------------------------------------------------------------------

displayError :: String -> (String, Maybe SourcePos) -> IO ()
displayError file (msg, Just (SourcePos path (unPos -> linum) (unPos -> colnum))) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg
displayError _ _ = error "displayError: impossible: no available source position"

helpMsg = unlines [
  "usage: elabzoo-typecheck [--help|nf|type]",
  "  --help : display this message",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Tm, String) -> IO ()
mainWith getOpt getTm = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, file) <- getTm
      case infer [] [] t of
        Left err -> displayError file err
        Right a  -> do
          print $ nf0 t
          putStrLn "  :"
          print $ quote [] a
    ["type"] -> do
      (t, file) <- getTm
      either (displayError file) (print . quote []) $ infer [] [] t
    _          -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
