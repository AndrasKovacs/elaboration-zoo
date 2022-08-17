
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

ex0 = main' "nf" $ unlines [
  "let id : (A : U) -> A -> A",
  "     = \\A x. x;",
  "let foo : U = U;",
  "let bar : U = id id;",     -- we cannot apply any function to itself (already true in simple TT)
  "id"
  ]

-- basic polymorphic functions
ex1 = main' "nf" $ unlines [
  "let id : (A : U) -> A -> A",
  "      = \\A x. x;",
  "let const : (A B : U) -> A -> B -> A",
  "      = \\A B x y. x;",
  "id ((A B : U) -> A -> B -> A) const"
  ]

-- Church-coded natural numbers (standard test for finding eval bugs)
ex2 = main' "nf" $ unlines [
  "let Nat  : U = (N : U) -> (N -> N) -> N -> N;",
  "let five : Nat = \\N s z. s (s (s (s (s z))));",
  "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);",
  "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z;",
  "let ten      : Nat = add five five;",
  "let hundred  : Nat = mul ten ten;",
  "let thousand : Nat = mul ten hundred;",
  "thousand"
  ]

-- syntax
--------------------------------------------------------------------------------

-- Minimal bidirectional elaboration
--   surface syntax vs core syntax
--      (intermediate: raw syntax -->(scope checking) -->raw syntax with indices
--   (our case: difference: no de Bruijn indices in surface syntax, but they're in core syntax)

-- | De Bruijn index.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int


type Name = String

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU                     -- U
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLet Name Raw Raw Raw  -- let x : A = t; u
  | RSrcPos SourcePos Raw  -- source position for error reporting
  deriving Show

-- core syntax
------------------------------------------------------------

type Ty = Tm

data Tm
  = Var Ix
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm


-- values
------------------------------------------------------------

type Env = [Val]

data Closure = Closure Env Tm

type VTy = Val

data Val
  = VVar Lvl
  | VApp Val ~Val
  | VLam Name {-# unpack #-} Closure
  | VPi Name ~VTy {-# unpack #-} Closure
  | VU

--------------------------------------------------------------------------------

infixl 8 $$
($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (u:env) t

eval :: Env -> Tm -> Val
eval env = \case
  Var (Ix x)  -> env !! x
  App t u     -> case (eval env t, eval env u) of
                   (VLam _ t, u) -> t $$ u
                   (t       , u) -> VApp t u
  Lam x t     -> VLam x (Closure env t)
  Pi x a b    -> VPi x (eval env a) (Closure env b)
  Let x _ t u -> eval (eval env t : env) u
  U           -> VU

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quote :: Lvl -> Val -> Tm
quote l = \case
  VVar x     -> Var (lvl2Ix l x)
  VApp t u   -> App (quote l t) (quote l u)
  VLam x t   -> Lam x (quote (l + 1) (t $$ VVar l))
  VPi  x a b -> Pi x (quote l a) (quote (l + 1) (b $$ VVar l))
  VU         -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)

-- | Beta-eta conversion checking. Precondition: both values have the same type.
conv :: Lvl -> Val -> Val -> Bool
conv l t u = case (t, u) of
  (VU, VU) -> True

  (VPi _ a b, VPi _ a' b') ->
       conv l a a'
    && conv (l + 1) (b $$ VVar l) (b' $$ VVar l)

  (VLam _ t, VLam _ t') ->
    conv (l + 1) (t $$ VVar l) (t' $$ VVar l)

  (VLam _ t, u) ->
    conv (l + 1) (t $$ VVar l) (VApp u (VVar l))
  (u, VLam _ t) ->
    conv (l + 1) (VApp u (VVar l)) (t $$ VVar l)

  (VVar x  , VVar x'   ) -> x == x'
  (VApp t u, VApp t' u') -> conv l t t' && conv l u u'

  _ -> False


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

showVal :: Cxt -> Val -> String
showVal cxt v = prettyTm 0 (map fst (types cxt)) (quote (lvl cxt) v) []

-- bidirectional algorithm:
--   use check when the type is already known
--   use infer if the type is unknown
-- (original Hindley-Milner does not use bidirectionality)
-- (even if you don't strictly need bidir, it's faster and has better errors)

check :: Cxt -> Raw -> VTy -> M Tm
check cxt t a = case (t, a) of
  -- setting the source pos
  (RSrcPos pos t, a) -> check (cxt {pos = pos}) t a

  -- checking Lam with Pi type (canonical checking case)
  -- (\x. t) : ((x : A) -> B)
  (RLam x t, VPi x' a b) ->
    Lam x <$> check (bind x a cxt) t (b $$ VVar (lvl cxt))
              -- go under a binder as usual

  -- fall-through checking
  (RLet x a t u, a') -> do     -- let x : a = t in u
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va          -- (I need to check with a VTy)
    let ~vt = eval (env cxt) t
    u <- check (define x vt va cxt) u a'
    pure (Let x a t u)

  -- only Lam and Let is checkable
  -- if the term is not checkable, we switch to infer (change of direction)
  _ -> do
    (t, tty) <- infer cxt t
    unless (conv (lvl cxt) tty a) $
      report cxt
        (printf
            "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
            (showVal cxt a) (showVal cxt tty))
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

  RU -> pure (U, VU)   -- U : U rule

  RApp t u -> do
    (t, tty) <- infer cxt t
    case tty of
      VPi _ a b -> do
        u <- check cxt u a
        pure (App t u, b $$ eval (env cxt) u)   -- t u : B[x |-> u]
      tty ->
        report cxt $ "Expected a function type, instead inferred:\n\n  " ++ showVal cxt tty

  RLam{} -> report cxt "Can't infer type for lambda expression"

  RPi x a b -> do
    a <- check cxt a VU
    b <- check (bind x (eval (env cxt) a) cxt) b VU
    pure (Pi x a b, VU)

  RLet x a t u -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    (u, uty) <- infer (define x vt va cxt) u
    pure (Let x a t u, uty)


-- printing
--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = fresh ns (x ++ "'")
           | otherwise = x

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
    Var (Ix x)                -> ((ns !! x)++)

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    Lam (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
                                   goLam ns (Lam (fresh ns -> x) t) =
                                     (' ':) . (x++) . goLam (x:ns) t
                                   goLam ns t =
                                     (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip ("_":ns) b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (x:ns) b where
                                   goPi ns (Pi "_" a b) =
                                     (" → "++) . go appp ns a . (" → "++) . go pip ("_":ns) b
                                   goPi ns (Pi (fresh ns -> x) a b) =
                                     piBind ns x a . goPi (x:ns) b
                                   goPi ns b =
                                     (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n    = "++) . go letp ns t . ("\nin\n"++) . go letp (x:ns) u

instance Show Tm where showsPrec p = prettyTm p []

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

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U"

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
      withPos ((RVar <$> pIdent) <|> (RU <$ symbol "U"))
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
  symbol ";"
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
  "usage: elabzoo-typecheck-closures-debruijn [--help|nf|type]",
  "  --help : display this message",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err -> displayError file err
        Right (t, a) -> do
          print $ nf [] t
          putStrLn "  :"
          print $ quote 0 a
    ["type"] -> do
      (t, file) <- getRaw
      case infer (emptyCxt (initialPos file)) t of
        Left err     -> displayError file err
        Right (t, a) -> print $ quote 0 a
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
