
{-# options_ghc
  -Wall
  -Wno-name-shadowing
  -Wno-missing-signatures
  -Wno-unused-do-bind
  -Wno-unused-matches
 #-}

{-# language
    ImplicitParams
  , ConstraintKinds
  , RankNTypes
  , Strict
  , EmptyCase
  , BlockArguments
  , LambdaCase #-}

module Main where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Maybe
import Data.Void
import Data.Coerce
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

--------------------------------------------------------------------------------

newtype Hide a = Hide a

instance Show (Hide a) where
  showsPrec n x acc = acc

-- syntax
--------------------------------------------------------------------------------

type Name = String
type Ty   = Tm
type Raw  = Tm

data Tm
  = Var Name                   -- x
  | Lam Name Tm                -- \x. t
  | App Tm Tm                  -- t u
  | U                          -- U
  | Pi Name Ty Ty              -- (x : A) -> B
  | Let Name Ty Tm Tm          -- let x : A = t; u
  | SrcPos (Hide SourcePos) Tm -- source position for error reporting
  | Quote Tm                   -- <t>
  | Splice Tm                  -- ~t
  | Box Tm                     -- ◻ A

--------------------------------------------------------------------------------

data Val
  = VVar Name
  | VApp Val ~Val
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VQuote Val
  | VSplice Val
  | VBox Val
  | VU

type Env = [(Name, Val)]
type EnvArg = (?env :: Env)

extEnv :: Name -> Val -> (EnvArg => a) -> EnvArg => a
extEnv x ~v act = let ?env = (x, v): ?env in act

bindEnv :: Name -> (EnvArg => Val -> a) -> EnvArg => a
bindEnv (fresh -> x) act =
  let v = VVar x in let ?env = (x,v): ?env in act v

fresh :: EnvArg => Name -> Name
fresh "_" = "_"
fresh x   = case lookup x ?env of
  Just _  -> fresh (x ++ "'")
  _       -> x

splice :: Val -> Val
splice = \case
  VQuote t -> t
  t        -> VSplice t

eval :: EnvArg => Tm -> Val
eval = \case
  Var x       -> fromJust $ lookup x ?env
  App t u     -> case (eval t, eval u) of
                   (VLam _ t, u) -> t u
                   (t       , u) -> VApp t u
  Lam x t     -> VLam x (\u -> extEnv x u (eval t))
  Pi x a b    -> VPi x (eval a) (\u -> extEnv x u (eval b))
  Let x _ t u -> extEnv x (eval t) (eval u)
  U           -> VU
  SrcPos _ t  -> eval t
  Quote t     -> VQuote (eval t)
  Splice t    -> splice (eval t)
  Box t       -> VBox (eval t)

quote :: EnvArg => Val -> Tm
quote = \case
  VVar x     -> Var x
  VApp t u   -> App (quote t) (quote u)
  VLam x t   -> Lam x $ bindEnv x \x -> quote (t x)
  VPi  x a b -> Pi x (quote a) $ bindEnv x \x -> quote (b x)
  VU         -> U
  VQuote t   -> Quote (quote t)
  VSplice t  -> Splice (quote t)
  VBox t     -> Box (quote t)

quote0 :: Val -> Tm
quote0 v = let ?env = [] in quote v


nf :: EnvArg => Tm -> Tm
nf = quote . eval

nf0 :: Tm -> Tm
nf0 = let ?env = [] in nf

-- | Beta-eta conversion checking
conv :: EnvArg => Val -> Val -> Bool
conv t u = case (t, u) of
  (VU        , VU           ) -> True
  (VBox t    , VBox t'      ) -> conv t t'
  (VQuote t  , VQuote t'    ) -> conv t t'
  (VQuote t  , t'           ) -> conv t (VSplice t')
  (t         , VQuote t'    ) -> conv (VSplice t) t'
  (VPi x a b , VPi x' a' b' ) -> conv a a' && bindEnv x \x -> conv (b x) (b' x)
  (VLam x t  , VLam x' t'   ) -> bindEnv x \x -> conv (t x) (t' x)
  (VLam x t  , u            ) -> bindEnv x \x -> conv (t x) (VApp u x)
  (t         , VLam x u     ) -> bindEnv x \x -> conv (VApp t x) (u x)
  (VVar x    , VVar x'      ) -> x == x'
  (VApp t u  , VApp t' u'   ) -> conv t t' && conv u u'
  (VSplice t , VSplice t'   ) -> conv t t'
  _                           -> False

type VTy   = Val
data Types = TNil | TBind Types Name ~VTy | TLock Types
type Cxt   = (?types :: Types, ?env :: Env)

extCxt :: Name -> VTy -> Val -> (Cxt => a) -> Cxt => a
extCxt x a v act =
  let ?types = TBind ?types x a; ?env = (x, v): ?env in
  act

lockCxt :: (Cxt => a) -> Cxt => a
lockCxt act = let ?types = TLock ?types in act

unlockCxt :: (Cxt => a) -> Cxt => a
unlockCxt act =
  let go TNil           = TNil
      go (TBind ts x a) = TBind (go ts) x a
      go (TLock ts)     = go ts in
  let ?types = go ?types in
  act

-- | Typechecking monad. After we throw an error, we annotate it at the innermost
--   point in the syntax where source position information is available from
--   a 'SrcPos' 'Tm' constructor.
type M = Either (String, Maybe SourcePos)

report :: String -> M a
report str = Left (str, Nothing)

quoteShow :: EnvArg => Val -> String
quoteShow = show . quote

addPos :: SourcePos -> M a -> M a
addPos pos ma = case ma of
  Left (msg, Nothing) -> Left (msg, Just pos)
  ma                  -> ma

check :: Cxt => Raw -> VTy -> M ()
check t a = case (t, a) of
  (SrcPos pos t, _) ->
    addPos (coerce pos) (check t a)

  (Lam x t, VPi (fresh -> x') a b) ->
    extCxt x a (VVar x') $ check t (b (VVar x'))

  (Quote t, VBox a) ->
    lockCxt $ check t a

  (Splice t, a) ->
    unlockCxt $ check t (VBox a)

  (Let x a t u, topa) -> do
    check a VU
    let va = eval a
    check t va
    extCxt x va (eval t) $ check u topa

  _ -> do
    tty <- infer t
    unless (conv tty a) $
      report (printf
        "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
        (quoteShow a) (quoteShow tty))

lookupVar :: Name -> Types -> Either Bool VTy
lookupVar x = \case
  TBind ts x' a | x == x' -> Right a
  TBind ts x' a           -> lookupVar x ts
  TLock ts                -> case lookupVar x ts of
                               Right{} -> Left True
                               x       -> x
  TNil                    -> Left False

infer :: Cxt => Raw -> M VTy
infer = \case

  SrcPos pos t -> addPos (coerce pos) (infer t)

  Var x -> case lookupVar x ?types of
    Left True  -> report $ "variable " ++ show x ++ " is locked"
    Left False -> report $ "variable " ++ show x ++ " is not in scope"
    Right a    -> pure a

  U -> pure VU

  App t u -> do
    tty <- infer t
    case tty of
      VPi _ a b -> do
        check u a
        pure (b (eval u))
      tty -> report $
        "Expected a function type, instead inferred:\n\n  "
        ++ quoteShow tty

  Lam{} ->
    report "Can't infer type for lambda expresion"

  Box t -> lockCxt do
    check t VU
    pure VU

  Pi x a b -> do
    check a VU
    extCxt x (eval a) (VVar x) $ check b VU
    pure VU

  Splice t -> unlockCxt do
    infer t >>= \case
      VBox a -> pure a
      a      -> report $ "Expected a boxed type, instead inferred:\n\n  "
                       ++ quoteShow a

  Quote t ->
    VBox <$> lockCxt (infer t)

  Let x a t u -> do
    check a VU
    let va = eval a
    check t va
    extCxt x va (eval t) $ infer u

infer0 :: Raw -> M VTy
infer0 t = let ?env = []; ?types = TNil in infer t

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- printing
--------------------------------------------------------------------------------

-- printing precedences
atomp   = 4  :: Int -- U, var
splicep = 3  :: Int -- splice
appp    = 2  :: Int -- application
pip     = 1  :: Int -- pi
letp    = 0  :: Int -- let, lambda

-- | Wrap in parens if expression precedence is lower than
--   enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go prec where

  piBind x a =
    showParen True ((x++) . (" : "++) . go letp a)

  go :: Int -> Tm -> ShowS
  go p = \case
    Var x       -> (x++)
    App t u     -> par p appp $ go appp t . (' ':) . go splicep u
    Lam x t     -> par p letp $ ("λ "++) . (x++) . goLam t where
                     goLam (Lam x t) = (' ':) . (x++) . goLam t
                     goLam t         = (". "++) . go letp t
    U           -> ("U"++)
    Pi "_" a b  -> par p pip $ go appp a . (" → "++) . go pip b
    Pi x a b    -> par p pip $ piBind x a . goPi b where
                     goPi (Pi x a b) | x /= "_" = piBind x a . goPi b
                     goPi b = (" → "++) . go pip b
    Let x a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp a
                     . ("\n    = "++) . go letp t . ("\nin\n"++) . go letp u
    SrcPos _ t  -> go p t
    Quote t     -> ('<':).go letp t.('>':)
    Splice t    -> par p splicep $ ('~':).go atomp t
    Box    t    -> par p appp $ ("◻ "++).go splicep t

instance Show Tm where showsPrec = prettyTm
-- deriving instance Show Tm

-- parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Tm -> Parser Tm
withPos p = SrcPos <$> (Hide <$> getSourcePos) <*> p

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

pBinder = pIdent <|> symbol "_"

pAtom =
      withPos ((Var <$> pIdent) <|> (U <$ symbol "U"))
  <|> parens pTm
  <|> (Quote <$> (char '<' *> pTm <* char '>'))

pSplice =
      (Splice <$> (char '~' *> pSplice))
  <|> pAtom

pSpine =
      (Box <$> (char '◻' *> pSplice))
  <|> (foldl1 App <$> some pSplice)

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
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pTm
  symbol "="
  t <- pTm
  symbol ";"
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


-- Closed evaluation
--------------------------------------------------------------------------------

data QVal
  = QVar Name
  | QApp QVal QVal
  | QLam Name (QVal -> QVal)
  | QPi Name QVal (QVal -> QVal)
  | QU
  | QLet Name QVal QVal (QVal -> QVal)



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
      case infer0 t of
        Left err -> displayError file err
        Right a  -> do
          print $ nf0 t
          putStrLn "  :"
          print $ quote0 a
    ["type"] -> do
      (t, file) <- getTm
      either (displayError file) (print . quote0) $ infer0 t
    _          -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)

ex1 = main' "type" $ unlines [
  "let Eq : (A : U) → A → A → U = λ A x y. (P : A → U) → P x → P y;",
  "let refl : (A : U)(x : A) → Eq A x x = λ A x P px. px;",

  "let Nat : U = (N : U)(z : N)(s : N → N) → N;",
  "let zero : Nat = λ N z s. z;",
  "let suc : Nat → Nat = λ n N z s. s (n N z s);",

  "let List : U → U = λ A. (L : U)(cons : A → L → L)(nil : L) → L;",
  "let nil  : (A : U) → List A = λ A L c n. n;",
  "let cons : (A : U) → A → List A → List A = λ A a as L c n. c a (as L c n);",
  "let map  : (A B : U) → (A → B) → List A → List B = λ A B f as L c n. as L (λ a bs. c (f a) bs) n;",

  -- ◻ is idempotent ComonadApply
  "let counit  : (A : ◻ U) → ◻ ~A → ~A = λ A x. ~x;",
  "let dup     : (A : ◻ U) → ◻ ~A → ◻ (◻ ~A) = λ A x. <<~x>>;",
  "let ap      : (A B : ◻ U) → ◻ (~A → ~B) → ◻ ~A → ◻ ~B = λ A B f a. <~f ~a>;",
  "let join    : (A : ◻ U) → ◻ (◻ ~A) → ◻ ~A = λ A x. <~~x>;",
  "let dupjoin : (A : ◻ U)(x : ◻ ~A) → Eq (◻ ~A) (join A (dup A x)) x = λ A x. refl (◻ ~A) x;",
  "let joindup : (A : ◻ U)(x : ◻ (◻ ~A)) → Eq (◻ (◻ ~A)) (dup A (join A x)) x = λ A x. refl (◻ (◻ ~A)) x;",

  "let inlMap : (A B : ◻ U) → (◻ ~A → ◻ ~B) → ◻ (List ~A → List ~B) = U;",

  -- "let unap : (A B : ◻ U) → (◻ ~A → ◻ ~B) → ◻ (~A → ~B) = λ A B f. <λ a. ~(f <a>)>;


  "join"

--      λ (A B : ◻ ~A) (f : ◻ ~A → ◻ ~B) → ◻ (~A → ~B)
--          <λ (a : ~A). ~(f <_>>)>
--                          _ :


  ]

-- ex1 = main' "type" $ unlines [
--   "-- basic polymorphic functions",
--   "let id : (A : U) -> A -> A",
--   "      = \\A x. x;",
--   "let const : (A B : U) -> A -> B -> A",
--   "      = \\A B x y. x;",
--   "",
--   "-- Church natural numbers",
--   "let Nat  : U = (N : U) -> (N -> N) -> N -> N;",
--   "let five : Nat = \\N s z. s (s (s (s (s z))));",
--   "let add  : Nat -> Nat -> Nat = \\a b N s z. a N s (b N s z);",
--   "let mul  : Nat -> Nat -> Nat = \\a b N s z. a N (b N s) z;",
--   "",
--   "let ten      : Nat = add five five;",
--   "let hundred  : Nat = mul ten ten;",
--   "let thousand : Nat = mul ten hundred;",
--   "",
--   "hundred"
--   ]
