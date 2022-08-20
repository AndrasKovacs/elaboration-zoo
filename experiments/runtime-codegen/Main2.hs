
{-# options_ghc -Wincomplete-patterns #-}

{-# language
  BlockArguments,
  ConstraintKinds,
  EmptyCase,
  ImplicitParams,
  LambdaCase,
  RankNTypes,
  Strict,
  TupleSections,
  ViewPatterns,
  StandaloneDeriving
  #-}

module Main2 where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Coerce
import Data.Maybe
import Data.Void
import GHC.Stack
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Printf
import Debug.Trace

import qualified Data.Set                   as S
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

--------------------------------------------------------------------------------

test = main' "run" $ unlines [
  "let Eq : (A : U) → A → A → U = λ A x y. (P : A → U) → P x → P y;",
  "let refl : (A : U)(x : A) → Eq A x x = λ A x P px. px;",

  "let Nat   : U   = (N : U)(z : N)(s : N → N) → N;",
  "let zero  : Nat = λ N z s. z;",
  "let one   : Nat = λ N z s. s z;",
  "let suc   : Nat → Nat = λ n N z s. s (n N z s);",
  "let three : Nat = λ N z s. s (s (s z));",

  "let Q : (A : U) → A → ◻ A = λ A x. <x>;",

  "let List  : U → U = λ A. (L : U)(cons : A → L → L)(nil : L) → L;",
  "let nil   : (A : U) → List A = λ A L c n. n;",
  "let cons  : (A : U) → A → List A → List A = λ A a as L c n. c a (as L c n);",
  "let foldr : (A B : U) → (A → B → B) → B → List A → B = λ A B c n as. as B c n;",

  "let map : (A B : ◻ U) → (◻ ~A → ◻ ~B) → ◻ (List ~A) → ◻ (List ~B)",
  "  = λ A B f as. <foldr ~A (List ~B) (λ a bs. cons ~B ~(f <a>) bs) (nil ~B) ~as>;",

  "let mapSucCode : ◻ (List Nat → List Nat)",
  "  = <λ xs. ~(map <Nat> <Nat> (λ n. <suc ~n>) <xs>)>;",

  "let FList : ◻ U → U = λ A. (L : ◻ U)(cons : ◻ ~A → ◻ ~L → ◻ ~L)(nil : ◻ ~L) → ◻ ~L;",

  "let fmap : (A B : ◻ U) → (◻ ~A → ◻ ~B) → FList A → FList B",
  "  = λ A B f as L c n. as L (λ a bs. c (f a) bs) n;",

  "let up : (A : ◻ U) → ◻ (List ~A) → FList A",
  "  = λ A as L c n. <foldr ~A ~L (λ a l. ~(c <a> <l>)) ~n ~as>;",

  "let down



  "mapSucCode"

  ]


--------------------------------------------------------------------------------

-- hiding things in derived Show instances
newtype Hide a = Hide a

instance Show (Hide a) where
  showsPrec n x acc = acc

impossible :: HasCallStack => a
impossible = error "impossible"

-- raw syntax
--------------------------------------------------------------------------------

type RTy = RTm

data RTm
  = RVar Name                    -- x
  | RLam Name RTm                -- \x. t
  | RApp RTm RTm                 -- t u
  | RU                           -- U
  | RPi Name RTy RTy               -- (x : A) -> B
  | RLet Name RTy RTm RTm         -- let x : A = t; u
  | RSrcPos (Hide SourcePos) RTm -- source position for errors
  | RQuote RTm                   -- <t>
  | RSplice RTm                  -- ~t
  | RBox RTm                     -- ◻ A
  deriving Show


-- syntax
--------------------------------------------------------------------------------

type Name = String
type Ty   = Tm

data Tm
  = LocalVar Name
  | TopVar Name
  | Lam Name Tm                -- \x. t
  | App Tm Tm                  -- t u
  | U                          -- U
  | Pi Name Ty Ty              -- (x : A) -> B
  | Let Name Ty Tm Tm          -- let x : A = t; u
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

type Env a = [(Name, a)]
type VEnv = Env Val

extEnv :: Name -> v -> ((?env :: Env v) => a) -> (?env :: Env v) => a
extEnv x ~v act = let ?env = (x, v): ?env in act

fresh :: (?env :: Env v) => Name -> Name
fresh "_" = "_"
fresh x   = case lookup x ?env of
  Just _  -> fresh (x ++ "'")
  _       -> x

bindEnv :: Name -> ((?env :: VEnv) => Val -> a) -> (?env :: VEnv) => a
bindEnv (fresh -> x) act =
  let v = VVar x in let ?env = (x,v): ?env in act v

vsplice :: Val -> Val
vsplice = \case VQuote t -> t; t -> VSplice t

vquote :: Val -> Val
vquote = \case VSplice t -> t; t -> VQuote t

lookupVar :: Name -> Env v -> v
lookupVar x env = fromJust $ lookup x env

eval :: (?env :: VEnv) => Tm -> Val
eval = \case
  LocalVar x  -> lookupVar x ?env
  TopVar x    -> lookupVar x ?env
  App t u     -> case (eval t, eval u) of
                   (VLam _ t, u) -> t u
                   (t       , u) -> VApp t u
  Lam x t     -> VLam x (\u -> extEnv x u (eval t))
  Pi x a b    -> VPi x (eval a) (\u -> extEnv x u (eval b))
  Let x _ t u -> extEnv x (eval t) (eval u)
  U           -> VU
  Quote t     -> vquote (eval t)
  Splice t    -> vsplice (eval t)
  Box t       -> VBox (eval t)

-- | Beta-eta conversion checking
conv :: (?env :: VEnv) => Val -> Val -> Bool
conv t u = case (t, u) of
  (VVar x    , VVar x'      ) -> x == x'
  (VApp t u  , VApp t' u'   ) -> conv t t' && conv u u'
  (VU        , VU           ) -> True
  (VBox t    , VBox t'      ) -> conv t t'
  (VQuote t  , VQuote t'    ) -> conv t t'
  (VSplice t , VSplice t'   ) -> conv t t'
  (VPi x a b , VPi x' a' b' ) -> conv a a' && bindEnv x \x -> conv (b x) (b' x)
  (VLam x t  , VLam x' t'   ) -> bindEnv x \x -> conv (t x) (t' x)
  (VLam x t  , u            ) -> bindEnv x \x -> conv (t x) (VApp u x)
  (t         , VLam x u     ) -> bindEnv x \x -> conv (VApp t x) (u x)
  _                           -> False

quote :: (?env :: VEnv) => Val -> Tm
quote = \case
  VVar x     -> LocalVar x
  VApp t u   -> App (quote t) (quote u)
  VLam x t   -> Lam x $ bindEnv x \x -> quote (t x)
  VPi  x a b -> Pi x (quote a) $ bindEnv x \x -> quote (b x)
  VU         -> U
  VQuote t   -> Quote (quote t)
  VSplice t  -> Splice (quote t)
  VBox t     -> Box (quote t)

quote0 :: Val -> Tm
quote0 = let ?env = [] in quote

nf0 :: Tm -> Tm
nf0 t = let ?env = [] in quote (eval t)


-- Staged evaluation
--------------------------------------------------------------------------------

type Stage = Int
type SEnv  = Env SVal

data SVal
  = SLocalVar Name
  | STopVar Name
  | SApp SVal SVal
  | SLam Name (SVal -> SVal)
  | SPi Name SVal (SVal -> SVal)
  | SLet Name SVal SVal (SVal -> SVal)
  | SQuote SVal
  | SSplice SVal
  | SBox SVal
  | SU

sapp :: SVal -> SVal -> SVal
sapp (SLam _ t) u = t u
sapp t          u = SApp t u

downStage :: ((?stage :: Stage) => a) -> ((?stage :: Stage) => a)
downStage act = let ?stage = ?stage - 1 in act

upStage :: ((?stage :: Stage) => a) -> ((?stage :: Stage) => a)
upStage act = let ?stage = ?stage + 1 in act

sQuote :: SVal -> SVal
sQuote = \case SSplice t -> t; t -> SQuote t

sSplice :: SVal -> SVal
sSplice = \case SQuote t -> t; t -> SSplice t

sSplice0 :: (?env :: SEnv) => SVal -> SVal
sSplice0 = \case SQuote t -> seval0 (gen t); t -> SSplice t

seval0 :: (?env :: SEnv) => Tm -> SVal
seval0 = \case
  LocalVar x  -> lookupVar x ?env
  TopVar x    -> lookupVar x ?env
  Lam x t     -> SLam x \u -> extEnv x u (seval0 t)
  App t u     -> sapp (seval0 t) (seval0 u)
  U           -> SU
  Pi x a b    -> SPi x (seval0 a) \u -> extEnv x u (seval0 b)
  Let x a t u -> extEnv x (seval0 t) (seval0 u)
  Quote t     -> sQuote (seval1 t)
  Splice t    -> sSplice0 (seval0 t)
  Box t       -> SBox (seval0 t)

seval1 :: (?env :: SEnv) => Tm -> SVal
seval1 t = let ?stage = 1 in seval t

seval :: (?env :: SEnv) => (?stage :: Stage) => Tm -> SVal
seval = \case
  LocalVar x  -> lookupVar x ?env
  TopVar x    -> STopVar x
  Lam x t     -> SLam x \u -> extEnv x u (seval t)
  App t u     -> SApp (seval t) (seval u)
  U           -> SU
  Pi x a b    -> SPi x (seval a) \u -> extEnv x u (seval b)
  Let x a t u -> SLet x (seval a) (seval t) \v -> extEnv x v (seval u)
  Quote t     -> sQuote (upStage (seval t))
  Splice t    -> sSplice $ case ?stage of 1 -> seval0 t
                                          _ -> downStage (seval t)
  Box t       -> SBox (seval t)

sBind :: Name -> ((?env :: SEnv) => Name -> SVal -> a) -> (?env :: SEnv) => a
sBind (fresh -> x) act =
  let v = SLocalVar x in let ?env = (x,v): ?env in act x v

gen :: (?env :: SEnv) => SVal -> Tm
gen = \case
  SLocalVar x  -> LocalVar x
  STopVar x    -> TopVar x
  SApp t u     -> App (gen t) (gen u)
  SLam x t     -> sBind x \x var -> Lam x (gen (t var))
  SPi x a b    -> let a' = gen a in sBind x \x var -> Pi x a' (gen (b var))
  SLet x a t u -> let a' = gen a; t' = gen t in sBind x \x var ->
                  Let x a' t' (gen (u var))
  SQuote t     -> Quote (gen t)
  SSplice t    -> Splice (gen t)
  SBox t       -> Box (gen t)
  SU           -> U


--------------------------------------------------------------------------------

type VTy    = Val
type TopCxt = (?top :: Env VTy, ?env :: VEnv)
type Cxt    = (?top :: Env VTy, ?local :: Env VTy, ?env :: VEnv)

extCxt :: Name -> VTy -> Val -> (Cxt => a) -> Cxt => a
extCxt x a v act =
  let ?local = (x, a) : ?local; ?env = (x, v): ?env in
  act

extTopCxt :: Name -> VTy -> Val -> (Cxt => a) -> Cxt => a
extTopCxt x a v act =
  let ?top = (x, a) : ?top; ?env = (x, v): ?env in
  act

-- | Typechecking monad. After we throw an error, we annotate it at the innermost
--   point in the syntax where source position information is available from
--   a 'SrcPos' 'Tm' constructor.
type M = Either (String, Maybe SourcePos)

report :: String -> M a
report str = Left (str, Nothing)

quoteShow :: (?env :: VEnv) => Val -> String
quoteShow = show . quote

addPos :: SourcePos -> M a -> M a
addPos pos ma = case ma of
  Left (msg, Nothing) -> Left (msg, Just pos)
  ma                  -> ma

check :: Cxt => RTm -> VTy -> M Tm
check t a = case (t, a) of
  (RSrcPos pos t, _) ->
    addPos (coerce pos) (check t a)

  (RLam x t, VPi (fresh -> x') a b) ->
    Lam x <$> extCxt x a (VVar x') (check t (b (VVar x')))

  (RQuote t, VBox a) -> Quote <$> check t a
  (RSplice t, a)     -> Splice <$> check t (VBox a)

  (RLet x a t u, topa) -> do
    a <- check a VU
    let va = eval a
    t <- check t va
    u <- extCxt x va (eval t) $ check u topa
    pure $ Let x a t u

  _ -> do
    (t, tty) <- infer t
    unless (conv tty a) $
      report (printf
        "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
        (quoteShow a) (quoteShow tty))
    pure t

infer :: Cxt => RTm -> M (Tm, VTy)
infer = \case

  RSrcPos pos t ->
    addPos (coerce pos) (infer t)

  RVar x -> do
    case lookup x ?local of
      Just a -> pure (LocalVar x, a)
      Nothing -> case lookup x ?top of
        Just a -> pure (TopVar x, a)
        Nothing -> report $ "variable " ++ show x ++ " is not in scope"

  RU -> pure (U, VU)

  RApp t u -> do
    (t, tty) <- infer t
    case tty of
      VPi _ a b -> do
        u <- check u a
        pure (App t u, b (eval u))
      tty -> report $
        "Expected a function type, instead inferred:\n\n  "
        ++ quoteShow tty

  RLam{} ->
    report "Can't infer type for lambda expresion"

  RBox t -> do
    t <- check t VU
    pure (Box t, VU)

  RPi x a b -> do
    a <- check a VU
    b <- extCxt x (eval a) (VVar x) $ check b VU
    pure (Pi x a b, VU)

  RSplice t -> do
    (t, tty) <- infer t
    case tty of
      VBox a -> pure (Splice t, a)
      a      -> report $ "Expected a boxed type, instead inferred:\n\n  "
                       ++ quoteShow a

  RQuote t -> do
    (t, tty) <- infer t
    pure (Quote t, VBox tty)

  RLet x a t u -> do
    a <- check a VU
    let va = eval a
    t <- check t va
    (u, uty) <- extCxt x va (eval t) $ infer u
    pure (Let x a t u, uty)

inferTop :: TopCxt => RTm -> M (Tm, VTy)
inferTop = \case
  RSrcPos pos t ->
    addPos (coerce pos) (inferTop t)

  RLet x a t u -> do
    let ?local = []
    a <- check a VU
    let va = eval a
    t <- check t va
    (u, uty) <- extTopCxt x va (eval t) $ inferTop u
    pure (Let x a t u, uty)

  t -> do
    let ?local = []
    infer t

inferTop0 :: RTm -> M (Tm, VTy)
inferTop0 = let ?top = []; ?env = [] in inferTop

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
    LocalVar x  -> (x++)
    TopVar x    -> (x++)
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
                     . ("\n    = "++) . go letp t . (";\n\n"++) . go letp u
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

withPos :: Parser RTm -> Parser RTm
withPos p = RSrcPos <$> (Hide <$> getSourcePos) <*> p

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
      withPos ((RVar <$> pIdent) <|> (RU <$ symbol "U"))
  <|> parens pTm
  <|> (RQuote <$> (char '<' *> pTm <* char '>'))

pSplice =
      (RSplice <$> (char '~' *> pSplice))
  <|> pAtom

pSpine =
      (RBox <$> (char '◻' *> pSplice))
  <|> (foldl1 RApp <$> some pSplice)

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pTm
  pure (foldr RLam t xs)

pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pTm)))
  pArrow
  cod <- pTm
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" sp <$> pTm

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pTm
  symbol "="
  t <- pTm
  symbol ";"
  u <- pTm
  pure $ RLet x a t u

pTm  = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)
pSrc = ws *> pTm <* eof

parseString :: String -> IO RTm
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (RTm, String)
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
  "usage: mltt-runtime-codegen [--help|nf|elab|run]",
  "  --help : display this message",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  elab   : read & typecheck expression from stdin, print it and its type",
  "  run    : read & typecheck expression from stdin, print result value"]

mainWith :: IO [String] -> IO (RTm, String) -> IO ()
mainWith getOpt getTm = do
  let get :: IO (Tm, VTy)
      get = do
        (t, file) <- getTm
        case inferTop0 t of
          Left err     -> displayError file err >> exitSuccess
          Right (t, a) -> pure (t, a)

  getOpt >>= \case
    ["--help"] ->
      putStrLn helpMsg
    ["nf"] -> do
      (t, a) <- get
      print $ nf0 t
      putStrLn "  :"
      print $ quote0 a
    ["elab"] -> do
      (t, a) <- get
      print t
    ["run"] -> do
      (t, a) <- get
      let ?env = []
      putStrLn $ show $ gen $ seval0 t
    _ ->
      putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
