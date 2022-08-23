
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
  PatternSynonyms,
  DerivingVia,
  StandaloneDeriving
  #-}

module Main where

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
  | RPi Name RTy RTy             -- (x : A) -> B
  | RLet Name RTy RTm RTm        -- let x : A = t; u
  | RSrcPos (Hide SourcePos) RTm -- source position for errors
  | RQuote RTm                   -- <t>
  | RSplice RTm                  -- ~t
  | RBox RTm                     -- ◻ A

  | RNat
  | RZero
  | RSuc
  | RInd

  deriving Show


-- syntax
--------------------------------------------------------------------------------

newtype Ix  = Ix  {unIx  :: Int} deriving (Eq, Show, Enum, Num) via Int
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Show, Enum, Num) via Int

type Name = String
type Ty   = Tm

data Tm
  = LocalVar Ix
  | TopVar Lvl
  | Lam Name Tm       -- \x. t
  | App Tm Tm         -- t u
  | U                 -- U
  | Pi Name Ty Ty     -- (x : A) -> B
  | Let Name Ty Tm Tm -- let x : A = t; u
  | Quote Tm          -- <t>
  | Splice Tm         -- ~t
  | Box Tm            -- ◻ A

  | Nat
  | Zero
  | Suc
  | Ind

--------------------------------------------------------------------------------

data Val
  = VVar Lvl
  | VApp Val ~Val
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VQuote Val
  | VSplice Val
  | VBox Val
  | VU

  | VNat
  | VZero
  | VSuc Val
  | VInd Val Val Val Val


type VEnv = (?env :: [Val])

extVEnv :: Val -> (VEnv => a) -> VEnv => a
extVEnv ~v act = let ?env = v: ?env in act

newVVar :: ((?lvl :: Lvl) => Val -> a) -> (?lvl :: Lvl) => a
newVVar act = let v = VVar ?lvl in let ?lvl = ?lvl + 1 in act v

vapp :: Val -> Val -> Val
vapp t ~u = case t of
  VLam _ t -> t u
  t        -> VApp t u

vind :: Val -> Val -> Val -> Val -> Val
vind p s z n = case n of
  VZero  -> z
  VSuc n -> s `vapp` n `vapp` vind p s z n
  n      -> VInd p s z n

eval :: VEnv => Tm -> Val
eval = \case
  LocalVar x  -> ?env !! coerce x
  TopVar x    -> ?env !! (length ?env - coerce x - 1)
  App t u     -> vapp (eval t) (eval u)
  Lam x t     -> VLam x (\u -> extVEnv u (eval t))
  Pi x a b    -> VPi x (eval a) (\u -> extVEnv u (eval b))
  Let x _ t u -> extVEnv (eval t) (eval u)
  U           -> VU
  Quote t     -> case eval t of VSplice t -> t; t -> VQuote t
  Splice t    -> case eval t of VQuote t -> t; t -> VSplice t
  Box t       -> VBox (eval t)

  Nat         -> VNat
  Zero        -> VZero
  Suc         -> VLam "n" VSuc
  Ind         -> VLam "p" \p -> VLam "s" \s -> VLam "z" \z -> VLam "n" \n ->
                 vind p s z n

-- | Beta-eta conversion checking
conv :: (?lvl :: Lvl) => Val -> Val -> Bool
conv t u = case (t, u) of
  (VVar x       , VVar x'          ) -> x == x'
  (VApp t u     , VApp t' u'       ) -> conv t t' && conv u u'
  (VU           , VU               ) -> True
  (VBox t       , VBox t'          ) -> conv t t'
  (VQuote t     , VQuote t'        ) -> conv t t'
  (VSplice t    , VSplice t'       ) -> conv t t'
  (VPi x a b    , VPi x' a' b'     ) -> conv a a' && newVVar \x -> conv (b x) (b' x)
  (VNat         , VNat             ) -> True
  (VZero        , VZero            ) -> True
  (VSuc n       , VSuc n'          ) -> conv n n'
  (VInd p s z n , VInd p' s' z' n' ) -> conv p p' && conv s s' && conv z z' && conv n n'
  (VLam x t     , VLam x' t'       ) -> newVVar \x -> conv (t x) (t' x)
  (VLam x t     , u                ) -> newVVar \x -> conv (t x) (VApp u x)
  (t            , VLam x u         ) -> newVVar \x -> conv (VApp t x) (u x)
  _                                  -> False

lvlToIx :: (?lvl :: Lvl) => Lvl -> Ix
lvlToIx x = coerce (?lvl - x - 1)

ixToLvl :: (?lvl :: Lvl) => Ix -> Lvl
ixToLvl x = ?lvl - coerce x - 1

quote :: (?lvl :: Lvl) => Val -> Tm
quote = \case
  VVar x       -> LocalVar (lvlToIx x)
  VApp t u     -> App (quote t) (quote u)
  VLam x t     -> Lam x $ newVVar \x -> quote (t x)
  VPi  x a b   -> Pi x (quote a) $ newVVar \x -> quote (b x)
  VU           -> U
  VQuote t     -> Quote (quote t)
  VSplice t    -> Splice (quote t)
  VBox t       -> Box (quote t)
  VNat         -> Nat
  VZero        -> Zero
  VSuc t       -> Suc `App` quote t
  VInd p s z n -> Ind  `App` quote p `App` quote s `App` quote z `App` quote n

quote0 :: Val -> Tm
quote0 = let ?lvl = 0 in quote

nf0 :: Tm -> Tm
nf0 t = let ?env = []; ?lvl = 0 in quote (eval t)


-- Multi-stage evaluation
--------------------------------------------------------------------------------

type Stage   = Int
type Closure = (?top :: [SVal]) => (?lvl :: Lvl) => SVal -> SVal

data SVal
  = SLocalVar Lvl
  | STopVar Lvl
  | SApp SVal SVal
  | SLam Name Closure
  | SPi Name SVal Closure
  | SLet Name SVal SVal Closure
  | SQuote SVal
  | SSplice SVal
  | SBox SVal
  | SU
  | SNat
  | SZero
  | SSucSym
  | SIndSym

pattern SSuc n = SApp SSucSym n
pattern SInd p s z n = SIndSym `SApp` p `SApp` s `SApp` z `SApp` n

runtop :: (?top :: [SVal], ?names :: [Name]) => Tm -> Tm
runtop t =
  let ?lvl = 0; ?stage = 0; ?local = [] in
  case t of
    Let x a t u -> let vt = seval t in let ?top = vt : ?top; ?names = x: ?names in runtop u
    t           -> gen (seval t)

-- map each local var to itself
idEnv :: Lvl -> [SVal]
idEnv l = map SLocalVar [l-1,l-2..0]

sapp0 :: (?top :: [SVal], ?lvl :: Lvl) => SVal -> SVal -> SVal
sapp0 t u = case t of
  SLam _ t -> t u
  t        -> SApp t u

sind0 :: (?top :: [SVal], ?lvl :: Lvl) => SVal -> SVal -> SVal -> SVal -> SVal
sind0 p s z n = case n of
  SZero  -> z
  SSuc n -> s `sapp0` n `sapp0` sind0 p s z n
  n      -> SInd p s z n

extSEnv :: Name -> SVal -> ((?local :: [SVal], ?names :: [Name]) => a)
                        -> ((?local :: [SVal], ?names :: [Name]) => a)
extSEnv x ~v act = let ?local = v : ?local; ?names = x : ?names  in act

seval :: (?top :: [SVal], ?local :: [SVal], ?lvl :: Lvl, ?stage :: Int, ?names :: [Name])
         => Tm -> SVal
seval = \case
  Lam x t    -> SLam x (\u -> extSEnv x u (seval t))
  Pi x a b   -> SPi x (seval a) (\u -> extSEnv x u (seval b))
  Quote t    -> let ?stage = ?stage + 1 in case seval t of
                  SSplice t -> t
                  t         -> SQuote t
  Box t      -> SBox (seval t)
  U          -> SU
  LocalVar x -> ?local !! coerce x
  Nat        -> SNat
  Zero       -> SZero
  Suc        -> SSucSym

  t -> case ?stage of
    0 -> case t of
      TopVar x    -> ?top !! (length ?top - coerce x - 1)
      App t u     -> sapp0 (seval t) (seval u)
      Let x a t u -> let vt = seval t in let ?local = vt : ?local in seval u
      Splice t    -> case seval t of
                       SQuote t ->
                         let ?local = idEnv ?lvl in
                         let gt = gen t in
                         trace ("CODE GENERATED:\n" ++ showTm ?names gt ++ "\n") $ seval gt
                       t -> SSplice t
      Ind         -> SLam "p" \p -> SLam "s" \s -> SLam "z" \z -> SLam "n" \n ->
                     sind0 p s z n
    _ -> case t of
      TopVar x    -> STopVar x
      App t u     -> SApp (seval t) (seval u)
      Let x a t u -> SLet x (seval a) (seval t) (\t -> extSEnv x t (seval u))
      Splice t    -> let ?stage = ?stage - 1 in case seval t of
                       SQuote t -> t
                       t        -> SSplice t
      Ind         -> SIndSym


newSVar :: ((?lvl :: Lvl) => SVal -> a) -> ((?lvl :: Lvl) => a)
newSVar act =
  let v = SLocalVar ?lvl in
  let ?lvl = ?lvl + 1 in
  act v

gen :: (?top :: [SVal], ?lvl :: Lvl) => SVal -> Tm
gen = \case
  SLocalVar x  -> LocalVar (lvlToIx x)
  STopVar x    -> TopVar x
  SApp t u     -> App (gen t) (gen u)
  SLam x t     -> newSVar \var -> Lam x (gen (t var))
  SPi x a b    -> let a' = gen a in newSVar \var -> Pi x a' (gen (b var))
  SLet x a t u -> let a' = gen a; t' = gen t in newSVar \var ->
                  Let x a' t' (gen (u var))
  SQuote t     -> Quote (gen t)
  SSplice t    -> Splice (gen t)
  SBox t       -> Box (gen t)
  SU           -> U

  SNat         -> Nat
  SZero        -> Zero
  SSucSym      -> Suc
  SIndSym      -> Ind

--------------------------------------------------------------------------------

type VTy    = Val
type TopCxt = (?top :: [(Name, VTy)], VEnv)
type Cxt    = (?top :: [(Name, VTy)], ?local :: [(Name, VTy)], VEnv, ?lvl :: Lvl)

bind :: Name -> VTy -> (Cxt => Val -> a) -> Cxt => a
bind x a act =
  let v = VVar ?lvl in
  let ?local = (x, a) : ?local; ?env = v: ?env; ?lvl = ?lvl + 1 in
  act v

define :: Name -> VTy -> Val -> (Cxt => a) -> Cxt => a
define x a ~v act =
  let ?local = (x, a) : ?local; ?env = v: ?env; ?lvl = ?lvl + 1 in
  act

defineTop :: Name -> VTy -> Val -> (Cxt => a) -> Cxt => a
defineTop x a ~v act =
  let ?top = (x, a) : ?top; ?env = v: ?env; ?lvl = ?lvl + 1 in
  act

-- | Typechecking monad. After we throw an error, we annotate it at the innermost
--   point in the syntax where source position information is available from
--   a 'SrcPos' 'Tm' constructor.
type M = Either (String, Maybe SourcePos)

report :: String -> M a
report str = Left (str, Nothing)

cxtNames :: Cxt => [Name]
cxtNames = map fst $ ?local ++ ?top

quoteShow :: Cxt => Val -> String
quoteShow t =
  -- show (quote t)
  showTm cxtNames (quote t)

addPos :: SourcePos -> M a -> M a
addPos pos ma = case ma of
  Left (msg, Nothing) -> Left (msg, Just pos)
  ma                  -> ma

check :: Cxt => RTm -> VTy -> M Tm
check t a = case (t, a) of
  (RSrcPos pos t, _) ->
    addPos (coerce pos) (check t a)

  (RLam x t, VPi x' a b) ->
    Lam x <$> (bind x a \x -> check t (b x))

  (RQuote t, VBox a) -> Quote <$> check t a
  (RSplice t, a)     -> Splice <$> check t (VBox a)

  (RLet x a t u, topa) -> do
    a <- check a VU
    let va = eval a
    t <- check t va
    u <- define x va (eval t) $ check u topa
    pure $ Let x a t u

  _ -> do
    (t, tty) <- infer t
    unless (conv tty a) $
      report (printf
        "type mismatch\n\nexpected type:\n\n  %s\n\ninferred type:\n\n  %s\n"
        (quoteShow a) (quoteShow tty))
    pure t

lookupVar :: Name -> [(Name, VTy)] -> Maybe (Ix, VTy)
lookupVar x xs = go 0 xs where
  go i [] = Nothing
  go i ((x', a):xs) | x == x' = Just (i, a)
                    | True    = go (i + 1) xs

infer :: Cxt => RTm -> M (Tm, VTy)
infer = \case

  RSrcPos pos t ->
    addPos (coerce pos) (infer t)

  RVar x -> do
    case lookupVar x ?local of
      Just (i, a) -> pure (LocalVar i, a)
      Nothing -> case lookupVar x ?top of
        Just (i, a) -> do
          let ?lvl = Lvl (length ?top)
          pure (TopVar (ixToLvl i), a)
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
    b <- bind x (eval a) \_ -> check b VU
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
    (u, uty) <- define x va (eval t) $ infer u
    pure (Let x a t u, uty)

  RNat ->
    pure (Nat, VU)

  RZero ->
    pure (Zero, VNat)

  RSuc -> do
    pure (Suc, VPi "_" VNat \_ -> VNat)

  RInd -> do
    let a = VPi "p" (VPi "_" VNat \_ -> VU) \p ->
            VPi "s" (VPi "n" VNat \n -> VPi "_" (vapp p n) \_-> vapp p (VSuc n)) \_ ->
            VPi "z" (vapp p VZero) \_ ->
            VPi "n" VNat \n ->
            vapp p n
    pure (Ind, a)


inferTop :: TopCxt => RTm -> M (Tm, VTy, [Name])
inferTop = \case
  RSrcPos pos t ->
    addPos (coerce pos) (inferTop t)

  RLet x a t u -> do
    let ?local = []; ?lvl = 0
    a <- check a VU
    let va = eval a
    t <- check t va
    (u, uty, ns) <- defineTop x va (eval t) $ inferTop u
    pure (Let x a t u, uty, ns)

  t -> do
    let ?local = []; ?lvl = 0
    (t, tty) <- infer t
    pure (t, tty, cxtNames)

inferTop0 :: RTm -> M (Tm, VTy, [Name])
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

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x   = case elem x ns of
  True -> fresh ns (x ++ "'")
  _    -> x

prettyTm :: [Name] -> Int -> Tm -> ShowS
prettyTm ns prec = go ns prec where

  localvar ns x acc = ns !! unIx x ++ acc

  topvar ns x acc =
    let ?lvl = Lvl $ length ns in
    localvar ns (lvlToIx x) acc

  piBind ns x a =
    showParen True ((x++) . (" : "++) . go ns letp a)

  go :: [Name] -> Int -> Tm -> ShowS
  go ns p = \case
    LocalVar x  -> localvar ns x
    TopVar x    -> topvar ns x

    App t u     -> par p appp $ go ns appp t . (' ':) . go ns splicep u

    Lam (fresh ns -> x) t -> par p letp $ ("λ "++) . (x++) . goLam (x:ns) t where
      goLam ns (Lam (fresh ns -> x) t) = (' ':) . (x++) . goLam (x:ns) t
      goLam ns t                       = (". "++) . go ns letp t

    U  -> ("U"++)

    Pi "_" a b ->
      par p pip $ go ns appp a . (" → "++) . go ("_":ns) pip b

    Pi (fresh ns -> x) a b -> par p pip $ piBind ns x a . goPi (x:ns) b where
      goPi ns (Pi (fresh ns -> x) a b) | x /= "_" = piBind ns x a . goPi (x:ns) b
      goPi ns b = (" → "++) . go ns pip b

    Let (fresh ns -> x) a t u ->
      par p letp $ ("let "++) . (x++) . (" : "++) . go ns letp a
      . ("\n    = "++) . go ns letp t . (";\n\n"++) . go (x:ns) letp u

    Quote t      -> ('<':).go ns letp t.('>':)
    Splice t     -> par p splicep $ ('~':).go ns atomp t
    Box    t     -> par p appp $ ("◻ "++).go ns splicep t

    Nat          -> ("Nat"++)
    Zero         -> ("zero"++)
    Suc          -> ("suc"++)
    Ind          -> ("ind"++)


deriving instance Show Tm

showTm :: [Name] -> Tm -> String
showTm ns t = prettyTm ns 0 t []

showTm0 :: Tm -> String
showTm0 = showTm []

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
keyword x = x == "let" || x == "in" || x == "λ" || x == "U" || x == "zero"
          || x == "suc" || x == "Nat" || x == "ind"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing (\c -> isAlphaNum c || c == '\'')
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
  <|> (RZero <$ pKeyword "zero")
  <|> (RNat <$ pKeyword "Nat")
  <|> (RSuc <$ pKeyword "suc")
  <|> (RInd <$ pKeyword "ind")

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
  let get :: IO (Tm, VTy, [Name])
      get = do
        (t, file) <- getTm
        case inferTop0 t of
          Left err -> displayError file err >> exitSuccess
          Right x  -> pure x

  getOpt >>= \case
    ["--help"] ->
      putStrLn helpMsg
    ["nf"] -> do
      (t, a, _) <- get
      putStrLn $ showTm0 $ nf0 t
      putStrLn "  :"
      putStrLn $ showTm0 $ quote0 a
    ["elab"] -> do
      (t, a, _) <- get
      putStrLn $ showTm0 t
    ["run"] -> do
      (t, a, ns) <- get
      let ?top = []; ?names = []
      let res = runtop t
      putStrLn "----------------------------------------"
      putStrLn $ showTm ns res
    _ ->
      putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
