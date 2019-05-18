
module Holes.Main (main, main') where

import Prelude hiding (all, pi)

import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Char
import Data.Foldable hiding (all)
import Data.Maybe
import Data.String ()
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec

import qualified Data.IntMap.Strict         as M
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

type Name = String

-- | Elaboration input contains holes which are filled in the output.
data Raw
  = RVar Name
  | RLam Name Raw
  | RApp Raw Raw
  | RU
  | RPi Name Raw Raw
  | RLet Name Raw Raw Raw
  | RHole
  deriving Show

type Meta = Int

-- | Metacontext. An unsolved meta is just a meta which isn't contained in
--   the metacontext.
type MCxt = M.IntMap Val

type Ty  = Tm
type VTy = Val

-- | Environment for values. A `Nothing` denotes a bound variable.
type Vals = Sub (Maybe Val)

-- | Elaboration context. We distinguish types of bound and defined variables.
data TyEntry = Bound VTy | Def VTy
data Cxt = Cxt {_vals :: Vals, _types :: Sub TyEntry}

-- | Monad for elaboration. The 'Int' counts the number of allocated metas.
type ElabM = StateT (Int, MCxt) (Either String)

-- | Empty context.
nil :: Cxt
nil = Cxt [] []

-- | Add a bound variable to context.
bind :: Name -> VTy -> Cxt -> Cxt
bind x a (Cxt vs tys) = Cxt ((x, Nothing):vs) ((x, Bound a):tys)

-- | Add a defined name to context.
define :: Name -> Val -> VTy -> Cxt -> Cxt
define x v a (Cxt vs tys) = Cxt ((x, Just v):vs) ((x, Def a):tys)


-- | Well-typed core terms without holes.
--   We use names everywhere instead of indices or levels.
data Tm
  = Var Name
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta Meta


data Head = HMeta Meta | HVar Name deriving Eq

-- | We use a spine form for neutral values, i.e. we have the head variable and
--   all arguments in a list. We need convenient access to both head and spine
--   when unifying and when solving metas.
data Val
  = VNe Head [Val]    -- [Val] here is in reverse order, i. e. the first Val in
                      -- the list is applied last to the head.
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

type Bind a = (Name, a)
type Sub  a = [Bind a]

pattern VVar :: Name -> Val
pattern VVar x = VNe (HVar x) []

pattern VMeta :: Meta -> Val
pattern VMeta m = VNe (HMeta m) []

-- | Generate a name such that it does not shadow anything in the current
--   environment. De Bruijn indices would make this unnecessary in a more
--   sophisticated implementation.
--
--   We only need to invent non-shadowing names when we want to go under
--   a (Val -> Val) closure. See 'quote' and 'unify' for examples of doing so.
fresh :: Vals -> Name -> Name
fresh vs "_" = "_" -- underscore marks unused binder
fresh vs x = case lookup x vs of
  Just _  -> fresh vs (x ++ "'")
  Nothing -> x

-- | Evaluation is up to a metacontext, so whenever we inspect a value during
--   elaboration, we always have to force it first, i.e. unfold solved metas and
--   compute until we hit a rigid head.
force :: MCxt -> Val -> Val
force ms = \case
  VNe (HMeta m) sp | Just t <- M.lookup m ms ->
    force ms (foldr (flip vApp) t sp)
  v -> v

forceM :: Val -> ElabM Val
forceM v = gets (\(_, ms) -> force ms v)

vApp :: Val -> Val -> Val
vApp (VLam _ t) u = t u
vApp (VNe h sp) u = VNe h (u:sp)
vApp _          _ = error "vApp: impossible"

eval :: MCxt -> Vals -> Tm -> Val
eval ms = go where
  go vs = \case
    Var x       -> maybe (VVar x) id (fromJust $ lookup x vs)
    Meta m      -> maybe (VMeta m) id (M.lookup m ms)
    App t u     -> vApp (go vs t) (go vs u)
    Lam x t     -> VLam x (\u -> go ((x, Just u):vs) t)
    Pi x a b    -> VPi x (go vs a) (\u -> go ((x, Just u):vs) b)
    Let x _ t u -> go ((x, Just (go vs t)):vs) u
    U           -> VU

evalM :: Cxt -> Tm -> ElabM Val
evalM cxt t = gets (\(_, ms) -> eval ms (_vals cxt) t)

-- |  Quote into fully forced normal forms.
quote :: MCxt -> Vals -> Val -> Tm
quote ms = go where
  go vs v = case force ms v of
    VNe h sp -> foldr (\v acc -> App acc (go vs v))
                      (case h of HMeta m -> Meta m; HVar x -> Var x)
                      sp
    VLam (fresh vs -> x) t ->
      Lam x (go ((x, Nothing):vs) (t (VVar x)))
    VPi (fresh vs -> x) a b ->
      Pi x (go vs a) (go ((x, Nothing):vs) (b (VVar x)))
    VU -> U

quoteM :: Vals -> Val -> ElabM Tm
quoteM vs v = gets $ \(_, ms) -> quote ms vs v

nf :: MCxt -> Vals -> Tm -> Tm
nf ms vs = quote ms vs . eval ms vs

nfM :: Vals -> Tm -> ElabM Tm
nfM vs t = gets $ \(_, ms) -> nf ms vs t


-- Unification
--------------------------------------------------------------------------------

-- | Check that all entries in a spine are bound variables.
checkSp :: [Val] -> ElabM [Name]
checkSp vs = forM vs $ \v -> forceM v >>= \case
  VVar x -> pure x
  _      -> throwError "non-variable value in meta spine"

-- | Scope check + occurs check a solution candidate. Inputs are a meta, a spine
--   of variable names (which comes from checkSp) and a RHS term in normal
--   form. In real implementations it would be a bad idea to solve metas with
--   normal forms (because of size explosion), but here it's the simplest thing
--   we can do. We don't have to worry about shadowing here, because normal
--   forms have no shadowing by our previous quote implementation.
checkSolution :: Meta -> [Name] -> Tm -> ElabM ()
checkSolution m sp rhs = lift $ go sp rhs where
  go :: [Name] -> Tm -> Either String ()
  go ns = \case
    Var x    -> unless (elem x ns) $
                  throwError ("solution scope error: " ++ show (m, sp, rhs))
    App t u  -> go ns t >> go ns u
    Lam x t  -> go (x:ns) t
    Pi x a b -> go ns a >> go (x:ns) b
    U        -> pure ()
    Meta m'  -> when (m == m') $
                  throwError ("occurs check: " ++ show (m, rhs))
    Let{}    -> error "impossible"

solve :: Vals -> Meta -> [Val] -> Val -> ElabM ()
solve vs m sp rhs = do
  -- check that spine consists of bound vars
  sp <- checkSp sp
  -- normalize rhs
  rhs <- quoteM vs rhs
  -- scope + ocurs check rhs
  checkSolution m sp rhs

  -- Wrap rhs into lambdas. NOTE: this operation ignores nonlinearity, because
  -- the innermost nonlinear variable occurrence simply shadows the other occurrences.
  rhs <- evalM nil (foldl' (flip Lam) rhs sp)

  -- add solution to metacontext
  modify (\(i, mcxt) -> (i, M.insert m rhs mcxt))

-- | Create fresh meta, return the meta applied to all current bound vars.
newMeta :: Cxt -> ElabM Tm
newMeta Cxt{..} = do

  -- There might be shadowed names in the context, but we don't care
  -- about that, since 'solve' ignores nonlinearity anyway.
  let sp = [Var x | (x, Bound{}) <- _types]
  (i, ms) <- get
  put (i + 1, ms)
  pure (foldr (flip App) (Meta i) sp)

-- | Unify two values. After unification succeeds, the LHS and RHS become
--   definitionally equal in the newly updated metacontext. We only need here
--   the value environment for generating non-shadowing names; with de Bruijn
--   levels we would only need an Int denoting the size of the environment.
unify :: Vals -> Val -> Val -> ElabM ()
unify = go where
  go vs t u = do
    ms <- gets snd
    case (force ms t, force ms u) of
      (VLam (fresh vs -> x) t, VLam _ t') ->
        go ((x, Nothing):vs) (t (VVar x)) (t' (VVar x))

      -- these two lines implement eta conversion for functions
      (VLam (fresh vs -> x) t, u) ->
        go ((x, Nothing):vs) (t (VVar x)) (vApp u (VVar x))
      (u, VLam (fresh vs -> x) t) ->
        go ((x, Nothing):vs) (vApp u (VVar x)) (t (VVar x))

      (VPi (fresh vs -> x) a b, VPi _ a' b') -> do
        go vs a a'
        go ((x, Nothing):vs) (b (VVar x)) (b' (VVar x))

      (VU, VU) -> pure ()
      (VNe h sp, VNe h' sp') | h == h' -> zipWithM_ (go vs) sp sp'
      (VNe (HMeta m) sp, t) -> solve vs m sp t
      (t, VNe (HMeta m) sp) -> solve vs m sp t
      (t, t') -> throwError ("can't unify " ++ show (quote ms vs t) ++ " with " ++
                             show (quote ms vs t'))

-- Elaboration
--------------------------------------------------------------------------------


check :: Cxt -> Raw -> VTy -> ElabM Tm
check cxt@Cxt{..} topT topA = case (topT, topA) of

  -- This is a bit tricky. We can only go under the VPi closure with a
  -- non-shadowing name, but we also need to ensure that the RLam binder is the
  -- same as the VPi binder. So we go under the binder with a common fresh
  -- non-shadowing name. In classic "locally nameless" style, the new name
  -- would be immediatly substituted into "t", but that's not only very slow,
  -- but also supposes that "t" is already well-scoped. So instead we just
  -- define "x" to be the new var when going under the binder. This acts as
  -- an efficient delayed substitution when we do unification under the binder.
  -- This subtlety does not come up with de Bruijn indices or levels.
  (RLam x t, VPi (fresh _vals -> x') a b) -> do
    let v = VVar x'
    Lam x <$> check (Cxt ((x, Just v):_vals) ((x, Bound a):_types)) t (b v)

  (RLet x a t u, topA) -> do
    a  <- check cxt a VU
    va <- evalM cxt a
    t  <- check cxt t va
    vt <- evalM cxt t
    u  <- check (define x vt va cxt) u topA
    pure $ Let x a t u

  (RHole, _) ->
    newMeta cxt

  -- we unify the expected and inferred types
  _ -> do
    (t, va) <- infer cxt topT
    unify _vals va topA
    pure t

infer :: Cxt -> Raw -> ElabM (Tm, VTy)
infer cxt@Cxt{..} = \case

  RVar "_" -> throwError "_ is not a valid name"
  RVar x   -> maybe (throwError ("var not in scope: " ++ x))
                    (\a -> pure (Var x, case a of Bound a -> a; Def a -> a))
                    (lookup x _types)

  RU -> pure (U, VU) -- type-in-type

  -- an upgrade to this would be to also proceed if the inferred type for "t"
  -- is meta-headed, in which case we would need to create two fresh metas and
  -- refine "t"'s type to a function type.
  RApp t u -> do
    (t, va) <- infer cxt t
    forceM va >>= \case
      VPi _ a b -> do
        u  <- check cxt u a
        vu <- evalM cxt u
        pure (App t u, b vu)
      _ -> throwError "expected a function type"

  -- we infer type for lambdas by checking them with a
  -- a function type made of fresh metas.
  RLam x t -> do
    a  <- newMeta cxt
    va <- evalM cxt a
    b  <- newMeta (bind x va cxt)
    ty <- evalM cxt (Pi x a b)
    t  <- check cxt (RLam x t) ty
    pure (t, ty)

  RPi x a b -> do
    a  <- check cxt a VU
    va <- evalM cxt a
    b <- check (bind x va cxt) b VU
    pure (Pi x a b, VU)

  -- inferring a type for a hole: we create two metas, one for the hole
  -- and one for its type.
  RHole -> do
    t  <- newMeta cxt
    va <- evalM cxt =<< newMeta cxt
    pure (t, va)

  RLet x a t u -> do
    a       <- check cxt a VU
    va      <- evalM cxt a
    t       <- check cxt t va
    vt      <- evalM cxt t
    (u, vb) <- infer (define x vt va cxt) u
    pure (Let x a t u, vb)


-- | Inline all meta solutions. Used for displaying elaboration output.
zonk :: MCxt -> Vals -> Tm -> Tm
zonk ms = go where

  goSp :: Vals -> Tm -> Either Val Tm
  goSp vs = \case
    Meta m | Just v <- M.lookup m ms -> Left v
    App t u -> either (\t -> Left (vApp t (eval ms vs u)))
                      (\t -> Right (App t (go vs u)))
                      (goSp vs t)
    t -> Right (go vs t)

  go :: Vals -> Tm -> Tm
  go vs = \case
    Var x        -> Var x
    Meta m       -> maybe (Meta m) (quote ms vs) (M.lookup m ms)
    U            -> U
    Pi x a b     -> Pi x (go vs a) (go ((x, Nothing):vs) b)
    App t u      -> either (\t -> quote ms vs (vApp t (eval ms vs u)))
                           (\t -> App t (go vs u))
                           (goSp vs t)
    Lam x t      -> Lam x (go ((x, Nothing):vs) t)
    Let x a t u  -> Let x (go vs a) (go vs t)
                          (go ((x, Nothing):vs) u)

zonkM :: Vals -> Tm -> ElabM Tm
zonkM vs t = gets (\(_, ms) -> zonk ms vs t)



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- printing
--------------------------------------------------------------------------------

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where
  goArg t      = go True t
  goPiBind x a = showParen True ((x++) . (" : "++) . go False a)
  goLamBind x  = (x++)

  goLam :: Tm -> ShowS
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
    U      -> ('U':)
    Meta m -> (("?"++).(show m++))

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

pAtom  = (RVar <$> pIdent)
     <|> parens pTm
     <|> (RU <$ symbol "U")
     <|> (RHole <$ symbol "_")

pSpine = foldl1 RApp <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pIdent
  char '.'
  t <- pTm
  pure (foldr RLam t xs)

pPi = do
  dom <- some (parens ((,) <$> some pIdent <*> (char ':' *> pTm)))
  pArrow
  cod <- pTm
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" sp <$> pTm

pLet = do
  symbol "let"
  x <- pIdent
  symbol ":"
  a <- pTm
  symbol "="
  t <- pTm
  symbol "in"
  u <- pTm
  pure $ RLet x a t u

pTm  = pLam <|> pLet <|> try pPi <|> funOrSpine
pSrc = ws *> pTm <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO Raw
parseStdin = parseString =<< getContents

-- main
--------------------------------------------------------------------------------

helpMsg = unlines [
  "usage: holes [--help|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & elaborate expression from stdin, print its normal form",
  "  type   : read & elaborate expression from stdin, print its type"]

mainWith :: IO [String] -> IO Raw -> IO ()
mainWith getOpt getTm = do
  let elab = do
        t <- getTm
        case (flip evalStateT (0, mempty) $ do
               (t, a) <- infer nil t
               t  <- zonkM [] t
               nt <- nfM [] t
               na <- quoteM [] a
               pure (t, nt, na)) of
          Left err -> putStrLn err >> exitSuccess
          Right x  -> pure x

  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, nt, na) <- elab
      print nt
    ["type"] -> do
      (t, nt, na) <- elab
      print na
    ["elab"] -> do
      (t, nt, na) <- elab
      print t
    _          -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) (parseString src)
