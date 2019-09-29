module Main where

import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.Morph
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Char
import Data.Bifunctor
import Data.Foldable
import Data.Maybe
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Data.Set                   as S
import qualified Data.IntMap.Strict         as M
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L


-- examples
--------------------------------------------------------------------------------

-- main' "elab" prints the input, but with holes filled by inferred values or
-- unsolved metas
ex1 = main' "elab" $ unlines [
  "let id : (A : U) -> A -> A",
  "      = \\A x. x in",
  "let id2 : (A : _) -> A -> A",
  "      = \\A x. id _ x in",
  "id"
  ]

-- example output which contains unsolved meta, as "?2 A x" in
-- id2. This means that "?2" is the second hole in the expression,
-- and is in a scope with "A" and "x" as bound variables.
ex2 = main' "elab" $ unlines [
  "let id : (A : U) -> A -> A",
  "      = \\A x. x in",
  "let id2 : (A : _) -> A -> A",
  "      = \\A x. id _ _ in",
  "id2"
  ]

-- ex3 = parseString $ unlines [
ex3 = main' "elab" $ unlines [
  "let id : (A : _) -> A -> A",
  "    = \\A x. x in",
  "let List : U -> U",
  "    = \\A. (L : _) -> (A -> L -> L) -> L -> L in",
  "let nil : (A : _) -> List A",
  "    = \\A L cons nil. nil in",
  "let cons : (A : _) -> A -> List A -> List A",
  "    = \\A x xs L cons nil. cons x (xs _ cons nil) in",
  "let Bool : U",
  "    = (B : _) -> B -> B -> B in",
  "let true : Bool",
  "    = \\B t f. t in",
  "let false : Bool",
  "    = \\B t f. f in",
  "let not : Bool -> Bool",
  "    = \\b B t f. b B f t in",
  "let list1 : List Bool",
  "    = cons _ (id _ true) (nil _) in",
  "let Eq : (A : _) -> A -> A -> U",
  "    = \\A x y. (P : A -> U) -> P x -> P y in",
  "let refl : (A : _)(x : A) -> Eq A x x",
  "    = \\A x P px. px in",
  "\\x. refl _ (cons _ true x)"
  ]

--------------------------------------------------------------------------------

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
  | RSrcPos SourcePos Raw
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


-- Errors
--------------------------------------------------------------------------------

data UnifyError
  = SpineError
  -- | Meta, spine, rhs, offending variable
  | ScopeError Meta [Name] Tm Name
  | OccursCheck Meta Tm
  | UnifyError Tm Tm

data ElabError
  = NameNotInScope Name
  -- | Inferred type.
  | ExpectedFunction Tm
  -- | Expected type, inferred type, unification error.
  | CheckError Tm Tm UnifyError
  | ExpectedFunctionFromMeta Tm UnifyError

instance Show UnifyError where
  show = \case
    SpineError -> "Non-variable value in meta spine."
    ScopeError m sp rhs x -> printf
      ("Solution scope error.\n" ++
       "Meta %s can only depend on %s variables,\n" ++
       "but the solution candidate\n\n" ++
       "  %s\n\n" ++
       "contains variable %s.")
      (show m) (show sp) (show rhs) x
    OccursCheck m rhs -> printf (
      "Meta %s occurs cyclically in its solution candidate:\n\n" ++
      "  %s")
      (show m) (show rhs)
    UnifyError lhs rhs -> printf
      ("Cannot unify\n\n" ++
       "  %s\n\n" ++
       "with\n\n" ++
       "  %s")
      (show lhs) (show rhs)

instance Show ElabError where
  show = \case
    NameNotInScope x ->
      "Name not in scope: " ++ x
    ExpectedFunction ty ->
      "Expected a function type, instead inferred:\n\n  " ++ show ty
    CheckError want have e -> printf (
      "%s\n\n" ++
      "Error occurred while unifying inferred type\n\n" ++
      "  %s\n\n" ++
      "with expected type\n\n" ++
      "  %s")
      (show e) (show have) (show want)
    ExpectedFunctionFromMeta ty e -> printf (
      "%s\n\n" ++
      "Error occurred while trying to refine inferred type\n\n" ++
      "  %s\n\n" ++
      "to a function type.")
      (show e) (show ty)

report :: MonadError (e, Maybe SourcePos) m => e -> m a
report e = throwError (e, Nothing)

addPos :: SourcePos -> ElabM a -> ElabM a
addPos pos ma =
  catchError ma $ \(msg, mpos) -> throwError (msg, mpos <|> Just pos)

displayError :: String -> (ElabError, Maybe SourcePos) -> IO ()
displayError file (msg, Just (SourcePos path (unPos -> linum) (unPos -> colnum))) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n\n" (show msg)
displayError _ _ = error "displayError: impossible: no available source position"

--------------------------------------------------------------------------------


-- | Monad for elaboration. The 'Int' counts the number of allocated metas.
--   After we throw an error, we annotate it at the innermost point in the
--   syntax where source position information is available from a 'RSrcPos'
--   constructor.
type M e    = StateT (Int, MCxt) (Either (e, Maybe SourcePos))
type ElabM  = M ElabError
type UnifyM = M UnifyError

mapError :: (e -> e') -> M e a -> M e' a
mapError f = hoist (first (first f))

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
--   when unifying and solving metas.
data Val
  = VNe Head [Val]    -- ^ [Val] here is in reverse order, i. e. the first Val in
                      --   the list is applied last to the head.
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

forceM :: Val -> M e Val
forceM v = gets (\(_, ms) -> force ms v)

vApp :: Val -> Val -> Val
vApp (VLam _ t) ~u = t u
vApp (VNe h sp) ~u = VNe h (u:sp)
vApp _           _ = error "vApp: impossible"

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

evalM :: Cxt -> Tm -> M e Val
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

quoteM :: Vals -> Val -> M e Tm
quoteM vs v = gets $ \(_, ms) -> quote ms vs v

nf :: MCxt -> Vals -> Tm -> Tm
nf ms vs = quote ms vs . eval ms vs

nfM :: Vals -> Tm -> M e Tm
nfM vs t = gets $ \(_, ms) -> nf ms vs t


-- Unification
--------------------------------------------------------------------------------

-- | Check that all entries in a spine are bound variables.
checkSp :: [Val] -> UnifyM [Name]
checkSp vs = forM vs $ \v -> forceM v >>= \case
  VVar x -> pure x
  v      -> report SpineError

-- | Scope check + occurs check a solution candidate. Inputs are a meta, a spine
--   of variable names (which comes from checkSp) and a RHS term in normal
--   form. In real implementations it would be a bad idea to solve metas with
--   normal forms (because of size explosion), but here it's the simplest thing
--   we can do. We don't have to worry about shadowing here, because normal
--   forms have no shadowing by our previous quote implementation.
checkSolution :: Meta -> [Name] -> Tm -> UnifyM ()
checkSolution m sp rhs = lift $ go sp rhs where
  go :: [Name] -> Tm -> Either (UnifyError, Maybe SourcePos) ()
  go ns = \case
    Var x    -> unless (elem x ns) $
                  report $ ScopeError m sp rhs x
    App t u  -> go ns t >> go ns u
    Lam x t  -> go (x:ns) t
    Pi x a b -> go ns a >> go (x:ns) b
    U        -> pure ()
    Meta m'  -> when (m == m') $
                  report $ OccursCheck m rhs
    Let{}    -> error "checkSolution: impossible: non-normal term"

solve :: Vals -> Meta -> [Val] -> Val -> UnifyM ()
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


-- | Remove duplicate elements.
ordNub :: Ord a => [a] -> [a]
ordNub = go S.empty where
  go s [] = []
  go s (a:as) | S.member a s = go s as
              | otherwise    = a : go (S.insert a s) as

-- | Create fresh meta, return the meta applied to all bound variables in scope.
newMeta :: Cxt -> ElabM Tm
newMeta Cxt{..} = do
  -- We drop the shadowed variables from the spine.
  let sp = map Var $ ordNub [x | (x, Bound{}) <- _types]
  (i, ms) <- get
  put (i + 1, ms)
  pure (foldr (flip App) (Meta i) sp)


-- | Unify two values. After unification succeeds, the LHS and RHS become
--   definitionally equal in the newly updated metacontext. We only need here
--   the value environment for generating non-shadowing names; with de Bruijn
--   levels we would only need an Int denoting the size of the environment.
unify :: Vals -> Val -> Val -> UnifyM ()
unify = go where
  go vs t u = do
    ms <- gets snd
    case (force ms t, force ms u) of
      (VLam (fresh vs -> x) t, VLam _ t') ->
        go ((x, Nothing):vs) (t (VVar x)) (t' (VVar x))

      -- these two cases implement eta conversion checking for functions
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
      (t, t') -> do
        t  <- quoteM vs t
        t' <- quoteM vs t'
        report (UnifyError t t')

-- Elaboration
--------------------------------------------------------------------------------


check :: Cxt -> Raw -> VTy -> ElabM Tm
check cxt@Cxt{..} topT topA = do
  topA <- forceM topA
  case (topT, topA) of
    (RSrcPos pos t, _) -> addPos pos (check cxt t topA)

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

    -- checking just falls through Let.
    (RLet x a t u, topA) -> do
      a   <- check cxt a VU
      ~va <- evalM cxt a
      t   <- check cxt t va
      ~vt <- evalM cxt t
      u   <- check (define x vt va cxt) u topA
      pure $ Let x a t u

    (RHole, _) ->
      newMeta cxt

    -- we unify the expected and inferred types
    _ -> do
      (t, va) <- infer cxt topT
      ~nTopA <- quoteM _vals topA
      ~nA    <- quoteM _vals va
      mapError (CheckError nTopA nA) (unify _vals va topA)
      pure t

-- | Create a fresh domain and codomain type.
freshPi :: Cxt -> Name -> ElabM (VTy, Val -> VTy)
freshPi cxt@Cxt{..} x = do
  a    <- newMeta cxt
  ~va  <- evalM cxt a
  b    <- newMeta (bind x va cxt)
  mcxt <- gets snd
  pure (va, \u -> eval mcxt ((x, Just u):_vals) b)

infer :: Cxt -> Raw -> ElabM (Tm, VTy)
infer cxt@Cxt{..} = \case
  RSrcPos pos t -> addPos pos (infer cxt t)

  RVar x -> case lookup x _types of
    Nothing -> report $ NameNotInScope x
    Just a  -> pure (Var x, case a of Bound a -> a; Def a -> a)

  RU -> pure (U, VU) -- type-in-type

  -- an upgrade to this would be to also proceed if the inferred type for "t"
  -- is meta-headed, in which case we would need to create two fresh metas and
  -- refine "t"'s type to a function type.
  RApp t u -> do
    (t, va) <- infer cxt t
    -- ensuring that t has function type.
    (a, b) <- forceM va >>= \case
      -- it's already a function
      VPi _ a b ->
        pure (a, b)

      -- if it has a meta-headed type, we only infer a non-dependent function
      -- type, because a dependent one is pretty hopeless with our current
      -- sophistication of unification
      va@(VNe (HMeta x) sp) -> do
        (a, b) <- freshPi cxt "x"
        ~na    <- quoteM _vals va
        mapError
          (ExpectedFunctionFromMeta na)
          (unify _vals va (VPi "x" a b))
        pure (a, b)

      tty -> do
        tty <- quoteM _vals tty
        report $ ExpectedFunction tty
    u   <- check cxt u a
    ~vu <- evalM cxt u
    pure (App t u, b vu)

  -- we infer type for lambdas by checking them with a
  -- a function type made of fresh metas.
  RLam x t -> do
    (a, b) <- freshPi cxt x
    let pi = VPi x a b
    t <- check cxt (RLam x t) pi
    pure (t, pi)

  RPi x a b -> do
    a   <- check cxt a VU
    ~va <- evalM cxt a
    b   <- check (bind x va cxt) b VU
    pure (Pi x a b, VU)

  -- inferring a type for a hole: we create two metas, one for the hole
  -- and one for its type.
  RHole -> do
    t  <- newMeta cxt
    va <- evalM cxt =<< newMeta cxt
    pure (t, va)

  RLet x a t u -> do
    a       <- check cxt a VU
    ~va     <- evalM cxt a
    t       <- check cxt t va
    ~vt     <- evalM cxt t
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

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

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

pBinder :: Parser Name
pBinder = pIdent <|> symbol "_"

pAtom =
      withPos ((    RVar <$> pIdent)
                <|> (RU <$ symbol "U")
                <|> (RHole <$ symbol "_"))
  <|> parens pTm

pSpine = foldl1 RApp <$> some pAtom

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
  symbol "let"
  x <- pIdent
  symbol ":"
  a <- pTm
  symbol "="
  t <- pTm
  symbol "in"
  u <- pTm
  pure $ RLet x a t u

pTm  = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)
pSrc = ws *> pTm <* eof

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
  src <- getContents
  t <- parseString src
  pure (t, src)

-- main
--------------------------------------------------------------------------------

helpMsg = unlines [
  "usage: elabzoo-holes [--help|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & elaborate expression from stdin, print its normal form",
  "  type   : read & elaborate expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getTm = do
  let elab = do
        (t, src) <- getTm
        case (flip evalStateT (0, mempty) $ do
               (t, a) <- infer nil t
               t  <- zonkM [] t
               nt <- nfM [] t
               na <- quoteM [] a
               pure (t, nt, na)) of
          Left err -> displayError src err >> exitSuccess
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
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
