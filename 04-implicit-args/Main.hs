
module Main where

import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.Morph
import Data.Bifunctor
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Char
import Data.Foldable
import Data.Maybe
import Data.Void
import System.Environment
import System.Exit
import Text.Megaparsec
import Text.Printf

import qualified Data.IntMap.Strict         as M
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L


ex1 = main' "elab" $ unlines [

  "let id : {A} -> A -> A = \\x. x in",

  -- by default metas are inserted for implicit arguments, but
  -- (!) can be used to stop insertion at any point. The (id!) expression
  --  has a polymorphic type, {A} → A → A
  "let id2 : {A} → A → A = id (id!) in",

  "let const : {A B} -> A -> B -> A",
  "    = \\x y. x in",

  -- definition types can be omitted
  "let constTy = {A B} → A → B → A in",

  -- explicit id function, used for annotation as in Idris
  "let the : (A : _) -> A -> A = \\_ x. x in",

  -- implicit application follows Agda convention.
  "let namedArgTest = const {B = U} U in",
  "let namedArgTest2 = the constTy (λ x y. x) {B = U} U in",

  -- bool
  "let Bool : U",
  "    = (B : _) -> B -> B -> B in",
  "let true : Bool",
  "    = \\B t f. t in",
  "let false : Bool",
  "    = \\B t f. f in",
  "let not : Bool -> Bool",
  "    = \\b B t f. b B f t in",

  -- lists
  "let List : U -> U",
  "    = \\A. (L : _) -> (A -> L -> L) -> L -> L in",
  "let nil : {A} -> List A",
  "    = \\L cons nil. nil in",
  "let cons : {A} -> A -> List A -> List A",
  "    = \\x xs L cons nil. cons x (xs L cons nil) in",
  "let map : {A B} -> (A -> B) -> List A -> List B",
  "    = \\{A}{B} f xs L c n. xs L (\\a. c (f a)) n in",
  "let list1 : List Bool",
  "    = cons true (cons false (cons true nil)) in",

  -- using ! when mapping over lists
  -- idlist has type "List ({A} -> A -> A)"
  "let idlist = map (const (id!)) list1 in",

  -- dependent function composition
  "let comp : {A}{B : A -> U}{C : {a} -> B a -> U}",
  "           (f : {a}(b : B a) -> C b)",
  "           (g : (a : A) -> B a)",
  "           (a : A)",
  "           -> C (g a)",
  "    = \\f g a. f (g a) in",

  "let compExample = comp (cons true) (cons false) nil in",

  -- nat
  "let Nat : U",
  "    = (N : U) -> (N -> N) -> N -> N in",
  "let mul : Nat -> Nat -> Nat",
  "    = \\a b N s z. a _ (b _ s) z in",
  "let ten : Nat",
  "    = \\N s z. s (s (s (s (s (s (s (s (s (s z))))))))) in",
  "let hundred = mul ten ten in",

  -- Leibniz equality
  "let Eq : {A} -> A -> A -> U",
  "    = \\{A} x y. (P : A -> U) -> P x -> P y in",
  "let refl : {A}{x : A} -> Eq x x",
  "    = \\_ px. px in",

  "the (Eq (mul ten ten) hundred) refl"
  ]


--------------------------------------------------------------------------------

type Name = String

data Icit = Impl | Expl deriving (Eq, Show)

icit :: Icit -> a -> a -> a
icit Impl i e = i
icit Expl i e = e

-- | Elaboration input contains holes which are filled in the output.
data Raw
  = RVar Name
  | RLam Name (Either Name Icit) Raw
  | RApp Raw Raw (Either Name Icit)
  | RU
  | RPi Name Icit Raw Raw
  | RLet Name Raw Raw Raw
  | RHole
  | RStopInsertion Raw
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
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | U
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta Meta

data Head = HMeta Meta | HVar Name deriving Eq

-- | We use a spine form for neutral values, i.e. we have the head variable and
--   all arguments in a list. We need convenient access to both head and spine
--   when unifying and when solving metas.
data Val
  = VNe Head [(Val, Icit)]
           -- [(Val, Icit)] here is in reverse order, i. e. the first Val in
           -- the list is applied last to the head. Note that spine entries are
           -- lazy because we use lazy lists and tuples (we have Strict pragma
           -- otherwise!)
  | VLam Name Icit (Val -> Val)
  | VPi Name Icit ~Val (Val -> Val)
  | VU

type Bind a = (Name, a)
type Sub  a = [Bind a]

pattern VVar :: Name -> Val
pattern VVar x = VNe (HVar x) []

pattern VMeta :: Meta -> Val
pattern VMeta m = VNe (HMeta m) []

-- | Option for behavior of meta insertion for implicit arguments.
data MetaInsertion
  = MIYes            -- ^ Try to insert metas.
  | MINo             -- ^ Don't try to insert metas.
  | MIUntilName Name -- ^ Try to insert metas, but only until
                     --   a specific named implicit argument.

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
  | NoNamedImplicitArg Name
  | CannotInferNamedLam
  | IcitMismatch Icit Icit

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
    NoNamedImplicitArg x -> printf
      "No named implicit argument with name %s." x
    CannotInferNamedLam ->
      "No type can be inferred for lambda with named implicit argument."
    IcitMismatch i i' -> printf (
      "Function icitness mismatch: expected %s, got %s.")
      (show i) (show i')

report :: MonadError (e, Maybe SourcePos) m => e -> m a
report e = throwError (e, Nothing)

--------------------------------------------------------------------------------

-- | Evaluation is up to a metacontext, so whenever we inspect a value during
--   elaboration, we always have to force it first, i.e. unfold solved metas and
--   compute until we hit a rigid head.
force :: MCxt -> Val -> Val
force ms = \case
  VNe (HMeta m) sp | Just t <- M.lookup m ms ->
    force ms (foldr (\(u, i) v -> vApp v u i) t sp)
  v -> v

forceM :: Val -> M e Val
forceM v = gets (\(_, ms) -> force ms v)

vApp :: Val -> Val -> Icit -> Val
vApp (VLam _ _ t) u i = t u
vApp (VNe h sp)   u i = VNe h ((u, i):sp)
vApp _            _ i = error "vApp: impossible"

eval :: MCxt -> Vals -> Tm -> Val
eval ms = go where
  go vs = \case
    Var x       -> maybe (VVar x) id (fromJust $ lookup x vs)
    Meta m      -> maybe (VMeta m) id (M.lookup m ms)
    App t u i   -> vApp (go vs t) (go vs u) i
    Lam x i t   -> VLam x i (\u -> go ((x, Just u):vs) t)
    Pi x i a b  -> VPi x i (go vs a) (\u -> go ((x, Just u):vs) b)
    Let x _ t u -> go ((x, Just (go vs t)):vs) u
    U           -> VU

evalM :: Cxt -> Tm -> M e Val
evalM cxt t = gets (\(_, ms) -> eval ms (_vals cxt) t)

-- |  Quote into fully forced normal forms.
quote :: MCxt -> Vals -> Val -> Tm
quote ms = go where
  go vs v = case force ms v of
    VNe h sp -> foldr (\(v, i) acc -> App acc (go vs v) i)
                      (case h of HMeta m -> Meta m; HVar x -> Var x)
                      sp
    VLam (fresh vs -> x) i t ->
      Lam x i (go ((x, Nothing):vs) (t (VVar x)))
    VPi (fresh vs -> x) i a b ->
      Pi x i (go vs a) (go ((x, Nothing):vs) (b (VVar x)))
    VU -> U

quoteM :: Vals -> Val -> M e Tm
quoteM vs v = gets $ \(_, ms) -> quote ms vs v

nf :: MCxt -> Vals -> Tm -> Tm
nf ms vs = quote ms vs . eval ms vs

nfM :: Vals -> Tm -> ElabM Tm
nfM vs t = gets $ \(_, ms) -> nf ms vs t


-- Unification
--------------------------------------------------------------------------------

-- | Check that all entries in a spine are bound variables.
checkSp :: [Val] -> UnifyM [Name]
checkSp vs = forM vs $ \v -> forceM v >>= \case
  VVar x -> pure x
  _      -> report SpineError

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
    Var x      -> unless (elem x ns) $
                    report $ ScopeError m sp rhs x
    App t u _  -> go ns t >> go ns u
    Lam x i t  -> go (x:ns) t
    Pi x i a b -> go ns a >> go (x:ns) b
    U          -> pure ()
    Meta m'    -> when (m == m') $
                    report $ OccursCheck m rhs
    Let{}      -> error "impossible"

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
  rhs <- evalM nil (foldl' (\t x -> Lam x Expl t) rhs sp)

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
  pure (foldr (\u t -> App t u Expl) (Meta i) sp)

-- | Unify two values. After unification succeeds, the LHS and RHS become
--   definitionally equal in the newly updated metacontext. We only need here
--   the value environment for generating non-shadowing names; with de Bruijn
--   levels we would only need an Int denoting the size of the environment.
unify :: Vals -> Val -> Val -> UnifyM ()
unify = go where
  go :: Vals -> Val -> Val -> UnifyM ()
  go vs t u = do
    ms <- gets snd
    case (force ms t, force ms u) of
      (VLam (fresh vs -> x) i t, VLam _ i' t') | i == i'-> do
        go ((x, Nothing):vs) (t (VVar x)) (t' (VVar x))

      -- these two lines implement eta conversion for functions
      (VLam (fresh vs -> x) i t, u) ->
        go ((x, Nothing):vs) (t (VVar x)) (vApp u (VVar x) i)
      (u, VLam (fresh vs -> x) i t) ->
        go ((x, Nothing):vs) (vApp u (VVar x) i) (t (VVar x))

      (VPi (fresh vs -> x) i a b, VPi _ i' a' b') -> do
        go vs a a'
        go ((x, Nothing):vs) (b (VVar x)) (b' (VVar x))

      (VU, VU) -> pure ()
      (VNe h sp, VNe h' sp') | h == h' -> zipWithM_ (go vs) (fst <$> sp) (fst <$> sp')
      (VNe (HMeta m) sp, t) -> solve vs m (fst <$> sp) t
      (t, VNe (HMeta m) sp) -> solve vs m (fst <$> sp) t
      (t, t') -> do
        t  <- quoteM vs t
        t' <- quoteM vs t'
        report (UnifyError t t')

-- Elaboration
--------------------------------------------------------------------------------

-- | Modify an elaboration action by (possibly) trying to insert
--   fresh metas for implicit arguments after performing the action.
insertMetas :: MetaInsertion -> Cxt -> ElabM (Tm, VTy) -> ElabM (Tm, VTy)
insertMetas ins cxt action = case ins of
  -- do nothing extra
  MINo  -> action
  -- insert a fresh meta for every implicit Pi argument
  MIYes -> do
    (t, va) <- action
    let go t va = forceM va >>= \case
          VPi x Impl a b -> do
            m  <- newMeta cxt
            mv <- evalM cxt m
            go (App t m Impl) (b mv)
          va -> pure (t, va)
    go t va
  -- insert a fresh meta for every implicit Pi argument, until we hit
  -- an implicit arg with the given name
  MIUntilName x -> do
    (t, va) <- action
    let go t va = forceM va >>= \case
          va@(VPi x' Impl a b) -> do
            if x == x' then
              pure (t, va)
            else do
              m  <- newMeta cxt
              mv <- evalM cxt m
              go (App t m Impl) (b mv)
          _ -> report (NoNamedImplicitArg x)
    go t va

addPos :: SourcePos -> ElabM a -> ElabM a
addPos pos ma =
  catchError ma $ \(msg, mpos) -> throwError (msg, mpos <|> Just pos)

check :: Cxt -> Raw -> VTy -> ElabM Tm
check cxt@Cxt{..} topT topA = case (topT, topA) of
  (RSrcPos pos t, _) -> addPos pos (check cxt t topA)

  -- if the icitness of the lambda matches the Pi type,
  -- check the lambda body as usual
  (RLam x ni t, VPi x' i' a b) | either (\x -> x == x' && i' == Impl) (==i') ni -> do
    let v    = VVar (fresh _vals x)
        cxt' = Cxt ((x, Just v):_vals) ((x, Bound a):_types)
    Lam x i' <$> check cxt' t (b v)

  -- otherwise if the Pi is implicit, insert a new implicit lambda
  (t, VPi x Impl a b) -> do
    let x' = fresh _vals x
    Lam x' Impl <$> check (bind x' a cxt) t (b (VVar x'))

  (RLet x a t u, topA) -> do
    a   <- check cxt a VU
    ~va <- evalM cxt a
    t   <- check cxt t va
    ~vt <- evalM cxt t
    u   <- check (define x vt va cxt) u topA
    pure $ Let x a t u

  (RHole, _) ->
    newMeta cxt

  _ -> do
    (t, va) <- infer MIYes cxt topT
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

infer :: MetaInsertion -> Cxt -> Raw -> ElabM (Tm, VTy)
infer ins cxt@Cxt{..} = \case
  RSrcPos pos t -> addPos pos (infer ins cxt t)

  RVar x -> insertMetas ins cxt $ case lookup x _types of
    Nothing -> report $ NameNotInScope x
    Just a  -> pure (Var x, case a of Bound a -> a; Def a -> a)

  RU -> pure (U, VU)

  RApp t u ni -> insertMetas ins cxt $ do
    let (insertion, i) = case ni of
          Left x  -> (MIUntilName x, Impl)
          Right i -> (icit i MINo MIYes, i)
    (t, va) <- infer insertion cxt t
    (a, b) <- forceM va >>= \case
      VPi x i' a b -> do
        unless (i == i') $
          report $ IcitMismatch i i'
        pure (a, b)
      va@(VNe (HMeta x) sp) -> do
        (a, b) <- freshPi cxt "x"
        ~na <- quoteM _vals va
        mapError
          (ExpectedFunctionFromMeta na)
          (unify _vals va (VPi "x" i a b))
        pure (a, b)
      tty -> do
        tty <- quoteM _vals tty
        report $ ExpectedFunction tty
    u <- check cxt u a
    ~vu <- evalM cxt u
    pure (App t u i, b vu)

  -- we infer type for lambdas by checking them with a
  -- a function type made of fresh metas.
  RLam _ Left{} _ ->
    report $ CannotInferNamedLam

  RLam x (Right i) t -> insertMetas ins cxt $ do
    (a, b) <- freshPi cxt x
    let pi = VPi x i a b
    t <- check cxt (RLam x (Right i) t) pi
    pure (t, pi)

  RPi x i a b -> do
    a   <- check cxt a VU
    ~va <- evalM cxt a
    b   <- check (bind x va cxt) b VU
    pure (Pi x i a b, VU)

  -- inferring a type for a hole: we create two metas, one for the hole
  -- and one for its type.
  RHole -> do
    t   <- newMeta cxt
    ~va <- evalM cxt =<< newMeta cxt
    pure (t, va)

  RLet x a t u -> do
    a        <- check cxt a VU
    ~va      <- evalM cxt a
    t        <- check cxt t va
    ~vt      <- evalM cxt t
    (!u, vb) <- infer ins (define x vt va cxt) u
    pure (Let x a t u, vb)

  RStopInsertion t ->
    infer MINo cxt t


-- | Inline all meta solutions. Used for displaying elaboration output.
zonk :: MCxt -> Vals -> Tm -> Tm
zonk ms = go where

  goSp :: Vals -> Tm -> Either Val Tm
  goSp vs = \case
    Meta m | Just v <- M.lookup m ms -> Left v
    App t u ni -> either (\t -> Left (vApp t (eval ms vs u) ni))
                         (\t -> Right (App t (go vs u) ni))
                         (goSp vs t)
    t -> Right (go vs t)

  go :: Vals -> Tm -> Tm
  go vs = \case
    Var x        -> Var x
    Meta m       -> maybe (Meta m) (quote ms vs) (M.lookup m ms)
    U            -> U
    Pi x i a b   -> Pi x i (go vs a) (go ((x, Nothing):vs) b)
    App t u ni   -> either (\t -> quote ms vs (vApp t (eval ms vs u) ni))
                           (\t -> App t (go vs u) ni)
                           (goSp vs t)
    Lam x i t    -> Lam x i (go ((x, Nothing):vs) t)
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

  go :: Bool -> Tm -> ShowS
  go p  = \case
    Var x -> (x++)
    Meta i -> ("?"++).(show i++)
    Let x a t u ->
      ("let "++) . (x++) . (" : "++) . go False  a . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False u
    App (App t u i) u' i' ->
      showParen p (go False  t . (' ':) . goArg  u i . (' ':) . goArg  u' i')
    App t u i  -> showParen p (go True  t . (' ':) . goArg  u i)
    Lam x i t  -> showParen p (("λ "++) . goLamBind x i . goLam t)
    t@Pi{}     -> showParen p (goPi False  t)
    U          -> ("U"++)

  goArg :: Tm -> Icit -> ShowS
  goArg t i = icit i (bracket (go False t)) (go True t)

  bracket :: ShowS -> ShowS
  bracket s = ('{':).s.('}':)

  goPiBind :: Name -> Icit -> Tm -> ShowS
  goPiBind x i a =
    icit i bracket (showParen True) ((x++) . (" : "++) . go False a)

  goPi :: Bool -> Tm -> ShowS
  goPi p (Pi x i a b)
    | x /= "_" = goPiBind x i a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; _ -> True) a .
       (" → "++) . go False b
  goPi p t = (if p then (" -> "++) else id) . go False t

  goLamBind :: Name -> Icit -> ShowS
  goLamBind x i = icit i bracket id ((if null x then "_" else x) ++)

  goLam :: Tm -> ShowS
  goLam (Lam x i t) = (' ':) . goLamBind x i . goLam t
  goLam t = (". "++) . go False t

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
braces p   = char '{' *> p <* char '}'
pArrow     = symbol "→" <|> symbol "->"
pBind      = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pAtom :: Parser Raw
pAtom  =
      withPos (    (RVar <$> pIdent)
               <|> (RU <$ char 'U')
               <|> (RHole <$ char '_'))
  <|> parens pTm

pArg :: Parser (Maybe (Either Name Icit, Raw))
pArg = (Nothing <$ char '!')
  <|>  (Just <$> (
           (try $ braces $ do {x <- pIdent; char '='; t <- pTm; pure (Left x, t)})
       <|> ((Right Impl,) <$> (char '{' *> pTm <* char '}'))
       <|> ((Right Expl,) <$> pAtom)))

pSpine :: Parser Raw
pSpine = do
  h <- pAtom
  args <- many pArg
  pure $ foldl
    (\t -> \case Nothing     -> RStopInsertion t
                 Just (i, u) -> RApp t u i)
    h args

pLamBinder :: Parser (Name, Either Name Icit)
pLamBinder =
      ((,Right Expl) <$> pBind)
  <|> try ((,Right Impl) <$> braces pBind)
  <|> braces (do {x <- pIdent; char '='; y <- pBind; pure (y, Left x)})

pLam :: Parser Raw
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTm
  pure $ foldr (uncurry RLam) t xs

pPiBinder :: Parser ([Name], Raw, Icit)
pPiBinder =
      braces ((,,Impl) <$> some pBind
                       <*> ((char ':' *> pTm) <|> pure RHole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (char ':' *> pTm))
pPi :: Parser Raw
pPi = do
  dom <- some pPiBinder
  pArrow
  cod <- pTm
  pure $ foldr (\(xs, a, i) t -> foldr (\x -> RPi x i a) t xs) cod dom

pFunOrSpine :: Parser Raw
pFunOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" Expl sp <$> pTm

pLet :: Parser Raw
pLet = do
  symbol "let"
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol "in"
  u <- pTm
  pure $ RLet x (maybe RHole id ann) t u

pTm :: Parser Raw
pTm = withPos (pLam <|> pLet <|> try pPi <|> pFunOrSpine)

pSrc :: Parser Raw
pSrc = ws *> pTm <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
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
  "usage: holes [--help|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & elaborate expression from stdin, print its normal form",
  "  type   : read & elaborate expression from stdin, print its type"]

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

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getTm = do
  let elab = do
        (t, src) <- getTm
        case (flip evalStateT (0, mempty) $ do
               (t, a) <- infer MIYes nil t
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
    _          -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
