

{-

ex1 = main' "elab" $ unlines [

  "let Bool  : U = (B : _) → B → B → B in",
  "let true  : Bool = λB t f. t in",
  "let false : Bool = λ B t f. f in",
  "let not   : Bool → Bool = λ b B t f. b B f t in",

  "let Pair  : U → U → U = λ A B. (P : U) → (A → B → P) → P in",
  "let pair  : {A B} → A → B → Pair A B = λ a b P p. p a b in",
  "let fst   : {A B} → Pair A B → A = λ f. f _ (λ x y. x) in",
  "let snd   : {A B} → Pair A B → B = λ f. f _ (λ x y. y) in",

  "let List   : U → U = λ A. (L : U) → (A → L → L) → L → L in",
  "let nil    : {A} → List A = λ L c n. n in",
  "let cons   : {A} → A → List A → List A = λ A As L c n. c A (As L c n) in",
  "let single : {A} → A → List A = λ A. cons A nil in",
  "let cat    : {A} → List A → List A → List A",
  "             = λ xs ys L c n. xs L c (ys L c n) in",

  "let the    : (A : _) → A → A = λ A x. x in",
  "let id     : {A : U} → A → A = λx. x in",
  "let Nat    : U = (N : U) → (N → N) → N → N in",
  "let zero   : Nat = λ N s z. z in",
  "let inc    : Nat → Nat = λ n N s z. s (n N s z) in",
  "let choose : {A} → A → A → A = λ x y. x in",
  "let auto   : ({A} → A → A) → ({A} → A → A) = λ f. f in",
  "let auto2  : {A} → ({A} → A → A) → A → A = λ f. f in",
  "let tail   : {A} → List A → List A = λ as. as in",
  "let poly   : ({A} → A → A) → Pair Nat Bool = λ f. pair (f zero) (f true) in",
  "let length : {A} → List A → Nat = λ as N s z. as N (λ _. s) z in",
  "let head   : {A} → List A → A = _ in",

  "let ids : List ({A} → A → A) = nil in",
  "let map : {A B} → (A → B) → List A → List B",
  "          = λ f as L c n. as L (λ a. c (f a)) n in",
  "let app : {A B} → (A → B) → A → B = λ f. f in",
  "let revapp : {A B} → A → (A → B) → B = λ a f. f a in",
  "let flip : {A B C} → (A → B → C) → B → A → C = λ f b a. f a b in",

  "let ST = Pair in",
  "let runST : {A} → ({S} → ST S A) → A = λ f. snd (f {U}) in",
  "let argST : {S} → ST S Nat = _ in",

  "let const : {A B} → A → B → A = λ x y. x in",

  ------------------------------------------------------------

  "let test = inc (id zero) in",

  "let test : List ({A} → A → A) = map (const id) (cons true nil) in",

  -- dependent function composition
  "let comp : {A}{B : A → U}{C : {a} → B a → U}",
  "           (f : {a}(b : B a) → C b)",
  "           (g : (a : A) → B a)",
  "           (a : A)",
  "           → C (g a)",
  "    = λ f g a. f (g a) in",

  "let comp2 : {A B C} → (B → C) → (A → B) → A → C",
  "    = λ f g x. f (g x) in",


  -- needs pruning with comp!
  "let compExample : List Bool → List Bool = comp2 (cons true) (cons false) in",

  -- Leibniz equality
  "let Eq : {A} -> A -> A -> U",
  "    = λ{A} x y. (P : A -> U) -> P x -> P y in",
  "let refl : {A}{x : A} -> Eq x x",
  "    = λ _ px. px in",

  -- "the (Eq (mul ten ten) hundred) refl"
  "U"
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

-- | Elaboration problem identifier.
type MId = Int

-- | List of blocked problems.
type Blocking = [MId]

data MetaEntry =

  -- | Unsolved meta
    Unsolved Blocking
  | Solved Val


  -- | Deferred checking, blocking on a 'Meta', blocking others.
  | Check SourcePos Cxt Raw ~VTy MId Blocking
  -- | Solved guarded constant
  | Unguarded Tm ~Val

-- | Metacontext, containing solved and unsolved elaboration problems.
type MCxt = M.IntMap MetaEntry

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
type ElabM = ReaderT SourcePos (StateT (Int, MCxt) (Either (ElabError, SourcePos)))

-- | Empty context.
nil :: Cxt
nil = Cxt [] []

-- | Add a bound variable to context.
bind :: Name -> VTy -> Cxt -> Cxt
bind x a (Cxt vs tys) = Cxt ((x, Nothing):vs) ((x, Bound a):tys)

-- | Add a defined name to context.
define :: Name -> Val -> VTy -> Cxt -> Cxt
define x v a (Cxt vs tys) = Cxt ((x, Just v):vs) ((x, Def a):tys)

getMetaEntry :: MId -> ElabM MetaEntry
getMetaEntry m = gets $ \(_, ms) -> ms M.! m

putMetaEntry :: MId -> MetaEntry -> ElabM ()
putMetaEntry m p = modify' (fmap (M.insert m p))

newMetaEntry :: MetaEntry -> ElabM MId
newMetaEntry p = do
  (i, ms) <- get
  put (i + 1, M.insert i p ms)
  pure i

subscribe :: MId -> MId -> ElabM ()
subscribe x y = do
  getMetaEntry y >>= \case
    Unsolved blocked       -> putMetaEntry y (Unsolved (x:blocked))
    Check pos cxt t a m bs -> putMetaEntry y (Check pos cxt t a m (x:bs))
    _                      -> error "impossible"


-- | Well-typed core terms without holes.
--   We use names everywhere instead of indices or levels.
data Tm
  = Var Name
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | U
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta MId
  | Guarded MId

data Head = HMeta MId | HVar Name | HGuarded MId deriving Eq

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

pattern VMeta :: MId -> Val
pattern VMeta i = VNe (HMeta i) []

pattern VGuarded :: MId -> Val
pattern VGuarded i = VNe (HGuarded i) []

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

data ElabError
  = SpineError Tm
  -- | Meta, spine, rhs, offending variable
  | ScopeError MId [Name] Tm Name
  | OccursCheck MId Tm
  | UnifyError Tm Tm
  | NameNotInScope Name
  -- | Inferred type.
  | ExpectedFunction Tm
  | NoNamedImplicitArg Name
  | CannotInferNamedLam
  | IcitMismatch Icit Icit

instance Show ElabError where
  show = \case
    SpineError t -> printf "Non-variable value in meta spine:\n\n  %s"  (show t)
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
    NameNotInScope x ->
      "Name not in scope: " ++ x
    ExpectedFunction ty ->
      "Expected a function type, instead inferred:\n\n  " ++ show ty
    NoNamedImplicitArg x -> printf
      "No named implicit argument with name %s." x
    CannotInferNamedLam ->
      "No type can be inferred for lambda with named implicit argument."
    IcitMismatch i i' -> printf (
      "Function icitness mismatch: expected %s, got %s.")
      (show i) (show i')

-- report :: MonadError (e, Maybe SourcePos) m => e -> m a
-- report e = throwError (e, Nothing)
report :: ElabError -> ElabM a
report err = do
  pos <- ask
  throwError (err, pos)

--------------------------------------------------------------------------------

forceHead :: MCxt -> Head -> Maybe Val
forceHead m = \case
  HMeta    x | Solved v      <- m M.! x -> Just v
  HGuarded x | Unguarded _ v <- m M.! x -> Just v
  _ -> Nothing

-- | Evaluation is up to a metacontext, so whenever we inspect a value during
--   elaboration, we always have to force it first, i.e. unfold solved metas and
--   compute until we hit a rigid head.
force :: MCxt -> Val -> Val
force m = \case
  VNe h sp | Just t <- forceHead m h ->
    force m (foldr (\(u, i) v -> vApp v u i) t sp)
  v -> v

forceM :: Val -> ElabM Val
forceM v = gets (\(_, ms) -> force ms v)

vApp :: Val -> Val -> Icit -> Val
vApp (VLam _ _ t) u i = t u
vApp (VNe h sp)   u i = VNe h ((u, i):sp)
vApp _            _ i = error "vApp: impossible"

eval :: MCxt -> Vals -> Tm -> Val
eval m = go where
  go vs = \case
    Var x       -> maybe (VVar x) id (fromJust $ lookup x vs)
    Meta x      -> maybe (VMeta x) id (forceHead m (HMeta x))
    Guarded x   -> maybe (VGuarded x) id (forceHead m (HGuarded x))
    App t u i   -> vApp (go vs t) (go vs u) i
    Lam x i t   -> VLam x i (\u -> go ((x, Just u):vs) t)
    Pi x i a b  -> VPi x i (go vs a) (\u -> go ((x, Just u):vs) b)
    Let x _ t u -> go ((x, Just (go vs t)):vs) u
    U           -> VU

evalM :: Cxt -> Tm -> ElabM Val
evalM cxt t = gets (\(_, ms) -> eval ms (_vals cxt) t)

-- |  Quote into fully forced normal forms.
quote :: MCxt -> Vals -> Val -> Tm
quote ms = go where
  go vs v = case force ms v of
    VNe h sp ->
      let h' = case h of
            HMeta x    -> Meta x
            HGuarded x -> Guarded x
            HVar x     -> Var x
      in foldr (\(v, i) acc -> App acc (go vs v) i) h' sp
    VLam (fresh vs -> x) i t ->
      Lam x i (go ((x, Nothing):vs) (t (VVar x)))
    VPi (fresh vs -> x) i a b ->
      Pi x i (go vs a) (go ((x, Nothing):vs) (b (VVar x)))
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
  v      -> do {t <- quoteM [] v; report $ SpineError t}

-- | Scope check + occurs check a solution candidate. Inputs are a meta, a spine
--   of variable names (which comes from checkSp) and a RHS term in normal
--   form. In real implementations it would be a bad idea to solve metas with
--   normal forms (because of size explosion), but here it's the simplest thing
--   we can do. We don't have to worry about shadowing here, because normal
--   forms have no shadowing by our previous quote implementation.
checkSolution :: MId -> [Name] -> Tm -> ElabM ()
checkSolution m sp rhs = go sp rhs where
  go ns = \case
    Var x      -> unless (elem x ns) $ report $ ScopeError m sp rhs x
    App t u _  -> go ns t >> go ns u
    Lam x i t  -> go (x:ns) t
    Pi x i a b -> go ns a >> go (x:ns) b
    U          -> pure ()
    Meta m'    -> when (m == m') $ report $ OccursCheck m rhs
    Guarded _  -> pure ()
    Let{}      -> error "impossible"


solveMeta :: Vals -> MId -> [Val] -> Val -> ElabM ()
solveMeta vs m sp rhs = do


  -- check that spine consists of bound vars
  sp <- checkSp sp
  -- normalize rhs
  rhs <- quoteM vs rhs
  -- scope + ocurs check rhs
  checkSolution m sp rhs

  -- Wrap rhs into lambdas. NOTE: this operation ignores nonlinearity, because
  -- the innermost nonlinear variable occurrence simply shadows the other occurrences.
  rhs <- evalM nil (foldl' (\t x -> Lam x Expl t) rhs sp)



  -- get blocked problems
  blocked <- getMetaEntry m >>= \case
    Unsolved blocked -> pure blocked
    _                -> error "impossible"

  -- add solution to mcxt
  putMetaEntry m (Solved rhs)

  -- unblock problems
  forM_ blocked $ \i -> getMetaEntry i >>= \case
    Check pos cxt t a m' blocked'
      | m == m' -> local (const pos) $ do
          na <- quoteM (_vals cxt) a
          t  <- check cxt t a
          ~v <- evalM cxt t
          putMetaEntry i (Unguarded t v)
      | otherwise -> error "impossible"
    p -> pure ()


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
  let sp = map Var $ ordNub [x | (x, Bound{}) <- _types, x /= "_"]
  i <- newMetaEntry (Unsolved [])
  pure (foldr (\u t -> App t u Expl) (Meta i) sp)

-- | Unify two values. After unification succeeds, the LHS and RHS become
--   definitionally equal in the newly updated metacontext. We only need here
--   the value environment for generating non-shadowing names; with de Bruijn
--   levels we would only need an Int denoting the size of the environment.
unify :: Vals -> Val -> Val -> ElabM ()
unify = go where
  go :: Vals -> Val -> Val -> ElabM ()
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
      (VNe (HMeta m) sp, t) -> solveMeta vs m (fst <$> sp) t
      (t, VNe (HMeta m) sp) -> solveMeta vs m (fst <$> sp) t
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

check :: Cxt -> Raw -> VTy -> ElabM Tm
check cxt@Cxt{..} topT topA = do
  topA <- forceM topA
  case (topT, topA) of
    (RSrcPos pos t, _) -> local (const pos) (check cxt t topA)

    -- if the icitness of the lambda matches the Pi type,
    -- check the lambda body as usual
    (RLam x ni t, VPi x' i' a b) | either (\x -> x == x' && i' == Impl) (==i') ni -> do
      let v    = VVar (fresh _vals x)
          cxt' = Cxt ((x, Just v):_vals) ((x, Bound a):_types)
      Lam x i' <$> check cxt' t (b v)

    -- otherwise if the Pi is implicit, insert a new implicit lambda
    (t, VPi x Impl a b) -> do
      let x' = fresh _vals x ++ "*"
      Lam x' Impl <$> check (bind x' a cxt) t (b (VVar x'))

    -- FUN HACK. When checking with meta-headed type, we try inferring
    -- if that doesn't work, backtrack and block checking on meta.
    (t, VNe h sp) | Just m <- (case h of HMeta m    -> Just m
                                         HGuarded m -> Just m
                                         _          -> Nothing) -> do
      let tryInfer = do
            (t, va) <- infer MIYes cxt topT
            unify _vals va topA
            pure t
          postpone = do
            pos <- ask
            x   <- newMetaEntry (Check pos cxt t topA m [])
            subscribe x m
            pure $ Guarded x

      state <- get
      tryInfer `catchError` \_ -> do
        traceM "catced"
        put state
        postpone


    -- (t, VNe (HMeta m) sp) -> do
    --   pos <- ask
    --   x   <- newMetaEntry (Check pos cxt t topA m [])
    --   subscribe x m
    --   pure $ Guarded x

    -- (t, VNe (HGuarded m) sp) -> do
    --   pos <- ask
    --   x   <- newMetaEntry (Check pos cxt t topA m [])
    --   subscribe x m
    --   pure $ Guarded x

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
      unify _vals va topA
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
  RSrcPos pos t -> local (const pos) (infer ins cxt t)

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

  -- special casing let inference
  RLet x RHole t u -> do
    (t, a)   <- infer MIYes cxt t
    ~vt      <- evalM cxt t
    (!u, vb) <- infer ins (define x vt a cxt) u
    a        <- quoteM _vals a
    pure (Let x a t u, vb)

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
    Meta x -> case ms M.! x of
      Solved v -> Left v
      _        -> Right (Meta x)
    Guarded x -> case ms M.! x of
      Unguarded t _ -> Right (go vs t)
      _             -> Right (Guarded x)
    App t u ni ->
      either (\t -> Left (vApp t (eval ms vs u) ni))
             (\t -> Right (App t (go vs u) ni))
             (goSp vs t)
    t -> Right (go vs t)

  go :: Vals -> Tm -> Tm
  go vs = \case
    Var x        -> Var x
    Meta x       -> case ms M.! x of
                     Solved v    -> quote ms vs v
                     _           -> Meta x
    Guarded x    -> case ms M.! x of
                     Unguarded t _ -> (go vs t)
                     _             -> Guarded x
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
    Guarded x -> ("?"++).(show x++)
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

displayError :: String -> (ElabError, SourcePos) -> IO ()
displayError file (msg, SourcePos path (unPos -> linum) (unPos -> colnum)) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n\n" (show msg)

pos0 :: SourcePos
pos0 = initialPos "(stdin)"

runElab0 :: ElabM a -> Either (ElabError, SourcePos) a
runElab0 ma = evalStateT (runReaderT ma pos0) (0, mempty)

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getTm = do

  let elab :: IO (Tm, Tm, Tm)
      elab = do
        (t, src) <- getTm
        let res = runElab0 $ do
               (t, a) <- infer MIYes nil t
               t  <- zonkM [] t
               nt <- nfM [] t
               na <- quoteM [] a
               pure (t, nt, na)
        case res of
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
-}

main = undefined
