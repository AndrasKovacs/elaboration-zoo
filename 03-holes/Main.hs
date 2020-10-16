{-# options_ghc -Wno-missing-pattern-synonym-signatures #-}

module Main where

import Control.Applicative hiding (many, some)
import Control.Exception hiding (try)
import Control.Monad
import Data.Char
import Data.IORef
import Data.Void
import System.Environment
import System.Exit
import System.IO.Unsafe
import Text.Megaparsec
import Text.Printf

import qualified Data.IntMap                as IM
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L


-- examples
--------------------------------------------------------------------------------

-- main' "elab" prints the input, but with holes filled by inferred values or
-- unsolved metas
ex1 = main' "elab" $ unlines [
  "let id : (A : U) -> A -> A",
  "      = \\A x. x;",
  "let id2 : (A : _) -> A -> A",
  "      = \\A x. id _ x;",
  "id"
  ]

-- example output which contains unsolved meta, as "?2 A x" in
-- id2. This means that "?2" is the second hole in the expression,
-- and is in a scope with "A" and "x" as bound variables.
ex2 = main' "elab" $ unlines [
  "let id : (A : U) -> A -> A",
  "      = \\A x. x ;",
  "let id2 : (A : _) -> A -> A",
  "      = \\A x. id _ _ ;",
  "id2"
  ]

-- ex3 = parseString $ unlines [
ex3 = main' "elab" $ unlines [
  "let id : (A : _) -> A -> A",
  "    = \\A x. x ;",
  "let List : U -> U",
  "    = \\A. (L : _) -> (A -> L -> L) -> L -> L ;",
  "let nil : (A : _) -> List A",
  "    = \\A L cons nil. nil ;",
  "let cons : (A : _) -> A -> List A -> List A",
  "    = \\A x xs L cons nil. cons x (xs _ cons nil) ;",
  "let Bool : U",
  "    = (B : _) -> B -> B -> B ;",
  "let true : Bool",
  "    = \\B t f. t ;",
  "let false : Bool",
  "    = \\B t f. f ;",
  "let not : Bool -> Bool",
  "    = \\b B t f. b B f t ;",
  "let list1 : List Bool",
  "    = cons _ (id _ true) (nil _) ;",
  "let Eq : (A : _) -> A -> A -> U",
  "    = \\A x y. (P : A -> U) -> P x -> P y ;",
  "let refl : (A : _)(x : A) -> Eq A x x",
  "    = \\A x P px. px ;",
  "\\x. refl _ (cons _ true true)"
  ]


-- Metacontext
--------------------------------------------------------------------------------

data MetaEntry = Solved Val | Unsolved

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMeta #-}

mcxt :: IORef (IM.IntMap MetaEntry)
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty

-- Snoc
--------------------------------------------------------------------------------

infixl 4 :>
pattern xs :> x = x : xs
{-# complete (:>), [] #-}

foldList :: b -> (b -> a -> b) -> [a] -> b
foldList nil snoc = foldr (flip snoc) nil

-- Raw syntax
--------------------------------------------------------------------------------

-- | De Bruijn index.
newtype Ix  = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

-- | Metavariable.
newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

type Name = String

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU                     -- U
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLet Name Raw Raw Raw  -- let x : A = t in u
  | RSrcPos SourcePos Raw  -- source position for error reporting
  | RHole                  -- _
  deriving Show

-- Core syntax
--------------------------------------------------------------------------------

data BD = Bound | Defined
  deriving Show

type Ty = Tm

data Tm
  = Var Ix
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]    -- optimized representation of inserted metas
  deriving Show

-- Evaluation
--------------------------------------------------------------------------------

type Env     = [Val]
type Spine   = [Val]
data Closure = Closure Env Tm
type VTy     = Val

data Val
  = VFlex MetaVar Spine
  | VRigid Lvl Spine
  | VLam Name {-# unpack #-} Closure
  | VPi Name ~VTy {-# unpack #-} Closure
  | VU

pattern VVar  x = VRigid x []
pattern VMeta m = VFlex m []

infixl 8 $$
($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (env :> u) t

vVar :: Env -> Ix -> Val
vVar (_  :> a) 0 = a
vVar (as :> _) n = vVar as (n - 1)
vVar _         _ = error "impossible"

vApp :: Val -> Val -> Val
vApp t ~u = case t of
  VLam _ t    -> t $$ u
  VFlex  m sp -> VFlex m (sp :> u)
  VRigid x sp -> VRigid x (sp :> u)
  _           -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  []      -> t
  sp :> u -> vAppSp t sp `vApp` u

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vAppBDs env v bds `vApp` t
  (env :> t , bds :> Defined) -> vAppBDs env v bds
  _                           -> error "impossible"

eval :: Env -> Tm -> Val
eval env = \case
  Var x              -> vVar env x
  App t u            -> vApp (eval env t) (eval env u)
  Lam x t            -> VLam x (Closure env t)
  Pi x a b           -> VPi x (eval env a) (Closure env b)
  Let x _ t u        -> eval (env :> eval env t) u
  U                  -> VU
  Meta m             -> vMeta m
  InsertedMeta m bds -> vAppBDs env (vMeta m) bds

force :: Val -> Val
force = \case
  VFlex m sp | Solved t <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []      -> t
  sp :> u -> App (quoteSp l t sp) (quote l u)

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m sp  -> quoteSp l (Meta m) sp
  VRigid x sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VLam x t    -> Lam x (quote (l + 1) (t $$ VVar l))
  VPi  x a b  -> Pi x (quote l a) (quote (l + 1) (b $$ VVar l))
  VU          -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)

-- Unification/metas
--------------------------------------------------------------------------------

freshMeta :: Cxt -> IO Tm
freshMeta cxt = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  modifyIORef' mcxt $ IM.insert m Unsolved
  pure $ InsertedMeta (MetaVar m) (bds cxt)

data PartialRenaming = PRen {
    dom :: Lvl
  , cod :: Lvl
  , ren :: IM.IntMap Lvl}

lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

invert :: Lvl -> Spine -> IO PartialRenaming
invert cod sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []        = pure (0, mempty)
      go (sp :> t) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _ -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom cod ren

rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []        = pure t
  goSp pren t (sp :> u) = App <$> goSp pren t sp <*> go pren u

  go :: PartialRenaming -> Val -> IO Tm
  go pren t = case force t of
    VFlex m' sp | m == m'   -> throwIO UnifyError
                | otherwise -> goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x t  -> Lam x <$> go (lift pren) (t $$ VVar (cod pren))
    VPi x a b -> Pi x <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren))
    VU        -> pure U

-- | lams : (Γ : Con) → Tm Γ A → Tm ∙ (Γ ⇒ A)
lams :: Lvl -> Tm -> Tm
lams l = go 0 where
  go x t | x == l = t
  go x t = Lam ("x"++show (x+1)) $ go (x + 1) t

solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do                           -- rhs : Val Γ A
  pren <- invert gamma sp                           -- ren : Ren Δ Γ
  rhs  <- rename m pren rhs                         -- rhs : Tm Δ A[ren]
  let solution = eval [] $ lams (dom pren) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]     , []       ) -> pure ()
  (sp :> t, sp' :> t') -> unifySp l sp sp' >> unify l t t'
  _                    -> throwIO UnifyError

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VLam _ t   , VLam _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ t'    ) -> unify (l + 1) (t `vApp` VVar l) (t' $$ VVar l)
  (VLam _ t   , t'           ) -> unify (l + 1) (t $$ VVar l) (t' `vApp` VVar l)
  (VU         , VU           ) -> pure ()
  (VPi x a b  , VPi x' a' b' ) -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp') | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp' ) | m == m' -> unifySp l sp sp'
  (VFlex m sp , t'           ) -> solve l m sp t'
  (t          , VFlex m' sp' ) -> solve l m' sp' t
  _                            -> throwIO UnifyError

-- Elaboration
--------------------------------------------------------------------------------

type Types = [(String, VTy)]

data Cxt = Cxt {
    env   :: Env           -- evaluation
  , lvl   :: Lvl           -- evaluation
  , types :: Types         -- raw name lookup, printing
  , bds   :: [BD]          -- fresh meta creation
  , pos   :: SourcePos     -- error reporting
  }

instance Show Cxt where
  show = show . cxtNames

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] 0 [] []

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l types bds pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, a)) (bds :> Bound) pos

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Val -> VTy -> Cxt
define (Cxt env l types bds pos) x ~t ~a  =
  Cxt (env :> t) (l + 1) (types :> (x, a)) (bds :> Defined) pos

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)

unifyCatch :: Cxt -> Val -> Val -> IO ()
unifyCatch cxt t t' =
  unify (lvl cxt) t t'
  `catch` \UnifyError ->
    throwIO $ Error cxt $ CantUnify (quote (lvl cxt) t) (quote (lvl cxt) t')

check :: Cxt -> Raw -> VTy -> IO Tm
check cxt t a = case (t, force a) of
  (RSrcPos pos t, a) ->
    check (cxt {pos = pos}) t a

  (RLam x t, VPi _ a b) ->
    Lam x <$> check (bind cxt x a) t (b $$ VVar (lvl cxt))

  (RLet x a t u, a') -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x vt va) u a'
    pure (Let x a t u)

  (RHole, a) ->
    freshMeta cxt

  (t, expected) -> do
    (t, inferred) <- infer cxt t
    unifyCatch cxt expected inferred
    pure t

infer :: Cxt -> Raw -> IO (Tm, VTy)
infer cxt = \case
  RSrcPos pos t ->
    infer (cxt {pos = pos}) t

  RVar x -> do
    let go ix (types :> (x', a))
          | x == x'   = pure (Var ix, a)
          | otherwise = go (ix + 1) types
        go ix [] =
          throwIO $ Error cxt $ NameNotInScope x

    go 0 (types cxt)

  RLam x t -> do
    a      <- eval (env cxt) <$> freshMeta cxt
    (t, b) <- infer (bind cxt x a) t
    pure (Lam x t, VPi x a $ closeVal cxt b)

  RApp t u -> do
    (t, tty) <- infer cxt t

    -- ensure that tty is Pi
    (a, b) <- case force tty of
      VPi x a b ->
        pure (a, b)
      tty -> do
        a <- eval (env cxt) <$> freshMeta cxt
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" a)
        unifyCatch cxt tty (VPi "x" a b)
        pure (a, b)

    u <- check cxt u a
    pure (App t u, b $$ eval (env cxt) u)

  RU ->
    pure (U, VU)

  RPi x a b -> do
    a <- check cxt a VU
    b <- check (bind cxt x (eval (env cxt) a)) b VU
    pure (Pi x a b, VU)

  RLet x a t u -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    (u, b) <- infer (define cxt x vt va) u
    pure (Let x a t u, b)

  RHole -> do
    a <- eval (env cxt) <$> freshMeta cxt
    t <- freshMeta cxt
    pure (t, a)


-- printing
--------------------------------------------------------------------------------

cxtNames :: Cxt -> [Name]
cxtNames = fmap fst . types

showVal :: Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (cxtNames cxt) (quote (lvl cxt) v) []

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

  goBDS :: Int -> [Name] -> MetaVar -> [BD] -> ShowS
  goBDS p ns m bds = case (ns, bds) of
    ([]      , []             ) -> (("?"++show m)++)
    (ns :> n , bds :> Bound   ) -> par p appp $ goBDS appp ns m bds . (' ':) . (n++)
    (ns :> n , bds :> Defined ) -> goBDS appp ns m bds
    _                           -> error "impossible"

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var (Ix x)                -> ((ns !! x)++)

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    Lam (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (ns:>x) t where
                                   goLam ns (Lam x t) = (' ':) . (x++) . goLam (ns:>x) t
                                   goLam ns t         = (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip (ns:>"_") b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (ns:>x) b where
                                   goPi ns (Pi x a b) | x /= "_" = piBind ns x a . goPi (ns:>x) b
                                   goPi ns b = (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n  = "++) . go letp ns t . (";\n\n"++) . go letp (ns:>x) u

    Meta m                    -> (("?"++show m)++)
    InsertedMeta m bds        -> goBDS p ns m bds

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

displayMetas :: IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(m, e) -> case e of
    Unsolved -> printf "let ?%s = ?;\n" (show m)
    Solved v -> printf "let ?%s = %s;\n" (show m) (showTm0 $ quote 0 v)
  putStrLn ""

-- errors
--------------------------------------------------------------------------------

data UnifyError = UnifyError
  deriving (Show, Exception)

data ElabError = NameNotInScope Name | CantUnify Tm Tm
  deriving (Show, Exception)

data Error = Error Cxt ElabError
  deriving (Show, Exception)

displayError :: String -> Error -> IO ()
displayError file (Error cxt e) = do

  let SourcePos path (unPos -> linum) (unPos -> colnum) = pos cxt
      lnum = show linum
      lpad = map (const ' ') lnum
      msg = case e of
        NameNotInScope x ->
          "Name not in scope: " ++ x
        CantUnify t t'   ->
          ("Cannot unify expected type\n\n" ++
           "  " ++ showTm cxt t ++ "\n\n" ++
           "with inferred type\n\n" ++
           "  " ++ showTm cxt t')

  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg


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
keyword x = x == "let" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pAtom :: Parser Raw
pAtom =
      withPos ((RVar <$> pIdent) <|> (RU <$ symbol "U") <|> (RHole <$ symbol "_"))
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
  symbol "let"
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

helpMsg = unlines [
  "usage: elabzoo-holes [--help|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do

  let elab = do
        (t, file) <- getRaw
        infer (emptyCxt (initialPos file)) t
          `catch` \e -> displayError file e >> exitSuccess

  reset
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ nf [] t
      putStrLn "  :"
      putStrLn $ showTm0 $ quote 0 a
    ["type"] -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ quote 0 a
    ["elab"] -> do
      (t, a) <- elab
      displayMetas
      putStrLn $ showTm0 t
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
