{-# options_ghc -Wno-missing-pattern-synonym-signatures #-}

module Main where

import Control.Applicative hiding (many, some)
import Control.Exception hiding (try)
import Control.Monad
import Data.Char
import Data.IORef
import Data.Void
import GHC.Stack
import System.Environment
import System.Exit
import System.IO.Unsafe
import Text.Megaparsec
import Text.Printf

import qualified Data.IntMap                as IM
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

-- Metacontext
--------------------------------------------------------------------------------

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

data MetaEntry = Solved Val | Unsolved ~VTy

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMeta #-}

mcxt :: IORef (IM.IntMap MetaEntry)
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

impossible :: HasCallStack => a
impossible = error "impossible"

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> impossible

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty

-- Snoc
--------------------------------------------------------------------------------

infixl 4 :>
pattern xs :> x <- x:xs where (:>) xs ~x = x:xs
{-# complete (:>), [] #-}

-- Raw syntax
--------------------------------------------------------------------------------

type Name = String

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU                     -- U
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLet Name Raw Raw Raw  -- let x : A = t; u
  | RSrcPos SourcePos Raw  -- source position for error reporting
  | RHole                  -- _
  | RTop                   -- Top
  | Rtt                    -- tt
  deriving Show

-- Core syntax
--------------------------------------------------------------------------------

-- | De Bruijn index.
newtype Ix = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

data BD = Bound | Defined
  deriving Show

type Ty = Tm

data Tm
  = Var Ix
  | Lam Name ~Ty Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]
  | Top
  | Tt
  deriving Show

-- Evaluation
--------------------------------------------------------------------------------

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

type Env     = [Val]
type Spine   = [Val]
data Closure = Closure Env Tm deriving Show
type VTy     = Val

data Val
  = VFlex MetaVar Spine ~VTy
  | VRigid Lvl Spine ~VTy
  | VLam Name ~VTy {-# unpack #-} Closure
  | VPi Name ~VTy {-# unpack #-} Closure
  | VU
  | VTop
  | Vtt
  deriving Show

pattern VVar x a = VRigid x [] a
pattern VMeta x a = VFlex x [] a

infixl 8 $$
($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (env :> u) t

appTy :: VTy -> Val -> VTy
appTy a ~t = case force a of
  VPi x _ b -> b $$ t
  _         -> impossible

vApp :: Val -> Val -> Val
vApp t ~u = case t of
  VLam _ _ t      -> t $$ u
  VFlex  m sp a   -> VFlex m (sp :> u) (appTy a u)
  VRigid x sp a   -> VRigid x (sp :> u) (appTy a u)
  _               -> impossible

-- Apply single value to multiple values
vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  []      -> t
  sp :> u -> vAppSp t sp `vApp` u

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved v   -> v
  Unsolved a -> VFlex m [] a

-- We apply a value to a mask of entries from the environment.
vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vAppBDs env v bds `vApp` t
  (env :> t , bds :> Defined) -> vAppBDs env v bds
  _                           -> impossible

eval :: Env -> Tm -> Val
eval env = \case
  Var x                -> env !! unIx x
  App t u              -> vApp (eval env t) (eval env u)
  Lam x a t            -> VLam x (eval env a) (Closure env t)
  Pi x a b             -> VPi x (eval env a) (Closure env b)
  Let _ _ t u          -> eval (env :> eval env t) u
  U                    -> VU
  Meta m               -> vMeta m
  InsertedMeta m bds   -> vAppBDs env (vMeta m) bds
  Top                  -> VTop
  Tt                   -> Vtt

force :: Val -> Val
force = \case
  VFlex m sp _ | Solved t <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []      -> t
  sp :> u -> App (quoteSp l t sp) (quote l u)

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m sp b  -> quoteSp l (Meta m) sp
  VRigid x sp a -> quoteSp l (Var (lvl2Ix l x)) sp
  VLam x a t    -> Lam x (quote l a) (quote (l + 1) (t $$ VVar l a))
  VPi  x a b    -> Pi x (quote l a) (quote (l + 1) (b $$ VVar l a))
  VU            -> U
  VTop          -> Top
  Vtt           -> Tt

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)


-- Metavariables and pattern unification
--------------------------------------------------------------------------------

freshMeta :: Cxt -> VTy -> IO Tm
freshMeta cxt ~a = do
  m <- readIORef nextMeta
  writeIORef nextMeta $! (m + 1)
  let mty = eval [] $ closeTy (locals cxt) (quote (lvl cxt) a)
  modifyIORef' mcxt $ IM.insert m (Unsolved mty)
  pure $! InsertedMeta (MetaVar m) (bds cxt)

-- | Check if a type has a definitionally unique inhabitant.
guardContractible :: Lvl -> VTy -> IO ()
guardContractible l a = case force a of
  VPi x a b -> guardContractible (l + 1) (b $$ VVar l a)
  VTop      -> pure ()
  _         -> throwIO UnifyError

-- partial renaming from Γ to Δ
data PartialRenaming = PRen {
    dom :: Lvl                -- size of Γ
  , cod :: Lvl                -- size of Δ
  , ren :: IM.IntMap Lvl }    -- mapping from Δ vars to Γ vars

lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

invert :: Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []        = pure (0, mempty)
      go (sp :> t) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) _ | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          VRigid _ _  a                       -> guardContractible gamma a >> pure (dom + 1, ren)
          VFlex _ _ a                         -> guardContractible gamma a >> pure (dom + 1, ren)
          _                                   -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []        = pure t
  goSp pren t (sp :> u) = App <$> goSp pren t sp <*> go pren u

  contract :: PartialRenaming -> VTy -> IO Tm
  contract pren a = case force a of
    VPi x a b -> Lam x <$> go pren a <*> contract (lift pren) (b $$ VVar (cod pren) a)
    VTop      -> pure Tt
    _         -> throwIO UnifyError

  go :: PartialRenaming -> Val -> IO Tm
  go pren t = case force t of
    VFlex m' sp a | m == m'   -> contract pren a   -- meta occurs error if not contractible
                  | otherwise -> goSp pren (Meta m') sp `catchUnify` contract pren a

    VRigid (Lvl x) sp a -> case IM.lookup x (ren pren) of
      Nothing -> contract pren a   -- scope error if not contractible
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp `catchUnify` contract pren a

    VLam x a t -> Lam x <$> go pren a <*> go (lift pren) (t $$ VVar (cod pren) a)
    VPi x a b  -> Pi x <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren) a)
    VU         -> pure U
    VTop       -> pure Top
    Vtt        -> pure Tt

-- | Wrap a term in Lvl number of lambdas. We get the domain info from the VTy
--   argument.
lams :: Lvl -> VTy -> Tm -> Tm
lams l a t = go a (0 :: Lvl) where
  go a l' | l' == l = t
  go a l' = case force a of
    VPi "_" a b -> Lam ("x"++show l') (quote l' a) $ go (b $$ VVar l' a) (l' + 1)
    VPi x a b   -> Lam x (quote l' a) $ go (b $$ VVar l' a) (l' + 1)
    _           -> impossible

solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs  <- rename m pren rhs
  mty <- case lookupMeta m of
    Unsolved a -> pure a
    _          -> impossible
  let solution = eval [] $ lams (dom pren) mty rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]     , []       ) -> pure ()
  (sp :> t, sp' :> t') -> unifySp l sp sp' >> unify l t t'
  _                    -> throwIO UnifyError -- rigid mismatch error

catchUnify :: IO a -> IO a -> IO a
catchUnify x y = x `catch` \UnifyError -> y

unifyEq :: Eq a => a -> a -> IO ()
unifyEq x y = if x == y then pure () else throwIO UnifyError

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = do
  case (force t, force u) of
   (VLam _ a t , VLam _ _ t'  ) -> unify (l + 1) (t $$ VVar l a) (t' $$ VVar l a)
   (t          , VLam _ a t'  ) -> unify (l + 1) (t `vApp` VVar l a) (t' $$ VVar l a)
   (VLam _  a t, t'           ) -> unify (l + 1) (t $$ VVar l a) (t' `vApp` VVar l a)
   (VU         , VU           ) -> pure ()
   (VTop       , VTop         ) -> pure ()
   (Vtt        , _            ) -> pure ()
   (_          , Vtt          ) -> pure ()
   (VPi x a b  , VPi x' a' b' ) -> unify l a a' >> unify (l + 1) (b $$ VVar l a) (b' $$ VVar l a)

   (VRigid x sp a, VRigid x' sp' _) ->
     (unifyEq x x' >> unifySp l sp sp') `catchUnify` guardContractible l a

   (t@(VFlex m sp a) , t'@(VFlex m' sp' _) )
     | m == m'   -> unifySp l sp sp' `catchUnify` guardContractible l a
     | otherwise -> solve l m sp t' `catchUnify` solve l m' sp' t

   (VFlex m sp _ , t'             ) -> solve l m sp t'
   (t            , VFlex m' sp' _ ) -> solve l m' sp' t
   _                                -> throwIO UnifyError  -- rigid mismatch error

-- Elaboration
--------------------------------------------------------------------------------

type Types = [(String, VTy)]

-- | Information about the local binders, used for efficiently creating types for
--   fresh metas.
data Locals
  = Here
  | Define Locals Name ~Ty ~Tm
  | Bind Locals Name ~Ty
  deriving Show


data Cxt = Cxt {           -- used for:
                           -----------------------------------
    env    :: Env           -- evaluation
  , lvl    :: Lvl           -- unification
  , types  :: Types         -- raw name lookup, pretty printing
  , locals :: Locals        -- types of fresh metas
  , bds    :: [BD]          -- fresh meta creation
  , pos    :: SourcePos     -- error reporting
  }

instance Show Cxt where
  show = show . cxtNames

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] 0 [] Here []

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l types locs bds pos) x ~a =
  Cxt (env :> VVar l a) (l + 1) (types :> (x, a))
      (Bind locs x (quote l a)) (bds :> Bound) pos

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Tm -> Val -> Ty -> VTy -> Cxt
define (Cxt env l types ls bds pos) x ~t ~vt ~a ~va =
  Cxt (env :> vt) (l + 1) (types :> (x, va))
      (Define ls x a t) (bds :> Defined) pos

-- | Convert type in context to a closed iterated Pi type.  Note: we need `Tm`
--   and `Ty` in `Locals` in order to make this operation efficient. With this, we
--   can simply move things over from `Path` without having to rename or quote
--   anything.
closeTy :: Locals -> Ty -> Ty
closeTy mcl b = case mcl of
  Here             -> b
  Bind mcl x a     -> closeTy mcl (Pi x a b)
  Define mcl x a t -> closeTy mcl (Let x a t b)

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
    Lam x (quote (lvl cxt) a) <$> check (bind cxt x a) t (b $$ VVar (lvl cxt) a)

  (RLet x a t u, a') -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x t vt a va) u a'
    pure (Let x a t u)

  (RHole, a) ->
    freshMeta cxt a

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
    a <- freshMeta cxt VU
    let va = eval (env cxt) a
    (t, b) <- infer (bind cxt x va) t
    pure (Lam x a t, VPi x va $ closeVal cxt b)

  RApp t u -> do
    (t, tty) <- infer cxt t

    -- ensure that tty is Pi
    (a, b) <- case force tty of
      VPi x a b ->
        pure (a, b)
      tty -> do
        a <- eval (env cxt) <$> freshMeta cxt VU
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" a) VU
        unifyCatch cxt (VPi "x" a b) tty
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
    (u, b) <- infer (define cxt x t vt a va) u
    pure (Let x a t u, b)

  RHole -> do
    a <- eval (env cxt) <$> freshMeta cxt VU
    t <- freshMeta cxt a
    pure (t, a)

  RTop ->
    pure (Top, VU)

  Rtt ->
    pure (Tt, VTop)


-- Printing
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

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
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
    _                           -> impossible

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var (Ix x)                -> ((ns !! x)++)

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    Lam (fresh ns -> x) _ t   -> par p letp $ ("λ "++) . (x++) . goLam (ns:>x) t where
                                   goLam ns (Lam (fresh ns -> x) _ t) =
                                     (' ':) . (x++) . goLam (ns:>x) t
                                   goLam ns t = (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip (ns:>"_") b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (ns:>x) b where
                                   goPi ns (Pi (fresh ns -> x) a b)
                                     | x /= "_" = piBind ns x a . goPi (ns:>x) b
                                   goPi ns b = (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n  = "++) . go letp ns t . (";\n\n"++) . go letp (ns:>x) u

    Meta m                    -> (("?"++show m)++)
    InsertedMeta m bds        -> goBDS p ns m bds
    Top                       -> ("Top"++)
    Tt                        -> ("tt"++)

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

displayMetas :: IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(m, e) -> case e of
    Unsolved _ -> printf "let ?%s = ?;\n" (show m)
    Solved v   -> printf "let ?%s = %s;\n" (show m) (showTm0 $ quote 0 v)
  putStrLn ""

contract :: Lvl -> VTy -> Maybe Tm
contract l a = case force a of
  VPi x a b -> Lam x (quote l a) <$> contract (l + 1) (b $$ VVar l a)
  VTop      -> pure Tt
  _         -> Nothing

-- | After elaboration, we try to contract all unsolved metas.
contractUnsolvedMetas :: IO ()
contractUnsolvedMetas = modifyIORef' mcxt $ IM.map $ \case
  e@Solved{}     -> e
  e@(Unsolved a) -> maybe e (\t -> Solved (eval [] t)) (contract 0 a)

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


-- Parsing
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
keyword x =
  x == "let" || x == "λ" || x == "U" || x == "Top" || x == "tt"

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
      withPos ((RVar <$> pIdent)
           <|> (RU <$ symbol "U")
           <|> (RHole <$ symbol "_")
           <|> (RTop <$ symbol "Top")
           <|> (Rtt  <$ symbol "tt")
              )
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
        t <- infer (emptyCxt (initialPos file)) t `catch` \e -> do
                displayError file e
                exitSuccess
        contractUnsolvedMetas
        pure t

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
