
module Types where

import Control.Monad.Reader
import Control.Monad.State.Strict
import Lens.Micro.Platform
import Text.Megaparsec
import Text.Printf

import qualified Data.IntMap.Strict as M
import qualified Data.IntSet        as IS

import Presyntax

--------------------------------------------------------------------------------

-- | Elaboration problem identifier.
type MId = Int

-- | List of blocked problems.
type Blocking = IS.IntSet

data MetaEntry
  = Unsolved Blocking
  | Solved Val

type VTy   = Val
type Sub a = [(Name, a)]
type Ty    = Tm
type Vals  = Sub (Either (Maybe Val) Val)  -- left: bound telescope var
                                           -- right: defined var
type MCxt  = M.IntMap MetaEntry

data TyEntry = Bound VTy | Def VTy

data ElabCxt = ElabCxt {
  elabCxtVals  :: Vals,
  elabCxtTypes :: Sub TyEntry,
  elabCxtPos   :: SourcePos}

data UnifyCxt  = UnifyCxt {
  unifyCxtVals  :: Vals,
  unifyCxtPos   :: SourcePos}

data St     = St {_nextMId :: Int, _mcxt :: MCxt}
data Err    = Err {errErr :: ElabError, errPos :: SourcePos}
type M cxt  = ReaderT cxt (StateT St (Either Err))
type ElabM  = M ElabCxt
type UnifyM = M UnifyCxt

data Tm
  = Var Name
  | Let Name Ty Tm Tm

  | Pi Name Icit Ty Ty
  | Lam Name Icit Tm
  | App Tm Tm Icit

  | Tel           -- Ty Γ
  | TEmpty        -- Tm Γ Tel
  | TCons Ty Ty   -- (A : Ty Γ) → Tm (Γ ▶ A) Tel → Tm Γ Tel
  | El Tm         -- Tm Γ Tel → Ty Γ

  | Tempty      -- Tm Γ (El TEmpty)
  | Tcons Tm Tm -- (t : Tm Γ A) → Tm Γ (Δ[id, t]) → Tm Γ (El (TCons A Δ))
  | Proj1 Tm    -- Tm Γ (El (TCons A Δ)) → Tm Γ A
  | Proj2 Tm    -- (t : Tm Γ (El (TCons A Δ))) → Tm Γ (El (Δ[id, Proj₁ t]))

  | PiTel Name Ty Ty  -- (A : Tm Γ Tel) → Ty (Γ ▶ El A) → Ty Γ
  | AppTel Ty Tm Tm   -- (A : Tm Γ Tel)(t : Tm Γ (PiTel A B))(u : Tm Γ A)
                      -- → Tm Γ B[id, u]
  | LamTel Name Ty Tm -- (A : Tm Γ Tel)(t : Tm (Γ ▶ El A) B) → Tm Γ (PiTel A B)

  | U
  | Meta MId


data Spine
  = SNil
  | SApp Spine ~Val Icit
  | SAppTel ~Val Spine ~Val
  | SProj1 Spine
  | SProj2 Spine

spLen :: Spine -> Int
spLen = go 0 where
  go n SNil             = n
  go n (SApp sp _ _)    = go (n + 1) sp
  go n (SAppTel _ sp _) = go (n + 1) sp
  go n (SProj1 sp)      = go (n + 1) sp
  go n (SProj2 sp)      = go (n + 1) sp

data Head
  = HVar Name
  | HMeta MId
  deriving (Eq, Show)

data Val
  = VNe Head Spine

  | VPi Name Icit ~Val (Val -> Val)
  | VLam Name Icit (Val -> Val)
  | VU

  | VTel
  | VEl ~Val
  | VTEmpty
  | VTCons ~Val Val
  | VTempty
  | VTcons ~Val ~Val

  | VPiTel Name ~Val (Val -> Val)
  | VLamTel Name ~Val (Val -> Val)

data MetaInsertion
  = MIYes
  | MINo
  | MIUntilName Name

pattern VVar :: Name -> Val
pattern VVar x = VNe (HVar x) SNil

pattern VMeta :: MId -> Val
pattern VMeta m = VNe (HMeta m) SNil

-- Pretty
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
    App (AppTel _ t u) u' i' ->
      showParen p (go False  t . (' ':) . goArg u Impl . (' ':) . goArg  u' i')
    App t u i    -> showParen p (go True  t . (' ':) . goArg  u i)
    Lam x i t    -> showParen p (("λ "++) . goLamBind x i . goLam t)
    t@Pi{}       -> showParen p (goPi False t)
    U            -> ("U"++)
    Tel          -> ("Tel"++)
    TEmpty       -> ("∙"++)
    TCons a as   -> showParen p (go False a . (" ▶ "++). go False as)
    Tempty       -> ("ε"++)
    El a         -> showParen p (("El "++) . go True a)
    Tcons t u    -> showParen p (go False t . (" ∷ "++). go False u)
    Proj1 t      -> showParen p (("₁ "++). go True t)
    Proj2 t      -> showParen p (("₂ "++). go True t)
    t@PiTel{}    -> showParen p (goPi False t)
    AppTel _ (App t u i) u'  ->
      showParen p (go False  t . (' ':) . goArg  u i . (" * "++) . goArg  u' Impl)
    AppTel _ (AppTel _ t u) u' ->
      showParen p (go False  t . (" * "++) . goArg u Impl . (" * "++) . goArg  u' Impl)
    AppTel _ t u -> showParen p (go True  t . (" * "++) . goArg u Impl)
    LamTel x a t -> showParen p (("λ* "++) . goLamBind x Impl . goLam t)

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

  goPi p (PiTel x a b)
    | x /= "_" = goPiBind x Impl a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; _ -> True) a .
       (" → "++) . go False b

  goPi p t = (if p then (" -> "++) else id) . go False t

  goLamBind :: Name -> Icit -> ShowS
  goLamBind x i = icit i bracket id ((if null x then "_" else x) ++)

  goLam :: Tm -> ShowS
  goLam (Lam x i t)    = (' ':) . goLamBind x i    . goLam t
  goLam (LamTel x a t) = (' ':) . goLamBind x Impl . goLam t
  goLam t = (". "++) . go False t

instance Show Tm where showsPrec = prettyTm

-- Errors
--------------------------------------------------------------------------------

data ElabError
  = SpineNonVar Tm
  | SpineProjection
  | ScopeError MId [Name] Tm Name -- ^ Meta, spine, rhs, offending variable
  | OccursCheck MId Tm
  | UnifyError Tm Tm
  | NameNotInScope Name
  | ExpectedFunction Tm -- ^ Inferred type.
  | NoNamedImplicitArg Name
  | CannotInferNamedLam
  | IcitMismatch Icit Icit

instance Show ElabError where
  show = \case
    SpineNonVar t -> printf "Non-variable value in meta spine:\n\n  %s"  (show t)
    SpineProjection -> "Projection in meta spine"
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

--------------------------------------------------------------------------------

makeFields ''ElabCxt
makeFields ''UnifyCxt
makeFields ''Err
makeLenses ''St
