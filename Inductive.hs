{-# language BangPatterns, Strict, LambdaCase #-}

import qualified Data.Text as T

type Name    = T.Text
type Unfold  = Int
type Sub a   = [(Name, a)]

-- | A definition with a type, a value, and an unfolding parameter.
--   A definition is only unfolded when applied to at least 'Int'
--   number of arguments.
data Def a = Def a a Unfold

-- | Environment entries. We instantiate it with 'Term' or 'Val'.
data Entry a
  -- | Defined values.
  = EDef {-# unpack #-} (Def a)
  -- | Data constructors with type.
  | DCon a
  -- | Type constructors with type.
  | TCon a
  -- | Bound variables with type.
  | Bound a

data Pat
  -- | Data constructor applied to variables.
  = PCon Name [Name]
  -- | Catch-all pattern.
  | PVar Name

-- | We only have possibly-case-splitting lambdas. Plain lambdas are expressed
--   with a single catch-all pattern.
data Tm
  = Var Name
  | App Tm Tm
  | Lam [(Pat, Tm)]
  | Pi Name Tm Tm
  | Let Name {-# unpack #-} (Def Tm) Tm
  | U

data Val
  = VVar Name
  | VApp Val ~Val
  | VLam [Pat] (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

data TopDecl
  = TopDef {-# unpack #-} (Def Tm)
  | Inductive (Sub Tm) Tm [(Name, Tm)]

type Program = [(Name, TopDecl)]
type VSub    = Sub (Entry Val)

--------------------------------------------------------------------------------

evalName :: VSub -> Unfold -> Name -> Val
evalName vs unfold x = case lookup x vs of
  Just e -> case e of
    EDef (Def _ v unfold') | unfold' >= unfold -> v
    _ -> VVar x
  _ -> error "evalName: name not in context"

evalApp :: VSub -> Unfold -> Tm -> Tm -> Val
evalApp vs unfold f a = _

eval :: VSub -> Tm -> Val
eval vs = \case
  Var x   -> evalName vs 0 x
  App f a -> evalApp vs 0 f a


