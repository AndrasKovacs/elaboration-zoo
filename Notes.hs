
module Notes where

import Control.Exception
import Control.Monad.Except

data Tm = Add !Tm !Tm | ILit !Int | StrLit !String

data FooException = FooException deriving (Show)
instance Exception FooException


-- add 10 to ILit-s if none of them are 0
foo :: Tm -> IO Tm
foo (Add a b)  = Add <$> foo a <*> foo b
foo (ILit 0)   = throw FooException
foo (ILit n)   = pure $ ILit (n + 10)
foo (StrLit s) = pure (StrLit s)


foo' :: Tm -> Either FooException Tm
foo' (Add a b)  = Add <$> foo' a <*> foo' b
foo' (ILit 0)   = throwError FooException
foo' (ILit n)   = pure $ ILit (n + 10)
foo' (StrLit s) = pure (StrLit s)





