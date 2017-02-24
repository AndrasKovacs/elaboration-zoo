    
type family HList (ts :: [*]) :: * where
  HList '[]       = ()
  HList (t ': ts) = (t, HList ts)

infixr 5 :>
pattern (:>) a b = (a, b)

foo :: HList [Int, Int, Int]
foo = 0 :> 4 :> 5 :> ()


