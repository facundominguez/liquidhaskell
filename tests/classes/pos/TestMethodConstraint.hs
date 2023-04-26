module TestMethodConstraint where

class B a where
  g :: a -> ()

class C a where
  {-@ f :: B b => a -> b -> () @-}
  f :: B b => a -> b -> ()

{-@
class D a where
  d :: B b => a -> b -> ()
@-}
