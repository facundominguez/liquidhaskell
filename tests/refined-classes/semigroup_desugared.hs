{-@ LIQUID "--reflection" @-}
module Semigroup where

import Prelude hiding (Semigroup(..), mappend)


infixl 3 ==.

-- {-@ reflect (==.) @-}
(==.) :: a -> a -> a
_ ==. x = x
{-# INLINE (==.) #-}

data QED = QED

-- {-@ reflect *** @-}
infixl 2 ***
x *** QED = ()



{-@
  data SemigroupD a = SemigroupD {
      sdMappend :: a -> a -> a
    , sdLawAssociative :: x : a
        -> y : a
        -> z : a
        -> {sdMappend (sdMappend x y) z = sdMappend x (sdMappend y z)}
    }
@-}

data SemigroupD a = SemigroupD {
      sdMappend :: a -> a -> a
    , sdLawAssociative :: a -> a -> a -> ()
    }

-- {-@ mappend 
-- {-@ assume mappend 
--  :: d : SemigroupD a 
--  -> x : a 
--  -> y : a 
--  -> z : {a | z = sdMappend d x y}
--  @-}

{-@ reflect mappend @-}
mappend :: SemigroupD a -> a -> a -> a
mappend d x y = sdMappend d x y

-- {-@ reflect lawAssociative @-}
-- {-@ lawAssociative 
{-@ assume lawAssociative 
 :: d : SemigroupD a
 -> x : a
 -> y : a
 -> z : a
 -> {mappend d (mappend d x y) z = mappend d x (mappend d y z)}
 @-}
lawAssociative :: SemigroupD a -> a -> a -> a -> ()
lawAssociative d x y z = sdLawAssociative d x y z

{-@ reflect mappendInt @-}
mappendInt :: Int -> Int -> Int
mappendInt a b = a + b

-- {-@ reflect semigroupInt @-}
-- {-@ lazy semigroupInt @-}
semigroupInt :: SemigroupD Int
semigroupInt = SemigroupD mappendInt lawAssociativeInt

-- {-@ reflect lawAssociativeInt @-}
{-@ lawAssociativeInt
 :: x : Int
 -> y : Int
 -> z : Int
 -> {mappendInt (mappendInt x y) z = mappendInt x (mappendInt y z)}
 @-}
lawAssociativeInt x y z = 
        mappendInt (mappendInt x y) z 
    ==. (x + y) + z
    ==. x + (y + z)
    ==. mappendInt x (mappendInt y z)
    *** QED

-- JP: Why does the previous work? I expected something like the following:
--
-- {-@ lawAssociativeInt
--  :: x : Int
--  -> y : Int
--  -> z : Int
--  -> {mappend semigroupInt (mappend semigroupInt x y) z = mappend semigroupInt x (mappend semigroupInt y z)}
--  @-}
-- lawAssociativeInt x y z = 
--         mappend semigroupInt (mappend semigroupInt x y) z 
--     ==. (x + y) + z
--     ==. x + (y + z)
--     ==. mappend semigroupInt x (mappend semigroupInt y z)
--     *** QED

