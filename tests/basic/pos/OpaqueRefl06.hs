{-@ LIQUID "--reflection"      @-}

module OpaqueRefl06 where

import GHC.List (filter)
import GHC.Real (even)

{-@ measure GHC.List.filter :: (a -> Bool) -> [a] -> [a] @-}
{-@ assume filter :: p:(a -> Bool) -> xs:[a] -> {v : [a] | v == GHC.List.filter p xs && len v <= len xs} @-}
{-@ measure GHC.Real.even :: Integral a => a -> Bool @-}
{-@ assume even :: Integral a => x:a -> {VV : Bool | VV == GHC.Real.even x} @-}

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even