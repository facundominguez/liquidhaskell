{-@ LIQUID "--reflection"      @-}

module OpaqueRefl06 where

{-@ measure GHC.List.filter :: (a -> Bool) -> [a] -> [a] @-}
{-@ assume GHC.List.filter :: p:(a -> Bool) -> xs:[a] -> {v : [a] | v == GHC.List.filter p xs && len v <= len xs} @-}
{-@ measure GHC.Real.even :: Integral a => a -> Bool @-}
{-@ assume GHC.Real.even :: Integral a => x:a -> {VV : Bool | VV == GHC.Real.even x} @-}

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even