{-@ LIQUID "--reflection"      @-}

module OpaqueRefl06 where

{-@ measure GHC.Internal.List.filter :: (a -> Bool) -> [a] -> [a] @-}
{-@ assume GHC.Internal.List.filter :: p:(a -> Bool) -> xs:[a] -> {v : [a] | v == GHC.Internal.List.filter p xs && len v <= len xs} @-}
{-@ measure GHC.Internal.Real.even :: a -> GHC.Types.Bool @-}
{-@ assume GHC.Internal.Real.even :: x:a -> {VV : GHC.Types.Bool | VV == GHC.Internal.Real.even x} @-}

{-@ reflect keepEvens @-}
keepEvens :: [Int] -> [Int]
keepEvens = filter even