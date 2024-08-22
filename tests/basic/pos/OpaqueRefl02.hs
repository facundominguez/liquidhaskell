-- | test if basic LH pipeline is functioning 

{-@ LIQUID "--reflection"      @-}

module OpaqueRefl02 (inc2, llen) where

{-@ measure llen @-}
llen        :: [a] -> Int
llen []     = 0
llen (x:xs) = 1 + llen xs

{-@ reflect inc2 @-}
inc2 :: [a]
inc2 = []