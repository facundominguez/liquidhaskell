-- | test reflection away from another imported module (ReflExt02B)

{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--reflection" @-}

module ReflExt02A where

import ReflExt02B

{-@ reflect myAdd @-}