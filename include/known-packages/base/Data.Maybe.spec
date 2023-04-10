module spec Data.Maybe where

import GHC.Types
import GHC.Maybe

maybe :: v:b -> (a -> b) -> u:(Maybe a) -> {w:b | not (isJust u) => w == v}
isNothing :: v:(Maybe a) -> {b:Bool | not (isJust v) == b}
fromMaybe :: v:a -> u:(Maybe a) -> {x:a | not (isJust u) => x == v}

measure isJust :: Maybe a -> Bool
  isJust (Just x)  = true
  isJust (Nothing) = false

fromJust :: {v:(Maybe a) | isJust v} -> a
measure fromJust :: Maybe a -> a
  fromJust (Just x) = x
