module spec Data.Maybe where

import GHC.Maybe

isJust :: v:(GHC.Maybe.Maybe a) -> {b:Bool | b = (v != GHC.Maybe.Nothing)}
maybe :: v:b -> (a -> b) -> u:(GHC.Maybe.Maybe a) -> {w:b | GHC.Maybe.Nothing = u => w == v}
isNothing :: v:(GHC.Maybe.Maybe a) -> {b:Bool | b = (GHC.Maybe.Nothing = v)}
fromJust :: {v:(GHC.Maybe.Maybe a) | GHC.Maybe.Nothing != v} -> a
fromMaybe :: v:a -> u:(GHC.Maybe.Maybe a) -> {x:a | GHC.Maybe.Nothing = u => x == v}
