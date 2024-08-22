module OpaqueRefl05 where

import Data.Char (ord, chr)

{-@ reflect incChar @-}
incChar :: Char -> Char
incChar c = chr (ord c + 1)

{-@ ord' :: c:Char -> { v:Int | v = ord c } @-}
ord' :: Char -> Int
ord' c = ord c