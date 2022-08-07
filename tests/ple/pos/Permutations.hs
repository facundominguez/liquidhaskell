{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Permutations where

import Language.Haskell.Liquid.ProofCombinators ((===), (***), QED(Admit, QED), (?), pleUnfold)
import Prelude hiding ((!!), (++), asTypeOf, concat, const, drop, foldr, id, map, take, reverse)

infixr 5 ++
{-@ infixr 5 ++ @-}
{-@ infixr 5 : @-}
{-@ infixl 9 !! @-}


{-@ lazy permutations @-}
{-@ reflect permutations @-}
permutations :: [a] -> [[a]]
permutations xs0 = xs0 : perms xs0 []

{-@
reflect perms
perms
  :: ts:[a]
  -> is:[a]
  -> { v:[[a]]
     | v = concat (map (aux2 ts is) (fromTo 0 (len ts - 1)))
     }
@-}
perms :: [a] -> [a] -> [[a]]
perms []     _  = []
perms (t0:ts0) is =
    mapInterleave t0 ts0 (permutations is) (perms ts0 (t0:is))
    `const`
          lemmaMapAux2 t0 ts0 is 0 (length ts0 - 1)
    `const`
          lemmaAppendAssoc
             (concat (map (aux1 t0 ts0 []) (permutations is)))
             []
             (concat (map (aux2 (t0:ts0) is) (fromTo 1 (length (t0:ts0) - 1))))
     `const`
          mapInterleave t0 ts0 (permutations is) []
{-
    `asTypeOf`
    const (concat (map (aux1 t0 ts0 []) (permutations is)) ++ perms ts0 (t0:is))
          (mapInterleave t0 ts0 (permutations is) (perms ts0 (t0:is)))
    `asTypeOf`
    const (concat (map (aux1 t0 ts0 []) (permutations is)) ++ concat (map (aux2 ts0 (t0:is)) (fromTo 0 (length ts0 - 1))))
          (perms ts0 (t0:is))
    `asTypeOf`
    const (concat (map (aux1 t0 ts0 []) (permutations is)) ++ concat (map (aux2 (t0:ts0) is) (fromTo 1 (length (t0:ts0) - 1))))
          (lemmaMapAux2 t0 ts0 is 0 (length ts0 - 1))
    `asTypeOf`
          (concat (map (aux1 t0 ts0 []) (permutations is)) ++ ([] ++ concat (map (aux2 (t0:ts0) is) (fromTo 1 (length (t0:ts0) - 1)))))
    `asTypeOf`
     const ((concat (map (aux1 t0 ts0 []) (permutations is)) ++ []) ++ concat (map (aux2 (t0:ts0) is) (fromTo 1 (length (t0:ts0) - 1))))
          (lemmaAppendAssoc
             (concat (map (aux1 t0 ts0 []) (permutations is)))
             []
             (concat (map (aux2 (t0:ts0) is) (fromTo 1 (length (t0:ts0) - 1))))
          )
    `asTypeOf`
      (mapInterleave t0 ts0 (permutations is) [] ++ concat (map (aux2 (t0:ts0) is) (fromTo 1 (length (t0:ts0) - 1))))
-}

{-@
reflect aux2
aux2 :: ts:[a] -> [a] -> { n:Int | n < len ts && n >= 0 } -> [[a]]
@-}
aux2 :: [a] -> [a] -> Int -> [[a]]
aux2 ts is n =
  mapInterleave (ts!!n) (drop (n+1) ts) (permutations (reverse (take n ts) ++ is)) []

{-@ reflect aux0 @-}
aux0 :: a -> ([a] -> [a]) -> [a] -> [a] -> Int -> [a]
aux0 t f ys ts n = f (insertAt n t ys ++ ts)

{-@ reflect aux1 @-}
aux1 :: a -> [a] -> [[a]] -> [a] -> [[a]]
aux1 t ts r p = interleave t ts p r

{-@
reflect mapInterleave
mapInterleave
  :: t:a
  -> ts:[a]
  -> ps:[[a]]
  -> r:[[a]]
  -> { v:[[a]] | v == concat (map (aux1 t ts []) ps) ++ r }
@-}
mapInterleave :: a -> [a] -> [[a]] -> [[a]] -> [[a]]
mapInterleave t ts ps r = foldr (interleave t ts) r ps `const` lemmaFoldrInterleave t ts ps r

{-@
reflect interleave
interleave
  :: t:a
  -> ts:[a]
  -> xs:[a]
  -> r:[[a]]
  -> { v:[[a]] | v == map (aux0 t id xs ts) (fromTo 0 (len xs - 1)) ++ r }
@-}
interleave :: a -> [a] -> [a] -> [[a]] -> [[a]]
interleave t ts xs r =
    let (_,zs) = interleave' t ts id xs r in zs

{-@
reflect interleave'
interleave'
  :: t:a
  -> ts:[a]
  -> f:([a] -> [a])
  -> ys:[a]
  -> r:[[a]]
  -> ( { v:[a] | v == ys ++ ts }
     , { v:[[a]] | v == map (aux0 t f ys ts) (fromTo 0 (len ys-1)) ++ r }
     )
@-}
interleave' :: a -> [a] -> ([a] -> [a]) -> [a] -> [[a]] -> ([a], [[a]])
interleave' t ts _ []     r = (ts, r)
interleave' t ts f (y:ys) r =
  let (us, zs) = interleave' t ts (snoc f y) ys r
   in (y:us, f (t:y:us) : zs `const` (lemmaMapAux0 t f y ys ts r 0 (length ys - 1)))


---------------------------------
-- map (take n) (take (factorial n) $ permutations ([1..n] ++ undefined)) == permutations [1..n]
--
-- take (factorial n) (permutations ([1..n] ++ r)) == map (++ r) (permutations [1..n])
--
-- permutations ([1..n] ++ r)
--   ==
--   map (++ r) (permutations [1..n]) ++ concat (map (aux2 ([1..n] ++ r) []) (fromTo n (n + len r - 1)))

{-@
lemmaPermutationsDecomposition
  :: { n:Int | n >= 0 }
  -> r:[Int]
  -> { permutations (fromTo 1 n ++ r)
       ==
       map (flipAppend r) (permutations (fromTo 1 n)) ++ concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo n (n + len r - 1)))
     }
@-}
lemmaPermutationsDecomposition :: Int -> [Int] -> ()
lemmaPermutationsDecomposition n r = lemmaPermsDecomposition n r

{-@
lemmaPermsDecomposition
  :: { n:Int | n >= 0 }
  -> r:[Int]
  -> { perms (fromTo 1 n ++ r) []
       ==
       map (flipAppend r) (perms (fromTo 1 n) []) ++ concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo n (n + len r - 1)))
     }
@-}
lemmaPermsDecomposition :: Int -> [Int] -> ()
lemmaPermsDecomposition n r =
    ()
      `const` perms (fromTo 1 n ++ r) []
      `const` lemmaLengthAppend (fromTo 1 n) r
      `const` lemmaLengthFromTo 1 n
      `const` lemmaFromToSplit 0 (n - 1) (n + length r - 1)
      `const` lemmaMapAppend (aux2 (fromTo 1 n ++ r) []) (fromTo 0 (n - 1)) (fromTo n (n + length r - 1))
      `const` lemmaConcatAppend
                (map (aux2 (fromTo 1 n ++ r) []) (fromTo 0 (n - 1)))
                (map (aux2 (fromTo 1 n ++ r) []) (fromTo n (n + length r - 1)))
      `const` lemmaConcatMapInterleave (fromTo 1 n) r 0 (n - 1)
      `const` perms (fromTo 1 n) []
{-
    perms (fromTo 1 n ++ r) []
    `asTypeOf`
    concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo 0 (length (fromTo 1 n ++ r) - 1)))
    `asTypeOf` case lemmaLengthAppend (fromTo 1 n) r of { () ->
    concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo 0 (length (fromTo 1 n) + length r - 1)))
    `asTypeOf` case lemmaLengthFromTo 1 n of { () ->
    concat (map (aux2 ((fromTo 1 n ++ r)) []) (fromTo 0 (n + length r - 1)))
    `asTypeOf`
    const (concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo 0 (n - 1) ++ fromTo n (n + length r - 1))))
          (lemmaFromToSplit 0 (n - 1) (n + length r - 1))
    `asTypeOf`
    const (
    const (concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo 0 (n - 1)))
             ++ concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo n (n + length r - 1)))
          )
          (lemmaMapAppend (aux2 (fromTo 1 n ++ r) []) (fromTo 0 (n - 1)) (fromTo n (n + length r - 1)))
          )
          (lemmaConcatAppend
            (map (aux2 (fromTo 1 n ++ r) []) (fromTo 0 (n - 1)))
            (map (aux2 (fromTo 1 n ++ r) []) (fromTo n (n + length r - 1)))
          )
    `asTypeOf`
    const (map (flipAppend r) (concat (map (aux2 (fromTo 1 n) []) (fromTo 0 (n - 1))))
             ++ concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo n (n + length r - 1))))
          (lemmaConcatMapInterleave (fromTo 1 n) r 0 (n - 1))
    `asTypeOf`
    (map (flipAppend r) (concat (map (aux2 (fromTo 1 n) []) (fromTo 0 (length (fromTo 1 n) - 1))))
       ++ concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo n (n + length r - 1))))
    `asTypeOf`
    (map (flipAppend r) (perms (fromTo 1 n) [])
       ++ concat (map (aux2 (fromTo 1 n ++ r) []) (fromTo n (n + length r - 1))))
    }}
    ***
    QED
-}


------------------------------
-- Auxiliary functions
------------------------------

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ inline const @-}
const :: a -> b -> a
const x _ = x

{-@
inline asTypeOf
asTypeOf :: x:a -> { y:a | x = y } -> { v:a | v = x }
@-}
asTypeOf :: a -> a -> a
asTypeOf x _ = x

{-@ reflect concat @-}
concat :: [[a]] -> [a]
concat [] = []
concat (x:xs) = x ++ concat xs

{-@ type Nat = { n:Int | n >= 0 } @-}

{-@
reflect !!
(!!) :: xs:[a] -> { n:Int | n < len xs && n >= 0 } -> a
@-}
(!!) :: [a] -> Int -> a
(x:xs) !! 0 = x
(x:xs) !! n = xs !! (n - 1)

{-@ reflect take @-}
{-@ take :: Nat -> _ -> _ @-}
take :: Int -> [a] -> [a]
take n xs
  | n > 0 =
    case xs of
      [] -> []
      x:xs -> x : take (n-1) xs
  | otherwise =
    []

{-@ reflect drop @-}
{-@ drop :: Nat -> _ -> _ @-}
drop :: Int -> [a] -> [a]
drop n xs
  | n > 0 =
    case xs of
      [] -> []
      _:xs -> drop (n-1) xs
  | otherwise =
    xs

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : xs ++ ys

{-@ reflect flipAppend @-}
flipAppend :: [a] -> [a] -> [a]
flipAppend xs ys = ys ++ xs

{-@ reflect insertAt @-}
{-@
insertAt
  :: n:Int
  -> y:a
  -> xs:[a]
  -> { v:[a] | v = take n xs ++ y : drop n xs }
@-}
insertAt :: Int -> a -> [a] -> [a]
insertAt n y xs =
  if n>0 then
    case xs of
      [] -> [y]
      z:zs -> z : insertAt (n - 1) y zs
  else
    y : xs

{-@ reflect map @-}
{-@ map :: forall <p :: a -> Bool, q :: b -> Bool>. (a<p> -> b<q>) -> [a<p>] -> [b<q>] @-}
map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = f x : map f xs

{-@ reflect foldr @-}
{-@ foldr :: (a -> b -> b) -> b -> [a] -> b @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

{-@ reflect fromTo @-}
{-@
fromTo
  :: a:Int
  -> b:Int
  -> [Int<{\x -> a <= x && x <= b}>]
     / [b-a+1]
@-}
fromTo :: Int -> Int -> [Int]
fromTo a b = if a <= b then a : fromTo (a + 1) b
               else []

{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

{-@
lemmaElemAtAppend
  :: xs:[a]
  -> ys:[a]
  -> { i:Int | 0 <= i && i < len xs }
  -> { (xs ++ ys) !! i == xs !! i }
@-}
lemmaElemAtAppend :: [a] -> [a] -> Int -> ()
lemmaElemAtAppend [] _ _ = ()
lemmaElemAtAppend (_:xs) ys i =
  if i > 0 then lemmaElemAtAppend xs ys (i - 1) else ()

{-@
lemmaDropAppend
  :: xs:[a]
  -> ys:[a]
  -> { i:Int | 0 <= i && i <= len xs }
  -> { drop i (xs ++ ys) == drop i xs ++ ys }
@-}
lemmaDropAppend :: [a] -> [a] -> Int -> ()
lemmaDropAppend [] _ _ = ()
lemmaDropAppend (_:xs) ys i =
  if i > 0 then lemmaDropAppend xs ys (i - 1) else ()

{-@
lemmaTakeAppend
  :: xs:[a]
  -> ys:[a]
  -> { i:Int | 0 <= i && i <= len xs }
  -> { take i (xs ++ ys) == take i xs }
@-}
lemmaTakeAppend :: [a] -> [a] -> Int -> ()
lemmaTakeAppend [] _ _ = ()
lemmaTakeAppend (_:xs) ys i =
  if i > 0 then lemmaTakeAppend xs ys (i - 1) else ()

{-@
lemmaMapAppend
  :: f:(a -> b)
  -> xs:[a]
  -> ys:[a]
  -> { map f xs ++ map f ys == map f (xs ++ ys) }
@-}
lemmaMapAppend :: (a -> b) -> [a] -> [a] -> ()
lemmaMapAppend f [] ys = ()
lemmaMapAppend f (_:xs) ys = lemmaMapAppend f xs ys

{-@
lemmaConcatAppend
  :: xs:[[a]]
  -> ys:[[a]]
  -> { concat (xs ++ ys) = concat xs ++ concat ys }
@-}
lemmaConcatAppend :: [[a]] -> [[a]] -> ()
lemmaConcatAppend [] _ = ()
lemmaConcatAppend (x:xs) ys =
  lemmaConcatAppend xs ys
   `const` lemmaAppendAssoc x (concat xs) (concat ys)

{-@
lemmaLengthFromTo
  :: i:Int
  -> { j:Int | i <= j + 1 }
  -> { len (fromTo i j) == j - i + 1 } / [j - i + 1]
@-}
lemmaLengthFromTo :: Int -> Int -> ()
lemmaLengthFromTo i j = if i <= j then lemmaLengthFromTo (i + 1) j else ()

{-@
lemmaLengthAppend
  :: xs:[a]
  -> ys:[a]
  -> { len (xs ++ ys) == len xs + len ys }
@-}
lemmaLengthAppend :: [a] -> [a] -> ()
lemmaLengthAppend [] _ = ()
lemmaLengthAppend (_:xs) ys = lemmaLengthAppend xs ys

{-@
lemmaFromToSplit
  :: a:Int
  -> { b:Int | a <= b + 1 }
  -> { c:Int | b <= c }
  -> { fromTo a b ++ fromTo (b + 1) c == fromTo a c } / [ b - a + 1 ]
@-}
lemmaFromToSplit :: Int -> Int -> Int -> ()
lemmaFromToSplit a b c =
  if a + 1 <= b then lemmaFromToSplit (a+1) b c else if a <= b then () else ()

{-
  if a + 1 <= b then
    (fromTo a b ++ fromTo (b + 1) c)
    `asTypeOf`
    (a:fromTo (a+1) b ++ fromTo (b + 1) c)
    `asTypeOf`
    const (a:fromTo (a+1) c)
          (lemmaFromToSplit (a+1) b c)
    `asTypeOf`
    fromTo a c
    ***
    QED
  else
    ()
-}

{-@ lemmaAppendId :: xs:[a] -> { xs = xs ++ [] } @-}
lemmaAppendId :: [a] -> ()
lemmaAppendId [] = ()
lemmaAppendId (_:xs) = lemmaAppendId xs

{-@
lemmaMapAux0
  :: t:a
  -> f:([a] -> [a])
  -> y:a
  -> ys:[a]
  -> ts:[a]
  -> r:[[a]]
  -> { i:Int | 0 <= i }
  -> j:Int
  -> { map (aux0 t (snoc f y) ys ts) (fromTo i j) ++ r
         == map (aux0 t f (y:ys) ts) (fromTo (i+1) (j+1)) ++ r
     } / [j-i+1]
@-}
lemmaMapAux0 :: a -> ([a] -> [a]) -> a -> [a] -> [a] -> [[a]] -> Int -> Int -> ()
lemmaMapAux0 t f y ys ts r i j =
    if i <= j then lemmaMapAux0 t f y ys ts r (i+1) j else ()

{-@ reflect snoc @-}
snoc :: ([a] -> [a]) -> a -> [a] -> [a]
snoc f y xs = f (y : xs)

{-@
lemmaInterleaveAppend
  :: t:a
  -> ts:[a]
  -> p:[a]
  -> r:[[a]]
  -> { interleave t ts p r == interleave t ts p [] ++ r }
@-}
lemmaInterleaveAppend :: a -> [a] -> [a] -> [[a]] -> ()
lemmaInterleaveAppend t ts p r =
  ()
    ? interleave t ts p r
    ? interleave t ts p []
    ? lemmaAppendAssoc (map (aux0 t id p ts) (fromTo 0 (length p - 1))) [] r


---------------------------------

-- Doesn't work:
-- rewriteWith lemmaInterleaveAppend [lemmaAppendAssoc]

{-@
lemmaFoldrInterleave
  :: t:a
  -> ts:[a]
  -> ps:[[a]]
  -> r:[[a]]
  -> { foldr (interleave t ts) r ps == concat (map (aux1 t ts []) ps) ++ r }
@-}
lemmaFoldrInterleave :: a -> [a] -> [[a]] -> [[a]] -> ()
lemmaFoldrInterleave t ts [] r = ()
lemmaFoldrInterleave t ts (p:ps) r =
  lemmaFoldrInterleave t ts ps r
    ? lemmaInterleaveAppend t ts p (concat (map (aux1 t ts []) ps) ++ r)
    ? lemmaAppendAssoc (interleave t ts p []) (concat (map (aux1 t ts []) ps)) r

{-@
lemmaAppendAssoc :: xs:[a] -> ys:[a] -> zs:[a] -> { xs ++ ys ++ zs = (xs ++ ys) ++ zs }
@-}
lemmaAppendAssoc :: [a] -> [a] -> [a] -> ()
lemmaAppendAssoc [] _ _ = ()
lemmaAppendAssoc (_:xs) ys zs = lemmaAppendAssoc xs ys zs

{-@
lemmaConcatMapInterleave
  :: ts:[a]
  -> r:[a]
  -> { i:Int | i >= 0 }
  -> { j:Int | j < len ts }
  -> { concat (map (aux2 (ts ++ r) []) (fromTo i j))
         == map (flipAppend r) (concat (map (aux2 ts []) (fromTo i j))) } / [j - i + 1]
@-}
lemmaConcatMapInterleave :: [a] -> [a] -> Int -> Int -> ()
lemmaConcatMapInterleave ts r i j =
    if i <= j then
      lemmaConcatMapInterleave ts r (i + 1) j
        `const` lemmaLengthAppend ts r
        `const` lemmaTakeAppend ts r i
        `const` lemmaElemAtAppend ts r i
        `const` lemmaDropAppend ts r (i + 1)
        `const` lemmaAppendInterleave (ts !! i) (drop (i + 1) ts) r (permutations (reverse (take i ts) ++ []))
        `const` lemmaMapAppend (flipAppend r) (aux2 ts [] i) (concat (map (aux2 ts []) (fromTo (i + 1) j)))
    else
      ()
{-
    if i <= j then
      case lemmaLengthAppend ts r of { () ->
      concat (map (aux2 (ts ++ r) []) (fromTo i j))
      `asTypeOf`
      concat (map (aux2 (ts ++ r) []) (i : fromTo (i + 1) j))
      `asTypeOf`
      (aux2 (ts ++ r) [] i ++ concat (map (aux2 (ts ++ r) []) (fromTo (i + 1) j)))
      `asTypeOf`
      const (aux2 (ts ++ r) [] i ++ map (flipAppend r) (concat (map (aux2 ts []) (fromTo (i + 1) j))))
            (lemmaConcatMapInterleave ts r (i + 1) j)
      `asTypeOf`
      (mapInterleave ((ts ++ r) !! i) (drop (i + 1) (ts ++ r)) (permutations (reverse (take i (ts ++ r)) ++ [])) []
         ++ map (flipAppend r) (concat (map (aux2 ts []) (fromTo (i + 1) j))))
      `asTypeOf`
      const (mapInterleave ((ts ++ r) !! i) (drop (i + 1) (ts ++ r)) (permutations (reverse (take i ts) ++ [])) []
             ++ map (flipAppend r) (concat (map (aux2 ts []) (fromTo (i + 1) j))))
            (lemmaTakeAppend ts r i)
      `asTypeOf`
      const (mapInterleave (ts !! i) (drop (i + 1) (ts ++ r)) (permutations (reverse (take i ts) ++ [])) []
             ++ map (flipAppend r) (concat (map (aux2 ts []) (fromTo (i + 1) j))))
            (lemmaElemAtAppend ts r i)
      `asTypeOf`
      const (mapInterleave (ts !! i) (drop (i + 1) ts ++ r) (permutations (reverse (take i ts) ++ [])) []
             ++ map (flipAppend r) (concat (map (aux2 ts []) (fromTo (i + 1) j))))
            (lemmaDropAppend ts r (i + 1))
      `asTypeOf`
      const (map (flipAppend r) (aux2 ts [] i) ++ map (flipAppend r) (concat (map (aux2 ts []) (fromTo (i + 1) j))))
            (lemmaAppendInterleave (ts !! i) (drop (i + 1) ts) r (permutations (reverse (take i ts) ++ [])))
      `asTypeOf`
      const (map (flipAppend r) (aux2 ts [] i ++ concat (map (aux2 ts []) (fromTo (i + 1) j))))
            (lemmaMapAppend (flipAppend r) (aux2 ts [] i) (concat (map (aux2 ts []) (fromTo (i + 1) j))))
      `asTypeOf`
      map (flipAppend r) (concat (map (aux2 ts []) (fromTo i j)))
      }
      ***
      QED
    else
      ()
-}

{-@
lemmaAppendInterleave
  :: t:a
  -> ts:[a]
  -> r:[a]
  -> ps:[[a]]
  -> { mapInterleave t (ts ++ r) ps [] == map (flipAppend r) (mapInterleave t ts ps []) }
@-}
lemmaAppendInterleave :: a -> [a] -> [a] -> [[a]] -> ()
lemmaAppendInterleave t ts r [] = ()
  ? mapInterleave t (ts ++ r) [] []
  ? mapInterleave t ts [] []
lemmaAppendInterleave t ts r (p:ps) =
  lemmaAppendInterleave t ts r ps
    `const` mapInterleave t (ts ++ r) (p:ps) []
    `const` mapInterleave t ts (p:ps) []
    `const` mapInterleave t (ts ++ r) ps []
    `const` mapInterleave t ts ps []
    `const` lemmaAppendAssoc (aux1 t (ts ++ r) [] p) (concat (map (aux1 t (ts ++ r) []) ps)) []
    `const` lemmaAppendInterleave t ts r ps
    `const` interleave t (ts ++ r) p []
    `const` lemmaAppendAux0 t p ts r (fromTo 0 (length p - 1))
    `const` lemmaAppendId (map (aux0 t id p ts) (fromTo 0 (length p - 1)))
    `const` lemmaAppendId (map (flipAppend r) (interleave t ts p []))
    `const` lemmaMapAppend (flipAppend r) (aux1 t ts [] p) (mapInterleave t ts ps [])
    `const` lemmaAppendAssoc (aux1 t ts [] p) (concat (map (aux1 t ts []) ps)) []

{-
  mapInterleave t (ts ++ r) (p:ps) []
  `asTypeOf`
  const (concat (map (aux1 t (ts ++ r) []) (p:ps)) ++ [])
        (mapInterleave t (ts ++ r) (p:ps) [])
  `asTypeOf`
   ((aux1 t (ts ++ r) [] p ++ concat (map (aux1 t (ts ++ r) []) ps)) ++ [])
  `asTypeOf`
   const (aux1 t (ts ++ r) [] p ++ concat (map (aux1 t (ts ++ r) []) ps) ++ [])
         (lemmaAppendAssoc (aux1 t (ts ++ r) [] p) (concat (map (aux1 t (ts ++ r) []) ps)) [])
  `asTypeOf`
   const (aux1 t (ts ++ r) [] p ++ mapInterleave t (ts ++ r) ps [])
         (mapInterleave t (ts ++ r) ps [])
  `asTypeOf`
   const (aux1 t (ts ++ r) [] p ++ map (flipAppend r) (mapInterleave t ts ps []))
         (lemmaAppendInterleave t ts r ps)
  `asTypeOf`
   const ((map (aux0 t id p (ts ++ r)) (fromTo 0 (length p - 1)) ++ []) ++ map (flipAppend r) (mapInterleave t ts ps []))
         (interleave t (ts ++ r) p [])
  `asTypeOf`
   const ((map (flipAppend r) (map (aux0 t id p ts) (fromTo 0 (length p - 1))) ++ []) ++ map (flipAppend r) (mapInterleave t ts ps []))
         (lemmaAppendAux0 t p ts r (fromTo 0 (length p - 1)))
  `asTypeOf`
   const ((map (flipAppend r) (interleave t ts p []) ++ []) ++ map (flipAppend r) (mapInterleave t ts ps []))
         (lemmaAppendId (map (aux0 t id p ts) (fromTo 0 (length p - 1))))
  `asTypeOf`
   const (map (flipAppend r) (aux1 t ts [] p) ++ map (flipAppend r) (mapInterleave t ts ps []))
         (lemmaAppendId (map (flipAppend r) (interleave t ts p [])))
  `asTypeOf`
   const (map (flipAppend r) (aux1 t ts [] p ++ mapInterleave t ts ps []))
         (lemmaMapAppend (flipAppend r) (aux1 t ts [] p) (mapInterleave t ts ps []))
  `asTypeOf`
   const (map (flipAppend r) (aux1 t ts [] p ++ concat (map (aux1 t ts []) ps) ++ []))
         (mapInterleave t ts ps [])
  `asTypeOf`
   const (map (flipAppend r) ((aux1 t ts [] p ++ concat (map (aux1 t ts []) ps)) ++ []))
         (lemmaAppendAssoc (aux1 t ts [] p) (concat (map (aux1 t ts []) ps)) [])
  `asTypeOf`
   map (flipAppend r) (mapInterleave t ts (p:ps) [])
  ***
  QED
-}

{-@
lemmaAppendAux0
  :: t:a
  -> p:[a]
  -> ts:[a]
  -> r:[a]
  -> xs:[Int]
  -> { map (aux0 t id p (ts ++ r)) xs == map (flipAppend r) (map (aux0 t id p ts) xs) }
@-}
lemmaAppendAux0  :: a -> [a] -> [a] -> [a] -> [Int] -> ()
lemmaAppendAux0 t p ts r [] = ()
lemmaAppendAux0 t p ts r (x:xs) =
  lemmaAppendAux0 t p ts r xs
    ? lemmaAppendAssoc (insertAt x t p) ts r

{-@
lemmaMapAux2
  :: t:a
  -> ts:[a]
  -> is:[a]
  -> { i:Int | 0 <= i }
  -> { j:Int | j < len ts }
  -> { map (aux2 ts (t:is)) (fromTo i j)
         == map (aux2 (t:ts) is) (fromTo (i+1) (j+1))
     } / [j-i+1]
@-}
lemmaMapAux2 :: a -> [a] -> [a] -> Int -> Int -> ()
lemmaMapAux2 t ts is i j =
  if i<=j then
    lemmaMapAux2 t ts is (i+1) j
      `const` lemmaAppendAssoc (reverse (take i ts)) [t] is
{-
    map (aux2 ts (t:is)) (fromTo i j)
    ===
    aux2 ts (t:is) i : map (aux2 ts (t:is)) (fromTo (i+1) j)
    ===
    const (aux2 ts (t:is) i : map (aux2 (t:ts) is) (fromTo (i+2) (j+1)))
          (lemmaMapAux2 t ts is (i+1) j)
    ===
    (mapInterleave (ts!!i) (drop (i+1) ts) (permutations (reverse (take i ts) ++ (t:is))) []
      : map (aux2 (t:ts) is) (fromTo (i+2) (j+1))
    )
    ===
    (mapInterleave (ts!!i) (drop (i+1) ts) (permutations (reverse (take i ts) ++ [t] ++ is)) []
       : map (aux2 (t:ts) is) (fromTo (i+2) (j+1))
    )
    ===
    const (mapInterleave (ts!!i) (drop (i+1) ts) (permutations ((reverse (take i ts) ++ [t]) ++ is)) []
             : map (aux2 (t:ts) is) (fromTo (i+2) (j+1))
          )
          (lemmaAppendAssoc (reverse (take i ts)) [t] is)
    ===
    (mapInterleave ((t:ts)!!(i+1)) (drop (i+2) (t:ts)) (permutations (reverse (take (i+1) (t:ts)) ++ is)) []
       : map (aux2 (t:ts) is) (fromTo (i+2) (j+1))
    )
    ===
    (aux2 (t:ts) is (i+1) : map (aux2 (t:ts) is) (fromTo (i+2) (j+1))
    ***
    QED
    -}
  else
    ()
