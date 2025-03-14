{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--ple" @-}
{- LIQUID "--smtsolver=cvc5" @-}
module Subst3 where

import Data.Maybe
import Data.Set
import Language.Haskell.Liquid.ProofCombinators ((?), (===), (==.), (==!), (***), QED(QED, Admit))

data Exp
  = Var Int
  | App Exp Exp
  | Lam Int Exp

{-@ measure freeVars @-}
freeVars :: Exp -> Set Int
freeVars = \case
    Var i -> singleton i
    App e0 e1 -> union (freeVars e0) (freeVars e1)
    Lam i e -> difference (freeVars e) (singleton i)

{-@ assume freshVar :: s:Set Int -> {v:Int | not (member v s)} @-}
freshVar :: Set Int -> Int
freshVar s = case lookupMax s of
    Nothing -> 0
    Just i -> i + 1

{-@ reflect freeVarsMaybe @-}
freeVarsMaybe :: Maybe Exp -> Set Int
freeVarsMaybe Nothing = empty
freeVarsMaybe (Just e) = freeVars e

{-@
type ScopedExp S = {e:Exp | isSubsetOf (freeVars e) S}
@-}

--------------------------------------------
-- A replaceable type for substitutions
--------------------------------------------

newtype Subst e = Subst [(Int, e)]

-- | A type with an assumed concrete representation
--
-- In contrast, we consider @Subst e@ as abstract/opaque.
type Assoc e = [(Int, e)]

-- | In the logic, we will reason with substitutions as if they were
-- association lists. @asAssoc s@ provides the association list of @s@.
--
-- We leave the function undefined to signal that it is only intended
-- to be used in the logic.
--
{-@ opaque-reflect asAssoc @-}
asAssoc :: Subst e -> Assoc e
asAssoc = undefined


{-@ reflect domain @-}
domain :: Assoc e -> Set Int
domain [] = empty
domain ((i, _) : s) = union (singleton i) (domain s)

-- | @freeVarsSubst used s@ computes the set of free variables in the range of
-- the substitution @s@ that will be used according to the set @used@.
--
-- Thus, @freeVars e0[x:=e1]@ include @freeVarsSubst (freeVars e0) [(x, e1)]@.
--
{-@ reflect freeVarsSubst @-}
freeVarsSubst :: Set Int -> Assoc Exp -> Set Int
freeVarsSubst used [] = empty
freeVarsSubst used ((i, e) : s) =
    if member i used then
      union
        (freeVars e)
        -- only add the free vars of the first occurrence of i
        (freeVarsSubst (difference used (singleton i)) s)
    else
      freeVarsSubst used s

{-@ inline extendAssoc @-}
extendAssoc :: Assoc e -> Int -> e -> Assoc e
extendAssoc s i e = (i, e) : s

{-@
assume extendSubst
  :: s:Subst a
  -> i:Int
  -> e:a
  -> { v:_
     |  union (domain (asAssoc s)) (singleton i) = domain (asAssoc v)
     && asAssoc v == extendAssoc (asAssoc s) i e
     }
@-}
extendSubst :: Subst a -> Int -> a -> Subst a
extendSubst (Subst s) i e = Subst ((i, e) : s)

{-@
assume lookupSubst
  :: i:Int
  -> s:Subst e
  -> { m:Maybe e
     | isJust m == member i (domain (asAssoc s))
     && m == lookupAssoc i (asAssoc s)
     }
@-}
lookupSubst :: Int -> Subst e -> Maybe e
lookupSubst i (Subst xs) = lookup i xs

{-@
reflect lookupAssoc
lookupAssoc
  :: i:Int
  -> s:Assoc e
  -> {m:Maybe e | isJust m == member i (domain s) }
@-}
lookupAssoc :: Int -> Assoc b -> Maybe b
lookupAssoc _ [] = Nothing
lookupAssoc x ((y, b) : xs)
    | x == y = Just b
    | otherwise = lookupAssoc x xs


-------------------------------------------
-- applying substitutions to expressions
-------------------------------------------

{-@
substitute
  :: scope:Set Int
  -> s:Subst (ScopedExp scope)
  -> {ei:Exp | isSubsetOf (difference (freeVars ei) (domain (asAssoc s))) scope }
  -> {v:Exp
     |    freeVars v
       ==
          union
            (difference (freeVars ei) (domain (asAssoc s)))
            (freeVarsSubst (freeVars ei) (asAssoc s))
     }
@-}
substitute :: Set Int -> Subst Exp -> Exp -> Exp
substitute scope s = \case
    Var i -> case lookupSubst i s of
      Nothing -> Var i  ? lemma_freeVarsSubst_sing i (asAssoc s)
      Just e -> e ? lemma_freeVarsSubst_sing i (asAssoc s)
    App e0 e1 ->
      App
        (substitute scope s e0)
        (substitute scope s e1)
      ? lemma_freeVarsSubst_union (freeVars e0) (freeVars e1) (asAssoc s)
    Lam i e
      | member i scope ->
          let j = freshVar scope
           in Lam j $
                substitute
                  (insert j scope)
                  (extendSubst s i (Var j))
                  e
                ? lemma_freeVarsSubst_extend scope (freeVars e) i (Var j) (asAssoc s)
      | otherwise ->
          Lam i $
            substitute
              (insert i scope)
              -- This has the effect of canceling the substitution of i
              -- whatever it was in f
              (extendSubst s i (Var i))
              e
            ? lemma_freeVarsSubst_extend scope (freeVars e) i (Var i) (asAssoc s)

----------
-- Lemmas
----------

{-@
lemma_freeVarsSubst_empty
  :: used:_
  -> {s:_ | Data.Set.null (intersection used (domain s))}
  -> { freeVarsSubst used s == empty }
@-}
lemma_freeVarsSubst_empty :: Set Int -> Assoc Exp -> ()
lemma_freeVarsSubst_empty used [] = ()
lemma_freeVarsSubst_empty used (_ : s) = lemma_freeVarsSubst_empty used s

{-@
lemma_freeVarsSubst_empty_long
  :: used:_
  -> {s:_ | Data.Set.null (intersection used (domain s))}
  -> { freeVarsSubst used s == empty }
@-}
lemma_freeVarsSubst_empty_long :: Set Int -> Assoc Exp -> ()
lemma_freeVarsSubst_empty_long used [] = ()
lemma_freeVarsSubst_empty_long used ((i, e) : s) =
        freeVarsSubst used ((i, e) : s)
    === -- unfold freeVarsSubst
        ( if member i used then
            union
              (freeVars e)
              (freeVarsSubst (difference used (singleton i)) s)
          else
            freeVarsSubst used s
        )
    === -- hypothesis: not (member i used)
        freeVarsSubst used s ? lemma_freeVarsSubst_empty_long used s
    === -- inductive hypothesis
        empty
    ***
        QED


{-
lemma_freeVarsSubst_sing :: Int -> Assoc Exp -> ()
lemma_freeVarsSubst_sing _ [] = ()
lemma_freeVarsSubst_sing i ((j, _) : s)
    | i == j =
      lemma_freeVarsSubst_empty empty s
    | otherwise =
      lemma_freeVarsSubst_sing i s ? lemma_freeVarsSubst_empty empty s
-}

{-@
lemma_freeVarsSubst_sing
  :: i:_
  -> s:_
  -> { freeVarsSubst (singleton i) s == freeVarsMaybe (lookupAssoc i s) }
@-}
lemma_freeVarsSubst_sing :: Int -> Assoc Exp -> ()
lemma_freeVarsSubst_sing _ [] = ()
lemma_freeVarsSubst_sing i ((j, e) : s) | i == j =
        freeVarsSubst (singleton i) ((j, e) : s)
    ==. -- unfold freeVarsSubst
        union
          (freeVars e)
          (freeVarsSubst (difference (singleton i) (singleton j)) s)
    ==. -- inductive hypothesis
        union
          (freeVars e)
          (empty ? lemma_freeVarsSubst_empty empty s)
    ==. -- set simplification
        freeVars e
    ==. -- unfold lookupAssoc and freeVarsMaybe
        freeVarsMaybe (lookupAssoc i ((j, e) : s))
    ***
        QED
lemma_freeVarsSubst_sing i ((j, e) : s) | otherwise =
    lemma_freeVarsSubst_sing i s ? lemma_freeVarsSubst_empty empty s


{-@
lemma_freeVarsSubst_union
  :: s1:_
  -> s2:_
  -> s:_
  -> { freeVarsSubst (union s1 s2) s
       == union (freeVarsSubst s1 s) (freeVarsSubst s2 s) }
@-}
lemma_freeVarsSubst_union :: Set Int -> Set Int -> Assoc Exp -> ()
lemma_freeVarsSubst_union _ _ [] = ()
lemma_freeVarsSubst_union s1 s2 ((i, _) : s) =
    lemma_freeVarsSubst_union
      (difference s1 (singleton i))
      (difference s2 (singleton i))
      s

{-@
lemma_freeVarsSubst_scoped
  :: scope:_
  -> used:_
  -> s:Assoc (ScopedExp scope)
  -> { isSubsetOf (freeVarsSubst used s) scope }
@-}
lemma_freeVarsSubst_scoped :: Set Int -> Set Int -> Assoc Exp -> ()
lemma_freeVarsSubst_scoped _ _ [] = ()
lemma_freeVarsSubst_scoped scope used ((i, _) : s) =
    lemma_freeVarsSubst_scoped scope (difference used (singleton i)) s

{-@
lemma_freeVarsSubst_extend
  :: scope:_
  -> used:_
  -> i:_
  -> {e:_ | Data.Set.null (intersection (freeVars e) scope)}
  -> s:Assoc (ScopedExp scope)
  -> { freeVarsSubst (difference used (singleton i)) s ==
       difference (freeVarsSubst used (extendAssoc s i e)) (freeVars e)
     }
@-}
lemma_freeVarsSubst_extend :: Set Int -> Set Int -> Int -> Exp -> Assoc Exp -> ()
lemma_freeVarsSubst_extend scope used i _ s =
    lemma_freeVarsSubst_scoped scope (difference used (singleton i)) s

