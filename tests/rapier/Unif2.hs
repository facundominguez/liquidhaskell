{-# LANGUAGE GHC2024 #-}

-- | In progress
module Unif2 where

import Control.Monad
import Control.Monad.State
import Data.Foldable qualified as Foldable
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

-- | We have plain variables
type Var = Int
-- | And we have applications of skolem functions for existential variables that
-- might have a pending substitution.
--
-- The applications are only allowed to be instantiated by unification
-- with terms whose free variables are in the domain of the substitution.
--
-- All occurrences of a skolem function must have pending substitutions
-- with exactly the same domain since the domain of the substitution gives
-- the arity of the skolem function.
type SkolemApp = (Int, Subst Term)

--------------------------------------
-- Substitutions and their operations
--------------------------------------

newtype Subst t = Subst [(Var,t)]
  deriving (Show, Functor, Foldable, Traversable)

lookupSubst :: Var -> Subst e -> Maybe e
lookupSubst i (Subst s) = lookup i s

emptySubst :: Subst e
emptySubst = Subst []

extendSubst :: Subst a -> Var -> a -> Subst a
extendSubst (Subst s) i e = Subst ((i, e) : s)

fromListSubst :: [(Var, t)] -> Subst t
fromListSubst = Subst

-----------------------
-- The logic language
-----------------------

-- | A language of terms with variables, functions, and constants.
data Term
  = V Var
  | SA SkolemApp
  -- Data constructors of the language (i.e. they are injective)
  | U
  | L Term
  | P Term Term
  deriving Show

-- | A language of first order formulas with equality, conjunction, implication
-- and quantifiers.
data Formula
  = Eq Term Term
  | Conj Formula Formula
  | Then Formula Formula
  | Exists Var Formula
  | Forall Var Formula
  deriving Show

{-@ measure freeVars @-}
freeVars :: Term -> Set Int
freeVars = \case
    V i -> Set.singleton i
    SA (_, s) -> freeVarsSubst s
    U -> Set.empty
    L t -> freeVars t
    P t0 t1 -> Set.union (freeVars t0) (freeVars t1)

freeVarsSubst :: Subst Term -> Set Int
freeVarsSubst (Subst s) = foldMap (freeVars . snd) s

{-@ assume freshVar :: s:Set Int -> {v:Int | not (member v s)} @-}
freshVar :: Set Int -> Int
freshVar s = case Set.lookupMax s of
    Nothing -> 0
    Just i -> i + 1

{-@
type ScopedTerm S = {t:Term | isSubsetOf (freeVars t) S}
@-}


------------------
-- Normalization
------------------

-- The goal of this normalization is to put a formula in prenex normal form,
-- eliminating existential quantification via skolemization and removing
-- implications via substitution and injectivity of term constructors.

-- | Rename universal and existential variables when they are bound more than
-- once.
--
rename
  :: Set Int -- the set of variables that can appear free in the input formula
  -> Formula
  -> Formula
rename scope0 ff0 = evalState (go ff0) Set.empty
  where
    go f0 = get >>= \bs -> case f0 of
      Forall v f
        | Set.member v bs -> do
          -- if v is already in the bound set, we rename it
          let u = freshVar bs
              bs' = Set.insert u bs
              f' = substituteFormula bs' (fromListSubst [(v, V u)]) f
          put bs'
          Forall u <$> go f'
        | otherwise -> do
           put (Set.insert v bs)
           Forall v <$> go f

      Exists v f
        | Set.member v bs -> do
          -- if v is already in the bound set, we rename it
          let u = freshVar bs
              bs' = Set.insert u bs
              f' = substituteFormula bs' (fromListSubst [(v, V u)]) f
          put bs'
          Exists u <$> go f'
        | otherwise -> do
           modify (Set.insert v)
           Exists v <$> go f

      Conj f1 f2 -> Conj <$> go f1 <*> go f2
      Then f1 f2 -> Then <$> go f1 <*> go f2
      Eq t0 t1 -> pure $ Eq t0 t1

-- | Replaces existential variables with skolem functions
--
-- It also has the side effect of renaming universally quantified variables that
-- are bound more than once.
skolemize :: Formula -> Formula
skolemize = go Map.empty []
  where
    -- eenv tells for every existential variable the skolem function to replace
    -- it with
    --
    -- uvs are the universally quantified variables in scope
    go eenv uvs f0 = case f0 of
      Forall v f ->
        Forall v $ go eenv (v : uvs) f

      Exists v f ->
        let eenv' = Map.insert v (mkSkolemApp v uvs) eenv
         in go eenv' uvs f

      Conj f1 f2 -> Conj (go eenv uvs f1) (go eenv uvs f2)
      Then f1 f2 -> Then (go eenv uvs f1) (go eenv uvs f2)
      Eq t0 t1 -> do
        let s = fromListSubst (Map.toList eenv)
            -- substitute variables with the skolem functions
         in Eq (substitute s t0) (substitute s t1)

-- | @mkSkolemApp v uvs@ makes a term with a skolem application for the
-- existential variable @v@ and the universally quantified variables in
-- scope @uvs@.
mkSkolemApp :: Var -> [Var] -> Term
mkSkolemApp v uvs = SA (v, idSubst uvs)
  where
    idSubst :: [Var] -> Subst Term
    idSubst vs = fromListSubst [(v, V v) | v <- vs]

substitute :: Subst Term -> Term -> Term
substitute s t = case t of
    V v -> case lookupSubst v s of
      Nothing -> V v
      Just t1 -> t1
    SA (v, s1) -> SA (v, composeSubst s1 s)
    U -> U
    L t1 -> L (substitute s t1)
    P t1 t2 -> P (substitute s t1) (substitute s t2)
  where
    composeSubst :: Subst Term -> Subst Term -> Subst Term
    composeSubst (Subst xs) s = Subst (map (fmap (substitute s)) xs)

substituteFormula :: Set Int -> Subst Term -> Formula -> Formula
substituteFormula scope s = \case
    Forall v f
      | Set.member v scope ->
        let u = freshVar scope
            scope' = Set.insert u scope
            s' = extendSubst s v (V u)
            f' = substituteFormula scope' s' f
         in
            Forall u f'
      | otherwise ->
        let scope' = Set.insert v scope
            -- This has the effect of canceling the substitution of v
            -- whatever it was in s
            s' = extendSubst s v (V v)
            f' = substituteFormula scope' s' f
         in
            Forall v f'
    Exists v f -> Exists v (substituteFormula scope s f)
    Conj f1 f2 -> Conj (substituteFormula scope s f1) (substituteFormula scope s f2)
    Then f1 f2 -> Then (substituteFormula scope s f1) (substituteFormula scope s f2)
    Eq t0 t1 -> Eq (substitute s t0) (substitute s t1)

-- Test formulas

tf0 :: Formula
tf0 = Forall 0 $ Exists 1 $ V 1 `Eq` V 0

tf1 :: Formula
tf1 =
  Forall 0 $ Exists 1 $ Forall 2 $
    (V 1 `Eq` V 0) `Conj` (Exists 1 $ V 1 `Eq` V 2)

tf2 :: Formula
tf2 =
  Forall 0 $ Exists 1 $
    (V 1 `Eq` V 0) `Conj` (Forall 2 $ Exists 1 $ V 1 `Eq` V 2)

tf3 :: Formula
tf3 =
  Conj
    (Forall 1 $ Exists 0 $ V 0 `Eq` V 1)
    (Forall 2 $ Exists 0 $ V 0 `Eq` V 2)


-- removal of implications and computation of prenex normal form still needs to
-- be implemented.

