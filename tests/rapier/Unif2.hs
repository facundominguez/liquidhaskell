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
import Debug.Trace qualified

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
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

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
  deriving (Eq, Ord, Show)

-- | A language of first order formulas with equality, conjunction, implication
-- and quantifiers.
data Formula
  = Eq Term Term
  | Conj Formula Formula
    -- | The implication form is constrained to allow only one
    -- equality in the antecedent.
  | Then (Term, Term) Formula
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
      Then eq1 f2 -> Then eq1 <$> go f2
      Eq t0 t1 -> pure $ Eq t0 t1

-- | Replaces existential variables with skolem functions
--
-- Every time that `SA (i,s)` occurs, the domain of `s` is exactly the set of
-- bound variables in scope.
skolemize :: Formula -> Formula
skolemize = go Map.empty []
  where
    -- eenv tells for every existential variable the skolem function to replace
    -- it with
    --
    -- uvs are the universally quantified variables in scope
    go :: Map Var Term -> [Var] -> Formula -> Formula
    go eenv uvs f0 = case f0 of
      Forall v f ->
        Forall v $ go eenv (v : uvs) f

      Exists v f ->
        let eenv' = Map.insert v (mkSkolemApp v uvs) eenv
         in go eenv' uvs f

      Conj f1 f2 -> Conj (go eenv uvs f1) (go eenv uvs f2)
      Then (t0, t1) f2 ->
        let s = fromListSubst (Map.toList eenv)
            -- substitute variables with the skolem functions
         in Then (substitute s t0, substitute s t1) (go eenv uvs f2)
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
    Exists v f
      | Set.member v scope ->
        let u = freshVar scope
            scope' = Set.insert u scope
            s' = extendSubst s v (V u)
            f' = substituteFormula scope' s' f
         in
            Exists u f'
      | otherwise ->
        let scope' = Set.insert v scope
            -- This has the effect of canceling the substitution of v
            -- whatever it was in s
            s' = extendSubst s v (V v)
            f' = substituteFormula scope' s' f
         in
            Exists v f'
    Conj f1 f2 -> Conj (substituteFormula scope s f1) (substituteFormula scope s f2)
    Then (t0, t1) f2 ->
      Then (substitute s t0, substitute s t1) (substituteFormula scope s f2)
    Eq t0 t1 -> Eq (substitute s t0) (substitute s t1)

-- | @toPrenex f@ transforms a formula into prenex normal form by moving all
-- the universal quantifiers to the front.
toPrenex :: Formula -> Formula
toPrenex f0 =
    let (vs, f') = go f0
     in foldr Forall f' vs
  where
    go (Forall v f) =
      let (vs, f') = go f
       in (v : vs, f')
    go (Exists v f) = error "toPrenex: unexpected"
    go (Conj f1 f2) =
      let (vs1, f1') = go f1
          (vs2, f2') = go f2
       in (vs1 ++ vs2, Conj f1' f2')
    go (Then eq1 f2) = Then eq1 <$> go f2
    go f@(Eq {}) = ([], f)


-- | Removes implications from the formula by substituting in the consequent
--
-- @x == t -> f@ becomes @f[x:=t]@
removeImplications :: Formula -> Formula
removeImplications = go
  where
    go (Forall v f) = Forall v (go f)
    go (Exists v f) = Exists v (go f)
    go (Conj f1 f2) = Conj (go f1) (go f2)
    go (Then eq1 f2) =
      case eq1 of
        -- The scope of the substitution is empty since we don't expect
        -- quantifiers in f or f2. This is a hack, but a hack that acomplishes
        -- the same as computing the appropriate scope.
        (V v, t) -> go $ substituteFormula mempty (fromListSubst [(v, t)]) f2
        (t, V v) -> go $ substituteFormula mempty (fromListSubst [(v, t)]) f2
        (U, U) -> go f2
        (L t1, L t2) -> go $ Then (t1, t2) f2
        (P ta1 ta2, P tb1 tb2) -> go $ Then (ta1, ta2) $ Then (tb1, tb2) f2
        (SA{}, _) -> Then eq1 $ go f2
        (_, SA{}) -> Then eq1 $ go f2
        _ -> Eq U U
    go f@(Eq {}) = f

-- | Removes constructors from equalities
--
-- @P a b == P c d -> e@ becomes @a == c -> b == d -> e@
removeConstructors :: Formula -> Formula
removeConstructors = go
  where
    go (Forall v f) = Forall v (go f)
    go (Exists v f) = Exists v (go f)
    go (Conj f1 f2) = Conj (go f1) (go f2)
    go (Then (t0, t1) f2) =
      foldr Then (go f2) $ goEq t0 t1
    go (Eq t0 t1) = case goEq t0 t1 of
      [] -> Eq U U
      xs -> foldr1 Conj $ map (uncurry Eq) xs

    goEq :: Term -> Term -> [(Term, Term)]
    goEq (L t1) (L t2) = goEq t1 t2
    goEq (P ta1 ta2) (P tb1 tb2) = goEq ta1 ta2 ++ goEq tb1 tb2
    goEq t0 t1 = [(t0, t1)]

-- | Assign terms to skolem functions.
--
-- When @unify@ returns pairs @(i, t) :: (Int, Term)@, @t@'s free variables are
-- in the scope of @i@ (the domain of the accompanying substitution).
--
-- Example:
--
-- > unify (t == SA (i, s))@ is @[(i, substitute (inverseSubst s) t)
--
unify :: Formula -> [(Int, Term)]
unify = go
  where
    go (Forall v f) = go f
    go (Exists v f) = go f
    go (Conj f1 f2) = go f1 ++ go f2
    go (Then _ f2) = go f2
    go (Eq t0 t1) = goEq t0 t1
      -- Checks to consider:
      --  * occurs check
      --  * scope check: the free variables of t are in the range of the substitution
    goEq t (SA (i, s))
      | Set.isSubsetOf (freeVars t) (freeVarsSubst (narrowForInvertibility s)) =
         case inverseSubst $ narrowForInvertibility s of
           Nothing -> []
           Just s' -> [(i, substitute s' t)]
    goEq (SA (i, s)) t
      | Set.isSubsetOf (freeVars t) (freeVarsSubst (narrowForInvertibility s)) =
         case inverseSubst $ narrowForInvertibility s of
           Nothing -> []
           Just s' -> [(i, substitute s' t)]
    goEq _ _ = []

-- TODO: consider what to do when unification introduces equalities of
-- constructors that might need to be eliminated

-- | @narrowForInvertibility s@ removes variables from @s@ if the range
-- is not a variable.
narrowForInvertibility :: Subst Term -> Subst Term
narrowForInvertibility (Subst xs) = Subst [(i, V j) | (i, V j) <- xs]

-- | @narrowInvertedSubst t s@ removes variables from the inversion of @s@
-- if the range doesn't match any subterm of @t@.
narrowInvertedSubst :: Term -> Subst Term -> Subst Term
narrowInvertedSubst t (Subst xs) =
  Subst [(i, t) | (i, t) <- xs, Set.member t s]
  where
    s = subTerms t

subTerms :: Term -> Set Term
subTerms t = Set.insert t (properSubTerms t)
  where
    properSubTerms :: Term -> Set Term
    properSubTerms (V _) = Set.empty
    properSubTerms (SA (_, s)) = subTermsSubst s
    properSubTerms U = Set.empty
    properSubTerms (L t1) = subTerms t1
    properSubTerms (P t1 t2) = Set.union (subTerms t1) (subTerms t2)

    subTermsSubst :: Subst Term -> Set Term
    subTermsSubst (Subst xs) = Set.unions $ map (subTerms . snd) xs

-- TODO: consider what to do with non-invertible substitutions like ?v[x\z,y\z] ?= z
--
-- At the moment we just pick the first of the variables with a duplicated
-- range.
inverseSubst :: Subst Term -> Maybe (Subst Term)
inverseSubst (Subst xs) = Subst <$> go xs
  where
    go [] = Just []
    go ((i, V j) : xs) = ((j, V i) :) <$> go xs
    go _ = Nothing

--- | Assign terms to existential variables in an attempt to make a formula
-- true.
unifyFormula :: Formula -> [(Int, Term)]
unifyFormula =
    traceUnify
          "                     unify" .
    unify .
    trace "        removeConstructors" .
    removeConstructors .
    trace "        removeImplications" .
    removeImplications .
    trace "                  toPrenex" .
    toPrenex .
    trace "                 skolemize" .
    skolemize .
    trace "                    rename" .
    rename Set.empty .
    trace "                   initial"
  where
    trace :: String -> Formula -> Formula
    trace label f = Debug.Trace.trace (label ++ ": " ++ ppFormula prettyName f) f
    traceUnify :: String -> [(Int, Term)] -> [(Int, Term)]
    traceUnify label xs = Debug.Trace.trace (label ++ ": " ++ showUnification xs) xs
    showUnification :: [(Int, Term)] -> String
    showUnification xs =
      let xs' = map (\(i, t) -> (prettyName i, ppTerm prettyName t)) xs
       in "[" ++ List.intercalate ", " (map (\(i, t) -> i ++ ":=" ++ t) xs') ++ "]"

-- pretty printing

-- | Pretty print a variable name
prettyName :: Int -> String
prettyName = ((["x", "y", "z", "u", "v", "w"] ++ [ "v" ++ show i | i <- [1..] ]) !!)

-- | Pretty print a formula
ppFormula :: (Int -> String) -> Formula -> String
ppFormula vnames = go
  where
    go (Forall v f) = "∀" ++ (vnames v) ++ ". " ++ go f
    go (Exists v f) = "∃" ++ (vnames v) ++ ". " ++ go f
    go (Conj f1 f2) = "(" ++ go f1 ++ ") ∧ (" ++ go f2 ++ ")"
    go (Then (t0, t1) f2) = go (Eq t0 t1) ++ " → " ++ go f2
    go (Eq t0 t1) = ppTerm vnames t0 ++ " == " ++ ppTerm vnames t1

ppTerm :: (Int -> String) -> Term -> String
ppTerm vnames t =
  case t of
    V i -> vnames i
    SA (i, s) -> vnames i ++ ppSubst vnames s
    U -> "U"
    L t1 -> "L(" ++ ppTerm vnames t1 ++ ")"
    P t1 t2 -> "P(" ++ ppTerm vnames t1 ++ ", " ++ ppTerm vnames t2 ++ ")"

ppSubst :: (Int -> String) -> Subst Term -> String
ppSubst vnames (Subst xs) =
  "[" ++ List.intercalate ", " (map (\(i, t) -> vnames i ++ ":=" ++ ppTerm vnames t) xs) ++ "]"


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

tf4 :: Formula
tf4 = Forall 0 $ Forall 1 $
  (V 0, L (V 1)) `Then` Exists 2 (Eq (V 0) (L (V 2)))

tf5 :: Formula
tf5 = Forall 0 $ Forall 1 $
  (V 0, L (V 1)) `Then` Forall 1 ((V 1, V 0) `Then` Exists 2 (Eq (V 1) (L (V 2))))

tf6 :: Formula
tf6 = Forall 0 $ Forall 0 $ Exists 1 (Eq (V 1) (V 0))

tf7 :: Formula
tf7 = Forall 0 $ Exists 1 $ Exists 2 $ (V 0, V 1) `Then` Eq (V 0) (V 2)
