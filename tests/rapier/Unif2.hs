{-# LANGUAGE GHC2024 #-}

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--exactdc" @-}

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
import Language.Haskell.Liquid.ProofCombinators

{-@ infixr ++ @-}

-- | We use a custom type for pairs to workaround bugs in Liquid Haskell
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2536
data P2 a b = P2 { fst2 :: a, snd2 :: b }
  deriving (Eq, Ord, Show)
{-@ data P2 a b = P2 { fst2 :: a, snd2 :: b } @-}

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

data Subst t = Subst [(Var,t)]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

lookupSubst :: Var -> Subst e -> Maybe e
lookupSubst i (Subst s) = lookup i s

emptySubst :: Subst e
emptySubst = Subst []

extendSubst :: Subst a -> Var -> a -> Subst a
extendSubst (Subst s) i e = Subst ((i, e) : s)

fromListSubst :: [(Var, t)] -> Subst t
fromListSubst = Subst

fromListSubstP2 :: [P2 Var t] -> Subst t
fromListSubstP2 = Subst . map (\(P2 i t) -> (i, t))

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

{-@ opaque-reflect freeVarsSubst @-}

{-@ ignore freeVarsSubst @-}
freeVarsSubst :: Subst Term -> Set Int
freeVarsSubst (Subst s) = Set.unions $ map (freeVars . snd) s

{-@ assume freshVar :: s:Set Int -> {v:Int | not (member v s)} @-}
freshVar :: Set Int -> Int
freshVar s = case Set.lookupMax s of
    Nothing -> 0
    Just i -> i + 1

{-@
type ScopedTerm S = {t:Term | isSubsetOf (freeVars t) S}
@-}

-- | The size of a formula is the number of its subformulas.
{-@ measure formulaSize @-}
{-@ formulaSize :: Formula -> Nat @-}
formulaSize :: Formula -> Int
formulaSize (Forall _ f) = 1 + formulaSize f
formulaSize (Exists _ f) = 1 + formulaSize f
formulaSize (Conj f1 f2) = 1 + formulaSize f1 + formulaSize f2
formulaSize (Then _ f2) = 1 + formulaSize f2
formulaSize (Eq t0 t1) = 1


------------------
-- Normalization
------------------

-- The goal of this normalization is to put a formula in prenex normal form,
-- eliminating existential quantification via skolemization and removing
-- implications via substitution and injectivity of term constructors.

-- | Rename universal and existential variables when they are bound more than
-- once.
--
{-@ ignore rename @-}
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
{-@ ignore skolemize @-}
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

{-@ ignore substitute @-}
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

{-@
substituteFormula
  :: Set Int
  -> Subst Term
  -> f:Formula
  -> {v:Formula | formulaSize f == formulaSize v}
@-}
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


{-@
lazy substituteSkolemsTerm
assume substituteSkolemsTerm
  :: Subst Term
  -> t:Term
  -> {v:Term |
       isSubsetOf (Set.listElts (scopesTerm v)) (Set.listElts (scopesTerm t))
     }
@-}
substituteSkolemsTerm :: Subst Term -> Term -> Term
substituteSkolemsTerm s t = case t of
    V v -> V v
    SA (v, s1) -> case lookupSubst v s of
      Just t1 -> substituteSkolemsTerm s1 t1
      Nothing -> SA (v, composeSubst s1 s)
    U -> U
    L t1 -> L (substituteSkolemsTerm s t1)
    P t1 t2 -> P (substituteSkolemsTerm s t1) (substituteSkolemsTerm s t2)
  where
    {-@ ignore composeSubst @-}
    composeSubst :: Subst Term -> Subst Term -> Subst Term
    composeSubst (Subst xs) s = Subst (map (fmap (substituteSkolemsTerm s)) xs)


{-@ opaque-reflect scopesSubst @-}
scopesSubst :: Subst Term -> [(Int, Set Int)]
scopesSubst (Subst xs) = concatMap (scopesTerm . snd) xs

-- opaque-reflect is needed so substituteSkolems can be used in the logic when
-- proving properties in the body of unify.
{-@ opaque-reflect substituteSkolems @-}
-- LH can show that substituteSkolems preserves formulaSize, but we need reacher
-- specifications for auxiliary functions if we want to verify the relationship
-- between scopes.
{-@
assume substituteSkolems
  :: s:Subst Term
  -> f:Formula
  -> {v:Formula |
          formulaSize f == formulaSize v
       && Set.isSubsetOf (Set.listElts (scopes v)) (Set.union (Set.listElts (scopesSubst s)) (Set.listElts (scopes f)))
     }
@-}
substituteSkolems :: Subst Term -> Formula -> Formula
substituteSkolems s = \case
    Forall v f ->
        let -- This has the effect of canceling the substitution of v
            -- whatever it was in s
            s' = extendSubst s v (V v)
            f' = substituteSkolems s' f
         in
            Forall v f'
    Exists v f ->
        let -- This has the effect of canceling the substitution of v
            -- whatever it was in s
            s' = extendSubst s v (V v)
            f' = substituteSkolems s' f
         in
            Exists v f'
    Conj f1 f2 -> Conj (substituteSkolems s f1) (substituteSkolems s f2)
    Then (t0, t1) f2 ->
      Then (substituteSkolemsTerm s t0, substituteSkolemsTerm s t1) (substituteSkolems s f2)
    Eq t0 t1 -> Eq (substituteSkolemsTerm s t0) (substituteSkolemsTerm s t1)

{-@
assume lemmaScopesSubst
  :: s:[(Int, Set Int)]
  -> ss:Subst {t:Term | isSubsetOf (Set.listElts (scopesTerm t)) (Set.listElts s)}
  -> { Set.isSubsetOf (Set.listElts (scopesSubst ss)) (Set.listElts s) }
@-}
lemmaScopesSubst :: [(Int, Set Int)] -> Subst Term -> ()
lemmaScopesSubst _ _ = ()

{-@
assume lemmaScopesAppend
  :: s0:[(Int, Set Int)]
  -> s1:[(Int, Set Int)]
  -> { Set.listElts (s0 ++ s1) = Set.union (Set.listElts s0) (Set.listElts s1) }
@-}
lemmaScopesAppend :: [(Int, Set Int)] -> [(Int, Set Int)] -> ()
lemmaScopesAppend _ _ = ()

{-@
assume lemmaScopesAppend2
  :: s0:[(Int, Set Int)]
  -> s1:[(Int, Set Int)]
  -> { Set.listElts (append s0 s1) = Set.union (Set.listElts s0) (Set.listElts s1) }
@-}
lemmaScopesAppend2 :: [(Int, Set Int)] -> [(Int, Set Int)] -> ()
lemmaScopesAppend2 _ _ = ()


-- | @toPrenex f@ transforms a formula into prenex normal form by moving all
-- the universal quantifiers to the front.
{-@ ignore toPrenex @-}
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
{-@ ignore removeImplications @-}
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
        (P ta1 ta2, P tb1 tb2) -> go $ Then (ta1, tb1) $ Then (ta2, tb2) f2
        (SA{}, _) -> Then eq1 $ go f2
        (_, SA{}) -> Then eq1 $ go f2
        _ -> Eq U U
    go f@(Eq {}) = f

-- | Removes constructors from equalities
--
-- @P a b == P c d -> e@ becomes @a == c -> b == d -> e@
{-@ ignore removeConstructors @-}
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
{-@ unify :: f:Formula -> [{p:_ | isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) (scopes f)) }] @-}
{-@ ignore unify @-} -- passes verification, but disabled for performance
unify :: Formula -> [P2 Int Term]
unify = go
  where
    {-@
        go
          :: f:Formula
          -> [ {p:_ |
                   isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) (scopes f))
                && isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts (scopes f))
               }
             ] / [formulaSize f]
      @-}
    {- rewriteWith go [lemmaScopesAppend, lemmaScopesAppend2] @-}
    go :: Formula -> [P2 Int Term]
    go (Forall v f) = go f
    go (Exists v f) = go f
    go (Conj f1 f2) =
      lemmaLookupLeft (scopes f1) (scopes f2) (go f1) ++ lemmaLookupRight (scopes f1) (scopes f2) (go f2)
    go (Then (t0, t1) f2) =
      let unifsT1 = goEq t0 t1
          unifsT1Subst = lemmaFromListSubst (append (scopesTerm t0) (scopesTerm t1)) unifsT1
       in (lemmaLookupLeft (append (scopesTerm t0) (scopesTerm t1)) (scopes f2) unifsT1
            ? lemmaAppendAssoc (scopesTerm t0) (scopesTerm t1) (scopes f2)
          )
          ++ lemmaLookupSetP2
               (append (scopesSubst unifsT1Subst) (scopes f2))
               (append (scopesTerm t0) (append (scopesTerm t1) (scopes f2))
                  ? lemmaScopesAppend (scopesSubst unifsT1Subst) (scopes f2)
                  ? lemmaScopesAppend (scopesTerm t0) (append (scopesTerm t1) (scopes f2))
                  ? lemmaScopesAppend (scopesTerm t1) (scopes f2)
                  ? lemmaScopesAppend (scopesTerm t0) (scopesTerm t1)
                  ? lemmaScopesSubst (append (scopesTerm t0) (scopesTerm t1)) unifsT1Subst
               )
               (lemmaLookupSetP2
                 (scopes (substituteSkolems unifsT1Subst f2))
                 (append (scopesSubst unifsT1Subst) (scopes f2)
                    ? lemmaScopesAppend (scopesSubst unifsT1Subst) (scopes f2)
                 )
                 (go (substituteSkolems unifsT1Subst f2))
               )
    go (Eq t0 t1) = goEq t0 t1

{-@ lazy goEq @-}
{-@
assume goEq
  :: t0:Term
  -> t1:Term
  -> [{p:_ |
           isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) (scopesTerm t0 ++ scopesTerm t1))
        && isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts (scopesTerm t0 ++ scopesTerm t1))
      }]
@-}
goEq :: Term -> Term -> [P2 Int Term]
-- Missing: occurs check
goEq t (SA (i, s))
      | Just s' <- inverseSubst $ narrowForInvertibility (freeVars t) s
      , let t' = substitute s' t
        -- Scope check
      , Set.isSubsetOf (freeVars t') (domainSubst s)
          -- For the first conjunct:
          --   prove that @Just s@ is @lookup i (scopesTerm t1)@
          --   use lemmaScopesAppend
          --
          -- For the second conjunct:
          --   prove that @scopesTerm of t'@ is @scopesTerm t0@
      =
        [P2 i t']
goEq (SA (i, s)) t
      | Just s' <- inverseSubst $ narrowForInvertibility (freeVars t) s
      , let t' = substitute s' t
      , Set.isSubsetOf (freeVars t') (domainSubst s)
      =
        [P2 i t']
goEq _ _ = []


{-@
assume lemmaFromListSubst
  :: s:[(Int, Set Int)]
  -> [{p:_ |
        isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts s)
      }]
  -> Subst
      ({vt:Term |
             isSubsetOf (Set.listElts (scopesTerm vt)) (Set.listElts s)
        })
@-}
lemmaFromListSubst :: [(Int, Set Int)] -> [P2 Int Term] -> Subst Term
lemmaFromListSubst s xs = Subst $ map (\(P2 i t) -> (i, t)) xs

{-@
lemmaAppendAssoc
  :: s0:[a]
  -> s1:[a]
  -> s2:[a]
  -> { s0 ++ (s1 ++ s2) = (s0 ++ s1) ++ s2 }
@-}
lemmaAppendAssoc :: [a] -> [a] -> [a] -> ()
lemmaAppendAssoc [] ys zs = ()
lemmaAppendAssoc (x:xs) ys zs = lemmaAppendAssoc xs ys zs

{-@
lemmaLookupLeft
  :: s0:[(Int, Set Int)]
  -> s1:[(Int, Set Int)]
  -> [{p:P2 Int Term |
             isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) s0)
          && isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts s0)
      }]
  -> [{p:P2 Int Term |
           isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) (s0 ++ s1))
        && isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts (s0 ++ s1))
      }]
@-}
lemmaLookupLeft :: [(Int, Set Int)] -> [(Int, Set Int)] -> [P2 Int Term] -> [P2 Int Term]
lemmaLookupLeft s0 s1 [] = []
lemmaLookupLeft s0 s1 (P2 i t : xs) =
    P2 i
       (t
         ? lemmaLookupAppendLeft i s0 s1
         ? lemmaScopesAppend s0 s1
       )
    : lemmaLookupLeft s0 s1 xs

{-@
lemmaLookupRight
  :: s0:[(Int, Set Int)]
  -> s1:[(Int, Set Int)]
  -> [{p:_ |
           isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) s1)
        && isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts s1)
      }]
  -> [{p:_ |
           isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) (s0 ++ s1))
        && isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts (s0 ++ s1))
      }]
@-}
lemmaLookupRight :: [(Int, Set Int)] -> [(Int, Set Int)] -> [P2 Int Term] -> [P2 Int Term]
lemmaLookupRight s0 s1 [] = []
lemmaLookupRight s0 s1 (P2 i t : xs) =
    P2 i
       (t ? lemmaLookupAppendRight i s0 s1
          ? lemmaScopesAppend s0 s1
       )
    : lemmaLookupRight s0 s1 xs

{-@
assume lemmaLookupSetP2
  :: s0:[(Int, Set Int)]
  // TODO: require that s0 and s1 provide the same scopes when they have
  // common existentials
  -> {s1:[(Int, Set Int)] | Set.isSubsetOf (Set.listElts s0) (Set.listElts s1)}
  -> [{p:_ |
           isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) s0)
        && isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts s0)
      }]
  -> [{p:_ |
           isSubsetOfJust (freeVars (snd2 p)) (lookup (fst2 p) s1)
        && isSubsetOf (Set.listElts (scopesTerm (snd2 p))) (Set.listElts s1)
      }]
@-}
lemmaLookupSetP2 :: [(Int, Set Int)] -> [(Int, Set Int)] -> [P2 Int Term] -> [P2 Int Term]
lemmaLookupSetP2 s0 s1 xs = xs


{-@
assume lemmaLookupAppendLeft
  :: i:Int
  -> xs:[(Int, a)]
  -> ys:[(Int, a)]
  -> { lookup i xs == lookup i (xs ++ ys) }
@-}
lemmaLookupAppendLeft :: Int -> [(Int, a)] -> [(Int, a)] -> ()
lemmaLookupAppendLeft _ _ _ = ()

{-@
assume lemmaLookupAppendRight
  :: i:Int
  -> xs:[(Int, a)]
// TODO: Here we would use the invariant that all occurrences of the same
// existential have the same scope.
//  -> {ys:[(Int, a)] | lookupsMatchIfSucceed (lookup i xs) (lookup i ys) }
  -> ys:[(Int, a)]
  -> { lookup i ys == lookup i (xs ++ ys) }
@-}
lemmaLookupAppendRight :: Int -> [(Int, a)] -> [(Int, a)] -> ()
lemmaLookupAppendRight _ _ _ = ()

{-@ reflect lookupsMatchIfSucceed @-}
lookupsMatchIfSucceed :: Maybe (Set Int) -> Maybe (Set Int) -> Bool
lookupsMatchIfSucceed Nothing _ = True
lookupsMatchIfSucceed _ Nothing = True
lookupsMatchIfSucceed (Just x) (Just y) = x == y

-- We could return sets instead of lists, if it were not for the
-- fact that we need to lookup scopes by their existential variable.
{-@ reflect scopes @-}
scopes :: Formula -> [(Int, Set Int)]
scopes (Forall _ f) = scopes f
scopes (Exists _ f) = scopes f
scopes (Conj f1 f2) = scopes f1 ++ scopes f2
scopes (Then (t0, t1) f2) = scopesTerm t0 ++ scopesTerm t1 ++ scopes f2
scopes (Eq t0 t1) = scopesTerm t0 ++ scopesTerm t1

{-@ reflect scopesTerm @-}
scopesTerm :: Term -> [(Int, Set Int)]
scopesTerm (V i) = []
scopesTerm (SA (i, s)) = [(i, domainSubst s)]
scopesTerm U = []
scopesTerm (L t) = scopesTerm t
scopesTerm (P t0 t1) = scopesTerm t0 ++ scopesTerm t1

{-@ opaque-reflect domainSubst @-}
{-@ ignore domainSubst @-}
domainSubst :: Subst e -> Set Int
domainSubst (Subst xs) = Set.fromList $ map fst xs

{-@ assume reflect ++ as append @-}

{-@ reflect append @-}
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x:xs) ys = x : append xs ys

{-@ assume reflect lookup as lookupR @-}
{-@ reflect lookupR @-}
lookupR :: Eq a => a -> [(a, b)] -> Maybe b
lookupR _ [] = Nothing
lookupR x ((y, v) : ys)
  | x == y = Just v
  | otherwise = lookupR x ys

{-@ reflect isSubsetOfJust @-}
isSubsetOfJust :: Ord a => Set a -> Maybe (Set a) -> Bool
isSubsetOfJust xs (Just ys) = Set.isSubsetOf xs ys
isSubsetOfJust xs Nothing = False

-- TODO: consider what to do when unification introduces equalities of
-- constructors that might need to be eliminated

-- | @narrowForInvertibility vs s@ removes pairs from @s@ if the range
-- is not a variable, or if the range is not a member of @vs@.
narrowForInvertibility :: Set Var -> Subst Term -> Subst Term
narrowForInvertibility vs (Subst xs) = Subst [(i, V j) | (i, V j) <- xs, Set.member j vs]

-- | @narrowInvertedSubst t s@ removes variables from the inversion of @s@
-- if the range doesn't match any subterm of @t@.
narrowInvertedSubst :: Term -> Subst Term -> Subst Term
narrowInvertedSubst t (Subst xs) =
  Subst [(i, t) | (i, t) <- xs, Set.member t s]
  where
    s = subTerms t

{-@ ignore subTerms @-}
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
{-@ ignore inverseSubst @-}
inverseSubst :: Subst Term -> Maybe (Subst Term)
inverseSubst (Subst xs) = Subst <$> go xs
  where
    go [] = Just []
    go ((i, V j) : xs) = ((j, V i) :) <$> go xs
    go _ = Nothing

--- | Assign terms to existential variables in an attempt to make a formula
-- true.
{-@ ignore unifyFormula @-}
unifyFormula :: Formula -> [P2 Int Term]
unifyFormula = unifyFormula' False

{-@ ignore unifyFormulaTrace @-}
unifyFormulaTrace :: Formula -> [P2 Int Term]
unifyFormulaTrace = unifyFormula' True

{-@ ignore unifyFormula' @-}
unifyFormula' :: Bool -> Formula -> [P2 Int Term]
unifyFormula' mustTrace =
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
    trace label f
      | mustTrace = Debug.Trace.trace (label ++ ": " ++ ppFormula prettyName f) f
      | otherwise = f
    traceUnify :: String -> [P2 Int Term] -> [P2 Int Term]
    traceUnify label xs
      | mustTrace = Debug.Trace.trace (label ++ ": " ++ showUnification xs) xs
      | otherwise = xs
    showUnification :: [P2 Int Term] -> String
    showUnification xs =
      let xs' = map (\(P2 i t) -> (prettyName i, ppTerm prettyName t)) xs
       in "[" ++ List.intercalate ", " (map (\(i, t) -> i ++ ":=" ++ t) xs') ++ "]"

-- pretty printing

-- | Pretty print a variable name
{-@ ignore prettyName @-}
prettyName :: Int -> String
prettyName = ((["x", "y", "z", "u", "v", "w", "r", "s", "t"] ++ [ "v" ++ show i | i <- [1..] ]) !!)
-- prettyName = ((["a", "b", "c", "t_f", "x_f", "l", "r" ] ++ ["x", "y", "z", "u", "v", "w", "r", "s", "t"] ++ [ "v" ++ show i | i <- [1..] ]) !!)

-- | Pretty print a formula
{-@ ignore ppFormula @-}
ppFormula :: (Int -> String) -> Formula -> String
ppFormula vnames = go
  where
    go (Forall v f) = "∀" ++ (vnames v) ++ ". " ++ go f
    go (Exists v f) = "∃" ++ (vnames v) ++ ". " ++ go f
    go (Conj f1 f2) = "(" ++ go f1 ++ ") ∧ (" ++ go f2 ++ ")"
    go (Then (t0, t1) f2) = go (Eq t0 t1) ++ " → " ++ go f2
    go (Eq t0 t1) = ppTerm vnames t0 ++ " == " ++ ppTerm vnames t1

{-@ ignore ppTerm @-}
ppTerm :: (Int -> String) -> Term -> String
ppTerm vnames t =
  case t of
    V i -> vnames i
    SA (i, s) -> vnames i ++ ppSubst vnames s
    U -> "U"
    L t1 -> "L(" ++ ppTerm vnames t1 ++ ")"
    P t1 t2 -> "P(" ++ ppTerm vnames t1 ++ ", " ++ ppTerm vnames t2 ++ ")"

{-@ ignore ppSubst @-}
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

infixr 7 `Then`
infixr 8 `Conj`

-- | forall a b c. exists t_f x_f. a = (b, c) -> a = (Int -> Int, Int) -> t_f = b -> x_f = c -> exists l r. t_f = l -> r /\ l = x_f /\ x_f = Int -> r = c
tf8 :: Formula
tf8 = Forall 0 $ Forall 1 $ Forall 2 $
  Exists 3 (Exists 4 $
    (V 0, P (V 1) (V 2))
      `Then` (V 0, P (P U U) U)
      `Then` (V 3, V 1)
      `Then` (V 4, V 2)
      `Then`
    Exists 5 (Exists 6 $
             Eq (V 3) (P (V 5) (V 6))
      `Conj` Eq (V 5) (V 4)
      `Conj` ((V 4, U) `Then` Eq (V 6) (V 2))
    )
  )

{-@ ignore test @-}
test :: IO ()
test = do
  let tests =
        [ ("tf0", (tf0, [(1,V 0)]))
        , ("tf1", (tf1, [(1,V 0), (3,V 2)]))
        , ("tf2", (tf2, [(1,V 0), (3,V 2)]))
        , ("tf3", (tf3, [(0,V 1), (3,V 2)]))
        , ("tf4", (tf4, [(2,V 1)]))
        , ("tf5", (tf5, [(3,V 1)]))
        , ("tf6", (tf6, [(2,V 1)]))
        , ("tf7", (tf7, [(1,SA (2,Subst [(0,SA (1,Subst [(0,V 0)]))]))]))
        , ("tf8", (tf8, [(3,P U U),(4,U),(5,U),(6,U)]))
        ]
  mapM_ runUnificationTest tests
  where
    runUnificationTest (name, (f, expected)) = do
      let result = unifyFormula f
      if result == map (uncurry P2) expected
        then putStrLn $ concat ["Test ", name, ": Passed"]
        else putStrLn $
               concat ["Test ", name, ": Failed\n", show expected, " but got ", show result, "\n"]
