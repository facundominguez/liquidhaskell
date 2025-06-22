{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--no-pattern-inline" @-}
module Unif2 where

import Data.List qualified as List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import Data.Set qualified as Set
import Debug.Trace qualified
-- BUG: this import is to avoid a bug in name resolution in Liquid Haskell
import qualified Data.Maybe as GHC.Internal.Maybe

-- from liquid-prelude:
import Language.Haskell.Liquid.ProofCombinators

-- from a sibling source file:
import State

-- We start with a preamble of definitions to introduce the interpretation of
-- the IntMap type as an array. Any @IntMap a b@ in this file is interpreted as
-- an array mapping integers to values of type @Set Int@, so we are careful to
-- not use @IntMap@ instantiated with other types.

{-@

// Syntax to express that any IntMap a b shoud be interpreted as an
// IntMapSetInt_t, which is Array Int (Option (Set Int))
embed IntMap * as IntMapSetInt_t

// Operations on IntMap's are declared to correspond in meaning to operations
// that have been defined in a patch to the liquid-fixpoint package prepared
// for this test.
define IntMap.empty     = (IntMapSetInt_default None)
define IntMap.insert x y m = (IntMapSetInt_store m x (Some y))
define IntMap.lookup x m =
         if (isSome (IntMapSetInt_select m x)) then
           (GHC.Internal.Maybe.Just (someVal (IntMapSetInt_select m x)))
         else
           GHC.Internal.Maybe.Nothing
define IntMap.delete x m = (Map_store m x None)

define IntMap.union x y = IntMapSetInt_union x y
define IntMap.difference x y = IntMapSetInt_difference x y
define intMapIsSubsetOf x y = IntMapSetInt_isSubsetOf x y
@-}

-- Only provided here for use in specifications
intMapIsSubsetOf :: IntMap (Set Int) -> IntMap (Set Int) -> Bool
intMapIsSubsetOf _ _ = undefined

{-@ inline mid @-}
mid :: IntMap (Set Int) -> IntMap (Set Int)
mid m = m


{-@ infixr ++ @-}

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
type SkolemApp = (Var, Subst Term)

--------------------------------------
-- Substitutions and their operations
--------------------------------------

data Subst t = Subst [(Var,t)]
  deriving (Eq, Ord, Show)

{-@
// Lookups should yield terms satisfying the predicate p as long as the
// variable i is in the domain of the substitution.
assume lookupSubst
  :: forall <p :: Term -> Bool>.
     s:Subst Term<p> -> {i:Int | Set.member i (domain s)} -> Term<p>
@-}
lookupSubst :: Subst Term -> Var -> Term
lookupSubst (Subst s) i = case lookup i s of
    Nothing -> V i
    Just e -> e

emptySubst :: Subst e
emptySubst = Subst []

{-@
// Extending a substitution should guarantee that the new domain includes the
// new variable.
assume extendSubst
  :: s:_
  -> m:_
  -> ss:ConsistentScopedSubst s m
  -> i:_
  -> t:ConsistentScopedTerm s m
  -> {v:ConsistentScopedSubst s m | union (domain ss) (singleton i) = domain v }
@-}
extendSubst
  :: Set Int -> IntMap (Set Int) -> Subst Term -> Var -> Term -> Subst Term
extendSubst _ _ (Subst s) i e = Subst ((i, e) : s)

{-@
// Creates a substitution whose domain includes all variables. Variables
// that are not in the input list are mapped to themselves.
assume fromListSubst :: _ -> {v:_ | Set_com empty = domain v}
@-}
fromListSubst :: [(Var, t)] -> Subst t
fromListSubst = Subst

{-@
// Like formListSubst, but with stronger guarantees.
assume fromListSubst2
  :: forall <p :: Term -> Bool>.
     s:_
  -> m:_
  -> [(Var, Term<p>)]
  -> {v:Subst Term<p> |
          consistentUnificationScopesSubst m v
       && isSubsetOf (freeVarsSubst v) s
       && Set_com empty = domain v
     }
@-}
fromListSubst2 :: Set Int -> IntMap (Set Int) -> [(Var, Term)] -> Subst Term
fromListSubst2 _ _ = Subst

{-@
// Creates a substitution that maps each variable in the set to itself.
assume fromSetIdSubst ::
    s:Set Int -> {v:_ | s = domain v && s = freeVarsSubst v}
@-}
fromSetIdSubst :: Set Int -> Subst Term
fromSetIdSubst s = Subst [(i, V i) | i <- Set.toList s]

{-@ opaque-reflect domain @-}
{-@ ignore domain @-}
domain :: Subst e -> Set Int
domain (Subst xs) = Set.fromList $ map fst xs

{-@ measure existsCount @-}
{-@ existsCount :: Formula -> Nat @-}
existsCount :: Formula -> Int
existsCount (Forall _ f) = existsCount f
existsCount (Exists _ f) = 1 + existsCount f
existsCount (Conj f1 f2) = existsCount f1 + existsCount f2
existsCount (Then _ f2) = existsCount f2
existsCount Eq{} = 0

-- BUG: isVar should work regardles of whether it is inline or reflect'ed
-- but for some reason it is only unfolded in proofs if declared as inline.
{-@ inline isVar @-}
isVar :: Term -> Bool
isVar V{} = True
isVar _ = False


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

{-@ measure freeVarsFormula @-}
freeVarsFormula :: Formula -> Set Int
freeVarsFormula = \case
    Forall v f -> Set.difference (freeVarsFormula f) (Set.singleton v)
    Exists v f -> Set.difference (freeVarsFormula f) (Set.singleton v)
    Conj f1 f2 -> Set.union (freeVarsFormula f1) (freeVarsFormula f2)
    Then (t0, t1) f2 ->
      Set.union (Set.union (freeVars t0) (freeVars t1)) (freeVarsFormula f2)
    Eq t0 t1 -> Set.union (freeVars t0) (freeVars t1)

{-@ opaque-reflect skolemSet @-}
skolemSet :: Term -> Set Var
skolemSet = \case
    V _ -> Set.empty
    SA (i, s) -> Set.insert i (skolemAppsSubst s)
    U -> Set.empty
    L t -> skolemSet t
    P t0 t1 -> Set.union (skolemSet t0) (skolemSet t1)

{-@ opaque-reflect freeVarsSubst @-}
{-@ ignore freeVarsSubst @-}
freeVarsSubst :: Subst Term -> Set Int
freeVarsSubst (Subst s) = Set.unions $ map (freeVars . snd) s

{-@ ignore skolemAppsSubst @-}
skolemAppsSubst :: Subst Term -> Set Int
skolemAppsSubst (Subst s) = Set.unions $ map (skolemSet . snd) s

{-@ assume freshVar :: s:Set Int -> {v:Int | not (member v s)} @-}
freshVar :: Set Int -> Int
freshVar s = case Set.lookupMax s of
    Nothing -> 0
    Just i -> i + 1

{-@
type ScopedTerm S = {t:Term | isSubsetOf (freeVars t) S}
type ScopedFormula S = {f:Formula | isSubsetOf (freeVarsFormula f) S}
type ConsistentScopedFormula S M =
     {f:Formula |
          isSubsetOf (freeVarsFormula f) S
       && consistentUnificationScopes M f
     }
type ConsistentScopedTerm S M =
     {t:Term | isSubsetOf (freeVars t) S && consistentUnificationScopesTerm M t}
type ConsistentScopedSubst S M =
     {ss:Subst Term |
           isSubsetOf (freeVarsSubst ss) S
        && consistentUnificationScopesSubst M ss
     }
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


-- BUG: assumed specs are ignored when the function is reflected
{-@
substitute
  :: s:_
  -> m:_
  -> ss:ConsistentScopedSubst s m
  -> ConsistentScopedTerm (domain ss) m
  -> ConsistentScopedTerm s m
@-}
substitute :: Set Int -> IntMap (Set Int) -> Subst Term -> Term -> Term
substitute s m ss t = case t of
    V v -> lookupSubst (castConsistentScopesSubst s m ss) v
    SA (v, s1) ->
      let s1' = castConsistentScopesSubst (domain ss) m s1
          ss' = composeSubst s m ss s1'
       in SA (v, ss')
    U -> U
    L t1 -> L (substitute s m ss t1)
    P t1 t2 -> P (substitute s m ss t1) (substitute s m ss t2)

{-@
ignore composeSubst
assume composeSubst
  :: s:_
  -> m:_
  -> s0:ConsistentScopedSubst s m
  -> s1:ConsistentScopedSubst (domain s0) m
  -> {v:ConsistentScopedSubst s m | domain v = domain s1}
@-}
composeSubst
  :: Set Int -> IntMap (Set Int) -> Subst Term -> Subst Term -> Subst Term
composeSubst s m s0 (Subst xs) =
  Subst (map (fmap (substitute s m s0)) xs)

{-@
substituteFormula
  :: s:Set Int
  -> m:IntMap (Set Int)
  -> ss:ConsistentScopedSubst s m
  -> {f:ScopedFormula (domain ss) | consistentUnificationScopes m f}
  -> {v:ScopedFormula s |
          formulaSize f == formulaSize v
       && consistentUnificationScopes m v
       && existsCount v = existsCount f
     } / [formulaSize f]
@-}
substituteFormula
  :: Set Int -> IntMap (Set Int) -> Subst Term -> Formula -> Formula
substituteFormula s m ss = \case
    Forall v f
      | Set.member v s ->
        let u = freshVar s
            s' = Set.insert u s
            ss' = extendSubst s' m ss v (V u)
            f' = substituteFormula s' m ss' f
         in
            Forall u f'
      | otherwise ->
        let s' = Set.insert v s
            ss' = extendSubst s' m ss v (V v)
            f' = substituteFormula s' m ss' f
         in
            Forall v f'
    Exists v f
      | Set.member v s ->
        let u = freshVar s
            s' = Set.insert u s
            ss' = extendSubst s' m ss v (V u)
            f' = substituteFormula s' m ss' f
         in
            Exists u f'
      | otherwise ->
        let s' = Set.insert v s
            ss' = extendSubst s' m ss v (V v)
            f' = substituteFormula s' m ss' f
         in
            Exists v f'
    Conj f1 f2 ->
      Conj (substituteFormula s m ss f1) (substituteFormula s m ss f2)
    Then (t0, t1) f2 ->
      Then (substitute s m ss t0, substitute s m ss t1)
           (substituteFormula s m ss f2)
    Eq t0 t1 -> Eq (substitute s m ss t0) (substitute s m ss t1)

{-@ reflect consistentUnificationScopes @-}
consistentUnificationScopes :: IntMap (Set Int) ->  Formula -> Bool
consistentUnificationScopes m (Forall _ f) = consistentUnificationScopes m f
consistentUnificationScopes m (Exists _ f) = consistentUnificationScopes m f
consistentUnificationScopes m (Conj f1 f2) =
      consistentUnificationScopes m f1 && consistentUnificationScopes m f2
consistentUnificationScopes m (Then (t0, t1) f2) =
     consistentUnificationScopes m f2
  && consistentUnificationScopesTerm m t0
  && consistentUnificationScopesTerm m t1
consistentUnificationScopes m (Eq t0 t1) =
     consistentUnificationScopesTerm m t0
  && consistentUnificationScopesTerm m t1

{-@ reflect consistentUnificationScopesTerm @-}
consistentUnificationScopesTerm :: IntMap (Set Int) -> Term -> Bool
consistentUnificationScopesTerm m (V _) = True
consistentUnificationScopesTerm m (SA (i, s)) =
       IntMap.lookup i m == Just (domain s)
    && consistentUnificationScopesSubst m s
consistentUnificationScopesTerm m U = True
consistentUnificationScopesTerm m (L t) = consistentUnificationScopesTerm m t
consistentUnificationScopesTerm m (P t0 t1) =
    consistentUnificationScopesTerm m t0 && consistentUnificationScopesTerm m t1

{-@ opaque-reflect consistentUnificationScopesSubst @-}
{-@ ignore consistentUnificationScopesSubst @-}
consistentUnificationScopesSubst :: IntMap (Set Int) -> Subst Term -> Bool
consistentUnificationScopesSubst m (Subst xs) =
    all (\(i, t) -> consistentUnificationScopesTerm m t) xs

{-@
assume castConsistentScopesSubst
  :: s:_
  -> m:_
  -> {ss:_ |
         consistentUnificationScopesSubst m ss
      && isSubsetOf (freeVarsSubst ss) s
     }
  -> {v:Subst (ConsistentScopedTerm s m) | v = ss}
@-}
castConsistentScopesSubst
  :: Set Int -> IntMap (Set Int) -> Subst Term -> Subst Term
castConsistentScopesSubst _ _ ss = ss

{-@
assume lemmaConsistentScopesSubst
  :: m:_
  -> ss:Subst {t:_ | consistentUnificationScopesTerm m t}
  -> { consistentUnificationScopesSubst m ss}
@-}
lemmaConsistentScopesSubst
  :: IntMap (Set Int) -> Subst Term -> ()
lemmaConsistentScopesSubst _ _ = ()


-- | Replaces existential variables with skolem functions
--
-- Every time that `SA (i,s)` occurs, the domain of `s` is exactly the set of
-- bound variables in scope.
{-@
ignore skolemize
assume skolemize
  :: sf:_
  -> f:ScopedFormula sf
  -> State
       <{\m0 ->
            isSubsetOf sf (IntMapSetInt_keys m0)
         && consistentUnificationScopes m0 f
        }

       , {\m0 v m ->
             consistentUnificationScopes m v
          && existsCount v = 0
          && isSubsetOf (freeVarsFormula v) sf
          && intMapIsSubsetOf m0 m
         }>
       _ _
@-}
skolemize :: Set Int -> Formula -> State (IntMap (Set Int)) Formula
skolemize sf (Forall v f) = do
    m <- get
    put (IntMap.insert v sf m)
    f' <- skolemize (Set.insert v sf) f
    pure (Forall v f')
-- BUG: LH hangs when trying to check the Exists case of skolemize
-- Therefore, we 'skip' it.
skolemize sf (Exists v f) = do
    m <- get
    let u = if IntMap.member v m then freshVar (Set.fromList (IntMap.keys m)) else v
        m' = IntMap.insert u sf m
    put m'
    let subst = fromListSubst [(v, SA (u, fromSetIdSubst sf))]
    skolemize sf (substituteFormula sf m' subst f)
skolemize sf (Conj f1 f2) = do
     f1' <- skolemize sf f1
     f2' <- skolemize sf f2
     pure (Conj f1' f2')
skolemize sf f@(Then (t0, t1) f2) = do
     f2' <- skolemize sf f2
     pure (Then (t0, t1) f2')
skolemize _ f@Eq{} = pure f

-- | Assign terms to skolem functions.
--
-- When @unify@ returns pairs @(i, t) :: (Var, Term)@, @t@'s free variables are
-- in the scope of @i@ (the domain of the accompanying substitution).
--
-- Example:
--
-- > unify (t == SA (i, s))@ is @[(i, substitute (inverseSubst s) t)
--
{-@
unify
  :: s:Set Int
  -> m:_
  -> {f:ConsistentScopedFormula s m | existsCount f = 0}
  -> Maybe [{p:(Var, {t:Term | consistentUnificationScopesTerm m t}) |
           isSubsetOfJust (freeVars (snd p)) (IntMap.lookup (fst p) m)
        && not (Set.member (fst p) (skolemSet (snd p)))
      }] / [formulaSize f]
@-}
unify :: Set Int -> IntMap (Set Int) -> Formula -> Maybe [(Var, Term)]
unify s m (Forall v f) = unify (Set.insert v s) m f
unify s m (Exists v f) = error "unify: the formula hasn't been skolemized"
unify s m (Conj f1 f2) = do
    unifyF1 <- unify s m f1
    unifyF2 <- unify s m (substituteSkolems s m f2 unifyF1)
    return (unifyF1 ++ unifyF2)
unify s m f@(Then (t0, t1) f2) = do
    case substEq s m t0 t1 of
      Nothing -> Just []
      Just xs ->
        let subst = fromListSubst2 s m xs
         in unify s m (substituteFormula s m subst f2)
unify s m (Eq t0 t1) = unifyEq s m t0 t1


{-@
substEq
  :: s:_
  -> m:_
  -> t0:ConsistentScopedTerm s m
  -> t1:ConsistentScopedTerm s m
  -> Maybe [(Var, ConsistentScopedTerm s m)]
@-}
substEq :: Set Int -> IntMap (Set Int) -> Term -> Term -> Maybe [(Var, Term)]
substEq _ _ (V i) t1 = Just [(i, t1)]
substEq _ _ t0 (V i) = Just [(i, t0)]
substEq s m (L t0) (L t1) = substEq s m t0 t1
substEq s m (P t0a t0b) (P t1a t1b) =
    -- TODO: apply the substitutions discovered in the first component to the
    -- second component. Needs working on the refinement type signature of substitute.
    (++) <$> substEq s m t0a t1a <*> substEq s m t0b t1b
substEq _ _ U U = Just []
substEq _ _ SA{} _ = Just []
substEq _ _ _ SA{} = Just []
substEq _ _ _ _ = Nothing


-- BUG: ignoring a function causes the asserted signature to be ignored
-- It needs to be assumed to work around it.
{-@
lazy unifyEq
unifyEq
  :: s:_
  -> m:_
  -> t0:ConsistentScopedTerm s m
  -> t1:ConsistentScopedTerm s m
  -> Maybe [{p:(Var, {t:Term | consistentUnificationScopesTerm m t}) |
           isSubsetOfJust (freeVars (snd p)) (IntMap.lookup (fst p) m)
        && not (Set.member (fst p) (skolemSet (snd p)))
      }]
@-}
unifyEq :: Set Int -> IntMap (Set Int) -> Term -> Term -> Maybe [(Var, Term)]
unifyEq s m t0@(SA (i, ss)) t1 = unifyEqEnd s m t0 t1
unifyEq s m t0 t1@(SA (i, ss)) = unifyEqEnd s m t1 t0
unifyEq s m (L t0) (L t1) = unifyEq s m t0 t1
unifyEq s m (P t0a t0b) (P t1a t1b) = do
    unifyT0a <- unifyEq s m t0a t1a
    unifyT0b <- unifyEq s m
                  (substituteSkolemsTerm s m t0b unifyT0a)
                  (substituteSkolemsTerm s m t1b unifyT0a)
    return $ unifyT0a ++ unifyT0b
unifyEq _ _ U U = Just []
unifyEq _ _ V{} t1 | Set.null (skolemSet t1) = Just []
unifyEq _ _ t0 V{} | Set.null (skolemSet t0) = Just []
unifyEq _ _ _ _ = Nothing

-- BUG: cannot define a termination metric if conflating unifyEq and unifyEqEnd
{-@
unifyEqEnd
  :: s:_
  -> m:_
  -> t0:ConsistentScopedTerm s m
  -> t1:ConsistentScopedTerm s m
  -> Maybe [{p:(Var, {t:Term | consistentUnificationScopesTerm m t}) |
           isSubsetOfJust (freeVars (snd p)) (IntMap.lookup (fst p) m)
        && not (Set.member (fst p) (skolemSet (snd p)))
      }]
@-}
unifyEqEnd :: Set Int -> IntMap (Set Int) -> Term -> Term -> Maybe [(Var, Term)]
unifyEqEnd s m t0@(SA (i, ss)) t1
    | Just ss' <- inverseSubst s m $ narrowForInvertibility (freeVars t1) ss
    , let t' = substitute
                 (freeVarsSubst ss') m
                 (ss' ? lemmaConsistentScopesSubst m ss') t1
    , not (Set.member i (skolemSet t'))
    , Set.isSubsetOf (freeVars t') (domain ss)
    = Just [(i, t')]
unifyEqEnd _ _ _ _ = Nothing

{-@ inline isSubsetOfJust @-}
isSubsetOfJust :: Ord a => Set a -> Maybe (Set a) -> Bool
isSubsetOfJust xs (Just ys) = Set.isSubsetOf xs ys
isSubsetOfJust xs Nothing = False

-- TODO: consider what to do when unification introduces equalities of
-- constructors that might need to be eliminated

-- | @narrowForInvertibility vs s@ removes pairs from @s@ if the range
-- is not a variable, or if the range is not a member of @vs@.
narrowForInvertibility :: Set Var -> Subst Term -> Subst Term
narrowForInvertibility vs (Subst xs) =
    Subst [(i, V j) | (i, V j) <- xs, Set.member j vs]

-- TODO: consider what to do with non-invertible substitutions
-- like ?v[x\z,y\z] ?= z
--
-- At the moment we just pick the first of the variables with a duplicated
-- range.
{-@
inverseSubst
  :: s:_
  -> m:_
  -> _
  -> Maybe
      ({v:Subst {t:_ | isVar t && consistentUnificationScopesTerm m t} |
         Set_com Set.empty == domain v
       })
@-}
inverseSubst :: Set Int -> IntMap (Set Int) -> Subst Term -> Maybe (Subst Term)
inverseSubst s m (Subst xs) = fromListSubst <$> go xs
  where
    {-@
    go :: _
       -> Maybe [(Var, {t:_ | isVar t && consistentUnificationScopesTerm m t})]
    @-}
    go :: [(Var, Term)] -> Maybe [(Var, Term)]
    go [] = Just []
    go ((i, V j) : xs) = do
       xs' <- go xs
       -- BUG: here LH is not accepting that @V i@ satisfies
       -- @consistentUnificationScopesTerm m (V i)@
       return ((j, V i ? skip ()) : xs')
    go _ = Nothing

{-@
substituteSkolems
  :: s:_
  -> m:_
  -> {f:ConsistentScopedFormula s m | existsCount f = 0}
  -> ss:[{p:(Var, {st:Term | consistentUnificationScopesTerm m st}) |
          isSubsetOfJustOrNothing
            (freeVars (snd p))
            (IntMap.lookup (fst p) m)
        }]
  -> {v:ConsistentScopedFormula s m |
          formulaSize f == formulaSize v
       && existsCount v = 0
     }
@-}
substituteSkolems
  :: Set Int -> IntMap (Set Int) -> Formula -> [(Var, Term)] -> Formula
substituteSkolems s m f0 ss = case f0 of
    Forall v f -> Forall v (substituteSkolems (Set.insert v s) m f ss)
    Exists v f -> error "substituteSkolems: the formula hasn't been skolemized"
    Conj f1 f2 ->
      Conj (substituteSkolems s m f1 ss) (substituteSkolems s m f2 ss)
    Then (t0, t1) f2 ->
      Then (substituteSkolemsTerm s m t0 ss, substituteSkolemsTerm s m t1 ss)
           (substituteSkolems s m f2 ss)
    Eq t0 t1 ->
      Eq (substituteSkolemsTerm s m t0 ss) (substituteSkolemsTerm s m t1 ss)

{-@
substituteSkolemsTerm
  :: s:_
  -> m:_
  -> t:ConsistentScopedTerm s m
  -> ss:[{p:(Var, {t:Term | consistentUnificationScopesTerm m t}) |
           isSubsetOfJustOrNothing
             (freeVars (snd p))
             (IntMap.lookup (fst p) m)
         }]
  -> ConsistentScopedTerm s m
lazy substituteSkolemsTerm
@-}
substituteSkolemsTerm
  :: Set Int -> IntMap (Set Int) -> Term -> [(Var, Term)] -> Term
substituteSkolemsTerm s m t ss = case t of
    V v -> V v
    SA (v, s1) -> case findPair v ss of
      -- BUG?: This looks like it could be checking that freeVars (snd p)
      -- is a subset of domain s1. But for some reason it doesn't.
      Just p -> substitute s m s1 (snd p ? skip ())
      Nothing -> let subst = fromListSubst2 s m ss
                  in SA (v, composeSubst s m subst s1)
    U -> U
    L t1 -> L (substituteSkolemsTerm s m t1 ss)
    P t1 t2 -> P (substituteSkolemsTerm s m t1 ss) (substituteSkolemsTerm s m t2 ss)

{-@ assume findPair :: a:_ -> [(a, b)] -> Maybe ({ra:_ | ra = a}, b) @-}
findPair :: Eq a => a -> [(a, b)] -> Maybe (a, b)
findPair a = List.find (\(x, _) -> a == x)

{-@ inline isSubsetOfJustOrNothing @-}
isSubsetOfJustOrNothing :: Set Int -> Maybe (Set Int) -> Bool
isSubsetOfJustOrNothing _ Nothing = True
isSubsetOfJustOrNothing s0 (Just s1) = Set.isSubsetOf s0 s1


-- | Used to skip cases that we don't want to verify
{-@ assume skip :: _ -> { false } @-}
skip :: () -> ()
skip () = ()

{-@
unifyFormula
  :: s:_
  -> {m:_ | isSubsetOf s (IntMapSetInt_keys m)}
  -> f:ConsistentScopedFormula s m
  -> Maybe [(Var, Term)]
@-}
unifyFormula :: Set Int -> IntMap (Set Int) -> Formula -> Maybe [(Var, Term)]
unifyFormula s m f =
    let (f', m') = runState (skolemize s f) m
     in unify s m' f'
