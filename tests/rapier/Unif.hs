{-# LANGUAGE GHC2024 #-}

module Unif where

import Control.Monad
import Control.Monad.State
import Data.Foldable qualified as Foldable
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

type Var = Int

-- Yeah, so, sorry about this. It's probably a little hard for Liquid Haskell to
-- reason about abstract fixed point of the sort. It makes writing this file
-- much more concise, though.
data TermF t
  = V Var
  | U
  | L t
  | R t
  | P t t
  deriving (Show, Functor, Foldable, Traversable)

-- See the unification-fd package.
zipMatch :: TermF t -> TermF u -> Maybe (TermF (t, u))
zipMatch (V x) (V y) | x == y = Just $ V x
zipMatch U U = Just $ U
zipMatch (L t) (L u) = Just $ L (t, u)
zipMatch (R t) (R u) = Just $ R (t, u)
zipMatch (P t t') (P u u') = Just $ P (t, u) (t', u')
zipMatch _ _ = Nothing

data Term = MkTerm (TermF Term)
  deriving Show

newtype Subst t = Subst [(Var,t)]
  deriving (Show, Functor, Foldable, Traversable)

lookupSubst :: Var -> Subst e -> Maybe e
lookupSubst i (Subst s) = lookup i s

emptySubst :: Subst e
emptySubst = Subst []

extendSubst :: Subst a -> Var -> a -> Subst a
extendSubst (Subst s) i e = Subst ((i, e) : s)

renameVar :: Var -> Subst Var -> Var
renameVar i (Subst s) = case lookup i s of
  Just x -> x
  Nothing -> i

-- TODO: add a separate in-scope set?
substTermF :: (TermF u -> u) -> (Subst u -> t -> u) -> Subst u -> TermF t -> u
substTermF mk r s (V x) = case lookupSubst x s of
  Just u -> u
  Nothing -> mk (V x)
substTermF mk r s t = mk $ fmap (r s) t

-- I don't think I actually need this
substTerm :: Subst Term -> Term -> Term
substTerm s (MkTerm t) = substTermF MkTerm substTerm s t

-- I don't think I actually need this either
renameTerm :: Subst Var -> Term -> Term
renameTerm s t = substTerm (fmap (MkTerm . V) s) t

--------------------------------------------------------

-- Really meant to be a different kind of variable than Var altogether. These
-- one will get unified, while Var are rigid as far a unification in concerned.
-- UVars have a domain, which is the list of Vars which can appear in its
-- solution.
type UVar = Int

data UTerm
  = Constr (TermF UTerm)
  | UV UVar (Subst UTerm) -- covers exactly the UVar's domain
  deriving Show

-- I changed my mind: in my earliest take, an UVar would take a `Subst Var`
-- because it's the only relevant thing. And really it's always a distinct bunch
-- of variable so that we can invert it (see below), however, this actually
-- creates more code, and in higher-order examples we wouldn't have this
-- property so I don't care about proving that it's true all that much.
--
-- So we don't need renaming. I'm leaving it here because I'm not using version
-- control 😬
--
-- renameUTerm :: Subst Var -> UTerm -> UTerm
-- renameUTerm s (Constr t) = substTermF (Constr . V) renameUTerm
-- renameUTerm s (UV v s') = UV v (fmap (\x -> renameVar x s) s')

substUTerm :: Subst UTerm -> UTerm -> UTerm
substUTerm s (Constr t) = substTermF Constr substUTerm s t
substUTerm s (UV v s') = UV v (fmap (substUTerm s) s')

substTermU :: Subst UTerm -> Term -> UTerm
substTermU s (MkTerm t) = substTermF Constr substTermU s t

--------------------------------------------------------

freshVar :: Set Var -> Var
freshVar s = case Set.lookupMax s of
    Nothing -> 0
    Just i -> i + 1

--------------------------------------------------------

data Formula
  = A Term Term
  | Conj Formula Formula
  | Exists Var Formula
  | Forall Var Formula
  deriving Show

type UnifProblem = [(UTerm, UTerm)]

-- Precondition: closed formula
--
-- Returns: a unification problem and a set containing the in-scope sets for
-- each of the generated UVar. The `Maybe UTerm` will always be `Nothing`, but
-- it's easier to use the same type as the eventual solution of the unification
-- problem.
prepFormula :: Formula -> (UnifProblem, Map UVar (Set Var, Maybe UTerm))
prepFormula a = runState (go Set.empty emptySubst a) Map.empty
  -- I know you won't like monads, feel free to expand, it just makes this
  -- easier to read.
  where
    go :: Set Var -> Subst UTerm -> Formula -> State (Map UVar (Set Var, Maybe UTerm)) UnifProblem
    go _in_scope s (A t u) = return [(substTermU s t, substTermU s u)]
    go in_scope s (Conj a b) = (++) <$> (go in_scope s a) <*> (go in_scope s b)
    go in_scope s (Forall x a) =
      -- I wrote this in de Bruijn indices recently, I must say that it's much
      -- easier with named variables!
      let y = freshVar in_scope in
      go (Set.insert y in_scope) (extendSubst s x (Constr (V y))) a
    go in_scope s (Exists x a) = do
      v <- freshUVar in_scope
      go in_scope (extendSubst s x v) a 

    -- I feel that this may be different from the original rapier: here we
    -- depend *for safety* on the fact that the in_scope set is *exactly* the
    -- variable which have been made available by a `Forall` above me.
    freshUVar :: Set Var -> State (Map UVar (Set Var, Maybe UTerm)) UTerm
    freshUVar in_scope = do
      uvars <- get
      let v = case Set.lookupMax (Map.keysSet uvars) of {Nothing -> 0; Just i -> i+1}
      put (Map.insert v (in_scope, Nothing) uvars)
      return $ UV v (idSubst in_scope)

    idSubst :: Set Var -> Subst UTerm
    idSubst in_scope = Subst $ map (\x -> (x, Constr (V x))) (Set.elems in_scope)
    -- I'm cheating here, using Subst locally. Should make a generic construct.

-- Maybe it'd be useful to use an in_scope set for this. Then you'd have to
-- return it from `prepFormula`. It's annoying but not a problem.
solveProb :: (UnifProblem, Map UVar (Set Var, Maybe UTerm)) -> Map UVar (Set Var, Maybe UTerm)
solveProb (prob, sol) = snd $ runState (go prob) sol
  -- Again I'm using a State monad. Frustrating for you, life-saving for me.
  where
    go :: UnifProblem -> State (Map UVar (Set Var, Maybe UTerm)) ()
    go [] = return ()
    go ((Constr t, Constr u):eqs) = case zipMatch t u of
      Nothing -> return () -- This should be some form of error, but since we
                           -- don't really care about the solution, only about
                           -- whether the scopes are correct, we're just going
                           -- to return a nonsense solution in error cases.
      Just eqs' -> go ((Foldable.toList eqs') ++ eqs)
    go (((UV v s), t):eqs) = do
      uvars <- get
      case Map.lookup v uvars of
        Nothing -> error "I except this case to be caught by Liquid Haskell"
        Just (in_scope, Just u) -> go ((u, t): eqs)
        Just (in_scope, Nothing) ->
          -- This invSubst bit is one of the big reason why this problem is
          -- interesting: it changes t, which is a term in the current scope,
          -- into a term in the scope of the UVar v. Tricky business.
          case invSubst s of
            Nothing -> go eqs -- Ambiguous case, we do something not
                              -- particularly sensible. A more realistic unifier
                              -- would keep the current equation on the side
                              -- until they become solvable or errors. This case
                              -- never actually happens in the first order case,
                              -- but whatever.
            Just s' -> do
              -- In a true unifier we'd do an occur check here, that v doesn't
              -- appear in t.
              put (Map.insert v (in_scope, Just (substUTerm s' t)) uvars)
              go eqs
    go ((t, u@UV{}):eqs) = go ((u, t) : eqs)

    invSubst :: Subst UTerm -> Maybe (Subst UTerm)
    invSubst s = do
      -- I'm using the list explicitly again. I'm such a hypocrite. Though this
      -- could easily be made a primitive, which is probably the way to go.
      Subst candidate <- traverse (\case {(Constr (V x)) -> Just x; _ -> Nothing}) s
      guard $ all_distinct (map snd candidate)
      return $ Subst (map (\(x, y) -> (y, (Constr (V x)))) candidate)

    -- Not the most efficient…
    all_distinct :: [Var] -> Bool
    all_distinct l = List.nub l == l

solve :: Formula -> Map UVar (Set Var, Maybe UTerm)
solve = solveProb . prepFormula
