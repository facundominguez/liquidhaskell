{-# LANGUAGE LambdaCase #-}
{-@ LIQUID "--higherorder" @-}
module Subst where

import Data.Set

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

{-@
type ScopedExp S = {e:Exp | isSubsetOf (freeVars e) S}
@-}

{-@
substitute
  :: scope:Set Int
  -> (Int -> ScopedExp scope)
  -> ScopedExp scope
  -> ScopedExp scope
@-}
substitute :: Set Int -> (Int -> Exp) -> Exp -> Exp
substitute scope f = \case
    Var i -> f i
    App e0 e1 -> App (substitute scope f e0) (substitute scope f e1)
    Lam i e
      | member i scope ->
          let j = freshVar scope
           in Lam j $
                substitute
                  (insert j scope)
                  (extendSubst f i (Var j))
                  e
      | otherwise ->
          Lam i $
            substitute
              (insert i scope)
              -- This has the effect of canceling the substitution of i
              -- whatever it was in f
              (extendSubst f i (Var i))
              e

extendSubst :: (Int -> a) -> Int -> a -> Int -> a
extendSubst f i e k = if k == i then e else f k

freshVar :: Set Int -> Int
freshVar s = case lookupMax s of
    Nothing -> 0
    Just i -> i + 1
