module Expr where

open import Data.Nat

data Var : Set where
  var : ℕ → Var

data Value : Set where
  const : ℕ → Value

data Store : Set where
  empty  : Store
  extend : Store → Var → Value → Store

data Lookup : Var → Store → Value → Set where
  l-here : forall {θ x v} → Lookup x (extend θ x v) v
  l-there : forall {θ x v x' v'} →
            Lookup x θ v →
            Lookup x (extend θ x' v') v

Expr : Set
Expr = Store → Value

