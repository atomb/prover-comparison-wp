module Assertion where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Unary

open import Expr

Assertion = Pred Store zero

and : Assertion → Assertion → Assertion
and P Q = P ∩ Q

or : Assertion → Assertion → Assertion
or P Q = P ∪ Q

not : Assertion → Assertion
not P = ∁ P

subst : Var → Expr → Assertion → Assertion
subst x e Q = λ θ → Q (extend θ x (e θ))
