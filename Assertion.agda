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

and-elimr : {P Q : Assertion}{θ : Store}
          → (and P Q) θ → Q θ
and-elimr (proj₁ , proj₂) = proj₂

and-eliml : {P Q : Assertion}{θ : Store}
          → (and Q P) θ → Q θ
and-eliml (proj₁ , proj₂) = proj₁

or-elim-1 : {P Q : Assertion}{θ : Store}
            → P θ → (or (not P) Q) θ → Q θ
or-elim-1 ptrue (inj₁ absurd) with absurd ptrue
... | ()
or-elim-1 ptrue (inj₂ qtrue) = qtrue

-- or-elim-3 : {N : Assertion}{θ : Store} → (or N Empty) θ → N θ

or-elim-2 : {P Q R : Assertion}{θ : Store}
          → P θ
          → or (and P Q) (and (not P) R) θ
          → Q θ
or-elim-2 ptrue (inj₁ (proj₁ , proj₂)) = proj₂
or-elim-2 ptrue (inj₂ (proj₁ , proj₂)) with proj₁ ptrue
... | ()
