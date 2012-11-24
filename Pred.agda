module Pred where

open import Data.Bool
open import Function hiding (_$_)
open import Relation.Binary.PropositionalEquality

open import Expr

Pred : Set
Pred = Store → Bool

pand  : Pred → Pred → Pred
pand P Q = λ θ → P θ ∧ Q θ

por  : Pred → Pred → Pred
por P Q = λ θ → P θ ∨ Q θ

pnot  : Pred → Pred
pnot P = λ θ → not (P θ)

pbool  : Bool → Pred
pbool b = λ _ → b

{- Begin silly stuff only necessary due to my limited knowledge of Agda. -}
and-elimr : {P Q : Pred}{θ : Store}
          → P θ ∧ Q θ ≡ true → Q θ ≡ true
and-elimr {P} {Q} {θ} with P θ
... | true = id
... | false = λ ()

and-eliml : {P Q : Pred}{θ : Store}
          → Q θ ∧ P θ ≡ true → Q θ ≡ true
and-eliml {P} {Q} {θ} with Q θ
... | true = λ _ → refl
... | false = λ ()

or-elim-1 : {P Q : Pred}{θ : Store}
            → P θ ≡ true → not (P θ) ∨ Q θ  ≡ true → Q θ ≡ true
or-elim-1 {P} {Q} {θ} with P θ | Q θ
... | false | false = λ z _ → z
... | false | true  = λ _ _ → refl
... | true  | false = λ _ z → z
... | true  | true  = λ _ _ → refl

or-elim-3 : {N : Pred}{θ : Store} → N θ ∨ false ≡ true → N θ ≡ true
or-elim-3 {N} {θ} with N θ
... | false = λ z → z
... | true = λ _ → refl


or-elim-2 : {P N W : Pred}{θ : Store}
          → P θ ≡ true
          → por (pand P N) (pand (pnot P) W) θ ≡ true
          → N θ ≡ true
or-elim-2 {P} {N} {W} {θ} with P θ | W θ
... | false | false = λ _ → λ ()
... | false | true  = λ ()
... | true  | false = λ _ → or-elim-3 {N} {θ}
... | true  | true  = λ _ → or-elim-3 {N} {θ}
{- End silly stuff -}
