module Pred where

open import Data.Bool

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
