module WPSound where

open import Data.Bool
open import Function
open import Relation.Binary.Core
open import Relation.Nullary.Negation

open import Command
open import Eval
open import Expr
open import WP
open import Pred

and-elimr : {P : Pred}{Q : Pred}{θ : Store}
          → P θ ∧ Q θ ≡ true → Q θ ≡ true
and-elimr {P} {Q} {θ} with P θ
... | true = id
... | false = λ ()

and-eliml : {P : Pred}{Q : Pred}{θ : Store}
          → Q θ ∧ P θ ≡ true → Q θ ≡ true
and-eliml {P} {Q} {θ} with Q θ
... | true = λ _ → refl
... | false = λ ()

or-elim-foo : {P : Pred}{Q : Pred}{θ : Store}
            → P θ ≡ true → not (P θ) ∨ Q θ  ≡ true → Q θ ≡ true
or-elim-foo {P} {Q} {θ} with P θ | Q θ
... | false | false = λ z _ → z
... | false | true  = λ _ _ → refl
... | true  | false = λ _ z → z
... | true  | true  = λ _ _ → refl

wp-sound-step : forall { p c Q R P θ θ' }
              → (p ⊢ θ , c ▷ θ' , skip)
              → (wp wlp c Q R ≡ P)
              → (P θ ≡ true)
              ---------------------------
              → (Q θ' ≡ true)
wp-sound-step {p} {assert P} {Q} {R} {.(pand P Q) } {θ} {.θ}
              (e-assert _) refl = and-elimr {P} {Q} {θ}
wp-sound-step {p} {assume P} {Q} {R} {.(por (pnot P) Q) } {θ} {.θ}
              (e-assume ptrue) refl = or-elim-foo {P} {Q} {θ} ptrue
wp-sound-step e-assign refl = id
wp-sound-step {p} {skip □ s2} {Q} {R}
              {.(pand (wp wlp skip Q R) (wp wlp s2 Q R))} {θ} {.θ}
              e-choice1 refl = and-eliml {wp wlp s2 Q R} {Q} {θ}
wp-sound-step {p} {s1 □ skip} {Q} {R}
              {.(pand (wp wlp s1 Q R) (wp wlp skip Q R))} {θ} {.θ}
              e-choice2 refl = and-elimr {wp wlp s1 Q R} {Q} {θ}
wp-sound-step e-seq1 refl = id
