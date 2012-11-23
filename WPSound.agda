module WPSound where

open import Data.Bool
open import Function hiding (_$_)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

open import Command
open import Eval
open import Expr
open import WP
open import Pred

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

wp-pres-step : forall { p θ s θ' s' N X W }
             → (wp s N X W θ ≡ true)
             → (p ⊢ θ , s ▷ θ' , s')
             ----------------------------
             → (wp s' N X W θ' ≡ true)

wp-pres-step {_} {θ} {assert P} {.θ} {skip} {N} {X} {W} wptrue (e-assert ptrue) =
  or-elim-2 {P} {N} {W} {θ} ptrue wptrue
wp-pres-step {_} {θ} {assume P} {.θ} {skip} {N} wptrue (e-assume ptrue) =
  or-elim-1 {P} {N} {θ} ptrue wptrue
wp-pres-step {_} {θ} {x ≔ e} {.(extend θ x (e θ))} wptrue e-assign = wptrue
wp-pres-step {_} {θ} {s1 □ s2} {.θ} {.s1} {N} {X} {W} wptrue e-choice1 =
  and-eliml {wp s2 N X W} {wp s1 N X W} {θ} wptrue
wp-pres-step {_} {θ} {s1 □ s2} {.θ} {.s2} {N} {X} {W} wptrue e-choice2 =
  and-elimr {wp s1 N X W} {wp s2 N X W} {θ} wptrue
wp-pres-step {_} {θ} {s1 $ s2} {θ'} {s1' $ .s2} wptrue (e-seq1 s1eval) =
  wp-pres-step wptrue s1eval
wp-pres-step {_} {θ} {skip $ s2} {.θ} {.s2} wptrue e-seq2 = wptrue
wp-pres-step {_} {θ} {raise $ s2} {.θ} {raise} wptrue e-seq3 = wptrue
wp-pres-step {_} {θ} {s1 ! s2} {_} {s1' ! .s2} wptrue (e-catch1 s1eval) =
  wp-pres-step wptrue s1eval
wp-pres-step {_} {θ} {raise ! s2} {.θ} {.s2} wptrue e-catch2 = wptrue
wp-pres-step {_} {θ} {skip ! s2} {.θ} {skip} wptrue e-catch3 = wptrue

wp-pres : forall { p θ s θ' s' N X W }
        → (wp s N X W θ ≡ true)
        → (p ⊢ θ , s ▷* θ' , s')
        -------------------------
        → (wp s' N X W θ' ≡ true)

wp-pres wptrue (e-base eval') = wp-pres-step wptrue eval'
wp-pres wptrue (e-ind first rest) =
  wp-pres (wp-pres-step wptrue first) rest
