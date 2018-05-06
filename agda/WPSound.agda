module WPSound where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function hiding (_$_)

open import Command
open import Eval
open import Expr
open import WP
open import Assertion

{-
wp-ctx-step : ∀ { E θ s θ' s' N X W }
            → wp s N X W θ
            → wp s' N X W θ'
            → wp (eapply E s) N X W θ
            → wp (eapply E s') N X W θ'
wp-ctx-step {ehole} = {!!}
wp-ctx-step {eseq E x} = {!!}
wp-ctx-step {ecatch E x} = {!!}
-}


wp-pres-step : ∀ { p θ s θ' s' N X W }
             → p ⊢ θ , s ▷ θ' , s'
             → wp s N X W θ
             -------------------------
             → wp s' N X W θ'

--wp-pres-step (e-context {E} {s} subeval) = {!!}
wp-pres-step (e-assert ptrue) =
  [ proj₂ , (λ pfalse → ⊥-elim (pfalse ptrue)) ∘ proj₁ ]
wp-pres-step (e-assume ptrue) =
  [ (λ pfalse → ⊥-elim (pfalse ptrue)) , id ]
wp-pres-step e-assign = id
wp-pres-step e-choice1 = proj₁
wp-pres-step e-choice2 = proj₂
wp-pres-step (e-seq1 s1eval) = wp-pres-step s1eval
wp-pres-step e-seq2 = id
wp-pres-step e-seq3 = id
wp-pres-step (e-catch1 s1eval) = wp-pres-step s1eval
wp-pres-step e-catch2 = id
wp-pres-step e-catch3 = id
wp-pres-step e-loop = {!!}

wp-pres : ∀ { p θ s θ' s' N X W }
        → p ⊢ θ , s ▷* θ' , s'
        → wp s N X W θ
        -------------------------
        → wp s' N X W θ'

wp-pres (e-base step) = wp-pres-step step
wp-pres (e-ind step steps) = wp-pres steps ∘ wp-pres-step step
