module WPSound

import Command
import Eval
import Expr
import WP
import Assertion

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


wp_pres_step : (pr : _)
            -> (t : Store) -> (s : Command)
            -> (t' : Store) -> (s' : Command)
            -> (n : Assertion) -> (x : Assertion) -> (w : Assertion)
            -> Eval pr t s t' s'
            -> wp s n x w t
             -------------------------
            -> wp s' n x w t'

--wp-pres-step (e-context {E} {s} subeval) = {!!}
{-
wp_pres_step (e-assert ptrue) =
  [ proj₂ , (λ pfalse → ⊥-elim (pfalse ptrue)) ∘ proj₁ ]
wp_pres_step (e-assume ptrue) =
  [ (λ pfalse → ⊥-elim (pfalse ptrue)) , id ]
-}
--wp_pres_step pr t (Assign y e) (extend t y (e t)) Skip n x w (E_Assign pr t y e) pre = pre
{-
wp_pres_step e-choice1 = proj₁
wp_pres_step e-choice2 = proj₂
wp_pres_step (e-seq1 s1eval) = wp_pres_step s1eval
wp_pres_step e-seq2 = id
wp_pres_step e-seq3 = id
wp_pres_step (e-catch1 s1eval) = wp_pres_step s1eval
wp_pres_step e-catch2 = id
wp_pres_step e-catch3 = id
-}
-- wp_pres_step e-loop = {!!}

{-
wp-pres : ∀ { p θ s θ' s' N X W }
        → p ⊢ θ , s ▷* θ' , s'
        → wp s N X W θ
        -------------------------
        → wp s' N X W θ'

wp-pres (e-base step) = wp-pres-step step
wp-pres (e-ind step steps) = wp-pres steps ∘ wp-pres-step step
-}
