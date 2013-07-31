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


wp_pres_step : {pr : Program}
            -> {t : Store} -> {s : Command}
            -> {t' : Store} -> {s' : Command}
            -> {n : Assertion} -> {x : Assertion} -> {w : Assertion}
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
wp_pres_step E_Assign pre = pre
wp_pres_step E_Choice1 pre = fst pre
wp_pres_step E_Choice2 pre = snd pre
{-
wp_pres_step (e-seq1 s1eval) = wp_pres_step s1eval
-}
wp_pres_step E_Seq2 pre = pre
wp_pres_step E_Seq3 pre = pre
{-
wp_pres_step (e-catch1 s1eval) = wp_pres_step s1eval
-}
wp_pres_step E_Catch2 pre = pre
wp_pres_step E_Catch3 pre = pre
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
