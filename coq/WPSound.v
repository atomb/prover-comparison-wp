Add LoadPath "/Users/atomb/projects/prover-comparison-wp/coq".
Require Import Command.
Require Import Eval.
Require Import Expr.
Require Import WP.
Require Import Assertion.

Lemma wp_pres_step :
  forall st s st' s' N X W,
  Eval st s st' s' ->
  wp s N X W st ->
  wp s' N X W st'.
    intros st s st' s' N X W e pre.
    generalize dependent W.
    generalize dependent X.
    generalize dependent N.
    induction e.
    simpl. intros N X W pre.
    induction pre.
    induction H.
    exact H0.
    induction H.
    contradiction.
    simpl. intros N X W pre.
    induction pre.
    contradiction.
    exact H.
    simpl. intros N X W pre.
    exact pre.
    simpl. intros N X W pre.
    induction pre.
    exact H.
    simpl. intros N X W pre.
    induction pre.
    exact H0.
    simpl. intros N X W pre.
    apply IHe.
    exact pre.
    simpl. intros N X W pre.
    exact pre.
    simpl. intros N X W pre.
    exact pre.
    simpl. intros N X W pre.
    apply IHe.
    exact pre.
    simpl. intros N X W pre.
    exact pre.
    simpl. intros N X W pre.
    exact pre.
Qed.

(*
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
*)