(*
module Axiomatic where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function hiding (_$_)
open import Relation.Binary.Core

open import Command
open import Eval
open import Expr
open import Assertion

data Triple : Assertion → Command → Assertion → Assertion → Assertion
            → Set' where
  a-assert : ∀ {P N X W}
           → Triple (or (and P N) (and (not P) W)) (assert P) N X W
  a-assume : ∀ {P N X W}
           → Triple (or (not P) N) (assume P) N X W
  a-assign : ∀ {e x N X W}
           → Triple (subst x e N) (x ≔ e) N X W
  a-choice : ∀ {s1 s2 P1 P2 N X W}
           → Triple P1 s1 N X W
           → Triple P2 s2 N X W
           → Triple (and P1 P2) (s1 □ s2) N X W
  a-seq    : ∀ {s1 s2 P1 P2 N X W}
           → Triple P2 s2 N X W
           → Triple P1 s1 P2 X W
           → Triple P1 (s1 $ s2) N X W
  a-skip   : ∀ {N X W}
           → Triple N skip N X W
  a-raise  : ∀ {N X W}
           → Triple X raise N X W
  a-catch  : ∀ {s1 s2 P1 P2 N X W}
           → Triple P2 s2 N X W
           → Triple P1 s1 N P2 W
           → Triple P1 (s1 ! s2) N X W
  a-loop   : ∀ {s N X W}
           → Triple N s N X W
           → Triple N (s * ) N X W

ax-wp-unique : ∀ { P P' s N X W }
             → Triple P  s N X W
             → Triple P' s N X W
             → P ≡ P'
ax-wp-unique a-assert a-assert = refl
ax-wp-unique a-assume a-assume = refl
ax-wp-unique a-assign a-assign = refl
ax-wp-unique (a-choice t1 t2) (a-choice t3 t4)
  with ax-wp-unique t1 t3 | ax-wp-unique t2 t4
... | refl | refl = refl
ax-wp-unique (a-seq t1 t2) (a-seq t3 t4) with ax-wp-unique t1 t3 
... | refl with ax-wp-unique t2 t4
... | refl = refl
ax-wp-unique a-skip a-skip = refl
ax-wp-unique a-raise a-raise = refl
ax-wp-unique (a-catch t1 t2) (a-catch t3 t4) with ax-wp-unique t1 t3
... | refl with ax-wp-unique t2 t4
... | refl = refl
ax-wp-unique (a-loop t1) (a-loop t2) = refl

ax-pres-step : ∀ { p P θ s P' θ' s' N X W }
             → p ⊢ θ , s ▷ θ' , s'
             → Triple P  s  N X W
             → Triple P' s' N X W
             → P θ
             -------------------------
             → P' θ'
ax-pres-step (e-assert Q) a-assert a-skip =
  [ proj₂ , (λ pfalse → ⊥-elim (pfalse Q)) ∘ proj₁ ]
ax-pres-step (e-assume Q) a-assume a-skip =
  [ (λ pfalse → ⊥-elim (pfalse Q)) , id ]
ax-pres-step e-assign a-assign a-skip = id
ax-pres-step e-choice1 (a-choice t1 t2) tr with ax-wp-unique t1 tr
... | refl = proj₁ 
ax-pres-step e-choice2 (a-choice t1 t2) tr with ax-wp-unique t2 tr
... | refl = proj₂
ax-pres-step (e-seq1 ev) (a-seq t1 t2) (a-seq t3 t4)
  with ax-wp-unique t1 t3
... | refl = ax-pres-step ev t2 t4
ax-pres-step e-seq2 (a-seq t1 a-skip) tr with ax-wp-unique t1 tr
... | refl = id
ax-pres-step e-seq3 (a-seq t1 a-raise) a-raise = id
ax-pres-step (e-catch1 ev) (a-catch t1 t2) (a-catch t3 t4)
  with ax-wp-unique t1 t3
... | refl = ax-pres-step ev t2 t4
ax-pres-step e-catch2 (a-catch t1 a-raise) t2
  with ax-wp-unique t1 t2
... | refl = id
ax-pres-step e-catch3 (a-catch t1 a-skip) a-skip = id
ax-pres-step e-loop (a-loop t1) (a-seq t2 t3)
  with ax-wp-unique t2 (a-loop t1)
... | refl with ax-wp-unique t1 t3
... | refl = id

*)
