module Axiomatic

import Command
import Eval
import Expr
import Assertion

data Triple : Assertion -> Command -> Assertion -> Assertion -> Assertion
           -> Type where
  A_Assert : {p, n, x, w : Assertion}
          -> Triple (or (and p n) (and (not p) w)) (assert p) n x w
  A_Assume : {p, n, x, w : Assertion}
          -> Triple (or (not p) n) (assume p) n x w
  A_Assign : {e : Expr}
          -> {y : Var}
          -> {n, x, w : Assertion}
          -> Triple (subst y e n) (Assign y e) n x w
  A_Choice : {s1, s2 : Command}
          -> {p1, p2 : Assertion}
          -> {n, x, w : Assertion}
          -> Triple p1 s1 n x w
          -> Triple p2 s2 n x w
          -> Triple (pand p1 p2) (Choice s1 s2) n x w
  A_Seq    : {s1, s2 : Command}
          -> {p1, p2 : Assertion}
          -> {n, x, w : Assertion}
          -> Triple p2 s2 n x w
          -> Triple p1 s1 p2 x w
          -> Triple p1 (Seq s1 s2) n x w
  A_Skip   : {n, x, w : Assertion}
          -> Triple n Skip n x w
  A_Raise  : {n, x ,w : Assertion}
          -> Triple x Raise n x w
  A_Catch  : {s1, s2 : Command}
          -> {p1, p2 : Assertion}
          -> {n, x, w : Assertion}
          -> Triple p2 s2 n x w
          -> Triple p1 s1 n p2 w
          -> Triple p1 (Catch s1 s2) n x w
  A_Loop   : {s : Command}
          -> {n, x, w : Assertion}
          -> Triple n s n x w
          -> Triple n (Loop s) n x w

ax_wp_unique : {s : Command}
            -> {p, p' : Assertion}
            -> {n, x, w : Assertion}
            -> Triple p  s n x w
            -> Triple p' s n x w
            -> p = p'
ax_wp_unique A_Assert A_Assert = refl
ax_wp_unique A_Assume A_Assume = refl
ax_wp_unique A_Assign A_Assign = refl
{-
ax_wp_unique (A_Choice t1 t2) (A_Choice t3 t4)
  with ax_wp_unique t1 t3 | ax_wp_unique t2 t4
... | refl | refl = refl
ax_wp_unique (A_Seq t1 t2) (A_Seq t3 t4) with ax_wp_unique t1 t3 
... | refl with ax_wp_unique t2 t4
... | refl = refl
-}
ax_wp_unique A_Skip A_Skip = refl
ax_wp_unique A_Raise A_Raise = refl
{-
ax_wp_unique (A_Catch t1 t2) (A_Catch t3 t4) with ax_wp_unique t1 t3
... | refl with ax_wp_unique t2 t4
... | refl = refl
-}
ax_wp_unique (A_Loop ind) (A_Loop ind) = refl

{-
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
-}
