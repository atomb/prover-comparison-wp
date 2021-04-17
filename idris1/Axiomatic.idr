module Axiomatic

import Command
import Eval
import Expr
import Assertion

%access public export
%default total

data Triple : Assertion -> Command -> Assertion -> Assertion -> Assertion
           -> Type where
  A_Assert : {p, n, x, w : Assertion}
          -> Triple (or (and p n) (and (not p) w)) (Assert p) n x w
  A_Assume : {p, n, x, w : Assertion}
          -> Triple (or (not p) n) (Assume p) n x w
  A_Assign : {e : Expr}
          -> {y : Var}
          -> {n, x, w : Assertion}
          -> Triple (subst y e n) (Assign y e) n x w
  A_Choice : {s1, s2 : Command}
          -> {p1, p2 : Assertion}
          -> {n, x, w : Assertion}
          -> Triple p1 s1 n x w
          -> Triple p2 s2 n x w
          -> Triple (and p1 p2) (Choice s1 s2) n x w
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
  {-
  A_Loop   : {s : Command}
          -> {n, x, w : Assertion}
          -> Triple n s n x w
          -> Triple n (Loop s) n x w
  -}

||| Theorem: the axiomatic semantics admit only one pre-condition leading a
||| given statement to a given triple of post-conditions.
ax_wp_unique : {s : Command}
            -> {p, p' : Assertion}
            -> {n, x, w : Assertion}
            -> Triple p  s n x w
            -> Triple p' s n x w
            -> p = p'
ax_wp_unique {s=Skip} A_Skip A_Skip = Refl
ax_wp_unique {s=(Assert f)} A_Assert A_Assert = Refl
ax_wp_unique {s=(Assume f)} A_Assume A_Assume = Refl
ax_wp_unique {s=(Assign x f)} A_Assign A_Assign = Refl
ax_wp_unique {s=(Seq x y)} (A_Seq z s) (A_Seq t u) =
  case ax_wp_unique z t of
    Refl => case ax_wp_unique s u of
              Refl => Refl
ax_wp_unique {s=(Choice x y)} (A_Choice z s) (A_Choice t u) =
  case ax_wp_unique z t of
    Refl => case ax_wp_unique s u of
              Refl => Refl
ax_wp_unique {s=Raise} A_Raise A_Raise = Refl
ax_wp_unique {s=(Catch x y)} (A_Catch z s) (A_Catch t u) =
  case ax_wp_unique z t of
    Refl => case ax_wp_unique s u of
              Refl => Refl
-- ax_wp_unique (A_Loop ind) (A_Loop ind) = refl

||| Theorem: if evaluation proceeds from (s, t) to (s', t') and s has
||| pre-condition p for a particular post-condition, and s' has pre-condition
||| p' for the same post-condition, and p holds of t, then p' holds of t'. This
||| is essentially like preservation in type systems.
ax_pres_step : {pr : Program}
       -> {t : Store} -> {s : Command}
       -> {t' : Store} -> {s' : Command}
       -> {p, p', n, x, w: Assertion}
       -> Eval pr t s t' s'
       -> Triple p s n x w
       -> Triple p' s' n x w
       -> p t
       -------------------------
       -> p' t'
ax_pres_step (E_Assert q) A_Assert A_Skip pre =
  case pre of
    (Left ptrue) => snd ptrue
    (Right pfalse) => void ((fst pfalse) q)
ax_pres_step (E_Assume q) A_Assume A_Skip pre =
  case pre of
    (Left ptrue) => void (ptrue q)
    (Right pfalse) => pfalse
ax_pres_step E_Assign A_Assign A_Skip pre = pre
ax_pres_step E_Choice1 (A_Choice t1 t2) tr pre =
  case ax_wp_unique t1 tr of
    Refl => fst pre
ax_pres_step E_Choice2 (A_Choice t1 t2) tr pre =
  case ax_wp_unique t2 tr of
    Refl => snd pre
ax_pres_step (E_Seq1 ev) (A_Seq t1 t2) (A_Seq t3 t4) pre =
  case ax_wp_unique t1 t3 of
    Refl => ax_pres_step ev t2 t4 pre
ax_pres_step E_Seq2 (A_Seq t1 A_Skip) tr pre =
  case ax_wp_unique t1 tr of
    Refl => pre
ax_pres_step E_Seq3 (A_Seq _ A_Raise) A_Raise pre = pre
ax_pres_step (E_Catch1 ev) (A_Catch t1 t2) (A_Catch t3 t4) pre =
  case ax_wp_unique t1 t3 of
    Refl => ax_pres_step ev t2 t4 pre
ax_pres_step E_Catch2 (A_Catch t1 A_Raise) t2 pre =
  case ax_wp_unique t1 t2 of
    Refl => pre
ax_pres_step E_Catch3 (A_Catch _ A_Skip) A_Skip pre = pre
