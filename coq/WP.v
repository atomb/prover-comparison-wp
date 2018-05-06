Require Import Command.
Require Import Expr.
Require Import Assertion.

Fixpoint wp (c : Command) (N X W: Assertion) : Assertion :=
  match c with
  | assert P     => or (and P N) (and (not P) W)
  | assume P     => or (not P) N
  | assign x e   => subst x e N
  | choice s1 s2 => and (wp s1 N X W) (wp s2 N X W)
  | seq s1 s2    => wp s1 (wp s2 N X W) X W
  | skip         => N
  | raise        => X
  | catch s1 s2  => wp s1 N (wp s2 N X W) W
  end.