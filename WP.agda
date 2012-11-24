module WP where

open import Command
open import Expr
open import Assertion

subst : Var → Expr → Assertion → Assertion
subst x e Q = λ θ → Q (extend θ x (e θ))

wp : Command -> Assertion -> Assertion -> Assertion -> Assertion
wp (assert P) N X W = or (and P N) (and (not P) W)
wp (assume P) N X W = or (not P) N
wp (x ≔ e)    N X W = subst x e N
wp (s1 □ s2)  N X W = and (wp s1 N X W) (wp s2 N X W)
wp (s1 $ s2)  N X W = wp s1 (wp s2 N X W) X W
wp skip       N X W = N
wp raise      N X W = X
wp (s1 ! s2)  N X W = wp s1 N (wp s2 N X W) W
