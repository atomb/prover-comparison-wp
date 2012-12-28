module WP where

open import Relation.Unary

open import Command
open import Expr
open import Assertion

wp : Command -> Assertion -> Assertion -> Assertion -> Assertion
wp (assert P) N X W = (P ∩ N) ∪ ((not P) ∩ W)
wp (assume P) N X W = (not P) ∪ N
wp (x ≔ e)    N X W = subst x e N
wp (s1 □ s2)  N X W = wp s1 N X W ∩ wp s2 N X W
wp (s1 $ s2)  N X W = wp s1 (wp s2 N X W) X W
wp skip       N X W = N
wp raise      N X W = X
wp (s1 ! s2)  N X W = wp s1 N (wp s2 N X W) W
-- Incorrect unless N is a loop invariant for s.
wp (s *)      N X W = N
