module WP where

open import Command
open import Expr
open import Pred

subst : Var → Expr → Pred → Pred
subst x e Q = λ θ → Q (extend θ x (e θ))

wp : Command -> Pred -> Pred -> Pred -> Pred
wp (assert P) N X W = por (pand P N) (pand (pnot P) W)
wp (assume P) N X W = por (pnot P) N
wp (x ≔ e)    N X W = subst x e N
wp (s1 □ s2)  N X W = pand (wp s1 N X W) (wp s2 N X W)
wp (s1 $ s2)  N X W = wp s1 (wp s2 N X W) X W
wp skip       N X W = N
wp raise      N X W = X
wp (s1 ! s2)  N X W = wp s1 N (wp s2 N X W) W
