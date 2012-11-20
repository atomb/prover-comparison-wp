module WP where

open import Command
open import Expr
open import Pred

data WPType : Set where
  wlp : WPType
  wvlp : WPType

subst : Var → Expr → Pred → Pred
subst x e Q = λ θ → Q (extend θ x (e θ))

wp : WPType → Command -> Pred -> Pred -> Pred
wp wlp   (assert p) q r = pand p q
wp wvlp  (assert p) q r = por (pnot p) q
wp ty    (assume p) q r = por (pnot p) q
wp ty    (x ≔ e)    q r = subst x e q
wp ty    (c1 □ c2)  q r = pand (wp ty c1 q r) (wp ty c2 q r)
wp ty    (c1 $ c2)  q r = wp ty c1 (wp ty c2 q r) r
wp ty    skip       q r = q
{-
wp ty    raise      q r = r
wp ty    (c1 ! c2)  q r = wp ty c1 q (wp ty c2 q r)
-}
