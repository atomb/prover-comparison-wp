module WP

import Command
import Expr
import Assertion

%access public export

%default total
wp : Command -> Assertion -> Assertion -> Assertion -> Assertion
wp (Assert p)     n x w = or (and p n) (and (not p) w)
wp (Assume p)     n x w = or (not p) n
wp (Assign y e)   n x w = subst y e n
wp (Choice s1 s2) n x w = and (wp s1 n x w) (wp s2 n x w)
wp (Seq s1 s2)    n x w = wp s1 (wp s2 n x w) x w
wp Skip           n x w = n
wp Raise          n x w = x
wp (Catch s1 s2)  n x w = wp s1 n (wp s2 n x w) w
-- Incorrect unless n is a loop invariant for s.
-- wp (Loop s)       n x w = n
