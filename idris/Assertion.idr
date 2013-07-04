module Assertion

import Expr

Pred : Type -> Type
Pred a = a -> Type

Assertion : Type
Assertion = Pred Store

and : Assertion -> Assertion -> Assertion
and p q s = (p s, q s)

or : Assertion -> Assertion -> Assertion
or p q s = Either (p s) (q s)

not : Assertion -> Assertion
not p s = Not (p s)

subst : Var -> Expr -> Assertion -> Assertion
subst x e q s = q (extend s x (e s))

true : Assertion
true _ = ()

false : Assertion
false _ = _|_
