module Pred

import Expr

Pred : Type
Pred = Store -> Bool

pand  : Pred -> Pred -> Pred
pand p q s = p s && q s

por  : Pred -> Pred -> Pred
por p q s = p s || q s

pnot  : Pred -> Pred
pnot p s = not (p s)

pbool  : Bool -> Pred
pbool b _ = b
