Inductive Var : Set :=
| var : nat -> Var.

Inductive Value : Set :=
| const : nat -> Value.

Inductive Store : Set :=
| empty  : Store
| extend : Store -> Var -> Value -> Store.

Inductive Lookup : Var -> Store -> Value -> Set :=
| l_here : forall s x v, Lookup x (extend s x v) v
| l_there : forall s x v x' v',
            Lookup x s v ->
            Lookup x (extend s x' v') v.

Definition Expr : Set := Store -> Value.