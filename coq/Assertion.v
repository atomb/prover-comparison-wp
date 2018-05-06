Require Import Expr.

Definition Assertion : Type := Store -> Prop.

Definition and (P Q : Assertion) : Assertion :=
  fun s : Store => P s /\ Q s.

Definition or (P Q : Assertion) : Assertion :=
  fun s : Store => P s \/ Q s.

Definition not (P : Assertion) : Assertion :=
  fun s : Store => not (P s).

Definition subst (x : Var) (e : Expr) (Q : Assertion) : Assertion :=
  fun s : Store => Q (extend s x (e s)).
