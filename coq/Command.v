Require Import Assertion.
Require Import Expr.

Inductive Command : Type :=
| skip   : Command
| assert : Assertion -> Command
| assume : Assertion -> Command
| assign : Var -> Expr -> Command
| seq    : Command -> Command -> Command
| choice : Command -> Command -> Command
| raise  : Command
| catch  : Command -> Command -> Command.
