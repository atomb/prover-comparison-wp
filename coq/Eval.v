Require Import Assertion.
Require Import Expr.
Require Import Command.

Inductive Eval : Store -> Command -> Store -> Command -> Type :=

| e_assert :
    forall st (P : Assertion),
    P st ->
    Eval st (assert P) st skip

| e_assume :
    forall st (P : Assertion),
    P st ->
    Eval st (assume P) st skip

| e_assign :
    forall st x e,
    Eval st (assign x e) (extend st x (e st)) skip

| e_choice1 :
    forall st s s',
    Eval st (choice s s') st s

| e_choice2 :
    forall st s s',
    Eval st (choice s s') st s'

| e_seq1 :
    forall st st' s1 s1' s2,
    Eval st s1 st' s1' ->
    Eval st (seq s1 s2) st' (seq s1' s2)

| e_seq2 :
    forall st s',
    Eval st (seq skip s') st s'

| e_seq3 :
    forall st s,
    Eval st (seq raise s) st raise

| e_catch1 :
    forall st st' s1 s1' s2,
    Eval st s1 st' s1' ->
    Eval st (catch s1 s2) st' (catch s1' s2)

| e_catch2 :
    forall st s,
    Eval st (catch raise s) st s

| e_catch3 :
    forall st s,
    Eval st (catch skip s) st skip.

Inductive EvalStar : Store -> Command -> Store -> Command -> Type :=

| e_base :
    forall st st' s s',
    Eval st s st' s' ->
    EvalStar st s st' s'

| e_ind :
    forall st st' st'' s s' s'',
    Eval st s st' s' ->
    EvalStar st' s' st'' s'' ->
    EvalStar st s st'' s''.
