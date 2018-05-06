import init.logic

namespace expr

inductive Var : Type
  | vn : nat -> Var

inductive Value : Type
  | const : nat -> Value

inductive Store : Type
  | empty : Store
  | extend : Var -> Value -> Store -> Store

def Expr := Store -> Value

end expr

namespace assertion

open expr
open expr.Store

def Assertion := Store -> Prop

def and (p : Assertion) (q : Assertion) (s : Store) :=
  p s /\ q s

def or (p : Assertion) (q : Assertion) (s : Store)  :=
  p s \/ q s

def not (p : Assertion) (s : Store) :=
  p s -> false

def subst (x : Var) (e : Expr) (q : Assertion) (s : Store) :=
  q (extend x (e s) s)

end assertion

namespace cmd

open expr
open assertion

inductive Command : Type
  | skip : Command
  | cassert : Assertion -> Command
  | cassume : Assertion -> Command
  | assign : Var -> Expr -> Command
  | seq : Command -> Command -> Command
  | choice : Command -> Command -> Command
  | raise : Command
  | catch : Command -> Command -> Command

inductive Declaration : Type
  | func : Var -> Assertion -> Command -> Assertion -> Assertion
         -> Declaration

inductive Program : Type
  | prog : list Declaration -> Program

inductive Context : Type
  | hole        : Context
  | seqleft     : Command -> Context -> Context
  | seqright    : Command -> Context -> Context
  | catchleft   : Command -> Context -> Context
  | catchright  : Command -> Context -> Context
  | choiceleft  : Command -> Context -> Context
  | choiceright : Command -> Context -> Context

inductive EvalContext : Type
  | ehole  : EvalContext
  | eseq   : Command -> EvalContext -> EvalContext
  | ecatch : Command -> EvalContext -> EvalContext

end cmd

namespace wp

open cmd
open cmd.Command
open assertion

def wp : Command -> Assertion -> Assertion -> Assertion -> Assertion
  | (cassert p)     n x w := or (and p n) (and (not p) w)
  | (cassume p)     n x w := or (not p) n
  | (assign y e)    n x w := subst y e n
  | (choice c1 c2)  n x w := and (wp c1 n x w) (wp c2 n x w)
  | (seq c1 c2)     n x w := wp c1 (wp c2 n x w) x w
  | skip            n x w := n
  | raise           n x w := x
  | (catch c1 c2)   n x w := wp c1 n (wp c2 n x w) w

end wp

namespace evaluation

open assertion
open cmd
open cmd.Command
open cmd.EvalContext
open expr
open expr.Store

definition ec_apply : EvalContext -> Command -> Command
  | ehole s := s
  | (eseq s2 E) s1 := seq (ec_apply E s1) s2
  | (ecatch s2 E) s1 := catch (ec_apply E s1) s2

inductive step : Store -> Command -> Store -> Command -> Type
  | e_assert  : ∀ {t : Store} {p : Assertion},
                p t ->
                -------------------------------------------
                step t (cassert p) t skip

  | e_assume  : ∀ {t : Store} {p : Assertion},
                p t ->
                -------------------------------------------
                step t (cassume p) t skip

  | e_assign  : ∀ {t x e},
                -------------------------------------------
                step t (assign x e) (extend x (e t) t) skip

  | e_choice1 : ∀ {t s1 s2},
                -------------------------------------------
                step t (choice s1 s2) t s1

  | e_choice2 : ∀ {t s1 s2},
                -------------------------------------------
                step t (choice s1 s2) t s2

  | e_seq1    : ∀ {t t' s1 s1' s2},
                step t s1 t' s1' ->
                -------------------------------------------
                step t (seq s1 s2) t' (seq s1' s2)

  | e_seq2    : ∀ {t s2},
                -------------------------------------------
                step t (seq skip s2) t s2

  | e_seq3    : ∀ {t s2},
                -------------------------------------------
                step t (seq raise s2) t raise

  | e_catch1  : ∀ {t t' s1 s1' s2},
                step t s1 t' s1' ->
                -------------------------------------------
                step t (catch s1 s2) t' (catch s1' s2)

  | e_catch2  : ∀ {t s2},
                -------------------------------------------
                step t (catch raise s2) t s2

  | e_catch3  : ∀ {t s2},
                -------------------------------------------
                step t (catch skip s2) t skip

end evaluation

namespace wpsound

open assertion
open cmd
open cmd.Command
open evaluation
open evaluation.step
open expr
open expr.Store
open wp
open sum

lemma wp_pres_step :
  ∀ {t s t' s' N X W},
  step t s t' s' →
  wp s N X W t →
  ----------------------
  wp s' N X W t' :=
  begin
    introv h1 h2,
    induction h1 generalizing N X W,
    simp [wp] at h2,
    simp [wp],
    simp [assertion.or, assertion.and, assertion.not] at h2,
    cases h2,
    cases h2,
    exact h2_right,
    cases h2,
    contradiction,
    simp [wp] at h2,
    simp [wp],
    simp [assertion.or, assertion.not] at h2,
    cases h2,
    contradiction,
    exact h2,
    simp [wp, subst] at h2,
    exact h2,
    simp [wp, assertion.and] at h2,
    cases h2,
    exact h2_left,
    simp [wp, assertion.and] at h2,
    cases h2,
    exact h2_right,
    simp [wp] at h2, simp [wp],
    apply h1_ih,
    exact h2,
    simp [wp] at h2,
    exact h2,
    simp [wp] at h2, simp [wp],
    exact h2,
    simp [wp] at h2, simp [wp],
    apply h1_ih,
    exact h2,
    simp [wp] at h2,
    exact h2,
    simp [wp] at h2, simp [wp],
    exact h2,
  end

end wpsound