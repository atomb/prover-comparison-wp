inductive Var : Type
  | Var : Nat -> Var

inductive Value : Type
  | const : Nat -> Value

inductive Store : Type
  | empty : Store
  | extend : Var -> Value -> Store -> Store

def Expr := Store -> Value

def Pred := Store -> Prop

def andp (p : Pred) (q : Pred) (s : Store) :=
  p s /\ q s

def orp (p : Pred) (q : Pred) (s : Store)  :=
  p s \/ q s

def notp (p : Pred) (s : Store) :=
  p s -> False

def subst (x : Var) (e : Expr) (q : Pred) (s : Store) :=
  q (Store.extend x (e s) s)

inductive Command : Type
  | skip : Command
  | assert : Pred -> Command
  | assume : Pred -> Command
  | assign : Var -> Expr -> Command
  | seq : Command -> Command -> Command
  | choice : Command -> Command -> Command
  | eraise : Command
  | ecatch : Command -> Command -> Command

open Command

def wp : Command -> Pred -> Pred -> Pred -> Pred
  | assert p,     n, x, w => orp (andp p n) (andp (notp p) w)
  | assume p,     n, x, w => orp (notp p) n
  | assign y e,   n, x, w => subst y e n
  | choice c1 c2, n, x, w => andp (wp c1 n x w) (wp c2 n x w)
  | seq c1 c2,    n, x, w => wp c1 (wp c2 n x w) x w
  | skip,         n, x, w => n
  | eraise,       n, x, w => x
  | ecatch c1 c2, n, x, w => wp c1 n (wp c2 n x w) w

inductive step : Store -> Command -> Store -> Command -> Type
  | e_assert:
    ∀ {t : Store} {p : Pred},
    p t ->
    -------------------------------------------
    step t (assert p) t skip

  | e_assume:
    ∀ {t : Store} {p : Pred},
    p t ->
    -------------------------------------------
    step t (assume p) t skip

  | e_assign:
    ∀ {t x e},
    -------------------------------------------
    step t (assign x e) (Store.extend x (e t) t) skip

  | e_choice1:
    ∀ {t s1 s2},
    -------------------------------------------
    step t (choice s1 s2) t s1

  | e_choice2:
    ∀ {t s1 s2},
    -------------------------------------------
    step t (choice s1 s2) t s2

  | e_seq1:
    ∀ {t t' s1 s1' s2},
    step t s1 t' s1' ->
    -------------------------------------------
    step t (seq s1 s2) t' (seq s1' s2)

  | e_seq2:
    ∀ {t s2},
    -------------------------------------------
    step t (seq skip s2) t s2

  | e_seq3:
    ∀ {t s2},
    -------------------------------------------
    step t (seq eraise s2) t eraise

  | e_catch1:
    ∀ {t t' s1 s1' s2},
    step t s1 t' s1' ->
    -------------------------------------------
    step t (ecatch s1 s2) t' (ecatch s1' s2)

  | e_catch2:
    ∀ {t s2},
   -------------------------------------------
   step t (ecatch eraise s2) t s2

  | e_catch3:
    ∀ {t s2},
    -------------------------------------------
    step t (ecatch skip s2) t skip

open step

theorem wp_pres_step
  {t s t' s' N X W}
  (h_step : step t s t' s')
  (h_wp : wp s N X W t) :
  ----------------------
  wp s' N X W t' :=
    by induction h_step generalizing N X W with
    | e_assert p =>
        cases h_wp with
          | inl p_and_n => { cases p_and_n; assumption }
          | inr negp_and_w => { cases negp_and_w; contradiction }
    | e_assume p =>
        cases h_wp with
          | inl negp => contradiction
          | inr n => assumption
    | e_assign => assumption
    | e_choice1 => { cases h_wp; assumption }
    | e_choice2 => { cases h_wp; assumption }
    | e_seq1 ih_step ih_wp => { apply ih_wp; assumption }
    | e_seq2 => assumption
    | e_seq3 => assumption
    | e_catch1 ih_step ih_wp => { apply ih_wp; assumption }
    | e_catch2 => assumption
    | e_catch3 => assumption