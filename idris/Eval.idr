module Eval

import Expr
import Command

eapply : EvalContext -> Command -> Command
eapply ehole s          = s
eapply (eseq   E s2) s1 = Seq (eapply E s1) s2
eapply (ecatch E s2) s1 = Catch (eapply E s1) s2

data Eval : Program -> Store -> Command -> Store -> Command -> Type where

  {-
  e-context : forall {E s s' θ θ' p}
            → p ⊢ θ , s ▷ θ' , s'
            --------------------------------------------
            → p ⊢ θ , (eapply E s) ▷ θ' , (eapply E s')
  -}

  E_Assert  : {pr : Program} -> {t : Store} -> {p : Assertion}
           -> p t
            --------------------------------
           -> Eval pr t (Assert p) t Skip

  E_Assume  : {pr : Program} -> {t : Store} -> {p : Assertion}
           -> p t
            --------------------------------
           -> Eval pr t (Assume p) t Skip

  E_Assign  : {pr : Program} -> {t : Store} -> {x : Var} -> {e : Expr}
            --------------------------------------------
           -> Eval pr t (Assign x e) (extend t x (e t)) Skip

  E_Choice1 : {p : Program} -> {t : Store} -> {s : Command} -> {s' : Command}
            ---------------------------
            -> Eval p t (Choice s s') t s

  E_Choice2 : {p : Program} -> {t : Store} -> {s : Command} -> {s' : Command}
            ----------------------------
            -> Eval p t (Choice s s') t s'

  E_Seq1    : {p : Program} -> {t : Store} -> {t' : Store}
           -> {s1 : Command} -> {s1' : Command} -> {s2 : Command}
           -> Eval p t s1 t' s1'
            ---------------------------------------
           -> Eval p t (Seq s1 s2) t' (Seq s1' s2)

  E_Seq2    : {p : Program} -> {t : Store} -> {s' : Command}
            --------------------------------
           -> Eval p t (Seq Skip s') t s'

  E_Seq3    : {p : Program} -> {t : Store} -> {s : Command}
            ----------------------------------
           -> Eval p t (Seq Raise s) t Raise

  E_Catch1  : {p : Program} -> {t : Store} -> {t' : Store}
           -> {s1 : Command} -> {s1' : Command} -> {s2 : Command}
           -> Eval p t s1 t' s1'
            ---------------------------------------
           -> Eval p t (Catch s1 s2) t' (Catch s1' s2)

  E_Catch2  : {p : Program} -> {t : Store} -> {s : Command}
            ------------------------------
           -> Eval p t (Catch Raise s) t s

  E_Catch3  : {p : Program} -> {t : Store} -> {s : Command}
            ---------------------------------
           -> Eval p t (Catch Skip s) t Skip

  E_Loop    : {p : Program} -> {t : Store} -> {s : Command}
            -----------------------------------
           -> Eval p t (Loop s) t (Seq s (Loop s))

  -- e-call    :

data Evals : Program -> Store -> Command -> Store -> Command -> Type where

  E_Base    : {p : Program} -> {t : Store} -> {t' : Store}
           -> {s : Command} -> {s' : Command}
           -> Eval p t s t' s'
            -----------------------
           -> Evals p t s t' s'

  E_Ind     : {p : Program} -> {t : Store} -> {t' : Store} -> {t'' : Store}
           -> {s : Command} -> {s' : Command} -> {s'' : Command}
           -> Eval p t s t' s'
           -> Evals p t' s' t'' s''
            ---------------------------
           -> Evals p t s t'' s''
