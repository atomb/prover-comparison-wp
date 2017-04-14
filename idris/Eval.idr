module Eval

import Assertion
import Command
import Expr

%access public export

eapply : EvalContext -> Command -> Command
eapply Ehole s          = s
eapply (ESeq   e s2) s1 = Seq (eapply e s1) s2
eapply (ECatch e s2) s1 = Catch (eapply e s1) s2

data Eval : Program -> Store -> Command -> Store -> Command -> Type where

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
           -> Eval pr t (Assign x e) (Extend t x (e t)) Skip

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

  {-
  E_Loop    : {p : Program} -> {t : Store} -> {s : Command}
            -----------------------------------
           -> Eval p t (Loop s) t (Seq s (Loop s))
  -}

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
