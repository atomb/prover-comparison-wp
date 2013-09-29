module WPSound

import Command
import Eval
import Expr
import WP
import Assertion

wp_pres_step : {pr : Program}
            -> {t : Store} -> {s : Command}
            -> {t' : Store} -> {s' : Command}
            -> {n : Assertion} -> {x : Assertion} -> {w : Assertion}
            -> Eval pr t s t' s'
            -> wp s n x w t
             -------------------------
            -> wp s' n x w t'

wp_pres_step (E_Assert ptrue) pre =
  case pre of
    Left p => snd p
    Right p => FalseElim ((fst p) ptrue)
wp_pres_step (E_Assume ptrue) pre =
  case pre of
    Left p => FalseElim (p ptrue)
    Right p => p
wp_pres_step E_Assign pre = pre
wp_pres_step E_Choice1 pre = fst pre
wp_pres_step E_Choice2 pre = snd pre
-- wp_pres_step (E_Seq1 s1eval) = wp_pres_step s1eval -- TODO
wp_pres_step E_Seq2 pre = pre
wp_pres_step E_Seq3 pre = pre
-- wp_pres_step (E_Catch1 s1eval) = wp_pres_step s1eval -- TODO
wp_pres_step E_Catch2 pre = pre
wp_pres_step E_Catch3 pre = pre
-- wp_pres_step E_Loop = {!!} -- TODO

wp_pres : {pr : Program}
       -> {t : Store} -> {s : Command}
       -> {t' : Store} -> {s' : Command}
       -> {n : Assertion} -> {x : Assertion} -> {w : Assertion}
       -> Evals pr t s t' s'
       -> wp s n x w t
        -------------------------
       -> wp s' n x w t'

wp_pres (E_Base step) = wp_pres_step step
wp_pres (E_Ind step steps) = wp_pres steps . wp_pres_step step
