module WPSound where

open import Data.Bool
open import Function hiding (_$_)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

open import Command
open import Eval
open import Expr
open import WP
open import Assertion

wp-pres-step : ∀ { p θ s θ' s' N X W }
             → (wp s N X W θ)
             → (p ⊢ θ , s ▷ θ' , s')
             -------------------------
             → (wp s' N X W θ')

wp-pres-step {_} {θ} {assert P} {.θ} {skip} {N} {X} {W} wptrue (e-assert ptrue) =
  or-elim-2 {P} {N} {W} ptrue wptrue
wp-pres-step {_} {θ} {assume P} {.θ} {skip} {N} wptrue (e-assume ptrue) =
  or-elim-1 {P} {N} ptrue wptrue
wp-pres-step wptrue e-assign = wptrue
wp-pres-step {_} {θ} {s1 □ s2} {.θ} {.s1} {N} {X} {W} wptrue e-choice1 =
  and-eliml {wp s2 N X W} {wp s1 N X W} wptrue
wp-pres-step {_} {θ} {s1 □ s2} {.θ} {.s2} {N} {X} {W} wptrue e-choice2 =
  and-elimr {wp s1 N X W} {wp s2 N X W} wptrue
wp-pres-step wptrue (e-seq1 s1eval) = wp-pres-step wptrue s1eval
wp-pres-step wptrue e-seq2 = wptrue
wp-pres-step wptrue e-seq3 = wptrue
wp-pres-step wptrue (e-catch1 s1eval) = wp-pres-step wptrue s1eval
wp-pres-step wptrue e-catch2 = wptrue
wp-pres-step wptrue e-catch3 = wptrue

wp-pres : ∀ { p θ s θ' s' N X W }
        → (wp s N X W θ)
        → (p ⊢ θ , s ▷* θ' , s')
        -------------------------
        → (wp s' N X W θ')

wp-pres wptrue (e-base eval') = wp-pres-step wptrue eval'
wp-pres wptrue (e-ind first rest) =
  wp-pres (wp-pres-step wptrue first) rest
