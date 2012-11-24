module WPSound where

open import Data.Bool
open import Data.Product
open import Data.Sum
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
             → wp s N X W θ
             → p ⊢ θ , s ▷ θ' , s'
             -------------------------
             → wp s' N X W θ'

wp-pres-step (inj₁ (ptrue , ntrue)) (e-assert ptrue') = ntrue
wp-pres-step (inj₂ (pfalse , wtrue)) (e-assert ptrue) with pfalse ptrue
... | ()
wp-pres-step (inj₁ pfalse) (e-assume ptrue) with pfalse ptrue
... | ()
wp-pres-step (inj₂ ntrue) (e-assume ptrue) = ntrue
wp-pres-step wptrue e-assign = wptrue
wp-pres-step ( wp1 , wp2 ) e-choice1 = wp1
wp-pres-step ( wp1 , wp2 ) e-choice2 = wp2
wp-pres-step wptrue (e-seq1 s1eval) = wp-pres-step wptrue s1eval
wp-pres-step wptrue e-seq2 = wptrue
wp-pres-step wptrue e-seq3 = wptrue
wp-pres-step wptrue (e-catch1 s1eval) = wp-pres-step wptrue s1eval
wp-pres-step wptrue e-catch2 = wptrue
wp-pres-step wptrue e-catch3 = wptrue

wp-pres : ∀ { p θ s θ' s' N X W }
        → wp s N X W θ
        → p ⊢ θ , s ▷* θ' , s'
        -------------------------
        → wp s' N X W θ'

wp-pres wptrue (e-base eval') = wp-pres-step wptrue eval'
wp-pres wptrue (e-ind first rest) = wp-pres (wp-pres-step wptrue first) rest
