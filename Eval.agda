module Eval where

open import Data.Bool
open import Data.Nat
open import Relation.Binary.Core

open import Expr
open import Command

eapply : EvalContext → Command → Command
eapply ehole s          = s
eapply (eseq   E s₂) s₁ = (eapply E s₁) $ s₂
eapply (ecatch E s₂) s₁ = (eapply E s₁) ! s₂

data _⊢_,_▷_,_ : Program → Store → Command → Store → Command → Set' where

  {-
  e-context : forall {E s s' θ θ' p}
            → p ⊢ θ , s ▷ θ' , s'
            --------------------------------------------
            → p ⊢ θ , (eapply E s) ▷ θ' , (eapply E s')
  -}

  e-assert  : ∀ {p θ P}
            → P θ
            --------------------------------
            → p ⊢ θ , (assert P) ▷ θ , skip

  e-assume  : ∀ {p θ P}
            → P θ
            --------------------------------
            → p ⊢ θ , (assume P) ▷ θ , skip

  e-assign  : ∀ {p θ x e}
            --------------------------------------------
            → p ⊢ θ , x ≔ e ▷ (extend θ x (e θ)) , skip

  e-choice1 : ∀ {p θ s s'}
            ---------------------------
            → p ⊢ θ , (s □ s') ▷ θ , s

  e-choice2 : ∀ {p θ s s'}
            ----------------------------
            → p ⊢ θ , (s □ s') ▷ θ , s'

  e-seq1    : ∀ {p θ θ' s1 s1' s2}
            → p ⊢ θ , s1 ▷ θ' , s1'
            ---------------------------------------
            → p ⊢ θ , (s1  $ s2) ▷ θ' , (s1' $ s2)

  e-seq2    : ∀ {p θ s'}
            --------------------------------
            → p ⊢ θ , (skip  $ s') ▷ θ , s'

  e-seq3    : ∀ {p θ s}
            ----------------------------------
            → p ⊢ θ , (raise $ s) ▷ θ , raise

  e-catch1  : ∀ {p θ θ' s1 s1' s2}
            → p ⊢ θ , s1 ▷ θ' , s1'
            ---------------------------------------
            → p ⊢ θ , (s1  ! s2) ▷ θ' , (s1' ! s2)

  e-catch2  : ∀ {p θ s}
            ------------------------------
            → p ⊢ θ , (raise ! s) ▷ θ , s

  e-catch3  : ∀ {p θ s}
            ---------------------------------
            → p ⊢ θ , (skip  ! s) ▷ θ , skip

  -- e-loop    : ∀ {p θ s}     → (p ⊢ θ , (s *)       ▷ θ , (s $ (s *)))
  -- e-call    :

data _⊢_,_▷*_,_ : Program → Store → Command → Store → Command → Set' where

  e-base    : ∀ {p θ θ' s s'}
            → p ⊢ θ , s ▷ θ' , s'
            -----------------------
            → p ⊢ θ , s ▷* θ' , s'

  e-ind     : ∀ {p θ θ' θ'' s s' s''}
            → p ⊢ θ , s ▷ θ' , s'
            → p ⊢ θ' , s' ▷* θ'' , s''
            ---------------------------
            → p ⊢ θ , s ▷* θ'' , s''
            
