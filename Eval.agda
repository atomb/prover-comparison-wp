module Eval where

open import Data.Bool
open import Data.Nat
open import Relation.Binary.Core

open import Expr
open import Command
open import Pred

{-
data EvalExpr : Store → Expr → Value → Set where
  e-var : forall {θ n x v} → Lookup x θ v → EvalExpr θ (evar n x) v
  e-val : forall {θ v} → EvalExpr θ (val v) v
  e-add : forall {θ e₁ e₂ v₁ v₂} →
          EvalExpr θ e₁ v₁ →
          EvalExpr θ e₂ v₂ →
          EvalExpr θ (binop add e₁ e₂) (addv v₁ v₂)
  e-inc : forall {θ e v} →
          EvalExpr θ e v →
          EvalExpr θ (unop inc e) (incv v)

data EvalPred : Store → Pred → Bool → Set where
  p-bool : forall {θ b} → EvalPred θ (pbool b) b
  p-and  : forall {θ p₁ p₂ b₁ b₂} →
           EvalPred θ p₁ b₁ →
           EvalPred θ p₂ b₂ →
           EvalPred θ (pand p₁ p₁) (b₁ ∧ b₂)
  p-or   : forall {θ p₁ p₂ b₁ b₂} →
           EvalPred θ p₁ b₁ →
           EvalPred θ p₂ b₂ →
           EvalPred θ (por p₁ p₁) (b₁ ∨ b₂)
  p-not  : forall {θ p b} → EvalPred θ p b → EvalPred θ (pnot p) (not b)
  p-eq   : forall {θ e₁ e₂ v₁ v₂} →
           EvalExpr θ e₁ v₂ →
           EvalExpr θ e₂ v₂ →
           v₁ ≡ v₂ → EvalPred θ (peq e₁ e₂) true
  p-neq  : forall {θ e₁ e₂ v₁ v₂} →
           EvalExpr θ e₁ v₂ →
           EvalExpr θ e₂ v₂ →
           v₁ ≢ v₂ → EvalPred θ (peq e₁ e₂) false
-}

eapply : EvalContext → Command → Command
eapply ehole s          = s
eapply (eseq   E s₂) s₁ = (eapply E s₁) $ s₂
--eapply (ecatch E s₂) s₁ = (eapply E s₁) ! s₂

data _⊢_,_▷_,_ : Program → Store → Command → Store → Command → Set where
  {-
  e-context : forall {p θ s θ' s' E} →
              (p ⊢ θ , s ▷ θ' , s') →
              (p ⊢ θ , (eapply E s) ▷ θ' , (eapply E s'))
  -}

  e-assert  : ∀ {p θ P}
            → (P θ ≡ true)
            ----------------------------------
            → (p ⊢ θ , (assert P) ▷ θ , skip)

  e-assume  : ∀ {p θ P}
            → (P θ ≡ true)
            ----------------------------------
            → (p ⊢ θ , (assume P) ▷ θ , skip)

  e-assign  : ∀ {p θ x e}
            ----------------------------------------------
            → (p ⊢ θ , x ≔ e ▷ (extend θ x (e θ)) , skip)

  e-choice1 : ∀ {p θ s s'}
            -------------------------------
            → ( p ⊢ θ , (s □ s') ▷ θ , s )

  e-choice2 : ∀ {p θ s s'}
            ---------------------------------
            → ( p ⊢ θ , (s □ s') ▷ θ , s' )

  e-seq1    : ∀ {p θ s'}
            ----------------------------------
            → (p ⊢ θ , (skip  $ s') ▷ θ , s')

  --e-seq2    : forall {p θ s}     → (p ⊢ θ , (raise $ s) ▷ θ , raise)
  --e-catch1  : forall {p θ s}     → (p ⊢ θ , (raise ! s) ▷ θ , s)
  --e-catch2  : forall {p θ s}     → (p ⊢ θ , (skip  ! s) ▷ θ , skip)
  -- e-loop    : forall {p θ s}     → (p ⊢ θ , (s *)       ▷ θ , (s $ (s *)))
  -- e-call    :
