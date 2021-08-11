module STLC.Properties.Determinism where

open import STLC.Term
open import STLC.Term.Reduction

open import Data.Nat using (ℕ; _+_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)


open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Relation.Binary.PropositionalEquality as Eq
  using (refl; _≡_; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


infix 4 _¬—→

_¬—→ : ∀ { n : ℕ } -> Term n -> Set 
t₁ ¬—→ = ¬ (∃[ t₂ ] (t₁ —→ t₂))

¬—→-value : ∀ { n : ℕ } { t : Term n } 
  -> Value t 
  -- --------
  -> t ¬—→
¬—→-value {_} {ƛ _} v = λ ()

—→-¬value : ∀ { n : ℕ } { t₁ t₂ : Term n } 
  -> t₁ —→ t₂
  -- ---------
  -> ¬ Value t₁
—→-¬value { _ } { _ } { t₂ } s v = ¬—→-value v (t₂ , s)

determinism : ∀ { n : ℕ } { t₁ t₂ t₃ : Term n } 
  -> t₁ —→ t₂
  -> t₁ —→ t₃
  -- --------
  -> t₂ ≡ t₃

determinism (β-·₁ s₁) (β-·₁ s₂) = cong₂ (_·_) (determinism s₁ s₂) refl
determinism (β-·₂ _ s₁) (β-·₂ _ s₂) =  cong₂ (_·_) refl (determinism s₁ s₂)
determinism (β-ƛ _) (β-ƛ _) = refl
determinism (β-·₁ s) (β-·₂ v _) = contradiction v (—→-¬value s)  
determinism (β-·₂ v _) (β-·₁ s) = contradiction v (—→-¬value s)  
determinism (β-·₂ _ s) (β-ƛ v) = contradiction v (—→-¬value s)  
determinism (β-ƛ v) (β-·₂ _ s) = contradiction v (—→-¬value s)  

