module STLC.Type.Relation where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import STLC.Term
open import STLC.Type

open import STLC.Type.Context using (Ctxt)

open import Data.Vec using (_∷_; lookup)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality as Eq
  using (refl; _≡_; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


infix 4 _⊢_⦂_

data _⊢_⦂_ { m n } (Γ : Ctxt m n) : Term m -> Type n -> Set where

  ⊢# : ∀ { x : Fin m } 
    -- ---------------
    -> Γ ⊢ # x ⦂ lookup Γ x 

  ⊢ƛ : ∀  { t τ₁ τ₂ } 
    -> τ₁ ∷ Γ ⊢ t ⦂ τ₂
    -- -----------------
    -> Γ ⊢ ƛ t ⦂ τ₁ ⇒ τ₂

  ⊢_·_ : ∀ { t₁ t₂ τ₁ τ₂ }
    -> Γ ⊢ t₁ ⦂ τ₁ ⇒ τ₂
    -> Γ ⊢ t₂ ⦂ τ₁
    -- ------------------
    -> Γ ⊢ t₁ · t₂ ⦂ τ₂  

_⊬_⦂_ : ∀ { m n } -> Ctxt m n -> Term m -> Type n -> Set
Γ ⊬ t ⦂ τ = ¬ (Γ ⊢ t ⦂ τ)

module Lemmas₀ where

  ⊢-subst : ∀ { m n } { Γ₁ Γ₂ : Ctxt m n } { t₁ t₂ : Term m } { τ₁ τ₂ : Type n } 
    -> Γ₁ ≡ Γ₂ -> t₁ ≡ t₂ -> τ₁ ≡ τ₂ -> Γ₁ ⊢ t₁ ⦂ τ₁ -> Γ₂ ⊢ t₂ ⦂ τ₂
  ⊢-subst refl refl refl hyp = hyp

  ⊢-Γ-subst : ∀ { m n } { Γ₁ Γ₂ : Ctxt m n } { t : Term m } { τ : Type n }
    -> Γ₁ ≡ Γ₂ -> Γ₁ ⊢ t ⦂ τ -> Γ₂ ⊢ t ⦂ τ
  ⊢-Γ-subst ≡-Γ hyp = ⊢-subst ≡-Γ refl refl hyp

  ⊢-τ-subst : ∀ { m n } { Γ : Ctxt m n } { t : Term m } { τ₁ τ₂ : Type n }
    -> τ₁ ≡ τ₂ -> Γ ⊢ t ⦂ τ₁ -> Γ ⊢ t ⦂ τ₂
  ⊢-τ-subst ≡-τ hyp = ⊢-subst refl refl ≡-τ hyp
  
-- TODO: Substitutions on typing derivations
-- TODO: Equivalent for Value e.g. value ⦂ τ relation w/ some lemmas :)


