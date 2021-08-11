module STLC.Type where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas using (TermLemmas)

open import Data.Nat using (ℕ; _+_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
  using (Star; ε; _◅_)

open import Data.Vec using (Vec; []; _∷_; lookup)

open import Relation.Binary.PropositionalEquality as Eq
  using (refl; _≡_; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


-- --------------------------------------------------------------------
-- Types 
-- --------------------------------------------------------------------
-- Recall that STLC types are defined as:
--  τ ::= α | τ -> τ  
-- where α denotes a type variable. 

infix 9 `_ 
infixr 7 _⇒_ 

data Type (n : ℕ) : Set where
  `_ : Fin n -> Type n
  _⇒_ : Type n -> Type n -> Type n


-- --------------------------------------------------------------------

module Substitution where

  -- This sub module defines application of the subtitution
  module Application₀ { T : ℕ -> Set } ( l : Lift T Type ) where
    open Lift l hiding  (var)


    -- Application of substitution to type 
    infixl 8 _/_

    _/_ : ∀ { m n : ℕ } -> Type m -> Sub T m n -> Type n 
    ` x / ρ = lift (lookup ρ x) 
    (τ₁ ⇒ τ₂) / ρ = (τ₁ / ρ) ⇒ (τ₂ / ρ)

    open Application (record { _/_ = _/_ }) using (_/✶_)

    -- The application of sequences of substitutions is defined
    -- by (_/✶_). We use this to prove some generic lemmas on
    -- the lifting of sets

    ⇒-/✶-lift : ∀ k { m n τ₁ τ₂ } (ρs : Subs T m n) -> 
        (τ₁ ⇒ τ₂) /✶ ρs ↑✶ k ≡ (τ₁ /✶ ρs ↑✶ k) ⇒ (τ₂ /✶ ρs ↑✶ k)
    ⇒-/✶-lift k ε = refl
    ⇒-/✶-lift k (ρ ◅ ρs) = cong₂ _/_ (⇒-/✶-lift k ρs) refl 

  t = record
    {var = `_
    ; app = Application₀._/_
    }

  open TermSubst t public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ { n } → Type (1 + n) → Type n → Type n
  τ₁ [/ τ₂ ] = τ₁ / sub τ₂


module Lemmas where
  
  module Lemmas₀ { T₁ T₂ } { l₁ : Lift T₁ Type} { l₂ : Lift T₂ Type } where
    open Substitution

    open Lifted l₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
    open Lifted l₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)
    
    /✶-↑✶ : ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) 
      -> (∀ k x -> ` x /✶₁ ρs₁ ↑✶₁ k ≡ ` x /✶₂ ρs₂ ↑✶₂ k) 
      -> ∀ k τ -> τ /✶₁ ρs₁ ↑✶₁ k ≡ τ /✶₂ ρs₂ ↑✶₂ k
    /✶-↑✶ ρs₁ ρs₂ hyp k (` x) = hyp k x
    /✶-↑✶ ρs₁ ρs₂ hyp k (τ₁ ⇒ τ₂) = 
      begin
        (τ₁ ⇒ τ₂) /✶₁ ρs₁ ↑✶₁ k
      ≡⟨ Application₀.⇒-/✶-lift _ k ρs₁ ⟩
        (τ₁ /✶₁ ρs₁ ↑✶₁ k) ⇒ (τ₂ /✶₁ ρs₁ ↑✶₁ k)
      ≡⟨ cong₂ (_⇒_) (/✶-↑✶ ρs₁ ρs₂ hyp k τ₁) (/✶-↑✶ ρs₁ ρs₂ hyp k τ₂) ⟩
        (τ₁ /✶₂ ρs₂ ↑✶₂ k) ⇒ (τ₂ /✶₂ ρs₂ ↑✶₂ k)
      ≡⟨ sym (Application₀.⇒-/✶-lift _ k ρs₂) ⟩
        (τ₁ ⇒ τ₂) /✶₂ ρs₂ ↑✶₂ k
      ∎

  t : TermLemmas Type
  t = record
    { termSubst = Substitution.t 
    ; app-var = refl
    ; /✶-↑✶ = Lemmas₀./✶-↑✶
    }

  open TermLemmas t public hiding (var)





module Operators where

  infixr 7 _⇒ⁿ_

  -- n-ary function type
  _⇒ⁿ_ : ∀ { n k } -> Vec (Type n) k -> Type n -> Type n
  [] ⇒ⁿ τ = τ
  (τ ∷ τs) ⇒ⁿ σ = τ ⇒ (τs ⇒ⁿ σ)



