module STLC.Term where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Nat using (ℕ; _+_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
  using (Star; ε; _◅_)

open import Data.Vec using (Vec; []; _∷_; lookup)

open import Relation.Binary.PropositionalEquality
  using (refl; _≡_; cong₂)

-- --------------------------------------------------------------------
-- Untyped terms and values
-- --------------------------------------------------------------------

infix 7 _·_

data Term (n : ℕ) : Set where
  # : (x : Fin n) -> Term n
  ƛ : Term (1 + n) -> Term n
  _·_ : Term n -> Term n -> Term n
  
data Value {n : ℕ} : Term n -> Set where
  ƛ :  
    ∀ { t }
    -- -----------
    -> Value (ƛ t)
  
-- --------------------------------------------------------------------

module Substitution where

  -- This sub module defines application of the subtitution
  -- TODO: Rename for consistency
  module SubstApplication { T : ℕ -> Set } ( l : Lift T Term ) where
    open Lift l hiding  (var)

    -- Application of substitution to term 
    infixl 8 _/_

    _/_ : ∀ { m n : ℕ } -> Term m -> Sub T m n -> Term n 
    # x / ρ = lift (lookup ρ x) 
    (ƛ t) / ρ = ƛ (t / ρ ↑)
    (t₁ · t₂) / ρ = (t₁ / ρ) · (t₂ / ρ)

    open Application (record { _/_ = _/_ }) using (_/✶_)


  open TermSubst (record { var = #; app = SubstApplication._/_ }) public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable term substitutions
  _[/_] : ∀ { n } → Term (1 + n) → Term n → Term n
  t₁ [/ t₂ ] = t₁ / sub t₂


-- --------------------------------------------------------------------

-- TODO: Add additional operators
-- TODO: Add constants w/ delta-rules








