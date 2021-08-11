module STLC.Term.Reduction where

open import STLC.Term as Term
open Term.Substitution using () renaming (_[/_] to _[/t_])

open import Data.Nat using (ℕ; _+_)


open import Relation.Binary.Construct.Closure.ReflexiveTransitive 
  using (Star)


infix 4 _—→_ 

data _—→_ { n : ℕ } : Term n -> Term n -> Set where

  β-·₁ : ∀ { t₁ t₂ l : Term n } 
    -> t₁ —→ t₂
    -- ----------------
    -> t₁ · l —→ t₂ · l

  β-·₂ : ∀ { v t₁ t₂ : Term n }
    -> Value v 
    -> t₁ —→ t₂ 
    -- ----------------
    -> v · t₁ —→ v · t₂

  β-ƛ : ∀ { t : Term (1 + n) } {v : Term n }
    -> Value v
    -- --------------------
    -> (ƛ t) · v —→ (t [/t v ]) 


infix 2 _—↠_ 

_—↠_ : { n : ℕ } -> Term n -> Term n -> Set
_—↠_ = Star (_—→_)

