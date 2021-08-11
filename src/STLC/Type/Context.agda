module STLC.Type.Context where

open import STLC.Type as Type using (Type)
open Type.Substitution using () renaming (_⊙_ to _⊙τ_; _/_ to _/τ_; wk to wk-τ)


open import Data.Nat using (ℕ; _+_)

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Substitution

open import Data.Vec using (Vec; []; _∷_; map; lookup)
open import Data.Vec.Properties
  using (map-∘; map-cong; lookup-map)


open import Relation.Binary.PropositionalEquality as Eq
  using (refl; _≡_; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)



-- --------------------------------------------------------------------
-- Typing Contexts
-- --------------------------------------------------------------------
-- A typing context Γ is the mapping from free term variables to 
-- types. A context Γ m n maps m term variables to tyhpes containing 
-- n type variables. 

Ctxt : ℕ -> ℕ -> Set
Ctxt m n = Vec (Type n) m

-- --------------------------------------------------------------------

module Substitution where

  infixl 8 _/_ _/Var_

  -- Type substitutions lifted to typing contexts
  _/_ : ∀ { m n p } -> Ctxt m n -> Sub Type n p -> Ctxt m p
  Γ / ρ = Γ ⊙τ ρ

  -- Weakening of typing contexts
  weaken : ∀ { m n } -> Ctxt m n -> Ctxt m (1 + n)
  weaken Γ = map Type.Substitution.weaken Γ

  -- Term variable substitution
  _/Var_ : ∀  { m n p } -> Sub Fin m n -> Ctxt n p -> Ctxt m p
  θ /Var Γ = map (lookup Γ) θ

module Lemmas where
  open Substitution

  private module Lemmas-τ = Type.Lemmas

  -- /Var and / commute 
  /Var-/-comm : ∀ { m n p q } (Γ : Ctxt p n) (θ : Sub Fin m p) (ρ : Sub Type n q) 
    -> (θ /Var Γ) / ρ ≡ θ /Var (Γ / ρ)
  /Var-/-comm Γ θ ρ = 
    begin
      (θ /Var Γ) / ρ
    ≡⟨ sym (map-∘ _ _ θ) ⟩
      map (λ x -> (lookup Γ x) /τ ρ) θ
    ≡⟨ map-cong (λ x → sym (Lemmas-τ.lookup-⊙ x {ρ₁ = Γ})) θ  ⟩
      map (λ x -> lookup (Γ / ρ) x) θ
    ∎

  -- /Var and weaken commute
  /Var-weaken-comm : ∀  { m n p } (θ : Sub Fin m p) (Γ : Ctxt p n) 
    -> weaken (θ /Var Γ) ≡ θ /Var (weaken Γ)
  /Var-weaken-comm θ Γ = 
    begin
      weaken (θ /Var Γ)
    ≡⟨ Lemmas-τ.map-weaken ⟩
      (θ /Var Γ) / wk-τ
    ≡⟨ /Var-/-comm Γ θ wk-τ ⟩
      θ /Var (Γ / wk-τ)
    ≡⟨ sym (cong (λ Γ -> θ /Var Γ) (Lemmas-τ.map-weaken {ρ = Γ})) ⟩
      θ /Var (weaken Γ)
    ∎

  -- /Var and lookup commute
  /Var-lookup-comm : ∀  { m n p } (x : Fin m) (θ : Sub Fin m p) (Γ : Ctxt p n) 
    -> lookup (θ /Var Γ) x ≡ lookup Γ (lookup θ x)
  /Var-lookup-comm x θ Γ = 
    begin
      lookup (θ /Var Γ) x 
    ≡⟨⟩
      lookup (map (lookup Γ) θ) x
    ≡⟨ lookup-map x (lookup Γ) θ ⟩
      lookup Γ (lookup θ x)
    ∎

  /Var-∷-comm : ∀ { m n p } (τ : Type n) (θ : Sub Fin m p) (Γ : Ctxt p n)
    -> τ ∷ (θ /Var Γ) ≡ (θ VarSubst.↑) /Var (τ ∷ Γ)
  /Var-∷-comm τ [] Γ = refl
  /Var-∷-comm τ (x ∷ θ) Γ = 
    begin
      τ ∷ ((x ∷ θ) /Var Γ)
    ≡⟨⟩
      τ ∷ (lookup Γ x) ∷ (θ /Var Γ)
    ≡⟨ cong (λ Γ' -> τ ∷ (lookup Γ x) ∷ Γ') lemma ⟩
      τ ∷ (lookup Γ x) ∷ map (lookup (τ ∷ Γ)) (map suc θ)
    ≡⟨⟩
      map (lookup (τ ∷ Γ)) (zero ∷ suc x ∷ map suc θ)
    ≡⟨⟩
      ((x ∷ θ) VarSubst.↑) /Var (τ ∷ Γ)
    ∎
    where 
      lemma = 
        begin 
          θ /Var Γ
        ≡⟨⟩
          map (lookup Γ) θ
        ≡⟨⟩
          map (λ x -> lookup (τ ∷ Γ) (suc x)) θ
        ≡⟨ map-∘ _ _ θ ⟩
          map (lookup (τ ∷ Γ)) (map suc θ)
        ∎
  
  -- invariant on renaming of id
  /Var-id-inv : ∀ { m n } (Γ : Ctxt m n) -> Γ ≡ (VarSubst.id /Var Γ)
  
  /Var-id-inv [] = refl
  /Var-id-inv (τ ∷ Γ) = 
    begin
      τ ∷ Γ
    ≡⟨ cong (λ Γ -> τ ∷ Γ) (/Var-id-inv Γ) ⟩
      τ ∷ (VarSubst.id /Var Γ)
    ≡⟨ /Var-∷-comm τ VarSubst.id Γ ⟩
      (VarSubst.id VarSubst.↑) /Var (τ ∷ Γ)
    ≡⟨⟩
      VarSubst.id /Var (τ ∷ Γ)
    ∎

  -- invariant on adding additional types, also known as the weakening lemma
  /Var-wk-inv : ∀ { m n } (Γ : Ctxt m n) -> (τ : Type n) -> Γ ≡ (VarSubst.wk /Var (τ ∷ Γ))
  /Var-wk-inv Γ τ = 
    begin
      Γ
    ≡⟨ /Var-id-inv Γ ⟩
      VarSubst.id /Var Γ
    ≡⟨ map-∘ _ _ VarSubst.id ⟩
      VarSubst.wk /Var (τ ∷ Γ)
    ∎