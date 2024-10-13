{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  We define the rules for exponentials and prove that they are isomorphisms.

  Naturality of this isomorphism is contained in `Dinaturality/NaturalityExample.agda`.
-}

module Dinaturality.Exponential where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cocartesian)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC; Setoids-Cocomplete)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

private
  variable
    o ℓ e : Level
    A B C Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

private
  variable
    F G H I J K L : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)
    F′ G′ H′ I′ J′ K′ L′ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})

-- Bidirectional rules for exponentials.
module _ {ℓ} {Γ : Category ℓ ℓ ℓ} where

  open import Categories.Category.Construction.Properties.Presheaves.CartesianClosed

  -- This extra op is necessary since we have presheaves and not copresheaves.
  open IsCartesianClosed (op (op Γ ⊗ Γ))

  module PCCC = CartesianClosed Presheaves-CartesianClosed
  module PC = Cartesian PCCC.cartesian
  module PBP = BinaryProducts PC.products

  -- We use this complicated formulation with the PBP module, containing the pointwise
  -- product of presheaves, in order to be able to later prove the naturality
  -- of the maps in `Dinaturality/ExponentialNatural.agda`, which needs to use this functor.
  -- The alternative, more direct, formulation would have been `SetA.-×- ∘F (F ※ G)`,
  -- postcomposing with the bifunctor taking the product of sets directly.
  lambda : {F G H : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
        → DinaturalTransformation (Functor.₀ PBP.-×- (F , G)) H
        → DinaturalTransformation G (Set.-⇨- ∘F (Functor.op F ∘F Swap ※ H))
  lambda {G = G} α = dtHelper record
    { α = λ X → record
      { to = λ a → record
        { to = λ b → α.α X $ (b , a)
        ; cong = λ x≈y → Func.cong (α.α X) (x≈y , Setoid.refl (F₀ G (X , X)))
        }
      ; cong = λ x₁≈y₁ x₂≈y₂ → Func.cong (α.α X) (x₂≈y₂ , x₁≈y₁)
      }
    ; commute = λ f x₁≈y₁ x₂≈y₂ → α.commute f (x₂≈y₂ , x₁≈y₁)
    } where module α = DinaturalTransformation α

  lambda⁻¹ : {F G H : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
          → DinaturalTransformation G (Set.-⇨- ∘F (Functor.op F ∘F Swap ※ H))
          → DinaturalTransformation (Functor.₀ PBP.-×- (F , G)) H
  lambda⁻¹ {G = G} α = dtHelper record
    { α = λ X → record
      { to = λ { (fxx , gxx) → (α.α X $ gxx) $ fxx }
      ; cong = λ { (eq1 , eq2) → Func.cong (α.α X) eq2 eq1  }
      }
    ; commute = λ { f (x₁≈y₁ , x₂≈y₂) → α.commute f x₂≈y₂ x₁≈y₁ }
    } where
      module α = DinaturalTransformation α

  -- The above maps are isomorphisms.

  lambda⁻¹⨟lambda-iso : {F G H : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
        →  (α : DinaturalTransformation G (Set.-⇨- ∘F (Functor.op F ∘F Swap ※ H)))
          → lambda {F = F} {G = G} {H = H} (lambda⁻¹ {F = F} {G = G} {H = H} α) ≃ᵈ α
  lambda⁻¹⨟lambda-iso α eq₁ eq₂ = Func.cong (DinaturalTransformation.α α _) eq₁ eq₂

  lambda⨟lambda⁻¹-iso : {F G H : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
        →  (α : DinaturalTransformation (Functor.₀ PBP.-×- (F , G)) H)
          → lambda⁻¹ {F = F} {G = G} {H = H} (lambda {F = F} {G = G} {H = H} α) ≃ᵈ α
  lambda⨟lambda⁻¹-iso α (eq₁ , eq₂) = Func.cong (DinaturalTransformation.α α _) (eq₁ , eq₂)

  -- Exponentials are functorial for dinaturals.
  ⇨-functor-dinat : ∀ {ℓ} {Γ : Category ℓ ℓ ℓ} {F G F′ G′ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    → DinaturalTransformation F′ F
    → DinaturalTransformation G G′
    → DinaturalTransformation (Set.-⇨- ∘F (Functor.op F ∘F Swap ※ G))
                              (Set.-⇨- ∘F (Functor.op F′ ∘F Swap ※ G′))
  ⇨-functor-dinat {F = F} {G = G} {F′ = F′} {G′ = G′} α β = dtHelper record
    { α = λ X → record
      { to = λ f → record
        { to = λ fxx → β.α X $ f $ α.α X $ fxx
        ; cong = λ x → Func.cong (β.α X) (Func.cong f (Func.cong (α.α X) x))
        }
      ; cong = λ fe eq → Func.cong (β.α X) (fe (Func.cong (α.α X) eq))
      }
    ; commute = λ f eq1 eq2 → β.commute f (eq1 (α.commute f eq2))
    } where
      module α = DinaturalTransformation α
      module β = DinaturalTransformation β
      module Γ = Reason Γ
      module G = Functor G
      module G′ = Functor G′
      module F = Functor F
      module F′ = Functor F′

  -- Naturality of this isomorphism is contained in `Dinaturality/NaturalityExample.agda`.
