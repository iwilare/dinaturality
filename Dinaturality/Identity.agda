{-# OPTIONS --safe --without-K #-}

{-
  The identity dinatural transformation.

  Dinaturality follows from (bi)functoriality.
-}

module Dinaturality.Identity where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
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
    Γ Δ : Category o ℓ e

idDT : ∀ {F : Functor (Product (op Γ) Γ) Δ} → DinaturalTransformation F F
idDT {Δ = Δ} {F = F} = dtHelper record
  { α = λ X → Category.id Δ
  ; commute = λ _ → Δ.idm-1 Δ.∙ [ F ]-commute Δ.∙ Δ.sym-idm-1
  } where
    module Δ = Reason Δ
