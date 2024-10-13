{-# OPTIONS --safe --without-K #-}

{-
  We define the functor [[Γᵒᵖ × Γ,Δ]ᵒᵖ x [Γᵒᵖ × Γ,Δ],Set] sending two difunctors
  to the set of dinatural transformations between them. Note that the functoriality here
  follows from the fact that we use functor categories where morphisms are *naturals*, for which
  the compositionality of dinaturals follows.

  This definition is crucial to express the *naturality* of the isomorphisms provided as rules,
  since it is naturality with respect to (compositions of other functors with) this functor.
  We will use this functor in `Dinaturality/NaturalityExample.agda`.
-}

module Dinaturality.DinaturalsFunctor where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry; opF⇐; opF⇒)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cocartesian)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC; Setoids-Cocomplete)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper; ≃-setoid; _<∘_; _∘>_) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

open import Dinaturality.Identity

import Reason

private
  variable
    o ℓ e : Level
    o′ ℓ′ e′ : Level
    A B C Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

-- The (di)functor sending difunctors into the set of dinaturals between them.
-- We use here composition of dinatural with naturals in the morphism part.
Dinats : ∀ {Γ : Category o ℓ e} {Δ : Category o′ ℓ′ e′}
       → Functor (op (Functors (op Γ ⊗ Γ) Δ) ⊗ Functors (op Γ ⊗ Γ) Δ)
                 (Setoids (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ e′))
Dinats {Γ = Γ} {Δ = Δ} = record
  { F₀ = λ (F , G) → ≃-setoid {F = F} {G = G}
  ; F₁ = λ { (α , β) → record
    { to = λ x → β <∘ (x ∘> α)
    ; cong = λ x → Δ.skip (Δ.rw x)
    } }
  ; identity = λ eq → Δ.id-0 Δ.∙ Δ.id-1 Δ.∙ eq
  ; homomorphism = λ eq → Δ.assoc Δ.∙ Δ.skip (Δ.skip (Δ.rw eq) Δ.∙ Δ.sym-assoc-3)
  ; F-resp-≈ = λ { (eq₁ , eq₂) eq → eq₂ ⟩∘⟨ eq ⟩∘⟨ eq₁ }
  } where
  module Γ = Reason Γ
  module Δ = Reason Δ
  open Δ.Chain
