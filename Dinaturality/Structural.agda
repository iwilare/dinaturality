{-# OPTIONS --safe --without-K #-}

{-
  Rules for products and terminals for dinaturals.
-}

module Dinaturality.Structural where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.Object.Terminal using (Terminal)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition renaming (function to _[⨾]_)
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
    Φ Q P R : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})

pattern * = lift Data.Unit.tt

-- Weakening, i.e., precomposition with projections.

π₁-cutˡ : DinaturalTransformation Φ P
        → DinaturalTransformation (SetA.-×- ∘F (Φ ※ Q)) P
π₁-cutˡ α = dtHelper record
    { α = λ X → proj₁ₛ [⨾] α.α X
    ; commute = λ z → α.commute z ⟨∘⟩ proj₁
    } where module α = DinaturalTransformation α

π₂-cutˡ : DinaturalTransformation Φ P
        → DinaturalTransformation (SetA.-×- ∘F (Q ※ Φ)) P
π₂-cutˡ α = dtHelper record
    { α = λ X → proj₂ₛ [⨾] α.α X
    ; commute = λ z → α.commute z ⟨∘⟩ proj₂
    } where module α = DinaturalTransformation α

-- (Propositional) contraction.

Δ-cutˡ : DinaturalTransformation (SetA.-×- ∘F (Q ※ (SetA.-×- ∘F (Q ※ Φ)))) P
       → DinaturalTransformation (SetA.-×- ∘F (Q ※ Φ)) P
Δ-cutˡ α = dtHelper record
  { α = λ X → < proj₁ₛ , < proj₁ₛ , proj₂ₛ >ₛ >ₛ [⨾] α.α X
  ; commute = λ z → α.commute z ⟨∘⟩ λ { (a , b) → (a , a , b) }
  } where module α = DinaturalTransformation α

-- Swapping.

swap-cut : DinaturalTransformation (SetA.-×- ∘F (Q ※ (SetA.-×- ∘F (R ※ Φ)))) P
         → DinaturalTransformation (SetA.-×- ∘F (R ※ (SetA.-×- ∘F (Q ※ Φ)))) P
swap-cut α = dtHelper record
  { α = λ X → < proj₂ₛ [⨾] proj₁ₛ , < proj₁ₛ , proj₂ₛ [⨾] proj₂ₛ >ₛ >ₛ [⨾] α.α X
  ; commute = λ z → α.commute z ⟨∘⟩ λ { (a , b , c) → (b , a , c) }
  } where module α = DinaturalTransformation α
