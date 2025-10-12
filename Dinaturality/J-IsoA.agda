{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  One of the two directions to show that J and J⁻¹ (defined in
  `Dinaturality/J.agda` and `Dinaturality/J-Inverse.agda`) are isomorphisms.
  The other direction is defined in `Dinaturality/J-IsoB.agda`.
-}
module Dinaturality.J-IsoA where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)
open Functor using (F₀; ₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

open import Dinaturality.Product renaming (π₁ to π₁ᵈ)

private
  variable
    o ℓ e : Level

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

open import Dinaturality.J using (J)
open import Dinaturality.J-Inverse using (J⁻¹)

{-
  One of the two directions of the isomorphism.
  This follows from functoriality, and corresponds to the computation rule for
  directed equality elimination.
-}
J⨟J⁻¹-iso : ∀ {o} {A Γ : Category o ℓ ℓ}
       (let module A = Category A)
       {Φ P : Functor (op (A ⊗ Γ) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
       (h : DinaturalTransformation {C = A ⊗ Γ} Φ P)
     → J⁻¹ {A = A} {Γ = Γ} {Φ = Φ} {P = P} (J {A = A} {Γ = Γ} {Φ = Φ} {P = P} h) ≃ᵈ h
J⨟J⁻¹-iso {A = A} {Γ = Γ} {Φ = Φ} {P = P} h eq = P.identity (Func.cong (h.α _) (Φ.identity eq))
  where
    module h = DinaturalTransformation h
    module Φ = Functor Φ
    module P = Functor P
