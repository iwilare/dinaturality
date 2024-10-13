{-# OPTIONS --safe --without-K #-}

{-
  Weakening of a dinatural transformation into a larger term context.
-}
module Dinaturality.Weakening where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open Functor using (F₀; ₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

weakening : ∀ {o ℓ} {A Γ : Category o ℓ ℓ}
    {F : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    {G : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
  → DinaturalTransformation F G
  → DinaturalTransformation {C = A ⊗ Γ} (F ∘F (πʳ ∘F πˡ ※ πʳ ∘F πʳ))
                                         (G ∘F (πʳ ∘F πˡ ※ πʳ ∘F πʳ))
weakening {A = A} {Γ = Γ} {F = F} {G = G} α = dtHelper record
  { α = λ { (A , X) → α.α X }
  ; commute = λ { (f1 , f2) e → α.commute f2 e }
  } where
  module α = DinaturalTransformation α
  module Γ = Reason Γ
  module F = Functor F
  module G = Functor G
  module FS {A} = Setoid (F₀ F A)
  module GS {A} = Setoid (F₀ G A)
  open module A = Reason A
