{-# OPTIONS --safe --without-K #-}

{-
  Reflexivity of directed equality.
-}

module Dinaturality.Refl where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.Object.Terminal using (Terminal)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open Functor using (F₀; ₁; homomorphism; F-resp-≈)
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
    Φ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})

pattern * = lift Data.Unit.tt

-- Directed equality is reflexive, precisely because of identities in hom-sets.

homRefl : DinaturalTransformation Φ Hom[ A ][-,-]
homRefl {A = A} = dtHelper record
  { α = λ X → record
    { to = λ { _ → A.id }
    ; cong = λ { _ → A.refl }
    }
  ; commute = λ { {X} {Y} f {_} {_} _ → A.id-swap-2 }
  } where module A = Reason A

-- Same as homRefl, but using terms (i.e., difunctors).

homRefl-term : ∀ {o} {A : Category o ℓ ℓ}
             → (F : Functor (op Γ ⊗ Γ) A)
             → DinaturalTransformation Φ (Hom[ A ][-,-] ∘F (Functor.op F ∘F Swap ※ F))
homRefl-term {Γ = Γ} {A = A} F  = dtHelper record
      { α = λ { e → record
        { to = λ x → id
        ; cong = λ _ → Equiv.refl
        } }
      ; commute = λ { {X} {Y} g {w} {q} p →
        begin F.₁ (Γ.id , g) ∘ id ∘ F.₁ (g , Γ.id) ≈⟨ skip identityˡ ⟩
              F.₁ (Γ.id , g) ∘ F.₁ (g , Γ.id) ≈⟨ [ F ]-commute ⟩
              F.₁ (g , Γ.id) ∘ F.₁ (Γ.id , g) ≈˘⟨ skip identityˡ ⟩
              F.₁ (g , Γ.id) ∘ id ∘ F.₁ (Γ.id , g) ∎ }
      } where
  module Γ = Reason Γ
  module F = Functor F
  open Reason A
  open Chain
