{-# OPTIONS --safe --without-K #-}

{-
  Rules for products and terminals for dinaturals.
-}

module Dinaturality.Product where

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
    Φ P Q : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)

  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})

pattern * = lift Data.Unit.tt

-- The unique dinatural from any dipresheaf into the dipresheaf constant in the terminal of Set.

! : DinaturalTransformation Φ (const SetT.⊤)
! = dtHelper record
  { α = λ X → record
    { to = λ _ → *
    ; cong = λ _ → *
    }
  ; commute = λ f _ → *
  }

!-unique : {α : DinaturalTransformation Φ (const SetT.⊤)}
         → α ≃ᵈ !
!-unique {α = α} = λ _ → *

-- Product of dinaturals.

productd : DinaturalTransformation Φ P
         → DinaturalTransformation Φ Q
         → DinaturalTransformation Φ (SetA.-×- ∘F (P ※ Q))
productd α β = dtHelper record
  { α = λ X → < α.α X , β.α X >ₛ
  ; commute = λ _ eq → α.commute _ eq , β.commute _ eq
  } where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β

-- Postcomposition with projections.

π₁-cutʳ : DinaturalTransformation Φ (SetA.-×- ∘F (P ※ Q))
        → DinaturalTransformation Φ P
π₁-cutʳ α = dtHelper record
  { α = λ X → α.α X [⨾] proj₁ₛ
  ; commute = λ z → proj₁ ⟨∘⟩ α.commute z
  } where module α = DinaturalTransformation α

π₂-cutʳ : DinaturalTransformation Φ (SetA.-×- ∘F (P ※ Q))
        → DinaturalTransformation Φ Q
π₂-cutʳ α = dtHelper record
  { α = λ X → α.α X [⨾] proj₂ₛ
  ; commute = λ z → proj₂ ⟨∘⟩ α.commute z
  } where module α = DinaturalTransformation α

-- The projections in terms of the rules above.

open import Dinaturality.Identity using (idDT)

π₁ : DinaturalTransformation (SetA.-×- ∘F (P ※ Q)) P
π₁ {P = P} {Q = Q} =
  π₁-cutʳ
    {Φ = SetA.-×- ∘F (P ※ Q)}
    {P = P}
    {Q = Q}
    (idDT {F = SetA.-×- ∘F (P ※ Q)})

π₂ : DinaturalTransformation (SetA.-×- ∘F (P ※ Q)) Q
π₂ {P = P} {Q = Q} =
  π₂-cutʳ
    {Φ = SetA.-×- ∘F (P ※ Q)}
    {P = P}
    {Q = Q}
    (idDT {F = SetA.-×- ∘F (P ※ Q)})

-- Isomorphisms.

iso-proj₁ : {α : DinaturalTransformation Φ P}
          → {β : DinaturalTransformation Φ Q}
          → π₁-cutʳ {P = P} {Q = Q} (productd {P = P} {Q = Q} α β) ≃ᵈ α
iso-proj₁ {α = α} = Func.cong (DinaturalTransformation.α α _)

iso-proj₂ : {α : DinaturalTransformation Φ P}
          → {β : DinaturalTransformation Φ Q}
          → π₂-cutʳ {P = P} {Q = Q} (productd {P = P} {Q = Q} α β) ≃ᵈ β
iso-proj₂ {β = β} = Func.cong (DinaturalTransformation.α β _)

iso-eta : {p : DinaturalTransformation Φ (SetA.-×- ∘F (P ※ Q))}
        → productd {P = P} {Q = Q} (π₁-cutʳ {P = P} {Q = Q} p) (π₂-cutʳ {P = P} {Q = Q} p) ≃ᵈ p
iso-eta {p = p} = Func.cong (DinaturalTransformation.α p _)
