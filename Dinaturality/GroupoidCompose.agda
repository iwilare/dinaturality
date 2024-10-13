{-# OPTIONS --safe --without-K #-}

{-
  When C is a groupoid, dinatural transformations which have C as domain always compose.
-}

module Dinaturality.GroupoidCompose where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Construct.Composition renaming (function to _∘ˢ_)

open import Categories.Category.Groupoid using (IsGroupoid)

open Functor using (F₀; ₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

private
  variable
    o ℓ e : Level
    A B C Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

groupoid-dinaturals-compose : ∀ {o} {A B : Category o ℓ ℓ} {F G H : Functor (Product (op A) A) B}
  → IsGroupoid A
  → DinaturalTransformation F G
  → DinaturalTransformation G H
  → DinaturalTransformation F H
groupoid-dinaturals-compose {A = A} {B = B} {F = F} {G = G} {H = H} g α β = dtHelper record
  { α = λ X → β.α X ∘ α.α X
  ; commute = λ { {X} {Y} f →
    let open Chain in
      begin H.₁ (A.id , f) ∘ (β.α X ∘ α.α X) ∘ F.₁ (f , A.id)
              ≈⟨ skip (assoc ∙ intro-2 ([ H ]-merge g.iso.isoˡ A.id-0 ∙ H.identity)) ⟩
            H.₁ (A.id , f) ∘ H.₁ (f , A.id) ∘ H.₁ (f g.⁻¹ , A.id) ∘ β.α X ∘ α.α X ∘ F.₁ (f , A.id)
              ≈⟨ skip-4 (intro-2 ([ G ]-merge A.id-0 g.iso.isoˡ ∙ G.identity)) ⟩
            H.₁ (A.id , f) ∘ H.₁ (f , A.id) ∘ H.₁ (f g.⁻¹ , A.id) ∘ β.α X ∘ G.₁ (A.id , f g.⁻¹) ∘ G.₁ (A.id , f) ∘ α.α X ∘ F.₁ (f , A.id)
              ≈⟨ skip-2 (sym-assoc ∙ rw-2 (β.op-commute (f g.⁻¹)) ∙ assoc ∙ skip-3 (α.commute f)) ⟩
            H.₁ (A.id , f) ∘ H.₁ (f , A.id) ∘ H.₁ (A.id , f g.⁻¹) ∘ β.α Y ∘ G.₁ (f g.⁻¹ , A.id) ∘ G.₁ (f , A.id) ∘ α.α Y ∘ F.₁ (A.id , f)
              ≈⟨ rw-2 [ H ]-commute ⟩
            H.₁ (f , A.id) ∘ H.₁ (A.id , f) ∘ H.₁ (A.id , f g.⁻¹) ∘ β.α Y ∘ G.₁ (f g.⁻¹ , A.id) ∘ G.₁ (f , A.id) ∘ α.α Y ∘ F.₁ (A.id , f)
              ≈⟨ skip (cancel-2 ([ H ]-merge A.id-0 g.iso.isoʳ ∙ H.identity) ∙ (skip (cancel-2 ([ G ]-merge g.iso.isoʳ A.id-0 ∙ G.identity)) ∙ sym-assoc)) ⟩
            H.₁ (f , A.id) ∘ (β.α Y ∘ α.α Y) ∘ F.₁ (A.id , f) ∎
            }
  } where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module G = Functor G
    module F = Functor F
    module H = Functor H
    module g = IsGroupoid g
    module A = Reason A
    open module B = Reason B
