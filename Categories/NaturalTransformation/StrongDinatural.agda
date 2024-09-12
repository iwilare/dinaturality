{-# OPTIONS --without-K --safe #-}
module Categories.NaturalTransformation.StrongDinatural where

open import Level
open import Data.Product
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Categories.Category
open import Categories.NaturalTransformation as NT hiding (_∘ʳ_)
open import Categories.Functor
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Bifunctor
open import Categories.Category.Product
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

record BistrongDinaturalTransformation (F G : Bifunctor (Category.op C) C D) : Set (levelOfTerm F) where
  eta-equality
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  open D hiding (op)
  open Commutation D

  field
    α           : ∀ X → D [ F.F₀ (X , X) , G.F₀ (X , X) ]
    commute     : ∀ {X Y W} (f : C [ X , Y ])
                  {px : D [ W , F.F₀ (X , X) ]}
                  {py : D [ W , F.F₀ (Y , Y) ]} →
                [ W ⇒ F.F₀ (X , Y) ]⟨
                  px              ⇒⟨ F.F₀ (X , X) ⟩
                  F.F₁ (C.id , f)
                ≈ py              ⇒⟨ F.F₀ (Y , Y) ⟩
                  F.F₁ (f , C.id)
                ⟩
                → [ W ⇒ G.F₀ (X , Y) ]⟨
                  px              ⇒⟨ F.F₀ (X , X) ⟩
                  α X             ⇒⟨ G.F₀ (X , X) ⟩
                  G.F₁ (C.id , f)
                ≈ py              ⇒⟨ F.F₀ (Y , Y) ⟩
                  α Y             ⇒⟨ G.F₀ (Y , Y) ⟩
                  G.F₁ (f , C.id)
                ⟩
    cocommute   : ∀ {X Y W} (f : C [ X , Y ])
                  {ix : D [ G.F₀ (X , X) , W ]}
                  {iy : D [ G.F₀ (Y , Y) , W ]} →
                [ G.F₀ (Y , X) ⇒ W ]⟨
                  G.F₁ (f , C.id) ⇒⟨ G.F₀ (X , X) ⟩
                  ix
                ≈ G.F₁ (C.id , f) ⇒⟨ G.F₀ (Y , Y) ⟩
                  iy
                ⟩
                → [ F.F₀ (Y , X) ⇒ W ]⟨
                  F.F₁ (f , C.id) ⇒⟨ F.F₀ (X , X) ⟩
                  α X             ⇒⟨ G.F₀ (X , X) ⟩
                  ix
                ≈ F.F₁ (C.id , f) ⇒⟨ F.F₀ (Y , Y) ⟩
                  α Y             ⇒⟨ G.F₀ (Y , Y) ⟩
                  iy
                ⟩

record StrongDinaturalTransformation (F G : Bifunctor (Category.op C) C D) : Set (levelOfTerm F) where
  eta-equality
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  open D hiding (op)
  open Commutation D

  field
    α          : ∀ X → D [ F.F₀ (X , X) , G.F₀ (X , X) ]
    commute    : ∀ {X Y W} (f : C [ X , Y ])
                  {px : D [ W , F.F₀ (X , X) ]}
                  {py : D [ W , F.F₀ (Y , Y) ]} →
                [ W ⇒ F.F₀ (X , Y) ]⟨
                  px              ⇒⟨ F.F₀ (X , X) ⟩
                  F.F₁ (C.id , f)
                ≈ py              ⇒⟨ F.F₀ (Y , Y) ⟩
                  F.F₁ (f , C.id)
                ⟩
                → [ W ⇒ G.F₀ (X , Y) ]⟨
                  px              ⇒⟨ F.F₀ (X , X) ⟩
                  α X             ⇒⟨ G.F₀ (X , X) ⟩
                  G.F₁ (C.id , f)
                ≈ py              ⇒⟨ F.F₀ (Y , Y) ⟩
                  α Y             ⇒⟨ G.F₀ (Y , Y) ⟩
                  G.F₁ (f , C.id)
                ⟩

idˢ : ∀ {F : Bifunctor (Category.op C) C D} → StrongDinaturalTransformation F F
idˢ {C = C} {D = D} {F = F} = record
  { α = λ X → D.id
  ; commute = λ f {px} {py} eq → begin F.F₁ (C.id , f) ∘ D.id ∘ px ≈⟨ refl⟩∘⟨ identityˡ ⟩
                                   F.F₁ (C.id , f) ∘ px ≈⟨ eq ⟩
                                   F.F₁ (f , C.id) ∘ py ≈˘⟨ refl⟩∘⟨ identityˡ ⟩
                                   F.F₁ (f , C.id) ∘ D.id ∘ py ∎
  } where
    module C = Category C
    module D = Category D
    module F = Functor F
    open D
    open HomReasoning

_≃ˢ_ : ∀ {F G : Bifunctor (Category.op C) C D} → StrongDinaturalTransformation F G → StrongDinaturalTransformation F G → Set _
_≃ˢ_ {D = D} α β = ∀ X → α.α X ≈ β.α X
  where
    module α = StrongDinaturalTransformation α
    module β = StrongDinaturalTransformation β
    open Category D

_∘ˢ_ : ∀ {F G H : Bifunctor (Category.op C) C D} → StrongDinaturalTransformation G H → StrongDinaturalTransformation F G → StrongDinaturalTransformation F H
_∘ˢ_ {C = C} {D = D} {F = F} {G = G} {H = H} α β = record
  { α       = λ X → α.α X ∘ β.α X
  ; commute = λ f {px} {py} eq →
    begin H.F₁ (C.id , f) ∘ (α.α _ ∘ β.α _) ∘ px ≈⟨ refl⟩∘⟨ assoc ⟩
          H.F₁ (C.id , f) ∘ α.α _ ∘ β.α _ ∘ px ≈⟨ α.commute f (β.commute f eq) ⟩
          H.F₁ (f , C.id) ∘ α.α _ ∘ β.α _ ∘ py ≈˘⟨ refl⟩∘⟨ assoc ⟩
          H.F₁ (f , C.id) ∘ (α.α _ ∘ β.α _) ∘ py ∎
  } where
  module α = StrongDinaturalTransformation α
  module β = StrongDinaturalTransformation β
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G
  module H = Functor H
  open D
  open HomReasoning
