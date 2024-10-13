{-# OPTIONS --safe --without-K #-}

{-
  Reindexing a dinatural transformation with a difunctor F : Cᵒᵖ × C → D.
-}

module Dinaturality.Reindexing where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
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
    F G H I J K L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

-- Reindexing a dinatural with a difunctor F.
reindexing : ∀ {o} {A Γ Δ : Category o ℓ ℓ}
    {H : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    {H′ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    (F : Functor (op Δ ⊗ Δ) Γ)
  → DinaturalTransformation H H′
  → DinaturalTransformation (H ∘F ((Functor.op F ∘F Swap) ※ F)) (H′ ∘F ((Functor.op F ∘F Swap) ※ F))
reindexing {A = A} {Γ = Γ} {Δ = Δ} {H = H} {H′ = H′} F α = dtHelper (record
  { α = λ X → record { to = λ p → α.α (F.₀ (X , X)) $ p ; cong = Func.cong (α.α (F.₀ (X , X))) }
  ; commute = λ { {X} {Y} f {x} {y} eq →
    let open RS (H′.₀ (F.₀ (Y , X) , F.₀ (X , Y))) in begin
      H′.₁ (F.₁ (f , Δ.id) , F.₁ (Δ.id , f)) $ α.α (F.₀ (X , X)) $ H.₁ (F.₁ (Δ.id , f) , F.₁ (f , Δ.id)) $ x
        ≈⟨ [ H′ ]-decompose₁ (Func.cong (α.α _) ([ H ]-decompose₁ eq)) ⟩
      H′.₁ (F.₁ (f , Δ.id) , Γ.id) $ H′.₁ (Γ.id , F.₁ (Δ.id , f)) $ α.α (F.₀ (X , X)) $ H.₁ (F.₁ (Δ.id , f) , Γ.id) $ H.₁ (Γ.id , F.₁ (f , Δ.id)) $ y
        ≈⟨ Func.cong (H′.₁ _) (α.commute (F.₁ (Δ.id , f)) HS.refl) ⟩
      H′.₁ (F.₁ (f , Δ.id) , Γ.id) $ H′.₁ (F.₁ (Δ.id , f) , Γ.id) $ α.α (F.₀ (X , Y)) $ H.₁ (Γ.id , F.₁ (Δ.id , f)) $ H.₁ (Γ.id , F.₁ (f , Δ.id)) $ y
        ≈⟨ [ H′ ]-resp-square ([ F ]-commute , Γ.refl) (Func.cong (α.α _) ([ H ]-resp-square (Γ.refl , [ F ]-commute) HS.refl)) ⟩
      H′.₁ (F.₁ (Δ.id , f) , Γ.id) $ H′.₁ (F.₁ (f , Δ.id) , Γ.id) $ α.α (F.₀ (X , Y)) $ H.₁ (Γ.id , F.₁ (f , Δ.id)) $ H.₁ (Γ.id , F.₁ (Δ.id , f)) $ y
        ≈⟨ Func.cong (H′.₁ _) (α.op-commute (F.₁ (f , Δ.id)) HS.refl) ⟩
      H′.₁ (F.₁ (Δ.id , f) , Γ.id) $ H′.₁ (Γ.id , F.₁ (f , Δ.id)) $ α.α (F.F₀ (Y , Y)) $ H.₁ (F.₁ (f , Δ.id) , Γ.id) $ H.₁ (Γ.id , F.₁ (Δ.id , f)) $ y
        ≈⟨ [ H′ ]-merge Γ.id-0 Γ.id-0 (Func.cong (α.α (F.F₀ (Y , Y))) ([ H ]-merge Γ.id-0 Γ.id-0 HS.refl)) ⟩
      H′.₁ (F.₁ (Δ.id , f) , F.₁ (f , Δ.id)) $ α.α (F.₀ (Y , Y)) $ H.₁ (F.₁ (f , Δ.id) , F.₁ (Δ.id , f)) $ y ∎
    }
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module Δ = Reason Δ
    module F = Functor F
    module H = Functor H
    module H′ = Functor H′
    module HS {A} = Setoid (F₀ H A)
    module H′S {A} = Setoid (F₀ H′ A)
    open Reason A

-- Special case of reindexing combined with weakening.
reindexing+weakening : ∀ {o} {A Γ : Category o ℓ ℓ}
         {H : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
         {G : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
           (F : Functor (op Γ ⊗ Γ) A)
  → DinaturalTransformation H G
  → DinaturalTransformation (H ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ))
                            (G ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ))
reindexing+weakening {A = A} {Γ = Γ} {H = H} {G = G} F α = dtHelper (record
  { α = λ X → record { to = λ p → α.α (_ , X) $ p ; cong = Func.cong (α.α (F₀ F (X , X) , X)) }
  ; commute = λ { {X} {Y} f {x} {y} eq →
    let open RS (F₀ G ((F₀ F (Y , X) , X) , F₀ F (X , Y) , Y)) in
      begin   G.₁ ((F.₁ (f , Γ.id) , Γ.id) , F.₁ (Γ.id , f) , f)
            $ α.α _
            $ H.₁ ((F.₁ (Γ.id , f) , f) , F.₁ (f , Γ.id) , Γ.id)
            $ x
              ≈˘⟨ [ G ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) (Func.cong (α.α _) ([ H ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) HS.refl)) ⟩
              G.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ G.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ α.α _
            $ H.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ H.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ x ≈⟨ Func.cong (G.₁ _) (α.commute (F.₁ (Γ.id , f) , f) HS.refl) ⟩
              G.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ G.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ α.α _
            $ H.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ H.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ x ≈⟨ [ G ]-resp-square (([ F ]-commute , Γ.id-swap) , A.refl , Γ.refl)
                  (Func.cong (α.α _)
                  ([ H ]-resp-square ((A.refl , Γ.refl) , [ F ]-commute , Γ.id-swap) eq)) ⟩
              G.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ G.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ α.α _
            $ H.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ H.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ≈⟨ Func.cong (G.₁ _) (α.op-commute (F.F₁ (f , Γ.id) , Γ.id) HS.refl) ⟩
              G.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ G.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ α.α _
            $ H.₁ ((F.₁ (f , Γ.id)  , Γ.id) , id , Γ.id)
            $ H.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ≈⟨ [ G ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) (Func.cong (α.α _) ([ H ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) HS.refl)) ⟩
              G.₁ ((F.₁ (Γ.id , f) , f) , F.₁ (f , Γ.id) , Γ.id)
            $ α.α _
            $ H.₁ ((F.₁ (f , Γ.id) , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ∎ }
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module H = Functor H
    module GS {X} = Setoid (F₀ G X)
    module HS {X} = Setoid (F₀ H X)
    module G = Functor G
    module F = Functor F
    open module A = Reason A
