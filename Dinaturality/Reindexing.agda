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

-- Reindexing a dinatural with a difunctor F.
reindexing : ∀ {o} {Γ Δ : Category o ℓ e}
    {Φ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    {P : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    (F : Functor (op Δ ⊗ Δ) Γ)
  → DinaturalTransformation Φ P
  → DinaturalTransformation (Φ ∘F ((Functor.op F ∘F Swap) ※ F)) (P ∘F ((Functor.op F ∘F Swap) ※ F))
reindexing {Γ = Γ} {Δ = Δ} {Φ = Φ} {P = P} F α = dtHelper (record
  { α = λ X → record { to = λ p → α.α (F.₀ (X , X)) $ p ; cong = Func.cong (α.α (F.₀ (X , X))) }
  ; commute = λ { {X} {Y} f {x} {y} eq →
    let open RS (P.₀ (F.₀ (Y , X) , F.₀ (X , Y))) in begin
      P.₁ (F.₁ (f , Δ.id) , F.₁ (Δ.id , f)) $ α.α (F.₀ (X , X)) $ Φ.₁ (F.₁ (Δ.id , f) , F.₁ (f , Δ.id)) $ x
        ≈⟨ [ P ]-decompose₁ (Func.cong (α.α _) ([ Φ ]-decompose₁ eq)) ⟩
      P.₁ (F.₁ (f , Δ.id) , Γ.id) $ P.₁ (Γ.id , F.₁ (Δ.id , f)) $ α.α (F.₀ (X , X)) $ Φ.₁ (F.₁ (Δ.id , f) , Γ.id) $ Φ.₁ (Γ.id , F.₁ (f , Δ.id)) $ y
        ≈⟨ Func.cong (P.₁ _) (α.commute (F.₁ (Δ.id , f)) ΦS.refl) ⟩
      P.₁ (F.₁ (f , Δ.id) , Γ.id) $ P.₁ (F.₁ (Δ.id , f) , Γ.id) $ α.α (F.₀ (X , Y)) $ Φ.₁ (Γ.id , F.₁ (Δ.id , f)) $ Φ.₁ (Γ.id , F.₁ (f , Δ.id)) $ y
        ≈⟨ [ P ]-resp-square ([ F ]-commute , Γ.refl) (Func.cong (α.α _) ([ Φ ]-resp-square (Γ.refl , [ F ]-commute) ΦS.refl)) ⟩
      P.₁ (F.₁ (Δ.id , f) , Γ.id) $ P.₁ (F.₁ (f , Δ.id) , Γ.id) $ α.α (F.₀ (X , Y)) $ Φ.₁ (Γ.id , F.₁ (f , Δ.id)) $ Φ.₁ (Γ.id , F.₁ (Δ.id , f)) $ y
        ≈⟨ Func.cong (P.₁ _) (α.op-commute (F.₁ (f , Δ.id)) ΦS.refl) ⟩
      P.₁ (F.₁ (Δ.id , f) , Γ.id) $ P.₁ (Γ.id , F.₁ (f , Δ.id)) $ α.α (F.F₀ (Y , Y)) $ Φ.₁ (F.₁ (f , Δ.id) , Γ.id) $ Φ.₁ (Γ.id , F.₁ (Δ.id , f)) $ y
        ≈⟨ [ P ]-merge Γ.id-0 Γ.id-0 (Func.cong (α.α (F.F₀ (Y , Y))) ([ Φ ]-merge Γ.id-0 Γ.id-0 ΦS.refl)) ⟩
      P.₁ (F.₁ (Δ.id , f) , F.₁ (f , Δ.id)) $ α.α (F.₀ (Y , Y)) $ Φ.₁ (F.₁ (f , Δ.id) , F.₁ (Δ.id , f)) $ y ∎
    }
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module Δ = Reason Δ
    module F = Functor F
    module Φ = Functor Φ
    module P = Functor P
    module ΦS {A} = Setoid (F₀ Φ A)

-- Special case of reindexing combined with weakening.
reindexing+weakening : ∀ {o} {A Γ : Category o ℓ ℓ}
    {Φ : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
    {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
    (F : Functor (op Γ ⊗ Γ) A)
  → DinaturalTransformation Φ P
  → DinaturalTransformation (Φ ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ))
                            (P ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ))
reindexing+weakening {A = A} {Γ = Γ} {Φ = Φ} {P = P} F α = dtHelper (record
  { α = λ X → record { to = λ p → α.α (_ , X) $ p ; cong = Func.cong (α.α (F₀ F (X , X) , X)) }
  ; commute = λ { {X} {Y} f {x} {y} eq →
    let open RS (F₀ P ((F₀ F (Y , X) , X) , F₀ F (X , Y) , Y)) in
      begin   P.₁ ((F.₁ (f , Γ.id) , Γ.id) , F.₁ (Γ.id , f) , f)
            $ α.α _
            $ Φ.₁ ((F.₁ (Γ.id , f) , f) , F.₁ (f , Γ.id) , Γ.id)
            $ x
              ≈˘⟨ [ P ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) (Func.cong (α.α _) ([ Φ ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) ΦS.refl)) ⟩
              P.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ P.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ α.α _
            $ Φ.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ Φ.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ x ≈⟨ Func.cong (P.₁ _) (α.commute (F.₁ (Γ.id , f) , f) ΦS.refl) ⟩
              P.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ P.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ α.α _
            $ Φ.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ Φ.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ x ≈⟨ [ P ]-resp-square (([ F ]-commute , Γ.id-swap) , A.refl , Γ.refl)
                  (Func.cong (α.α _)
                  ([ Φ ]-resp-square ((A.refl , Γ.refl) , [ F ]-commute , Γ.id-swap) eq)) ⟩
              P.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ P.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ α.α _
            $ Φ.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ Φ.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ≈⟨ Func.cong (P.₁ _) (α.op-commute (F.F₁ (f , Γ.id) , Γ.id) ΦS.refl) ⟩
              P.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ P.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ α.α _
            $ Φ.₁ ((F.₁ (f , Γ.id)  , Γ.id) , id , Γ.id)
            $ Φ.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ≈⟨ [ P ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) (Func.cong (α.α _) ([ Φ ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) ΦS.refl)) ⟩
              P.₁ ((F.₁ (Γ.id , f) , f) , F.₁ (f , Γ.id) , Γ.id)
            $ α.α _
            $ Φ.₁ ((F.₁ (f , Γ.id) , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ∎ }
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module Φ = Functor Φ
    module ΦS {X} = Setoid (F₀ Φ X)
    module P = Functor P
    module F = Functor F
    open module A = Reason A
