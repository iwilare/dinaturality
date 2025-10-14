{-# OPTIONS --safe --without-K #-}

{-
  Given a dinatural transformation α : F(x,y,¬x,¬y) → G(x,y,¬x,¬y), we show that this
  restricts to a dinatural transformation Δ : F(x,¬x,x,¬x) → G(x,¬x,x,¬x), where naturality in both variables
  is collapsed to a single variable. This is a special case of the reindexing operation
  given in (Dinaturality/Reindexing) for F = Swap. The case of having a natural as input
  is obtained by selecting F and G to be mute in their ctr variant variables
  (but still have signature F, G : Cᵒᵖ ⊗ C → D).
-}

module Dinaturality.DinaturalCollapse where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
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
    A B C Γ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

private
  variable
    F G H I J K L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

-- This map is derivable in terms of reindexing (Dinaturality/Reindexing) for F = Swap,
-- but we define it here explicitly for a cleaner statement.
Δ : DinaturalTransformation {C = A ⊗ op A} F G
  → DinaturalTransformation {C = A} (F ∘F (idF ※ Swap)) (G ∘F (idF ※ Swap))
Δ {A = A} {F = F} {G = G} α = dtHelper record
  { α = λ X → α.α (X , X)
  ; commute = λ { {X} {Y} f eq → let open RS (G.F₀ ((X , Y) , Y , X)) in
      begin    G.₁ ((A.id , f) , f , A.id)
               $ α.α (X , X)
               $ F.₁ ((f , A.id) , A.id , f)
               $ _  ≈˘⟨ [ G ]-merge (A.id-0 , A.id-1) (A.id-0 , A.id-0) (Func.cong (α.α _) ([ F ]-merge (A.id-0 , A.id-0) (A.id-0 , A.id-1) FS.refl)) ⟩
                G.₁ ((A.id , f) , A.id , A.id)
               $ G.₁ ((A.id , A.id) , f , A.id)
               $ α.α (X , X)
               $ F.₁ ((f , A.id) , A.id , A.id)
               $ F.₁ ((A.id , A.id) , A.id , f)
               $ _ ≈⟨ Func.cong (G.₁ _) (α.commute (f , A.id) (Func.cong (F.₁ _) eq)) ⟩
               G.₁ ((A.id , f) , A.id , A.id)
                $ G.₁ ((f , A.id) , A.id , A.id)
                $ α.α (Y , X)
                $ F.₁ ((A.id , A.id) , f , A.id)
                $ F.₁ ((A.id , A.id) , A.id , f)
                $ _ ≈⟨ [ G ]-resp-square (((A.id-swap , A.id-swap) , A.refl , A.refl)) (Func.cong (α.α _) ([ F ]-resp-square ((A.refl , A.refl) , A.id-swap , A.id-swap) FS.refl)) ⟩
               G.₁ ((f , A.id) , A.id , A.id)
                $ G.₁ ((A.id , f) , A.id , A.id)
                $ α.α (Y , X)
                $ F.₁ ((A.id , A.id) , A.id , f)
                $ F.₁ ((A.id , A.id) , f , A.id)
                $ _ ≈⟨ Func.cong (G.₁ _) (α.op-commute (A.id , f) FS.refl)  ⟩
               G.₁ ((f , A.id) , A.id , A.id)
                $ G.₁ ((A.id , A.id) , A.id , f)
                $ α.α (Y , Y)
                $ F.₁ ((A.id , f) , A.id , A.id)
                $ F.₁ ((A.id , A.id) , f , A.id)
                $ _ ≈⟨ [ G ]-merge (A.id-0 , A.id-0) (A.id-0 , A.id-1) (Func.cong (α.α _) ([ F ]-merge (A.id-0 , A.id-1) (A.id-0 , A.id-0) FS.refl)) ⟩
               G.₁ ((f , A.id) , A.id , f)
                $ α.α (Y , Y)
                $ F.₁ ((A.id , f) , f , A.id)
                $ _ ∎ }
  } where
  module F = Functor F
  module G = Functor G
  module α = DinaturalTransformation α
  module A = Reason A
  module FS {A} = Setoid (F₀ F A)
