module Dinaturality.GroupoidCompose where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid; SingletonSetoid-⊤)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.StrongDinatural using (StrongDinaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Categories.Object.Terminal using (Terminal)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition renaming (function to _∘ˢ_)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Groupoid using (IsGroupoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong₂; trans; cong; sym)
open import Relation.Binary.Construct.Closure.Equivalence using (isEquivalence; EqClosure; setoid; return; join; map; gmap; fold; gfold)

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

F-swap : Functor (A ⊗ B ⊗ C) (B ⊗ A ⊗ C)
F-swap = assocˡ _ _ _ ∘F (Swap ⁂ idF) ∘F assocʳ _ _ _

F-reorder : Functor (op A ⊗ A ⊗ op B ⊗ C) (op (A ⊗ B) ⊗ A ⊗ C)
F-reorder = assocʳ _ _ _ ∘F (idF ⁂ F-swap)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)

groupoid-dinaturals-compose : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → IsGroupoid A
  → DinaturalTransformation F G
  → DinaturalTransformation G H
  → DinaturalTransformation F H
groupoid-dinaturals-compose {A = A} {F = F} {G = G} {H = H} g α β = dtHelper record
  { α = λ X → α.α X ∘ˢ β.α X
  ; commute = λ { {X} {Y} f eq →
    let open RS (H.F₀ (X , Y)) in
      begin H.₁ (id , f) $ β.α X $ α.α X $ F.₁ (f , id) $ _
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α _) (GS.sym (GS.trans ([ G ]-merge g.iso.isoˡ A.id-0 GS.refl) (G.identity GS.refl)))) ⟩
            H.₁ (id , f) $ β.α X $ G.₁ (f , id) $ G.₁ (f g.⁻¹ , id) $ α.α X $ F.₁ (f , id) $ _
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α _) (Func.cong (G.₁ _) (Func.cong (G.₁ _) (Func.cong (α.α _) (FS.sym (FS.trans ([ F ]-merge A.id-0 g.iso.isoˡ FS.refl) (F.identity FS.refl))))))) ⟩
            H.₁ (id , f) $ β.α X $ G.₁ (f , id) $ G.₁ (f g.⁻¹ , id) $ α.α X $ F.₁ (id , f g.⁻¹) $ F.₁ (id , f) $ F.₁ (f , id) $ _
              ≈⟨ β.commute f (α.op-commute (f g.⁻¹) FS.refl) ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (id , f) $ G.₁ (id , f g.⁻¹) $ α.α Y $ F.₁ (f g.⁻¹ , id) $ F.₁ (id , f) $ F.₁ (f , id) $ _
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α _) (Func.cong (G.₁ _) (Func.cong (G.₁ _) (Func.cong (α.α _) (Func.cong (F.₁ _) ([ F ]-commute FS.refl)))))) ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (id , f) $ G.₁ (id , f g.⁻¹) $ α.α Y $ F.₁ (f g.⁻¹ , id) $ F.₁ (f , id) $ F.₁ (id , f) $ _
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α _) (GS.trans ([ G ]-merge A.id-0 g.iso.isoʳ GS.refl) (G.identity GS.refl))) ⟩
            H.₁ (f , id) $ β.α Y $ α.α Y $ F.₁ (f g.⁻¹ , id) $ F.₁ (f , id) $ F.₁ (id , f) $ _
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α _) (Func.cong (α.α _) (FS.trans ([ F ]-merge g.iso.isoʳ A.id-0 FS.refl) (F.identity (Func.cong (F.₁ _) eq))))) ⟩
            H.₁ (f , id) $ β.α Y $ α.α Y $ F.₁ (id , f) $ _ ∎}
  } where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module G = Functor G
    module F = Functor F
    module H = Functor H
    module g = IsGroupoid g
    module GS {A} = Setoid (F₀ G A)
    module FS {A} = Setoid (F₀ F A)
    module HS {A} = Setoid (F₀ H A)
    open module A = Reason A
