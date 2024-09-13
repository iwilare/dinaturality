module Dinaturality.Delta where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Categories.Object.Terminal using (Terminal)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong₂; trans; cong; sym)
open import Relation.Binary.Construct.Closure.Equivalence using (isEquivalence; EqClosure; setoid; return; join; map; gmap; fold; gfold)

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

F-swap : Functor (A ⊗ B ⊗ C) (B ⊗ A ⊗ C)
F-swap = assocˡ _ _ _ ∘F (Swap ⁂ idF) ∘F assocʳ _ _ _

F-reorder : Functor (op A ⊗ A ⊗ op B ⊗ C) (op (A ⊗ B) ⊗ A ⊗ C)
F-reorder = assocʳ _ _ _ ∘F (idF ⁂ F-swap)

private
  variable
    F G H I J K L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt

-- derivable in terms of reindexing for F = Swap, given here for a cleaner statement
Δ :
    DinaturalTransformation {C = A ⊗ op A} F G
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
