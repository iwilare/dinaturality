module Dinaturality.Refl where

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
open import Categories.NaturalTransformation.StrongDinatural using (StrongDinaturalTransformation; _≃ˢ_)
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
  variable
    F G H I J K L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt

homRefl : ∀ {o ℓ} {A : Category o ℓ ℓ}
      → DinaturalTransformation (const SetT.⊤) Hom[ A ][-,-]
homRefl {A = A} = dtHelper record
  { α = λ X → record
    { to = λ { * → A.id }
    ; cong = λ { * → A.refl }
    }
  ; commute = λ { {X} {Y} f {*} {*} * → A.id-swap-2 }
  } where module A = Reason A

homRefl-term : ∀ {o} {A : Category o ℓ ℓ}
      → (F : Functor (op Γ ⊗ Γ) A)
      → DinaturalTransformation H (Hom[ A ][-,-] ∘F (Functor.op F ∘F Swap ※ F))
homRefl-term {Γ = Γ}  {H = H}{A = A} F  = dtHelper record
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
  module H = Functor H
  open Reason A
  open Chain
