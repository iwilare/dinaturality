

module Dinaturality.Failure.ComposeReflLeftStrong where

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

composeReflLeftStrong : ∀ {o ℓ} {A : Category o ℓ ℓ}
      → (F : Functor (op A ⊗ A) (Setoids ℓ ℓ))
      → StrongDinaturalTransformation Hom[ A ][-,-] F
      → StrongDinaturalTransformation (const SetT.⊤) F
composeReflLeftStrong {A = A} F α = record
  { α = λ X → record
    { to = λ { * → α.α X $ A.id }
    ; cong = λ { * → FS.refl }
    }
  ; commute = λ { {W} {X} {Y} f {px} {py} x e →
      α.commute {W} {X} {Y} f
        {px = record { to = λ Y → A.id ; cong = λ _ → A.refl } }
        {py = record { to = λ Y → A.id ; cong = λ _ → A.refl }}
        (λ _ → A.id-swap-2) e
    }
  } where
    module A = Reason A
    module F = Functor F
    module FS {A} = Setoid (F₀ F A)
    module α = StrongDinaturalTransformation α

composeReflLeftStrong⁻¹ : ∀ {o ℓ} {A : Category o ℓ ℓ}
      → (F : Functor (op A ⊗ A) (Setoids ℓ ℓ))
      → StrongDinaturalTransformation (const SetT.⊤) F
      → StrongDinaturalTransformation Hom[ A ][-,-] F
composeReflLeftStrong⁻¹ {A = A} F α = record
  { α = λ X → record
    { to = λ { f → α.α X $ * }
    ; cong = λ { e → FS.refl }
    }
  ; commute = λ { {W} {X} {Y} f {px} {py} x e →
      α.commute  {W} {X} {Y} f
          {px = record { to = λ _ → * ; cong = λ _ → * } }
          {py = record { to = λ _ → * ; cong = λ _ → * }}
          (λ _ → *) e
    }
  } where
    module A = Reason A
    module F = Functor F
    module FS {A} = Setoid (F₀ F A)
    module α = StrongDinaturalTransformation α

iso1 : ∀ {o ℓ} {A : Category o ℓ ℓ}
      → (F : Functor (op A ⊗ A) (Setoids ℓ ℓ))
      → (α : StrongDinaturalTransformation (const SetT.⊤) F)
      → composeReflLeftStrong F (composeReflLeftStrong⁻¹ F α) ≃ˢ α
iso1 F α X {*} {*} * = Setoid.refl (F₀ F (X , X))

iso2 : ∀ {o ℓ} {A : Category o ℓ ℓ}
      → (F : Functor (op A ⊗ A) (Setoids ℓ ℓ))
      → (α : StrongDinaturalTransformation Hom[ A ][-,-] F)
      → composeReflLeftStrong⁻¹ F (composeReflLeftStrong F α) ≃ˢ α
iso2 {A = A} F α X {e} {e′} eq = let open RS (F₀ F (X , X)) in
    begin α.α X $ id ≈˘⟨ F.identity FS.refl ⟩
          F.₁ (id , id) $ α.α X $ id
            ≈⟨ α.commute {X} {X} {F.₀ (X , X)} id
                    {px = record { to = λ r → id ; cong = {!   !} }}
                    {py = record { to = λ r → e′ ; cong = {!   !} }}
                    {!   !}
                    {!   !}
               --α.commute {X} {X} {F.₀ (X , X)} {!   !}
               -- {px = record { to = λ x → {!   !} ; cong = λ x → {!  !} }}
               -- {py = record { to = λ x → {!   !} ; cong = λ x → {!   !} }}
               -- (λ e → skip (rw {!  eq !})) {!   !}
              ⟩
          F.₁ (id , id) $ α.α X $ e′ ≈⟨ F.identity FS.refl ⟩
          α.α X $ e′ ∎
  where
    module α = StrongDinaturalTransformation α
    module FS {A} = Setoid (F₀ F A)
    module F = Functor F
    open module A = Reason A
