{-# OPTIONS --lossy-unification #-}

module Dinaturality.J-IsoB where

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

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

open import Dinaturality.Product renaming (π₁ to π₁ᵈ)

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
    F G H I K L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt


-- modifier on a single variable
pos = πʳ
neg = πˡ

-- series of variables
positives = πʳ
negatives = πˡ

-- variables out of 2-tuple

va = πˡ
vb = πʳ

-- variables out of 3-tuple

v1 = πˡ

v2 : Functor (Product A (Product B C)) B
v2 = πˡ ∘F πʳ

v3 : Functor (Product A (Product B C)) C
v3 = πʳ ∘F πʳ

------------------------------------------------------------------------------------------

open import Dinaturality.J using (J; J⁻¹)

iso2 : ∀ {o} {A C : Category o ℓ ℓ}
       (let module A = Category A)
       {Γ P : Functor (op (A ⊗ C) ⊗ (A ⊗ C)) (Setoids ℓ ℓ)}
       (h : DinaturalTransformation {C = A.op ⊗ A ⊗ C}
        (SetA.-×- ∘F ((Hom[ A ][-,-] ∘F (v1 ∘F pos ※ v2 ∘F pos))
                  ※ (Γ ∘F ((v2 ∘F neg ※ v3 ∘F neg) ※ v1 ∘F neg ※ v3 ∘F pos))))
        (P ∘F ((v1 ∘F pos ※ v3 ∘F neg) ※ v2 ∘F pos ※ v3 ∘F pos)))
     → J {A = A} {C = C} {Γ = Γ} {P = P} (J⁻¹ {A = A} {C = C} {Γ = Γ} {P = P} h) ≃ᵈ h
iso2 {A = A} {C = C} {Γ = Γ} {P = P} h {a , B , X} {x1 , x2} {y1 , y2} (eq1 , eq2) =
  let open RS (F₀ P ((a , X) , B , X))
      module A = Reason A in
      begin F₁ P ((x1 , Category.id C) , A.id , Category.id C) $ DinaturalTransformation.α h (B , B , X) $ (A.id , F₁ Γ ((A.id , Category.id C) , x1 , Category.id C) $ x2)
              ≈⟨ Func.cong (F₁ P _) (Func.cong (DinaturalTransformation.α h _) ((A.sym-id-0 A.∙ A.sym-id-0) , Setoid.refl (F₀ Γ ((B , X) , B , X)))) ⟩
            F₁ P ((x1 , Category.id C) , A.id , Category.id C) $ DinaturalTransformation.α h (B , B , X) $ (A.id A.∘ A.id A.∘ A.id , F₁ Γ ((A.id , Category.id C) , x1 , Category.id C) $ x2)
              ≈⟨ DinaturalTransformation.commute h (x1 , A.id  , Category.id C) (A.refl , (Setoid.refl (F₀ Γ ((B , X) , a , X)))) ⟩
            F₁ P ((A.id , Category.id C) , A.id , Category.id C) $ DinaturalTransformation.α h (a , B , X) $ (A.id A.∘ A.id A.∘ x1 , F₁ Γ ((A.id , Category.id C) , A.id , Category.id C) $ x2)
              ≈⟨ Functor.identity P (Func.cong (DinaturalTransformation.α h (a , B , X)) ((A.id-0 A.∙ A.id-0 A.∙ eq1) , Functor.identity Γ eq2)) ⟩
            DinaturalTransformation.α h (a , B , X) $ (y1 , y2) ∎
