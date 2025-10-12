{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  One of the two directions to show that J and J⁻¹ (defined in
  `Dinaturality/J.agda` and `Dinaturality/J-Inverse.agda`) are isomorphisms.
  The other direction is defined in `Dinaturality/J-IsoA.agda`.
-}
module Dinaturality.J-IsoB where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)

open Functor using (F₀; ₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

private
  variable
    o ℓ e : Level
    A B C : Category o ℓ e

open import Dinaturality.Product renaming (π₁ to π₁ᵈ)

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})

{-
  We define here some helpers with variables in order to
  improve readibility of the main rule.
-}

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

open import Dinaturality.J using (J)
open import Dinaturality.J-Inverse using (J⁻¹)

{-
  One of the two directions of the isomorphism.
  This follows from dinaturality.

  Technical note: we do not sure modules here and fully qualify as many identifiers
  as possible in order to make typechecking faster.
-}
J⁻¹⨟J-iso : ∀ {o} {A Γ : Category o ℓ ℓ}
       (let module A = Category A)
       {Φ P : Functor (op (A ⊗ Γ) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
       (h : DinaturalTransformation {C = A.op ⊗ A ⊗ Γ}
        (SetA.-×- ∘F ((Hom[ A ][-,-] ∘F (v1 ∘F pos ※ v2 ∘F pos))
                  ※ (Φ ∘F ((v2 ∘F neg ※ v3 ∘F neg) ※ v1 ∘F neg ※ v3 ∘F pos))))
        (P ∘F ((v1 ∘F pos ※ v3 ∘F neg) ※ v2 ∘F pos ※ v3 ∘F pos)))
     → J {A = A} {Γ = Γ} {Φ = Φ} {P = P} (J⁻¹ {A = A} {Γ = Γ} {Φ = Φ} {P = P} h) ≃ᵈ h
J⁻¹⨟J-iso {A = A} {Γ = Γ} {Φ = Φ} {P = P} h {a , B , X} {x1 , x2} {y1 , y2} (eq1 , eq2) =
  let open RS (F₀ P ((a , X) , B , X))
      module A = Reason A in
      begin Functor.F₁ P ((x1 , Category.id Γ) , A.id , Category.id Γ) $ DinaturalTransformation.α h (B , B , X) $ (A.id , Functor.F₁ Φ ((A.id , Category.id Γ) , x1 , Category.id Γ) $ x2)
              ≈⟨ Func.cong (Functor.F₁ P _) (Func.cong (DinaturalTransformation.α h _) ((A.sym-id-0 A.∙ A.sym-id-0) , Setoid.refl (F₀ Φ ((B , X) , B , X)))) ⟩
            Functor.F₁ P ((x1 , Category.id Γ) , A.id , Category.id Γ) $ DinaturalTransformation.α h (B , B , X) $ (A.id A.∘ A.id A.∘ A.id , Functor.F₁ Φ ((A.id , Category.id Γ) , x1 , Category.id Γ) $ x2)
              ≈⟨ DinaturalTransformation.commute h (x1 , A.id  , Category.id Γ) (A.refl , (Setoid.refl (F₀ Φ ((B , X) , a , X)))) ⟩
            Functor.F₁ P ((A.id , Category.id Γ) , A.id , Category.id Γ) $ DinaturalTransformation.α h (a , B , X) $ (A.id A.∘ A.id A.∘ x1 , Functor.F₁ Φ ((A.id , Category.id Γ) , A.id , Category.id Γ) $ x2)
              ≈⟨ Functor.identity P (Func.cong (DinaturalTransformation.α h (a , B , X)) ((A.id-0 A.∙ A.id-0 A.∙ eq1) , Functor.identity Φ eq2)) ⟩
            DinaturalTransformation.α h (a , B , X) $ (y1 , y2) ∎
