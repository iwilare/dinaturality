{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  Main rule for the inverse of directed equality introduction.

  The isomorphism is split into the module `Dinaturality/J-Iso.agda`
  because of Agda often running out of memory.
-}
module Dinaturality.J-Inverse where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
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

open import Dinaturality.HelperVariables

private
  variable
    o ℓ e : Level
    A B C Φ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

private
  variable
    F G H I K L : Functor (op Γᵒᵖ ⊗ Φ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})

------------------------------------------------------------------------------------------

{-
  Inverse map for directed equality elimination, instantiating with identity.

  The other direction is contained in `Dinaturality/J.agda`.

  Compared to the version with in the paper, here we have to reorder the
  term context because of the signature for dinatural transformations, which
  is always of the form Cᵒᵖ × C for some C.
-}
J⁻¹ :
  ∀ {o} {A Γ : Category o ℓ ℓ}
    (let module A = Category A)
    {Φ P : Functor (op (A ⊗ Γ) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = A.op ⊗ A ⊗ Γ}
      (SetA.-×- ∘F ((Hom[ A ][-,-] ∘F (v1 ∘F cov ※ v2 ∘F cov))
                 ※ (Φ ∘F ((v2 ∘F ctr  ※ v3 ∘F ctr ) ※ v1 ∘F ctr  ※ v3 ∘F cov))))
      (P ∘F ((v1 ∘F cov ※ v3 ∘F ctr ) ※ v2 ∘F cov ※ v3 ∘F cov))
  → DinaturalTransformation {C = A ⊗ Γ}
      Φ
      P
J⁻¹ {A = A} {Γ = Γ} {Φ = Φ} {P = P} h = dtHelper (record
  { α = λ { (A , X) → record
    -- Definition of the main map.
    { to = λ { k → h.α (A , A , X) $ (id , k) }
    ; cong = λ eq → Func.cong (h.α _) (A.refl , eq)
    } }
  ; commute =
  λ { {X1 , X2} {Y1 , Y2} (f1 , f2) {k1} {k2} eq → let open RS (P.F₀ ((X1 , X2) , Y1 , Y2)) in
    begin P.₁ ((id , Γ.id) , f1 , f2)
           $ h.α (X1 , X1 , X2)
           $ (id , Φ.F₁ ((f1 , f2) , id , Γ.id) $ k1) ≈⟨ Func.cong (P.₁ _) (Func.cong (h.α _) (A.sym-id-1 ∙ A.sym-id-2 , ΦS.refl)) ⟩
          P.₁ ((id , Γ.id) , f1 , f2)
           $ h.α (X1 , X1 , X2)
           $ (id ∘ id ∘ id , Φ.₁ ((f1 , f2) , id , Γ.id) $ k1) ≈⟨ h.commute (id , f1 , f2) (A.refl , eq) ⟩
          P.₁ ((id , f2) , id , Γ.id)
           $ h.α _
           $ (f1 ∘ id ∘ id , Φ.F₁ ((id , Γ.id) , id , f2) $ _) ≈˘⟨ [ P ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) (Func.cong (h.α _) (A.sym-id-swap-2 , [ Φ ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) ΦS.refl)) ⟩
          P.₁ ((id , f2) , id , Γ.id)
          $ P.₁ ((id , Γ.id) , id , Γ.id)
           $ h.α _
           $ (id ∘ id ∘ f1 , Φ.F₁ ((id , Γ.id) , id , Γ.id) $ Φ.F₁ ((id , Γ.id) , id , f2) $ _) ≈⟨ Func.cong (P.₁ _) (h.op-commute (f1 , id , Γ.id) (A.refl , ΦS.refl)) ⟩
          P.₁ ((id , f2) , id , Γ.id)
           $ P.₁ ((f1 , Γ.id) , id , Γ.id)
           $ h.α (Y1 , Y1 , Y2)
           $ (id ∘ id ∘ id , Φ.₁ ((id , Γ.id) , f1 , Γ.id) $ Φ.₁ ((id , Γ.id) , id , f2) $ k2) ≈⟨ [ P ]-merge (A.id-1 , Γ.id-0) (A.id-1 , Γ.id-0) (Func.cong (h.α _) ((A.id-0 ∙ A.id-0) , [ Φ ]-merge (A.id-1 , Γ.id-0) (A.id-1 , Γ.id-0) ΦS.refl)) ⟩
          P.F₁ ((f1 , f2) , id , Γ.id)
           $ h.α (Y1 , Y1 , Y2)
           $ (id , Φ.F₁ ((id , Γ.id) , f1 , f2) $ k2) ∎
      }
  }) where
    module Φ = Functor Φ
    module P = Functor P
    open module A = Reason A
    module Γ = Reason Γ
    module h = DinaturalTransformation h
    module ΦS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)
