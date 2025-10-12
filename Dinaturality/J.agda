{-# OPTIONS --safe --without-K #-}

{-
  Main rule for directed equality elimination (and introduction, via its inverse direction).

  The inverse direction is contained in `Dinaturality/J-Inverse.agda`.

  This module contains the maps in both directions.
  The isomorphism is split into the module `Dinaturality/J-Iso.agda`
  because of Agda often running out of memory.
-}
module Dinaturality.J where

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
    A B Γ Φ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

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

v2 : Functor (Product A (Product B Γ)) B
v2 = πˡ ∘F πʳ

v3 : Functor (Product A (Product B Γ)) Γ
v3 = πʳ ∘F πʳ

------------------------------------------------------------------------------------------

{-
  Directed equality elimination.

  Compared to the version with in the paper, here we have to reorder the
  term context because of the signature for dinatural transformations, which
  is always of the form Cᵒᵖ × C for some Γ.
-}
J :
  ∀ {o} {A Γ : Category o ℓ ℓ}
    (let module A = Category A)
    {Φ P : Functor (op (A ⊗ Γ) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = A ⊗ Γ}
      Φ
      P
  → DinaturalTransformation {C = A.op ⊗ A ⊗ Γ}
      (SetA.-×- ∘F ((Hom[ A ][-,-] ∘F (v1 ∘F pos ※ v2 ∘F pos))
                 ※ (Φ ∘F ((v2 ∘F neg ※ v3 ∘F neg) ※ v1 ∘F neg ※ v3 ∘F pos))))
      (P ∘F ((v1 ∘F pos ※ v3 ∘F neg) ※ v2 ∘F pos ※ v3 ∘F pos))
J {A = A} {Γ = Γ} {Φ = Φ} {P = P} h = dtHelper (record
  { α = λ { (A , B , X) → record
    -- Definition of the main map.
    { to = λ { (f , k) → P.₁ ((f , Γ.id) , A.id , Γ.id) $ h.α (B , X) $ Φ.₁ ((A.id , Γ.id) , f , Γ.id) $ k }
    ; cong = λ { (feq , eq) → P.F-resp-≈ ((feq , Γ.refl) , A.refl , Γ.refl) (Func.cong (h.α _) (Φ.F-resp-≈ ((A.refl , Γ.refl) , feq , Γ.refl ) eq)) }
    } }
  ; commute = λ { {X1 , X2 , X3} {Y1 , Y2 , Y3} (f1 , f2 , f3) {e1 , k1} {e2 , k2} (eq1 , eq2) →
      let open RS (P.F₀ ((Y1 , X3) , Y2 , Y3)) in
      begin P.₁ ((f1 , Γ.id) , f2 , f3)
             $ P.₁ ((id ∘ e1 ∘ id , Γ.id) , id , Γ.id)
             $ h.α (X2 , X3)
             $ Φ.F₁ ((id , Γ.id) , id ∘ e1 ∘ id , Γ.id)
             $ Φ.F₁ ((f2 , f3) , f1 , Γ.id)
             $ k1 ≈⟨ [ P ]-resp-square ((((assoc-3 ∙ idm-2) , Γ.refl) , A.id-swap , Γ.id-swap)) (Func.cong (h.α _) ([ Φ ]-resp-square ((A.id-swap , Γ.id-swap) , (assoc-3 ∙ idm-2) , Γ.refl) eq2)) ⟩
            P.₁ ((e1 ∘ f1 , Γ.id) , id , Γ.id)
             $ P.₁ ((id , Γ.id) , f2 , f3)
             $ h.α (X2 , X3)
             $ Φ.₁ ((f2 , f3) , id , Γ.id)
             $ Φ.₁ ((id , Γ.id) , e1 ∘ f1 , Γ.id)
             $ k2 ≈⟨ Func.cong (P.₁ _) (h.commute _ ΦS.refl) ⟩
            P.₁ ((e1 ∘ f1 , Γ.id) , id , Γ.id)
            $ P.₁ ((f2 , f3) , id , Γ.id)
            $ h.α (Y2 , Y3)
            $ Φ.₁ ((id , Γ.id) , f2 , f3)
            $ Φ.₁ ((id , Γ.id) , e1 ∘ f1 , Γ.id)
            $ k2 ≈⟨ [ P ]-resp-square (((skip (rw eq1) ∙ sym-id-1) , Γ.id-swap) , A.refl , Γ.refl) (Func.cong (h.α _) ([ Φ ]-resp-square ((A.refl , Γ.refl) , ((skip (rw eq1) ∙ sym-id-1) , Γ.id-swap)) ΦS.refl)) ⟩
            P.₁ ((id , f3) , id , Γ.id)
            $ P.₁ ((f2 ∘ e2 ∘ f1 , Γ.id) , id , Γ.id)
            $ h.α (Y2 , Y3)
            $ Φ.₁ ((id , Γ.id) , f2 ∘ e2 ∘ f1 , Γ.id)
            $ Φ.₁ ((id , Γ.id) , id , f3)
            $ k2 ∎
      }
  }) where
    module Φ = Functor Φ
    module P = Functor P
    open module A = Reason A
    module Γ = Reason Γ
    module h = DinaturalTransformation h
    module ΦS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)
