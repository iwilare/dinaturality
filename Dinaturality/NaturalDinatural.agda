{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  Correspondence between dinaturals into Set and certain natural transformations with $hom$ in the domain.

  (This file takes particularly long to typecheck.)
-}

module Dinaturality.NaturalDinatural where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

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

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)

dinat⇒homnat : ∀ {o} {A : Category o ℓ ℓ} {P Q : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → DinaturalTransformation P Q
  → NaturalTransformation Hom[ A ][-,-] (Set.-⇨- ∘F (Functor.op P ∘F Swap ※ Q))
dinat⇒homnat {A = A} {P = P} {Q = Q} α = ntHelper record
  { η = λ { (X , Y) → record
    { to = λ { f → record
      { to = λ x → Q.₁ (id , f) $ α.α X $ P.₁ (f , id) $ x
      ; cong = λ eq → Func.cong (Q.₁ _) (Func.cong (α.α X) (Func.cong (P.₁ _) eq))
      } }
    ; cong = λ x eq → Q.F-resp-≈ (A.refl , x) (Func.cong (α.α X) (P.F-resp-≈ (x , A.refl) eq))
    } }
  ; commute =
    λ { {X1 , X2} {Y1 , Y2} (f1 , f2) {x} {y} eq1 eq2 →
        let open RS (Q.F₀ (Y1 , Y2)) in
        begin Q.₁ (id , f2 ∘ x ∘ f1) $ α.α Y1 $ P.₁ (f2 ∘ x ∘ f1 , id) $ _
              ≈˘⟨ [ Q ]-merge identity² A.refl (Func.cong (α.α Y1)
                  ([ P ]-merge A.refl identity² (PS.sym eq2))) ⟩
              Q.₁ (id , f2) $ Q.₁ (id , x ∘ f1) $ α.α Y1 $ P.₁ (x ∘ f1 , id) $ P.₁ (f2 , id) $ _
                ≈⟨ Func.cong (Q.₁ _) (α.commute (x ∘ f1) PS.refl) ⟩
              Q.₁ (id , f2) $ Q.₁ (x ∘ f1 , id) $ α.α X2 $ P.₁ (id , x ∘ f1) $ P.₁ (f2 , id) $ _
                ≈⟨ [ Q ]-resp-square (assoc ∙ id-2 ∙ rw eq1 , A.refl {x = f2 ∘ id}) (Func.cong (α.α X2)
                  ([ P ]-resp-square (A.refl {x = f2 ∘ id} , assoc ∙ (id-2 ∙ rw eq1)) PS.refl)) ⟩
              Q.₁ (f1 , f2) $ Q.₁ (y , id) $ α.α X2 $ P.₁ (id , y) $ P.₁ (f2 , f1) $ _
                ≈⟨ Func.cong (Q.₁ _) (α.op-commute y PS.refl) ⟩
              Q.₁ (f1 , f2) $ Q.₁ (id , y) $ α.α X1 $ P.₁ (y , id) $ P.F₁ (f2 , f1) $ _ ∎ }
  } where
    module α = DinaturalTransformation α
    module P = Functor P
    module Q = Functor Q
    module PS {A} = Setoid (F₀ P A)
    module QS {A} = Setoid (F₀ Q A)
    open module A = Reason A

homnat⇒dinat : ∀ {o} {A : Category o ℓ ℓ} {P Q : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → NaturalTransformation Hom[ A ][-,-] (Set.-⇨- ∘F (Functor.op P ∘F Swap ※ Q))
  → DinaturalTransformation P Q
homnat⇒dinat {A = A} {P = P} {Q = Q} α = dtHelper (record
  { α = λ X → record
    { to = λ x → (α.η (X , X) $ id) $ x
    ; cong = λ eq → Func.cong (α.η (X , X) $ id) eq
    }
  ; commute = λ { {X} {Y} f eq → let open RS (Q.F₀ (X , Y)) in
    begin Q.₁ (id , f) $ (α.η (X , X) $ id) $ P.₁ (f , id) $ _ ≈⟨ α.sym-commute (id , f) A.refl PS.refl ⟩
          (α.η (X , Y) $ f ∘ id ∘ id) $ _ ≈⟨ Func.cong (α.η (X , Y)) id-swap-2 eq ⟩
          (α.η (X , Y) $ id ∘ id ∘ f) $ _ ≈⟨ α.commute (f , id) A.refl PS.refl ⟩
          Q.₁ (f , id) $ (α.η (Y , Y) $ id) $ P.₁ (id , f) $ _ ∎ }
  }) where
    module α = NaturalTransformation α
    module P = Functor P
    module Q = Functor Q
    module PS {A} = Setoid (F₀ P A)
    module QS {A} = Setoid (F₀ Q A)
    open module A = Reason A

-- The above maps are isomorphisms.

dinat⇒homnat⨟homnat⇒dinat-iso : ∀ {o ℓ} {A : Category o ℓ ℓ} {P Q : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
       (α : DinaturalTransformation P Q)
     → homnat⇒dinat {A = A} {P = P} {Q = Q} (dinat⇒homnat {A = A} {P = P} {Q = Q} α) ≃ᵈ α
dinat⇒homnat⨟homnat⇒dinat-iso {A = A} {P = P} {Q = Q} α {x} {y} eq =
  Q.identity (Func.cong (α.α x) (P.identity eq))
  where
    module α = DinaturalTransformation α
    module P = Functor P
    module Q = Functor Q
    module PS {A} = Setoid (F₀ P A)
    open module A = Reason A

homnat⇒dinat⨟dinat⇒homnat-iso : ∀ {o ℓ} {A : Category o ℓ ℓ} {P Q : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
       (α : NaturalTransformation Hom[ A ][-,-] (Set.-⇨- ∘F (Functor.op P ∘F Swap ※ Q)))
     → dinat⇒homnat {A = A} {P = P} {Q = Q} (homnat⇒dinat {A = A} {P = P} {Q = Q} α) ≃ⁿ α
homnat⇒dinat⨟dinat⇒homnat-iso {A = A} {P = P} {Q = Q} α {x1 , x2} {f} eq₁ eq₂ =
  begin Q.₁ (id , f) $ (α.η (x1 , x1) $ id) $ P.₁ (f , id) $ _ ≈⟨ α.sym-commute (A.id , f) A.refl eq₂ ⟩
        (α.η (x1 , x2) $ f ∘ id ∘ id) $ _ ≈⟨ Func.cong (α.η (x1 , x2)) (id-2-1 ∙ eq₁) PS.refl ⟩
        (α.η (x1 , x2) $ _) $ _ ∎
  where
    module α = NaturalTransformation α
    module P = Functor P
    module Q = Functor Q
    open RS (Q.₀ (x1 , x2))
    module PS {A} = Setoid (P.₀ A)
    module QS {A} = Setoid (Q.₀ A)
    open module A = Reason A
