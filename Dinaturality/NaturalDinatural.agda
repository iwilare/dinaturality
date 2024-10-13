{-# OPTIONS --safe --without-K #-}

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

dinat⇒homnat : ∀ {o} {A : Category o ℓ ℓ} {F G : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → DinaturalTransformation F G
  → NaturalTransformation Hom[ A ][-,-] (Set.-⇨- ∘F (Functor.op F ∘F Swap ※ G))
dinat⇒homnat {A = A} {F = F} {G = G} α = ntHelper record
  { η = λ { (X , Y) → record
    { to = λ { f → record
      { to = λ x → G.₁ (id , f) $ α.α X $ F.₁ (f , id) $ x
      ; cong = λ eq → Func.cong (G.₁ _) (Func.cong (α.α X) (Func.cong (F.₁ _) eq))
      } }
    ; cong = λ x eq → G.F-resp-≈ (A.refl , x) (Func.cong (α.α X) (F.F-resp-≈ (x , A.refl) eq))
    } }
  ; commute =
    λ { {X1 , X2} {Y1 , Y2} (f1 , f2) {x} {y} eq1 eq2 →
        let open RS (G.F₀ (Y1 , Y2)) in
        begin G.₁ (id , f2 ∘ x ∘ f1) $ α.α Y1 $ F.₁ (f2 ∘ x ∘ f1 , id) $ _
              ≈˘⟨ [ G ]-merge identity² A.refl (Func.cong (α.α Y1)
                  ([ F ]-merge A.refl identity² (KS.sym eq2))) ⟩
              G.₁ (id , f2) $ G.₁ (id , x ∘ f1) $ α.α Y1 $ F.₁ (x ∘ f1 , id) $ F.₁ (f2 , id) $ _
                ≈⟨ Func.cong (G.₁ _) (α.commute (x ∘ f1) KS.refl) ⟩
              G.₁ (id , f2) $ G.₁ (x ∘ f1 , id) $ α.α X2 $ F.₁ (id , x ∘ f1) $ F.₁ (f2 , id) $ _
                ≈⟨ [ G ]-resp-square (assoc ∙ id-2 ∙ rw eq1 , A.refl) (Func.cong (α.α X2)
                  ([ F ]-resp-square (A.refl , assoc ∙ (id-2 ∙ rw eq1)) KS.refl)) ⟩
              G.₁ (f1 , f2) $ G.₁ (y , id) $ α.α X2 $ F.₁ (id , y) $ F.₁ (f2 , f1) $ _
                ≈⟨ Func.cong (G.₁ _) (α.op-commute y KS.refl) ⟩
              G.₁ (f1 , f2) $ G.₁ (id , y) $ α.α X1 $ F.₁ (y , id) $ F.F₁ (f2 , f1) $ _ ∎ }
  } where
    module α = DinaturalTransformation α
    module G = Functor G
    module F = Functor F
    module HS {A} = Setoid (F₀ G A)
    module KS {A} = Setoid (F₀ F A)
    open module A = Reason A

homnat⇒dinat : ∀ {o} {A : Category o ℓ ℓ} {F G : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → NaturalTransformation Hom[ A ][-,-] (Set.-⇨- ∘F (Functor.op F ∘F Swap ※ G))
  → DinaturalTransformation F G
homnat⇒dinat {A = A} {F = F} {G = G} α = dtHelper (record
  { α = λ X → record
    { to = λ x → (α.η (X , X) $ id) $ x
    ; cong = λ eq → Func.cong (α.η (X , X) $ id) eq
    }
  ; commute = λ { {X} {Y} f eq → let open RS (G.F₀ (X , Y)) in
    begin G.₁ (id , f) $ (α.η (X , X) $ id) $ F.₁ (f , id) $ _ ≈⟨ α.sym-commute (id , f) A.refl KS.refl ⟩
          (α.η (X , Y) $ f ∘ id ∘ id) $ _ ≈⟨ Func.cong (α.η (X , Y)) id-swap-2 eq ⟩
          (α.η (X , Y) $ id ∘ id ∘ f) $ _ ≈⟨ α.commute (f , id) A.refl KS.refl ⟩
          G.₁ (f , id) $ (α.η (Y , Y) $ id) $ F.₁ (id , f) $ _ ∎ }
  }) where
    module α = NaturalTransformation α
    module G = Functor G
    module F = Functor F
    module HS {A} = Setoid (F₀ G A)
    module KS {A} = Setoid (F₀ F A)
    open module A = Reason A

-- The above maps are isomorphisms.

dinat⇒homnat⨟homnat⇒dinat-iso : ∀ {o ℓ} {A : Category o ℓ ℓ} {F G : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
       (α : DinaturalTransformation F G)
     → homnat⇒dinat {A = A} {F = F} {G = G} (dinat⇒homnat {A = A} {F = F} {G = G} α) ≃ᵈ α
dinat⇒homnat⨟homnat⇒dinat-iso {A = A} {F = F} {G = G} α {x} {y} eq =
  G.identity (Func.cong (α.α x) (F.identity eq))
  where
    module α = DinaturalTransformation α
    module G = Functor G
    module F = Functor F
    module KS {A} = Setoid (F₀ F A)
    open module A = Reason A

homnat⇒dinat⨟dinat⇒homnat-iso : ∀ {o ℓ} {A : Category o ℓ ℓ} {F G : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
       (α : NaturalTransformation Hom[ A ][-,-] (Set.-⇨- ∘F (Functor.op F ∘F Swap ※ G)))
     → dinat⇒homnat {A = A} {F = F} {G = G} (homnat⇒dinat {A = A} {F = F} {G = G} α) ≃ⁿ α
homnat⇒dinat⨟dinat⇒homnat-iso {A = A} {F = F} {G = G} α {x1 , x2} {f} eq₁ eq₂ =
  begin G.₁ (id , f) $ (α.η (x1 , x1) $ id) $ F.₁ (f , id) $ _ ≈⟨ α.sym-commute (A.id , f) A.refl eq₂ ⟩
        (α.η (x1 , x2) $ f ∘ id ∘ id) $ _ ≈⟨ Func.cong (α.η (x1 , x2)) (id-2-1 ∙ eq₁) KS.refl ⟩
        (α.η (x1 , x2) $ _) $ _ ∎
  where
    module α = NaturalTransformation α
    module G = Functor G
    module F = Functor F
    open RS (G.₀ (x1 , x2))
    module HS {A} = Setoid (G.₀ A)
    module KS {A} = Setoid (F.₀ A)
    open module A = Reason A
