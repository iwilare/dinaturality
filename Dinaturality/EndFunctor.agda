{-# OPTIONS --safe --without-K #-}

{-
  We define the parametric end of a functor F : A × Aᵒᵖ × Γ → Set, taking the end in A.

  The action on morphisms (i.e., on natural transformations) is not required in the rest of the formalization.
-}

module Dinaturality.EndFunctor where

open import Level using (Level; _⊔_) renaming (zero to zeroℓ; suc to sucℓ)

import Categories.Functor.Hom as Hom
import Relation.Binary.Reasoning.Setoid as RS

open import Categories.Category
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Data.Product using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

import Reason

endFunctor : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    → Functor (Product (Category.op A) (Product A Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))
    → Functor Γ (Setoids (o ⊔ ℓ) (o ⊔ ℓ))
endFunctor {A = A} {Γ = Γ} F = record
  { F₀ = λ G → record
    { Carrier =
      Σ (∀ X → FS.Carrier {X} {X} {G})
        (λ k →
          ∀ {A B} (f : A ⇒ B)
          → (F.₁ (f , id , Γ.id) ⟨$⟩ k B) ≈ˢ (F.₁ (id , f , Γ.id) ⟨$⟩ k A))
    ; _≈_ = λ { (p , _) (e , _) → ∀ {X} → (p X) ≈ˢ (e X) }
    ; isEquivalence = record
      { refl = FS.refl
      ; sym = λ x → FS.sym x
      ; trans = λ p q → FS.trans p q
      }
    }
  ; F₁ = λ {B} {C} f → record
    { to = λ { (p , e) →
      (λ X → F.₁ (id , id , f) ⟨$⟩ p X) ,
      λ {T} {R} m → begin
        F.₁ (m , id , Γ.id) ⟨$⟩ (F.₁ (id , id , f) ⟨$⟩ (p _)) ≈⟨ [ F ]-resp-square (A.sym-id-swap {f = m} , A.refl , Γ.sym-id-swap {f = f}) FS.refl ⟩
        F.₁ (id , id , f) ⟨$⟩ (F.₁ (m , id , Γ.id) ⟨$⟩ (p _)) ≈⟨ Func.cong (F.₁ (id , id , f)) (e m) ⟩
        F.₁ (id , id , f) ⟨$⟩ (F.₁ (id , m , Γ.id) ⟨$⟩ (p _)) ≈⟨ [ F ]-resp-square (A.refl {T} {T} {id ∘ id} , A.sym-id-swap , Γ.id-swap) (FS.refl {T} {T} {B} {p T}) ⟩ --[ F ]-resp-square (A.refl {A = {!   !}} {B = {!   !}} , ?) FS.refl ⟩
        F.₁ (id , m , Γ.id) ⟨$⟩ (F.₁ (id , id , f) ⟨$⟩ (p _)) ∎ }
    ; cong = λ eq → Func.cong (F.F₁ (id , id , f)) eq
    }
  ; identity = λ eq → F.identity eq
  ; homomorphism = λ { {X} {Y} {Z} {f} {g} eq →
      begin
       F.₁ (id , id , g Γ.∘ f) ⟨$⟩ _ ≈˘⟨ [ F ]-merge identity² (identity² , Γ.refl) (FS.sym eq) ⟩
       F.₁ (id , id , g) ⟨$⟩ (F.₁ (id , id , f) ⟨$⟩ _) ∎ }
  ; F-resp-≈ = λ f≈g eq → F.F-resp-≈ (Equiv.refl , Equiv.refl , f≈g) eq
  } where module F = Functor F
          module Γ = Reason Γ
          open module A = Reason A
          open module FS {A} {B} {Γ} = Setoid (F.₀ (A , B , Γ)) renaming (_≈_ to _≈ˢ_)
          open module MRS {A} {B} {Γ} = RS (F.₀ (A , B , Γ))
