{-# OPTIONS --safe --without-K #-}

{-
  We validate the rules for ends, and prove that they are isomorphisms.

  We do not prove naturality here, although it is easy to
  check given the parametric way in which the maps below are defined.

  (This file is particularly slow to typecheck.)
-}

module Dinaturality.End where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

open import Dinaturality.HelperVariables
open import Dinaturality.EndFunctor using (endFunctor)

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

F-reorder : Functor (op A ⊗ A ⊗ op C ⊗ C) (op (A ⊗ C) ⊗ A ⊗ C)
F-reorder = assocʳ _ _ _ ∘F (idF ⁂ F-swap)

private
  variable
    F G H I J K L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

-- Rules for ends, both directions.

endL : ∀ {o ℓ e} {A Γ : Category o ℓ e}
  {Φ : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
  {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
  → DinaturalTransformation Φ (endFunctor (P ∘F F-reorder))
  → DinaturalTransformation (Φ ∘F (vb ∘F ctr ※ vb ∘F cov)) P
endL {A = A} {Γ = Γ} {Φ = Φ} {P = P} α = dtHelper (record
      { α = λ { (X , G) → record
        { to = λ pxx → proj₁ (α.α G $ pxx) X
        ; cong = λ eq → Func.cong (α.α G) eq
        } }
      ; commute = λ {X} {Y} (f1 , f2) eq → let open RS (F₀ P (X , Y)) in begin
        P.₁ ((id , Γ.id) , (f1 , f2)) $ (proj₁ (α.α (proj₂ X) $ Φ.₁ (f2 , Γ.id) $ _) (proj₁ X)) ≈˘⟨ [ P ]-merge (id-0 , Γ.id-0) (id-0 , Γ.id-1) PS.refl ⟩
        P.₁ ((id , Γ.id) , (id , f2)) $ P.₁ ((id , Γ.id) , (f1 , Γ.id)) $ (proj₁ (α.α (proj₂ X) $ Φ.₁ (f2 , Γ.id) $ _) (proj₁ X)) ≈˘⟨ Func.cong (P.₁ _) (proj₂ (α.α (proj₂ X) $ Φ.₁ (f2 , Γ.id) $ _) f1) ⟩
        P.₁ ((id , Γ.id) , id , f2) $ P.₁ ((f1 , Γ.id) , id , Γ.id) $ (proj₁ (α.α (proj₂ X) $ Φ.₁ (f2 , Γ.id) $ _) (proj₁ Y)) ≈⟨ [ P ]-resp-square ((id-swap , Γ.refl) , Equiv.refl , Γ.id-swap) PS.refl ⟩
        P.₁ ((f1 , Γ.id) , id , Γ.id) $ P.₁ ((id , Γ.id) , id , f2) $ (proj₁ (α.α (proj₂ X) $ Φ.₁ (f2 , Γ.id) $ _) (proj₁ Y)) ≈⟨ Func.cong (P.₁ _) (α.commute f2 eq) ⟩
        P.₁ ((f1 , Γ.id) , id , Γ.id) $ P.₁ ((id , f2) , id , Γ.id) $ (proj₁ (α.α (proj₂ Y) $ Φ.₁ (Γ.id , f2) $ _) (proj₁ Y)) ≈⟨ [ P ]-merge (id-0 , Γ.id-1) (id-0 , Γ.id-0) PS.refl ⟩
        P.₁ ((f1 , f2) , id , Γ.id) $ (proj₁ (α.α (proj₂ Y) $ Φ.₁ (Γ.id , f2) $ _) (proj₁ Y)) ∎
      })
  where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module Φ = Functor Φ
    module P = Functor P
    module ΦS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)
    open Reason A

endR : ∀ {o ℓ e} {A Γ : Category o ℓ e}
  {Φ : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
  {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
  → DinaturalTransformation (Φ ∘F (vb ∘F ctr ※ vb ∘F cov)) P
  → DinaturalTransformation Φ (endFunctor (P ∘F F-reorder))
endR {A = A} {Γ = Γ} {Φ = Φ} {P = P} α = dtHelper (record
      { α = λ X → record
        { to = λ pxx → (λ A → α.α (A , X) $ pxx) , λ {Q} {W} f →
          let open module ZZ = RS (F₀ P ((Q , X) , W , X)) in
          begin F₁ P ((f , Γ.id) , id , Γ.id) $ α.α (W , X) $ pxx ≈⟨ Func.cong (F₁ P _) (Func.cong (α.α _) (Setoid.sym (F₀ Φ (X , X)) (Functor.identity Φ (Setoid.refl (F₀ Φ (X , X)))))) ⟩
                F₁ P ((f , Γ.id) , id , Γ.id) $ α.α (W , X) $ F₁ Φ (Γ.id , Γ.id) $ pxx ≈⟨ α.op-commute (f , Γ.id) (Setoid.refl (F₀ Φ _)) ⟩
                F₁ P ((id , Γ.id) , f , Γ.id) $ α.α (Q , X) $ F₁ Φ (Γ.id , Γ.id) $ pxx ≈⟨ Func.cong (F₁ P _) (Func.cong (α.α _) (Functor.identity Φ (Setoid.refl (F₀ Φ (X , X))))) ⟩
                F₁ P ((id , Γ.id) , f , Γ.id) $ α.α (Q , X) $ pxx ∎
        ; cong = λ eq → Func.cong (α.α _) eq
        }
      ; commute = λ {X} {Y} f eq → α.commute (id , f) eq
      })
  where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    open Reason A

-- The two maps above are isomorphisms (in Set).

endL⨟endR-iso : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {Φ : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → (α : DinaturalTransformation Φ (endFunctor (P ∘F F-reorder)))
    → endR {A = A} {Γ = Γ} {Φ = Φ} {P = P} (endL α) ≃ᵈ α
endL⨟endR-iso α eq = Func.cong (DinaturalTransformation.α α _) eq

endR⨟endL-iso : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {Φ : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → (α : DinaturalTransformation (Φ ∘F (vb ∘F ctr ※ vb ∘F cov)) P)
    → endL {A = A} {Γ = Γ} {Φ = Φ} {P = P} (endR α) ≃ᵈ α
endR⨟endL-iso α eq = Func.cong (DinaturalTransformation.α α _) eq

{-
  This map exemplifies the fact that $∀x.Φ(x,¬x,y)$ implies $Φ(t(y),t(y),y)$, i.e., that universal
  quantification implies that the property holds for any concrete term $t(y)$, here represented by difunctors.
  This is derivable with `endR` and the reindexing as in `Dinatural/Reindexing.agda`,
  but we define it here explicitly for convenience.

  This is not used in any development.
-}
{-
endProjection : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {Φ : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    (F : Functor (op Γ ⊗ Γ) A)
  → DinaturalTransformation Φ (endFunctor (P ∘F F-reorder))
  → DinaturalTransformation Φ (P ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ))
endProjection {A = A} {Γ = Γ} {Φ = Φ} {P = P} F α = dtHelper (record
  { α = λ X → record
    { to = λ fxx → proj₁ (α.α X $ fxx) (F₀ F (X , X))
    ; cong = λ eq → Func.cong (α.α X) eq
    }
  ; commute = λ {X} {Y} m {x} {y} eq →
    let open module ZZ = RS (F₀ P ((F₀ F (Y , X) , X) , F₀ F (X , Y) , Y)) in
    begin P.₁ ((F.₁ (m , Γ.id) , Γ.id) , F.₁ (Γ.id , m) , m) $ proj₁ (α.α X $ Φ.₁ (m , Γ.id) $ x) (F.₀ (X , X))
            ≈⟨ [ P ]-decompose₂ PS.refl ⟩
          P.₁ ((id , Γ.id) , F.₁ (Γ.id , m) , m) $ P.₁ ((F.₁ (m , Γ.id) , Γ.id) , id , Γ.id) $ proj₁ (α.α X $ Φ.₁ (m , Γ.id) $ x) (F.₀ (X , X))
            ≈⟨ Func.cong (F₁ P _) (proj₂ (α.α X $ Φ.₁ (m , Γ.id) $ x) _) ⟩
          P.₁ ((id , Γ.id) , F.₁ (Γ.id , m) , m) $ P.₁ ((id , Γ.id) , F.₁ (m , Γ.id) , Γ.id) $ proj₁ (α.α X $ Φ.₁ (m , Γ.id) $ x) (F.₀ (Y , X))
            ≈⟨ [ P ]-resp-square ((Equiv.refl , Γ.refl) , sym-id-1 , Γ.id-swap) PS.refl ⟩
          P.₁ ((id , Γ.id) , F.₁ (Γ.id , m) ∘ F.₁ (m , Γ.id) , Γ.id) $ P.₁ ((id , Γ.id) , id , m) $ proj₁ (α.α X $ Φ.₁ (m , Γ.id) $ x) (F.₀ (Y , X))
            ≈⟨ Func.cong (F₁ P _) (PS.sym (α.op-commute m (ΦS.sym eq))) ⟩
          P.₁ ((id , Γ.id) , F.₁ (Γ.id , m) ∘ F.₁ (m , Γ.id) , Γ.id) $ P.₁ ((id , m) , id , Γ.id) $ proj₁ (α.α Y $ Φ.₁ (Γ.id , m) $ y) (F.₀ (Y , X))
            ≈⟨ F-resp-≈ P ((Equiv.refl , Γ.refl) , [ F ]-commute , Γ.refl) PS.refl ⟩
          P.₁ ((id , Γ.id) , F.₁ (m , Γ.id) ∘ F.₁ (Γ.id , m) , Γ.id) $ P.₁ ((id , m) , id , Γ.id) $ proj₁ (α.α Y $ Φ.₁ (Γ.id , m) $ y) (F.₀ (Y , X))
            ≈⟨ [ P ]-resp-square ((Equiv.refl , Γ.id-swap) , id-1 , Γ.refl) PS.refl ⟩
          P.₁ ((id , m) , F.₁ (m , Γ.id) , Γ.id) $ P.₁ ((id , Γ.id) , F.₁ (Γ.id , m) , Γ.id) $ proj₁ (α.α Y $ Φ.₁ (Γ.id , m) $ y) (F.₀ (Y , X))
            ≈⟨ Func.cong (F₁ P _) (PS.sym (proj₂ (α.α Y $ F₁ Φ (Γ.id , m) $ y) _)) ⟩
          P.₁ ((id , m) , F.₁ (m , Γ.id) , Γ.id) $ P.₁ ((F.₁ (Γ.id , m) , Γ.id) , id , Γ.id) $ proj₁ (α.α Y $ Φ.₁ (Γ.id , m) $ y) (F.₀ (Y , Y))
            ≈⟨ [ P ]-merge (id-1 , Γ.identityˡ) (id-1 , Γ.id-1) PS.refl ⟩
          P.₁ ((F.₁ (Γ.id , m) , m) , F.₁ (m , Γ.id) , Γ.id) $ proj₁ (α.α Y $ Φ.₁ (Γ.id , m) $ y) (F.₀ (Y , Y)) ∎
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module F = Functor F
    module Φ = Functor Φ
    module P = Functor P
    module ΦS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)
    open Reason A
-}
