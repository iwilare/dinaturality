module Dinaturality.End where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
open import Categories.NaturalTransformation.StrongDinatural
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Categories.Object.Terminal using (Terminal)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition renaming (function to setoidComposition)
open import Function.Construct.Identity renaming (function to setoidIdentity)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong₂; trans; cong; sym)
open import Relation.Binary.Construct.Closure.Equivalence using (isEquivalence; EqClosure; setoid; return; join; map; gmap; fold; gfold)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

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

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt

endAdjL : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {Z : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → DinaturalTransformation P (endFunctor (Z ∘F F-reorder))
    → DinaturalTransformation (P ∘F (πʳ ∘F πˡ ※ πʳ ∘F πʳ)) Z
endAdjL {A = A} {Γ = Γ} {P = P} {Z = Z} α = dtHelper (record
      { α = λ { (X , G) → record
        { to = λ pxx → proj₁ (α.α G $ pxx) X
        ; cong = λ eq → Func.cong (α.α G) eq
        } }
      ; commute = λ {X} {Y} (f1 , f2) eq → let open RS (F₀ Z (X , Y)) in begin
        Z.₁ ((id , Γ.id) , (f1 , f2)) $ (proj₁ (α.α (proj₂ X) $ P.₁ (f2 , Γ.id) $ _) (proj₁ X)) ≈˘⟨ [ Z ]-merge (id-0 , Γ.id-0) (id-0 , Γ.id-1) ZS.refl ⟩
        Z.₁ ((id , Γ.id) , (id , f2)) $ Z.₁ ((id , Γ.id) , (f1 , Γ.id)) $ (proj₁ (α.α (proj₂ X) $ P.₁ (f2 , Γ.id) $ _) (proj₁ X)) ≈˘⟨ Func.cong (Z.₁ _) (proj₂ (α.α (proj₂ X) $ P.₁ (f2 , Γ.id) $ _) f1) ⟩
        Z.₁ ((id , Γ.id) , id , f2) $ Z.₁ ((f1 , Γ.id) , id , Γ.id) $ (proj₁ (α.α (proj₂ X) $ P.₁ (f2 , Γ.id) $ _) (proj₁ Y)) ≈⟨ [ Z ]-resp-square ((id-swap , Γ.refl) , Equiv.refl , Γ.id-swap) ZS.refl ⟩
        Z.₁ ((f1 , Γ.id) , id , Γ.id) $ Z.₁ ((id , Γ.id) , id , f2) $ (proj₁ (α.α (proj₂ X) $ P.₁ (f2 , Γ.id) $ _) (proj₁ Y)) ≈⟨ Func.cong (Z.₁ _) (α.commute f2 eq) ⟩
        Z.₁ ((f1 , Γ.id) , id , Γ.id) $ Z.₁ ((id , f2) , id , Γ.id) $ (proj₁ (α.α (proj₂ Y) $ P.₁ (Γ.id , f2) $ _) (proj₁ Y)) ≈⟨ [ Z ]-merge (id-0 , Γ.id-1) (id-0 , Γ.id-0) ZS.refl ⟩
        Z.₁ ((f1 , f2) , id , Γ.id) $ (proj₁ (α.α (proj₂ Y) $ P.₁ (Γ.id , f2) $ _) (proj₁ Y)) ∎
      })
  where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module P = Functor P
    module Z = Functor Z
    module ZS {A} = Setoid (F₀ Z A)
    module PS {A} = Setoid (F₀ P A)
    open Reason A

endAdjR : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {Z : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → DinaturalTransformation (P ∘F (πʳ ∘F πˡ ※ πʳ ∘F πʳ)) Z
    → DinaturalTransformation P (endFunctor (Z ∘F F-reorder))
endAdjR {A = A} {Γ = Γ} {P = P} {Z = Z} α = dtHelper (record
      { α = λ X → record
        { to = λ pxx → (λ A → α.α (A , X) $ pxx) , λ {Q} {W} f →
          let open module ZZ = RS (F₀ Z ((Q , X) , W , X)) in
          begin F₁ Z ((f , Γ.id) , id , Γ.id) $ α.α (W , X) $ pxx ≈⟨ Func.cong (F₁ Z _) (Func.cong (α.α _) (Setoid.sym (F₀ P (X , X)) (Functor.identity P (Setoid.refl (F₀ P (X , X)))))) ⟩
                F₁ Z ((f , Γ.id) , id , Γ.id) $ α.α (W , X) $ F₁ P (Γ.id , Γ.id) $ pxx ≈⟨ α.op-commute (f , Γ.id) (Setoid.refl (F₀ P _)) ⟩
                F₁ Z ((id , Γ.id) , f , Γ.id) $ α.α (Q , X) $ F₁ P (Γ.id , Γ.id) $ pxx ≈⟨ Func.cong (F₁ Z _) (Func.cong (α.α _) (Functor.identity P (Setoid.refl (F₀ P (X , X))))) ⟩
                F₁ Z ((id , Γ.id) , f , Γ.id) $ α.α (Q , X) $ pxx ∎
        ; cong = λ eq → Func.cong (α.α _) eq
        }
      ; commute = λ {X} {Y} f eq → α.commute (id , f) eq
      })
  where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    open Reason A

endAdjL⨟endAdjR-iso : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {Z : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → (α : DinaturalTransformation P (endFunctor (Z ∘F F-reorder)))
    → endAdjR {A = A} {Γ = Γ} {P = P} {Z = Z} (endAdjL α) ≃ᵈ α
endAdjL⨟endAdjR-iso α = λ x₁ → Func.cong (DinaturalTransformation.α α _) x₁

endAdjR⨟endAdjL-iso : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {Z : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → (α : DinaturalTransformation (P ∘F (πʳ ∘F πˡ ※ πʳ ∘F πʳ)) Z)
    → endAdjL {A = A} {Γ = Γ} {P = P} {Z = Z} (endAdjR α) ≃ᵈ α
endAdjR⨟endAdjL-iso α = {!   !}

{-
endProjection : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {Z : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    (F : Functor (op Γ ⊗ Γ) A)
  → DinaturalTransformation P (endFunctor (Z ∘F F-reorder))
  → DinaturalTransformation P (Z ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ))
endProjection {A = A} {Γ = Γ} {P = P} {Z = Z} F α = dtHelper (record
  { α = λ X → record
    { to = λ fxx → proj₁ (α.α X $ fxx) (F₀ F (X , X))
    ; cong = λ eq → Func.cong (α.α X) eq
    }
  ; commute = λ {X} {Y} m {x} {y} eq →
    let open module ZZ = RS (F₀ Z ((F₀ F (Y , X) , X) , F₀ F (X , Y) , Y)) in
    begin Z.₁ ((F.₁ (m , Γ.id) , Γ.id) , F.₁ (Γ.id , m) , m) $ proj₁ (α.α X $ P.₁ (m , Γ.id) $ x) (F.₀ (X , X))
            ≈⟨ [ Z ]-decompose₂ ZS.refl ⟩
          Z.₁ ((id , Γ.id) , F.₁ (Γ.id , m) , m) $ Z.₁ ((F.₁ (m , Γ.id) , Γ.id) , id , Γ.id) $ proj₁ (α.α X $ P.₁ (m , Γ.id) $ x) (F.₀ (X , X))
            ≈⟨ Func.cong (F₁ Z _) (proj₂ (α.α X $ P.₁ (m , Γ.id) $ x) _) ⟩
          Z.₁ ((id , Γ.id) , F.₁ (Γ.id , m) , m) $ Z.₁ ((id , Γ.id) , F.₁ (m , Γ.id) , Γ.id) $ proj₁ (α.α X $ P.₁ (m , Γ.id) $ x) (F.₀ (Y , X))
            ≈⟨ [ Z ]-resp-square ((Equiv.refl , Γ.refl) , sym-id-1 , Γ.id-swap) ZS.refl ⟩
          Z.₁ ((id , Γ.id) , F.₁ (Γ.id , m) ∘ F.₁ (m , Γ.id) , Γ.id) $ Z.₁ ((id , Γ.id) , id , m) $ proj₁ (α.α X $ P.₁ (m , Γ.id) $ x) (F.₀ (Y , X))
            ≈⟨ Func.cong (F₁ Z _) (ZS.sym (α.op-commute m (PS.sym eq))) ⟩
          Z.₁ ((id , Γ.id) , F.₁ (Γ.id , m) ∘ F.₁ (m , Γ.id) , Γ.id) $ Z.₁ ((id , m) , id , Γ.id) $ proj₁ (α.α Y $ P.₁ (Γ.id , m) $ y) (F.₀ (Y , X))
            ≈⟨ F-resp-≈ Z ((Equiv.refl , Γ.refl) , [ F ]-commute , Γ.refl) ZS.refl ⟩
          Z.₁ ((id , Γ.id) , F.₁ (m , Γ.id) ∘ F.₁ (Γ.id , m) , Γ.id) $ Z.₁ ((id , m) , id , Γ.id) $ proj₁ (α.α Y $ P.₁ (Γ.id , m) $ y) (F.₀ (Y , X))
            ≈⟨ [ Z ]-resp-square ((Equiv.refl , Γ.id-swap) , id-1 , Γ.refl) ZS.refl ⟩
          Z.₁ ((id , m) , F.₁ (m , Γ.id) , Γ.id) $ Z.₁ ((id , Γ.id) , F.₁ (Γ.id , m) , Γ.id) $ proj₁ (α.α Y $ P.₁ (Γ.id , m) $ y) (F.₀ (Y , X))
            ≈⟨ Func.cong (F₁ Z _) (ZS.sym (proj₂ (α.α Y $ F₁ P (Γ.id , m) $ y) _)) ⟩
          Z.₁ ((id , m) , F.₁ (m , Γ.id) , Γ.id) $ Z.₁ ((F.₁ (Γ.id , m) , Γ.id) , id , Γ.id) $ proj₁ (α.α Y $ P.₁ (Γ.id , m) $ y) (F.₀ (Y , Y))
            ≈⟨ [ Z ]-merge (id-1 , Γ.identityˡ) (id-1 , Γ.id-1) ZS.refl ⟩
          Z.₁ ((F.₁ (Γ.id , m) , m) , F.₁ (m , Γ.id) , Γ.id) $ proj₁ (α.α Y $ P.₁ (Γ.id , m) $ y) (F.₀ (Y , Y)) ∎
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module F = Functor F
    module P = Functor P
    module Z = Functor Z
    module ZS {A} = Setoid (F₀ Z A)
    module PS {A} = Setoid (F₀ P A)
    open Reason A
-}
