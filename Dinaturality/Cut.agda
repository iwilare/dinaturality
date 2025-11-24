{-# OPTIONS --safe --without-K #-}

{-
  Composition between naturals and dinaturals.

  Properties of these maps are defined in CutAssociativity, CutCoherence, CutIdentities.
-}

module Dinaturality.Cut where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
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

open import Dinaturality.HelperVariables

private
  variable
    o ℓ e : Level
    A B C D E Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

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
  improve readibility for the variables used in the entailments.
-}

cut-din : ∀
  {Φ Q : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
  {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (Φ ∘F ((v1 ∘F cov ※ v3 ∘F ctr ) ※ v2 ∘F cov ※ v3 ∘F cov)) -- v1 and v2 only covariant
                            (P ∘F (v1 ∘F cov ※ v2 ∘F cov)) -- v1 and v2 only covariant
  → DinaturalTransformation {C = Δ ⊗ Γ} (SetA.-×- ∘F (P ∘F (v1 ∘F ctr  ※ v1 ∘F cov) ※ Φ)) Q
  → DinaturalTransformation Φ Q
cut-din {Δ = Δ} {Γ = Γ} {Φ = Φ} {Q} {P} α γ = dtHelper record
  { α = λ { (X , Z) → record
    { to = λ p → γ.α (X , Z) $ (α.α (X , X , Z) $ p , p)
    ; cong = λ e → Func.cong (γ.α (X , Z)) (Func.cong (α.α (X , X , Z)) e , e)
    } }
  ; commute = λ { {X , Y} {Z , W} (f , g) {x} {y} e →
    let module QR {X} {Y} {Z} {W} = RS (Q.₀ ((X , Y) , Z , W))
        module PS {X} {Y} = Setoid (P.₀ (X , Y))
        module ΦS {X} {Y} {Z} {W} = Setoid (Φ.₀ ((X , Y) , Z , W))
        open QR {X} {Y} {Z} {W} in
      begin
        Q.₁ ((Δ.id , Γ.id) , f , g) $ γ.α (X , Y) $ (α.α (X , X , Y) $ Φ.₁ ((f , g) , Δ.id , Γ.id) $ x , Φ.₁ ((f , g) , Δ.id , Γ.id) $ x)
          ≈˘⟨ Func.cong (Q.₁ _) (Func.cong (γ.α (X , Y)) (P.identity (Func.cong (α.α (X , X , Y)) ([ Φ ]-merge (Δ.identityˡ , Γ.identityʳ) (Δ.identity² , Γ.identityʳ) ΦS.refl)) , ΦS.refl)) ⟩
        Q.₁ ((Δ.id , Γ.id) , f , g) $ γ.α (X , Y) $ (P.₁ (Δ.id , Δ.id) $ α.α (X , X , Y) $ Φ.₁ ((f , Γ.id) , Δ.id , Γ.id) $ Φ.₁ ((Δ.id , g) , Δ.id , Γ.id) $ x , Φ.₁ ((f , g) , Δ.id , Γ.id) $ x)
          ≈⟨ Func.cong (Q.₁ _) (Func.cong (γ.α (X , Y)) ((α.op-commute (f , Δ.id , Γ.id) ΦS.refl) , ΦS.refl)) ⟩
        Q.₁ ((Δ.id , Γ.id) , f , g) $ γ.α (X , Y) $ (P.₁ (f , Δ.id) $ α.α (Z , X , Y) $ Φ.₁ ((Δ.id , Γ.id) , Δ.id , Γ.id) $ Φ.₁ ((Δ.id , g) , Δ.id , Γ.id) $ x , Φ.₁ ((f , g) , Δ.id , Γ.id) $ x)
          ≈⟨ γ.commute (f , g) (Func.cong (α.α (Z , X , Y)) (Φ.identity (Func.cong (Φ.₁ ((Δ.id , g) , Δ.id , Γ.id)) e)) , e) ⟩
        Q.₁ ((f , g) , Δ.id , Γ.id) $ γ.α (Z , W) $ (P.₁ (Δ.id , f) $ α.α (Z , X , Y) $ Φ.₁ ((Δ.id , g) , Δ.id , Γ.id) $ y , Φ.₁ ((Δ.id , Γ.id) , f , g) $ y)
          ≈⟨ Func.cong (Q.₁ _) (Func.cong (γ.α (Z , W)) (α.commute (Δ.id , f , g) ΦS.refl , ΦS.refl)) ⟩
        Q.₁ ((f , g) , Δ.id , Γ.id) $ γ.α (Z , W) $ (P.₁ (Δ.id , Δ.id) $ α.α (Z , Z , W) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y , Φ.₁ ((Δ.id , Γ.id) , f , g) $ y)
          ≈⟨ Func.cong (Q.₁ _) (Func.cong (γ.α (Z , W)) (P.identity PS.refl , ΦS.refl)) ⟩
        Q.₁ ((f , g) , Δ.id , Γ.id) $ γ.α (Z , W) $ (α.α (Z , Z , W) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y , Φ.₁ ((Δ.id , Γ.id) ,  f , g) $ y) ∎ }
  } where
    module Γ = Category Γ
    module Δ = Category Δ
    module Φ = Functor Φ
    module Q = Functor Q
    module P = Functor P
    open module α = DinaturalTransformation α
    open module γ = DinaturalTransformation γ

cut-nat : ∀
  {Φ Q : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
  {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = Δ ⊗ Γ} Φ (P ∘F (v1 ∘F ctr  ※ v1 ∘F cov))
  → DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (SetA.-×- ∘F (P ∘F (v1 ∘F cov ※ v2 ∘F cov) -- v1 and v2 only covariant
                                       ※ Φ ∘F ((v2 ∘F ctr  ※ v3 ∘F ctr ) ※ v1 ∘F ctr  ※ v3 ∘F cov))) -- v1 and v2 only ctr variant
                            (Q ∘F ((v1 ∘F cov ※ v3 ∘F ctr ) ※ v2 ∘F cov ※ v3 ∘F cov)) -- v1 and v2 only covariant
  → DinaturalTransformation Φ Q
cut-nat {Δ = Δ} {Γ = Γ} {Φ = Φ} {Q} {P} γ α = dtHelper (record
  { α = λ { (X , Z) → record
    { to = λ p → α.α (X , X , Z) $ (γ.α (X , Z) $ p , p)
    ; cong = λ e → Func.cong (α.α (X , X , Z)) (Func.cong (γ.α (X , Z)) e , e)
    }  }
  ; commute = λ { {X , Y} {Z , W} (f , g) {x} {y} e →
    let module QR {X} {Y} {Z} {W} = RS (Q.₀ ((X , Y) , Z , W))
        module PS {X} {Y} = Setoid (P.₀ (X , Y))
        module ΦS {X} {Y} {Z} {W} = Setoid (Φ.₀ ((X , Y) , Z , W))
        open QR {X} {Y} {Z} {W} in
      begin
        Q.₁ ((Δ.id , Γ.id) , f , g) $ α.α (X , X , Y) $ (γ.α (X , Y) $ Φ.₁ ((f , g) , Δ.id , Γ.id) $ x , Φ.₁ ((f , g) , Δ.id , Γ.id) $ x)
          ≈˘⟨ Func.cong (Q.₁ _) (Func.cong (α.α _) (P.identity PS.refl , ΦS.refl)) ⟩
        Q.₁ ((Δ.id , Γ.id) , f , g) $ α.α (X , X , Y) $ (P.₁ (Δ.id , Δ.id) $ γ.α (X , Y) $ Φ.₁ ((f , g) , Δ.id , Γ.id) $ x , Φ.₁ ((f , g) , Δ.id , Γ.id) $ x)
          ≈⟨ α.commute (Δ.id , f , g) (PS.refl , ΦS.refl) ⟩
        Q.₁ ((Δ.id , g) , Δ.id , Γ.id) $ α.α (X , Z , W) $ (P.₁ (Δ.id , f) $ γ.α (X , Y) $ Φ.₁ ((f , g) , Δ.id , Γ.id) $ x , Φ.₁ ((Δ.id , Γ.id) , Δ.id , g) $ x)
          ≈˘⟨ Func.cong (Q.₁ _) (Q.identity (Func.cong (α.α _) (γ.op-commute (f , g) (ΦS.sym e) , Φ.identity (Func.cong (Φ.₁ _) (ΦS.sym e))))) ⟩
        Q.₁ ((Δ.id , g) , Δ.id , Γ.id) $ Q.₁ ((Δ.id , Γ.id) , Δ.id , Γ.id) $ α.α (X , Z , W) $ (P.₁ (f , Δ.id) $ γ.α (Z , W) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y , Φ.₁ ((Δ.id , Γ.id) , Δ.id , Γ.id) $ Φ.₁ ((Δ.id , Γ.id) , Δ.id , g) $ y)
          ≈⟨ Func.cong (Q.₁ _) (α.op-commute (f , Δ.id , Γ.id) (PS.refl , ΦS.refl)) ⟩
        Q.₁ ((Δ.id , g) , Δ.id , Γ.id) $ Q.₁ ((f , Γ.id) , Δ.id , Γ.id) $ α.α (Z , Z , W) $ (P.₁ (Δ.id , Δ.id) $ γ.α (Z , W) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y , Φ.₁ ((Δ.id , Γ.id) , f , Γ.id) $ Φ.₁ ((Δ.id , Γ.id) , Δ.id , g) $ y)
          ≈⟨ [ Q ]-merge (Δ.identityʳ , Γ.identityˡ) (Δ.identity² , Γ.identityʳ) (Func.cong (α.α _) (PS.refl , [ Φ ]-merge (Δ.identity² , Γ.identityʳ) (Δ.identityʳ , Γ.identityˡ) ΦS.refl)) ⟩
        Q.₁ ((f , g) , Δ.id , Γ.id) $ α.α (Z , Z , W) $ (P.₁ (Δ.id , Δ.id) $ γ.α (Z , W) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y , Φ.₁ ((Δ.id , Γ.id) , f , g) $ y)
          ≈⟨ Func.cong (Q.₁ _) (Func.cong (α.α _) (P.identity PS.refl , ΦS.refl)) ⟩
        Q.₁ ((f , g) , Δ.id , Γ.id) $ α.α (Z , Z , W) $ (γ.α (Z , W) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y , Φ.₁ ((Δ.id , Γ.id) , f , g) $ y) ∎ }
  })
  where
    module Γ = Category Γ
    module Δ = Category Δ
    module Φ = Functor Φ
    module Q = Functor Q
    module P = Functor P
    open module α = DinaturalTransformation α
    open module γ = DinaturalTransformation γ
