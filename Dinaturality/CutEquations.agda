{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  Equational theory for the two kinds of cuts.
-}

module Dinaturality.CutEquations where

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
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper; _∘>_) renaming (_≃_ to _≃ᵈ_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition renaming (function to _[⨾]_)
open import Relation.Binary.Bundles using (Setoid)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

open import Dinaturality.Cut

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

weaken-helper :  ∀ {Δ Γ : Category o ℓ e}
  {Φ : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
  {P Q : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → NaturalTransformation
      (SetA.-×- ∘F (Q ∘F (v1 ∘F cov ※ v2 ∘F cov) ※
        (SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)) ∘F
        ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov)))
      (SetA.-×- ∘F (Q ∘F (v1 ∘F cov ※ v2 ∘F cov) -- v1 and v2 only covariant
             ※ Φ ∘F ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov))) -- v1 and v2 only contravariant
weaken-helper {Φ = Φ} {Q = Q} = ntHelper record
  { η = λ X → < proj₁ₛ , proj₂ₛ  [⨾] proj₂ₛ >ₛ
  ; commute = λ { (f , g , h) (x , y , m) →
    Func.cong (F₁ Q _) x , Func.cong (F₁ Φ _) m }
  }

assoc-nat-din-nat : ∀ {Δ Γ : Category o ℓ e}
  {Φ R : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
  {P Q : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → {α : DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (Φ ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov)) -- v1 and v2 only covariant
                            (P ∘F (v1 ∘F cov ※ v2 ∘F cov))} -- v1 and v2 only covariant
  → {γ : DinaturalTransformation {C = Δ ⊗ Γ} (SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)) (Q ∘F (v1 ∘F contra ※ v1 ∘F cov))}
  → {β : DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (SetA.-×- ∘F (Q ∘F (v1 ∘F cov ※ v2 ∘F cov) -- v1 and v2 only covariant
                                       ※ Φ ∘F ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov))) -- v1 and v2 only contravariant
                            (R ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov))} -- v1 and v2 only covariant
  → (let -- weakening of β to add P as one of the hypotheses (since cut-nat requires the same Φ)
         β′ : DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                (SetA.-×- ∘F (Q ∘F (v1 ∘F cov ※ v2 ∘F cov) ※
                  (SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)) ∘F
                  ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov)))
                (R ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov))
         β′ = β ∘> weaken-helper {Φ = Φ} {P = P} {Q = Q})
  →  cut-din {Φ = Φ} {Q = R} {P = P} α
      (cut-nat {Φ = (SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ))} {Q = R} {P = Q} γ β′)
  ≃ᵈ cut-nat {Φ = Φ} {Q = R} {P = Q}
       (cut-din {Φ = Φ} {Q = Q ∘F (v1 ∘F contra ※ v1 ∘F cov)} {P = P} α γ) β
assoc-nat-din-nat {Φ = Φ} {R} {P} {Q} {α = α} {γ = γ} {β = β} e =
    Func.cong (β.α _) (Func.cong (γ.α _) (Func.cong (α.α _) e , e) , e)
  where
    module α = DinaturalTransformation α
    module γ = DinaturalTransformation γ
    module β = DinaturalTransformation β
