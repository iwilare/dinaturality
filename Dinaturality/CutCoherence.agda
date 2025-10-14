{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  Equational theory for the two kinds of cuts -- coherence for din-cut and nat-cut for the case of naturals.
-}

module Dinaturality.CutCoherence where

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
open import Categories.Category.Product.Properties
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper; _<∘_; _∘>_) renaming (_≃_ to _≃ᵈ_)
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
open import Dinaturality.Product using (π₁; π₂)
open import Dinaturality.Reindexing using (reindexing)

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

-- In the semantics, the statement for coherence is essentially trivial, since both compositions
-- coincide. The important part shown here in the formalization is the fact that the signature
-- of cut-din and cut-nat can be massaged in such a way that the statement typechecks
-- only by 1. copying some hypotheses, 2. applying appropriate weakening operations,
-- 3. applying some trivial isomorphisms which are transparent in the syntax and on the pen-and-paper semantics.
-- The main difficulty in typechecking this is that we need to simplify functor compositions manually:
-- we do so by writing many helpers (which aid in readibility and typechecking speed) rather than using combinators,
-- since they compute.

-- This helper is only used in the coherence theorem below: this just simplifies some
-- compositions of functors. We prove it manually instead of using combinators for typechecking speed.
{-
simple-cov-convert-iso : ∀ {Δ Γ : Category o ℓ e}
    {Q : Functor Δ (Setoids ℓ ℓ)}
  → NaturalTransformation {C = op (op Δ ⊗ Δ ⊗ Γ) ⊗ op Δ ⊗ Δ ⊗ Γ}
    (Q ∘F v1 ∘F cov)
    ((Q ∘F cov) ∘F (v1 ∘F cov ※ v2 ∘F cov))
simple-cov-convert-iso {Q = Q} = ntHelper record
  { η = λ X → record { to = λ x → x ; cong = λ e → e }
  ; commute = λ { (f , g) x → Func.cong (F₁ Q f) x }
  } where
  module Q = Functor Q
    -}

-- This helper is only used in the coherence theorem below: this applies
-- weakening with P in the propositional context and simplifies composition of functors.
helper-coherence-prop-weaken : ∀ {Δ Γ : Category o ℓ e}
    {Φ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    {P Q : Functor Δ (Setoids ℓ ℓ)}
  → NaturalTransformation {C = op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ}
    (SetA.-×- ∘F ((Q ∘F cov) ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ SetA.-×- ∘F (P ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov))))
    (SetA.-×- ∘F (Q ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov)))
helper-coherence-prop-weaken {Φ = Φ} {P = P} {Q = Q} = ntHelper record
  { η = λ X → record
    { to = λ { (q , p , f) → (q , f) }
    ; cong = λ { (q , p , f) → q , f }
    }
  ; commute = λ { _ (q , p , f) → Func.cong (Q.₁ _) q , Func.cong (Φ.₁ _) f }
  } where
  module Φ = Functor Φ
  module P = Functor P
  module Q = Functor Q

-- This helper is only used to lift α in the correct context in a single step, saving on typechecking time:
-- this applies weakening in the terms context to add an extra op Δ (which is assumed in cuts, but here is not used since it's natural),
-- and simplifies the functor composition in both hypothesis and conclusion.
-- This helper could be reimplemented using reindexing to weaken everything appropriately, at the
-- cost of having to manually simplify functor compositions.
helper-coherence-ctx-weaken-left-side : ∀ {Δ Γ : Category o ℓ e}
    {Φ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    {P Q : Functor Δ (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = Δ ⊗ Γ}
    (SetA.-×- ∘F (P ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov)))
      (Q ∘F va ∘F cov)
  → DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
      ((SetA.-×- ∘F (P ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov)))
                 ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov))
      ((Q ∘F cov) ∘F (v1 ∘F cov ※ v2 ∘F cov))
helper-coherence-ctx-weaken-left-side {Φ = Φ} {P = P} {Q = Q} α = dtHelper record
  { α = λ { (X , Y , Z) → record { to = λ x → α.α (Y , Z) $ x ; cong = Func.cong (α.α _) } }
  ; commute = λ { (f , g , h) e → α.commute (g , h) e }
  } where
  module Φ = Functor Φ
  module P = Functor P
  module Q = Functor Q
  module α = DinaturalTransformation α

-- Simple isomorphism to simplify composition of projections.
-- Could be implemented directly using combinators, kept here for readibility.
helper-coherence-simple-cov-iso : ∀ {Δ Γ : Category o ℓ e}
    {Q : Functor Δ (Setoids ℓ ℓ)}
  → NaturalTransformation {C = op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ} (Q ∘F va ∘F cov) ((Q ∘F cov) ∘F (v1 ∘F contra ※ v1 ∘F cov))
helper-coherence-simple-cov-iso {Q = Q} = ntHelper record
  { η = λ X → record { to = λ x → x ; cong = λ e → e }
  ; commute = λ { (f , g) x → Func.cong (Q.₁ _) x }
  } where
  module Q = Functor Q

-- This helper is only used to lift α in the correct context in a single step, saving on typechecking time:
-- this applies weakening in the terms context to add an extra op Δ (which is assumed in cuts, but here is not used since it's natural),
-- and simplifies the functor composition in both hypothesis and conclusion, and adds an extra P in the propositional context.
helper-coherence-ctx-prop-weaken-right-side : ∀ {Δ Γ : Category o ℓ e}
    {Φ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    {P Q R : Functor Δ (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = Δ ⊗ Γ} (SetA.-×- ∘F (Q ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov))) (R ∘F va ∘F cov)
  → DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
      (SetA.-×- ∘F ((Q ∘F cov) ∘F (v1 ∘F cov ※ v2 ∘F cov) ※
      (SetA.-×- ∘F (P ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov)))
         ∘F ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov)))
      ((R ∘F va ∘F cov) ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov))
helper-coherence-ctx-prop-weaken-right-side {Φ = Φ} {P = P} {Q = Q} {R = R} β = dtHelper record
  { α = λ { (X , Y , Z) → record
    { to = λ { (p , q , r) → β.α (Y , Z) $ (p , r) }
    ; cong = λ { (p , q , r) → Func.cong (β.α _) (p , r) }
    } }
  ; commute = λ { (f , g , h) (p , q , r) → β.commute (g , h) (p , r) }
  } where
  module Φ = Functor Φ
  module P = Functor P
  module Q = Functor Q
  module R = Functor R
  module β = DinaturalTransformation β

-- In the semantics this statement is essentially trivial: the important aspect of this theorem is to show
-- that the signature of cut-din and cut-nat can be massaged in such a way that the statement typechecks
-- only by appropriately 1. copying some hypotheses, 2. applying weakening operations,
-- 3. applying some trivial isomorphisms which are transparent in the syntax and on the pen-and-paper semantics.
cut-coherence : ∀ {Δ Γ : Category o ℓ e}
    {Φ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    {P Q R : Functor Δ (Setoids ℓ ℓ)}
  → {α : DinaturalTransformation {C = Δ ⊗ Γ} (SetA.-×- ∘F (P ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov))) (Q ∘F va ∘F cov)}
  → {β : DinaturalTransformation {C = Δ ⊗ Γ} (SetA.-×- ∘F (Q ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov))) (R ∘F va ∘F cov)}
  → cut-din {Φ = SetA.-×- ∘F (P ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov))} {Q = R ∘F va ∘F cov} {P = Q ∘F cov}
         (helper-coherence-ctx-weaken-left-side {Φ = Φ} {P = P} {Q = Q} α)
         (β ∘> helper-coherence-prop-weaken {Φ = Φ} {P = P} {Q = Q})
          ≃ᵈ
    cut-nat {Φ = SetA.-×- ∘F (P ∘F va ∘F cov ※ Φ ∘F (vb ∘F contra ※ vb ∘F cov))} {Q = R ∘F va ∘F cov} {P = Q ∘F cov}
         (helper-coherence-simple-cov-iso {Q = Q} <∘ α)
         (helper-coherence-ctx-prop-weaken-right-side {Φ = Φ} {P = P} {Q = Q} {R = R} β)
cut-coherence {Δ = Δ} {Γ = Γ} {Φ = Φ} {P} {Q} {R} {α = α} {β = β} (p , q) = Func.cong (β.α _) (Func.cong (α.α _) (p , q) , q)
  where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module Δ = Reason Δ
    module Φ = Functor Φ
    module P = Functor P
    module Q = Functor Q
    module ΦS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)
    module QS {A} = Setoid (F₀ Q A)
