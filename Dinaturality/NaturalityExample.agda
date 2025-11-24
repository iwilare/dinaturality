{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  We show here an example of naturality for rule isomorphisms.

  In our formalization, we only formally prove naturality (in the dipresheaves)
  for the rules for implications (exp) and (exp⁻¹).

  Naturality for other rules is particularly easy to verify on paper, (all rules
  defined here are defined parametrically in each of the dipresheaves given),
  but it is not as feasible to verify fully formally the rest of the maps for the rules;
  in particular, the maps for the (J) and (J⁻¹) rules and those for (co)ends have
  particularly long compilation times and extremely high memory consumption, which
  makes even providing a statement for naturality not practical for a fully formal verification.

  In particular we show here that the (exp) and (exp⁻¹) rules form a natural isomorphism.
  We choose to focus on this example because the underlying map is the fastest to typecheck,
  and to sketch the general approach, which applies to all rules.

  ---------------------------------------------------------------------------------

  The idea to formalize this is to lift the rules in terms of natural maps in functor categories, where
  each construction (e.g., pointwise products of dipresheaves, pointwise exponentials of dipresheaves)
  are taken to be functors.

  The main technical aspect of this proof is the fact that we use the `Dinats` functor,
  defined in `Dinaturality/DinaturalsFunctor.agda`, which is the functor sending two
  dipresheaves A, B to the set of dinatural transformations between them. Crucially,
  this admits an action on morphisms (on functor categories) precisely because naturals
  compose with dinaturals.

  In particular, to show this rule as a natural isomorphism we essentially show that the two functors,
  inhabiting the functor categories [[Γᵒᵖ×Γ,Set]ᵒᵖ × [Γᵒᵖ×Γ,Set]ᵒᵖ × [Γᵒᵖ×Γ,Set],Set],

  Dinat(- x =, ≡) ≅ Dinat(=, -ᵒᵖ ⇒ ≡)

  are isomorphic (where isomorphisms in functor categories are taken to be natural isomorphisms,
  as in `agda-categories`). We indicate with -,=,≡ the placeholders for difunctors, with
  ∙ x ∙ the functor computing the pointwise product of presheaves, with ∙ ⇒ ∙
  the functor computing the pointwise exponential is the pointwise exponential of presheaves,
  and ᵒᵖ is the operation sending a functor to its opposite *seen as a functor*.
  Note that this isomorphism is ctr variant in the first two arguments (since they appear
  on the left of the dinaturality functor) and covariant in the last.
-}

module Dinaturality.NaturalityExample where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry; opF⇐; opF⇒)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cocartesian)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC; Setoids-Cocomplete)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
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
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})

module _ {ℓ} (Γ : Category ℓ ℓ ℓ) where

  -- We need to fetch the proof that the category of presheaves is cartesian.
  open import Categories.Category.Construction.Properties.Presheaves.CartesianClosed

  -- this extra op is necessary since we have presheaves and not copresheaves.
  open IsCartesianClosed (op (op Γ ⊗ Γ))

  -- We need to be extremely careful! This module contains the exponential of presheaves, which is NOT the pointwise one.
  module PCCC = CartesianClosed Presheaves-CartesianClosed
  module PC = Cartesian PCCC.cartesian
  -- Pointwise products of presheaves *as functor*.
  module PBP = BinaryProducts PC.products

  -- We need to manually define the pointwise exponential of dipresheaves.
  PointwiseHom : Functor (op (Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ))
                           ⊗ Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ))
                         (Functors (Product (op Γ) Γ) (Setoids ℓ ℓ))
  PointwiseHom = record
    { F₀ = λ { (A , B) → Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B) }
    ; F₁ = λ { {A1 , A2} {B1 , B2} (f , g) →
      let module f = NaturalTransformation f
          module g = NaturalTransformation g in
      ntHelper record
        { η = λ { (X1 , X2) → record
          { to = λ k → record
            { to = λ q → g.η (X1 , X2) $ k $ f.η (X2 , X1) $ q
            ; cong = λ eq → Func.cong (g.η _) (Func.cong k (Func.cong (f.η _) eq))
            }
          ; cong = λ eq eqs → Func.cong (g.η _) (eq (Func.cong (f.η _) eqs))
          } }
        ; commute = λ f eq eqs → g.commute _ (eq (f.sym-commute _ eqs))
        }
      }
    ; identity = λ eq eqs → eq eqs
    ; homomorphism = λ { {_} {_} {_} {f₁ , g₁} {f₂ , g₂} eq eqs →
      Func.cong (NaturalTransformation.η g₂ _)
        (Func.cong (NaturalTransformation.η g₁ _) (eq
          (Func.cong (NaturalTransformation.η f₁ _)
            (Func.cong (NaturalTransformation.η f₂ _) eqs)))) }
    ; F-resp-≈ = λ { (eq₁ , eq₂) eq eqs → eq₂ (eq (eq₁ eqs)) }
    }

  {-
    In order to state the isomorphism, it is crucial to use
    the `Dinats` functor, which is the functor sending two dipresheaves
    A, B to the set of dinatural transformations between them: this is
    a functor defined on functor categories where morphisms are *naturals*;
    and so it is well-defined because naturals compose with dinaturals.
  -}
  open import Dinaturality.DinaturalsFunctor using (Dinats)

  -- Rules for implication and the proof that they are isomorphisms.
  open import Dinaturality.Implication using (lambda; lambda⁻¹; lambda⁻¹⨟lambda-iso; lambda⨟lambda⁻¹-iso)

  -- The next implicit arguments to Dinat are needed because of --lossy-unification.

  -- The functor given by (A, B, Φ) ↦ Dinat(A × B, Φ), ctr variant in A, B, and covariant in Φ.
  -- Crucially, we use here the `PBP.-×-` which, as a whole, is the pointwise product of presheaves.
  -- The signature of `PBP.-×-` is `Functor (C ⊗ C) C` where C := Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ).
  functor-↑ : Functor ((op (Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ))
                     ⊗ op (Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ)))
                     ⊗     Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ))
                  (Setoids (sucℓ ℓ) ℓ)
  functor-↑ = Dinats {Γ = Γ} {Δ = Setoids ℓ ℓ} ∘F (Functor.op PBP.-×- ∘F πˡ ※ πʳ)

  -- The functor given by (A, B, Φ) ↦ Dinat(B, Fᵒᵖ ⇒ Φ), ctr variant in A, B, and covariant in Φ.
  functor-↓ : Functor ((op (Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ))
                     ⊗ op (Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ)))
                     ⊗    Functors (op Γ ⊗ Γ) (Setoids ℓ ℓ))
                  (Setoids (sucℓ ℓ) ℓ)
  functor-↓ = Dinats {Γ = Γ} {Δ = Setoids ℓ ℓ} ∘F (πʳ ∘F πˡ ※ PointwiseHom ∘F (πˡ ∘F πˡ ※ πʳ))

  -- There is a natural isomorphism between the above functors.
  iso : NaturalIsomorphism functor-↑ functor-↓
  iso = niHelper record
    { η = λ { ((A , Φ) , B) → record
      { to = λ α → lambda {A = A} {B = B} {Φ = Φ} α
      ; cong = λ eq eq₁ eq₂ → eq (eq₂ , eq₁)
      } }
    ; η⁻¹ = λ { ((A , Φ) , B) → record
      { to = λ α → lambda⁻¹ {A = A} {B = B} {Φ = Φ} α
      ; cong = λ { eq (eq₁ , eq₂) → eq eq₂ eq₁ }
      } }
    ; commute = λ { ((f , g) , h) eq eq₁ eq₂ →
      -- This is the naturality statement itself.
      -- Naturality is trivial to prove, essentially because in Setoid
      -- everything computes down and the only thing left to prove is the fact that
      -- a certain function respects the setoid equality.
      Func.cong (NaturalTransformation.η h _) (eq (Func.cong (NaturalTransformation.η f _) eq₂
                                                , (Func.cong (NaturalTransformation.η g _) eq₁))) }
      -- It is simply faster to write the proof by hand instead of using the
      -- previously proven isos because they have a different structure.
    ; iso = λ X → record
      -- As above, the actual isomorphism is trivial to prove because of computation
      -- in Setoid, where we only need to propagate setoid equalities.
      { isoˡ = λ { {α} {β} eq (eq₁ , eq₂) → eq (eq₁ , eq₂) }
      ; isoʳ = λ { {α} {β} eq eq₁ eq₂ → eq eq₁ eq₂ }
      }
    }
