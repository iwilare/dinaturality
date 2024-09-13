module Dinaturality.MuteContext.NaturalDinatural where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid; SingletonSetoid-⊤)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.StrongDinatural using (StrongDinaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Categories.Object.Terminal using (Terminal)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong₂; trans; cong; sym)
open import Relation.Binary.Construct.Closure.Equivalence using (isEquivalence; EqClosure; setoid; return; join; map; gmap; fold; gfold)

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

F-swap : Functor (A ⊗ B ⊗ C) (B ⊗ A ⊗ C)
F-swap = assocˡ _ _ _ ∘F (Swap ⁂ idF) ∘F assocʳ _ _ _

F-reorder : Functor (op A ⊗ A ⊗ op B ⊗ C) (op (A ⊗ B) ⊗ A ⊗ C)
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

pointdinat⇒homnat : ∀ {o} {A : Category o ℓ ℓ} {H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
         → DinaturalTransformation (const SetT.⊤) H
         → NaturalTransformation Hom[ A ][-,-] H
pointdinat⇒homnat {A = A} {H = H} α = ntHelper record
  { η = λ { (X1 , X2) → record { to = λ x → H.₁ (id , x) $ α.α X1 $ * ; cong = λ eq → H.F-resp-≈ (A.refl , eq) HS.refl } }
  ; commute = λ { {X1 , X2} {Y1 , Y2} (f1 , f2) {x} {y} eq → let open RS (H.₀ (Y1 , Y2)) in
    begin H.F₁ (id , f2 ∘ x ∘ f1) $ α.α Y1 $ * ≈˘⟨ [ H ]-merge id-0 assoc-2 HS.refl ⟩
          H.F₁ (id , f2 ∘ x) $ H.F₁ (id , f1) $ α.α Y1 $ * ≈⟨ Func.cong (H.₁ _) (α.commute f1 *) ⟩
          H.₁ (id , f2 ∘ x) $ H.F₁ (f1 , id) $ α.α X1 $ * ≈⟨ [ H ]-resp-square (id-swap , assoc ∙ id-2 ∙ skip eq) HS.refl ⟩
          H.₁ (f1 , f2) $ H.F₁ (id , y) $ α.α X1 $ * ∎ }
  } where
    module α = DinaturalTransformation α
    module H = Functor H
    module HS {A} = Setoid (F₀ H A)
    open module A = Reason A

homnat⇒pointdinat : ∀ {o} {A : Category o ℓ ℓ} {H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
         → NaturalTransformation Hom[ A ][-,-] H
         → DinaturalTransformation (const SetT.⊤) H
homnat⇒pointdinat {A = A} {H = H} α = dtHelper record
  { α = λ X → record { to = λ { * → α.η (X , X) $ id } ; cong = λ * → HS.refl }
  ; commute = λ { {X} {Y} f {*} {*} * → let open RS (H.F₀ (X , Y)) in
    begin H.₁ (id , f) $ α.η (X , X) $ id ≈˘⟨ α.commute (id , f) A.refl ⟩
          α.η (X , Y) $ f ∘ id ∘ id ≈⟨ Func.cong (α.η _) id-swap-2 ⟩
          α.η (X , Y) $ id ∘ id ∘ f ≈⟨ α.commute (f , id) A.refl ⟩
          H.₁ (f , id) $ α.η (Y , Y) $ id ∎ }
  } where
    module α = NaturalTransformation α
    module H = Functor H
    module HS {A} = Setoid (F₀ H A)
    open module A = Reason A

iso1 : ∀ {o} {A : Category o ℓ ℓ} {H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
       (α : NaturalTransformation Hom[ A ][-,-] H)
     → pointdinat⇒homnat (homnat⇒pointdinat α) ≃ⁿ α
iso1 {A = A} {H = H} α {x1 , x2} {y} {w} eq = let open RS (H.₀ (x1 , x2)) in
  begin H.₁ (id , y) $ α.η (x1 , x1) $ id ≈˘⟨ α.commute (id , y) A.refl ⟩
        α.η (x1 , x2) $ y ∘ id ∘ id ≈⟨ Func.cong (α.η _) (id-2-1 ∙ eq) ⟩
        α.η (x1 , x2) $ w ∎
  where
    module α = NaturalTransformation α
    module H = Functor H
    module HS {A} = Setoid (F₀ H A)
    open module A = Reason A

iso2 : ∀ {o} {A : Category o ℓ ℓ} {H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
       (α : DinaturalTransformation (const SetT.⊤) H)
     → homnat⇒pointdinat (pointdinat⇒homnat α) ≃ᵈ α
iso2 {A = A} {H = H} α {X} {*} * = let open RS (H.₀ (X , X)) in
  begin H.F₁ (id , id) $ α.α X $ * ≈⟨ H.identity HS.refl ⟩
        α.α X $ * ∎
  where
    module α = DinaturalTransformation α
    module H = Functor H
    module HS {A} = Setoid (F₀ H A)
    open module A = Reason A
