{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
  Equational theory for the two kinds of cuts -- left and right identity for both kinds of cuts.
-}

module Dinaturality.CutIdentities where

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

-- Helper used to get rid of functor compositions.
-- Up to naturally isomorphic functors, this is just the projection Q x P x Φ → Q x Φ.
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
  ; commute = λ { (f , g , h) (x , y , m) → Func.cong (F₁ Q _) x , Func.cong (F₁ Φ _) m }
  }

-- Helper to collapse (i.e. via dinatural collapse) x and y in a dinatural with shape
--      P(x,y,¬z,z) x Φ(¬x,¬y,¬z,z) → Q(x,y)
-- to one
--      P(¬w,w,¬z,z) x Φ(w,¬w,¬z,z) → Q(¬w,w)
-- This helper could be defined using reindexing: we write it out explicitly because reindexing takes
-- takes too much time to compile, and the functor obtained is only isomorphic to the one needed later.
collapse-helper : ∀ {Δ Γ : Category o ℓ e}
    {Φ Q : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
    {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (SetA.-×- ∘F (P ∘F (v1 ∘F cov ※ v2 ∘F cov) -- v1 and v2 only covariant
                                       ※ Φ ∘F ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov))) -- v1 and v2 only contravariant
                            (Q ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov)) -- v1 and v2 only covariant
  → DinaturalTransformation (SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)) Q
collapse-helper {Δ = Δ} {Γ} {Φ} {Q} {P} β = dtHelper record
  { α = λ { (D , G) → record { to = λ { (p , k) → β.α (D , D , G) $ (p , k) } ; cong = λ { (e , q) → Func.cong (β.α _) (e , q) } } }
  ; commute = λ { {X , Y} {Z , W} (f , g) {x , y} {z , w} (e , q) → let open RS (Q.₀ ((X , Y) , (Z , W))) in
   begin Q.₁ ((Δ.id , Γ.id) , f , g) $ β.α (X , X , Y) $ (P.₁ (f , Δ.id) $ x , Φ.₁ ((f , g) , Δ.id , Γ.id) $ y) ≈˘⟨ Func.cong (Q.₁ _) (Func.cong (β.α _) (P.identity PS.refl , ΦS.refl)) ⟩
         Q.₁ ((Δ.id , Γ.id) , f , g) $ β.α (X , X , Y) $ (P.₁ (Δ.id , Δ.id) $ P.₁ (f , Δ.id) $ x , Φ.₁ ((f , g) , Δ.id , Γ.id) $ y) ≈⟨ β.commute (Δ.id , f , g) (PS.refl , q) ⟩
         Q.₁ ((Δ.id , g) , Δ.id , Γ.id) $ β.α (X , Z , W) $ (P.₁ (Δ.id , f) $ P.₁ (f , Δ.id) $ x , Φ.₁ ((Δ.id , Γ.id) , Δ.id , g) $ w) ≈⟨ Func.cong (Q.₁ _) (Func.cong (β.α _) ([ P ]-commute e , ΦS.refl)) ⟩
         Q.₁ ((Δ.id , g) , Δ.id , Γ.id) $ β.α (X , Z , W) $ (P.₁ (f , Δ.id) $ P.₁ (Δ.id , f) $ z , Φ.₁ ((Δ.id , Γ.id) , Δ.id , g) $ w) ≈˘⟨ Func.cong (Q.₁ _) (Q.identity ((Func.cong (β.α _) (PS.refl , Φ.identity ΦS.refl)))) ⟩
         Q.₁ ((Δ.id , g) , Δ.id , Γ.id) $ Q.₁ ((Δ.id , Γ.id) , Δ.id , Γ.id) $ β.α (X , Z , W) $ (P.₁ (f , Δ.id) $ P.₁ (Δ.id , f) $ z , Φ.₁ ((Δ.id , Γ.id) , Δ.id , Γ.id) $ Φ.₁ ((Δ.id , Γ.id) , Δ.id , g) $ w) ≈⟨ Func.cong (Q.₁ _) (β.op-commute (f , Δ.id , Γ.id) (PS.refl , ΦS.refl)) ⟩
         Q.₁ ((Δ.id , g) , Δ.id , Γ.id) $ Q.₁ ((f , Γ.id) , Δ.id , Γ.id) $ β.α (Z , Z , W) $ (P.₁ (Δ.id , Δ.id) $ P.₁ (Δ.id , f) $ z , Φ.₁ ((Δ.id , Γ.id) , f , Γ.id) $ Φ.₁ ((Δ.id , Γ.id) , Δ.id , g) $ w) ≈⟨ [ Q ]-merge (Δ.identityʳ  , Γ.identityˡ) (Δ.identity² , Γ.identity²) (Func.cong (β.α _) (P.identity PS.refl , [ Φ ]-merge (Δ.identity² , Γ.identity²) (Δ.identityʳ  , Γ.identityˡ) ΦS.refl)) ⟩
         Q.₁ ((f , g) , Δ.id , Γ.id) $ β.α (Z , Z , W) $ (P.₁ (Δ.id , f) $ z , Φ.₁ ((Δ.id , Γ.id) , f , g) $ w) ∎
   }
  } where
    module β = DinaturalTransformation β
    module Γ = Reason Γ
    module Δ = Reason Δ
    module Φ = Functor Φ
    module P = Functor P
    module Q = Functor Q
    module ΦS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)
    module QS {A} = Setoid (F₀ Q A)

{-
-- version with reindexing
collapse-helper : ∀ {Δ Γ : Category o ℓ e}
    {Φ Q : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
    {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (SetA.-×- ∘F (P ∘F (v1 ∘F cov ※ v2 ∘F cov) -- v1 and v2 only covariant
                                       ※ Φ ∘F ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov))) -- v1 and v2 only contravariant
                            (Q ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov)) -- v1 and v2 only covariant
  → DinaturalTransformation
      ((SetA.-×- ∘F
        (P ∘F (v1 ∘F cov ※ v2 ∘F cov) ※
         Φ ∘F ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov)))
       ∘F
       (Functor.op (va ∘F contra ※ va ∘F cov ※ vb ∘F cov) ∘F Swap ※
        va ∘F contra ※ va ∘F cov ※ vb ∘F cov))
      ((Q ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov)) ∘F
       (Functor.op (va ∘F contra ※ va ∘F cov ※ vb ∘F cov) ∘F Swap ※
        va ∘F contra ※ va ∘F cov ※ vb ∘F cov))
collapse-helper β = reindexing (va ∘F contra ※ va ∘F cov ※ vb ∘F cov) β
-}

----------------------------- cut-nat identities ---------------------------

-- Precomposing with π : (SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)) (P ∘F (v1 ∘F contra ※ v1 ∘F cov))
-- is equivalent to simply collapse naturality to dinaturality.
-- Again, β needs to be weakened to add P as one of the hypotheses (since cuts require the same Φ)
cut-nat-idˡ : ∀ {Δ Γ : Category o ℓ e}
  {Φ Q : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
  {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → {β : DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (SetA.-×- ∘F (P ∘F (v1 ∘F cov ※ v2 ∘F cov) -- v1 and v2 only covariant
                                       ※ Φ ∘F ((v2 ∘F contra ※ v3 ∘F contra) ※ v1 ∘F contra ※ v3 ∘F cov))) -- v1 and v2 only contravariant
                            (Q ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov))} -- v1 and v2 only covariant
  → cut-nat {Φ = SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)} {Q = Q} {P = P}
            π₁
            (β ∘> weaken-helper {Φ = Φ} {P = P} {Q = P})
  ≃ᵈ collapse-helper β
cut-nat-idˡ {Φ = Φ} {Q} {P} {β = β} e = Func.cong (β.α _) e
  where
    module β = DinaturalTransformation β

-- Helper to deal with simplifications of projections. This is a natural *isomorphism*.
iso-helper : ∀ {Δ Γ : Category o ℓ e}
    (P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ))
  → NaturalTransformation {C = op (op Δ ⊗ Δ ⊗ Γ) ⊗ op Δ ⊗ Δ ⊗ Γ} (P ∘F (v1 ∘F cov ※ v2 ∘F cov))
      ((P ∘F (v1 ∘F contra ※ v1 ∘F cov)) ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov))
iso-helper P = ntHelper record
  { η = λ X → record { to = λ x → x ; cong = λ x → x }
  ; commute = λ x e → Func.cong (P.₁ _) e
  } where
  module P = Functor P

cut-nat-idʳ : ∀ {Δ Γ : Category o ℓ e}
    {Φ : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
    {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → {γ : DinaturalTransformation {C = Δ ⊗ Γ} Φ (P ∘F (v1 ∘F contra ※ v1 ∘F cov))} -- v1 and v2 only covariant
  → cut-nat {Φ = Φ} {Q = P ∘F (v1 ∘F contra ※ v1 ∘F cov)} {P = P} γ
      (iso-helper P <∘ π₁ {P = P ∘F (v1 ∘F cov ※ v2 ∘F cov)})
  ≃ᵈ γ
cut-nat-idʳ {Φ = Φ} {P} {γ = γ} = Func.cong (γ.α _)
  where
    module γ = DinaturalTransformation γ

----------------------------- cut-din identities ---------------------------

-- Helper to collapse (i.e. via dinatural collapse) x and y in a dinatural with shape
--      Φ(x,y,¬z,z) → P(x,y)
-- to one
--      Φ(w,¬w,¬z,z) → P(¬w,w)
-- This helper could be defined using reindexing: we write it out explicitly because reindexing takes
-- takes too much time to compile, and the functor obtained is only isomorphic to the one needed later.
collapse-helper-simple : ∀ {Δ Γ : Category o ℓ e}
    {Φ : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
    {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (Φ ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov)) -- v1 and v2 only covariant
                            (P ∘F (v1 ∘F cov ※ v2 ∘F cov))
  → DinaturalTransformation {C = Δ ⊗ Γ} Φ (P ∘F (v1 ∘F contra ※ v1 ∘F cov))
collapse-helper-simple {Δ = Δ} {Γ} {Φ} {P} β = dtHelper record
  { α = λ { (D , G) → record { to = λ { v → β.α (D , D , G) $ v } ; cong = λ { v → Func.cong (β.α _) v } } }
  ; commute = λ { {X , Y} {Z , W} (f , g) {x} {y} e →
  let open RS (P.₀ (X , Z)) in
  begin P.₁ (Δ.id , f) $ β.α (X , X , Y) $ Φ.₁ ((f , g) , Δ.id , Γ.id) $ x ≈˘⟨ Func.cong (P.₁ _) (Func.cong (β.α _) ([ Φ ]-merge (Δ.identityʳ , Γ.identityˡ) (Δ.identity² , Γ.identity²) ΦS.refl)) ⟩
        P.₁ (Δ.id , f) $ β.α (X , X , Y) $ Φ.₁ ((Δ.id , g) , Δ.id , Γ.id) $ Φ.₁ ((f , Γ.id) , Δ.id , Γ.id) $ x ≈⟨ β.commute (Δ.id , f , g) ΦS.refl ⟩
        P.₁ (Δ.id , Δ.id) $ β.α (X , Z , W) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ Φ.₁ ((f , Γ.id) , Δ.id , Γ.id) $ x ≈⟨ Func.cong (P.₁ _) (Func.cong (β.α _) ([ Φ ]-resp-square (((Δ.id-swap {f = f} , Γ.Equiv.refl) , Δ.id-swap {f = f} , Γ.id-swap {f = g})) e)) ⟩
        P.₁ (Δ.id , Δ.id) $ β.α (X , Z , W) $ Φ.₁ ((f , Γ.id) , Δ.id , Γ.id) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y ≈⟨ β.op-commute (f , Δ.id , Γ.id) ΦS.refl ⟩
        P.₁ (f , Δ.id) $ β.α (Z , Z , W) $ Φ.₁ ((Δ.id , Γ.id) , Δ.id , Γ.id) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y ≈⟨ Func.cong (P.₁ _) (Func.cong (β.α _) (Φ.identity ΦS.refl)) ⟩
        P.₁ (f , Δ.id) $ β.α (Z , Z , W) $ Φ.₁ ((Δ.id , Γ.id) , f , g) $ y ∎
  }
  } where
    module β = DinaturalTransformation β
    module Γ = Reason Γ
    module Δ = Reason Δ
    module Φ = Functor Φ
    module P = Functor P
    module ΦS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)

cut-din-idʳ : ∀ {Δ Γ : Category o ℓ e}
    {Φ : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
    {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → {α : DinaturalTransformation {C = op Δ ⊗ Δ ⊗ Γ}
                            (Φ ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov)) -- v1 and v2 only covariant
                            (P ∘F (v1 ∘F cov ※ v2 ∘F cov))} -- v1 and v2 only covariant
  → cut-din {Φ = Φ} {Q = P ∘F (πˡ ∘F πˡ ※ πˡ ∘F πʳ)} α π₁ ≃ᵈ collapse-helper-simple {Φ = Φ} {P = P} α
cut-din-idʳ {Φ = Φ} {P} {α = α} = Func.cong (α.α _)
  where
    module α = DinaturalTransformation α

-- Natural isomorphism helper used to propagate projections into a product.
helper-product-iso : ∀ {Δ Γ : Category o ℓ e}
    {Φ : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
    {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → NaturalTransformation {C = op (op Δ ⊗ Δ ⊗ Γ) ⊗ op Δ ⊗ Δ ⊗ Γ}
      ((SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)) ∘F
       ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov))
      (SetA.-×- ∘F (P ∘F (v1 ∘F cov ※ v2 ∘F cov) ※ Φ ∘F ((v1 ∘F cov ※ v3 ∘F contra) ※ v2 ∘F cov ※ v3 ∘F cov)))
helper-product-iso {Δ = Δ} {Γ} {Φ} {P} = ntHelper record
  { η = λ X → record { to = λ x → x ; cong = λ e → e }
  ; commute = λ { x (p , q) → Func.cong (P.₁ _) p , Func.cong (Φ.₁ _) q }
  } where
  module P = Functor P
  module Φ = Functor Φ

helper-project-simple : ∀ {Γ : Category o ℓ e}
    {Φ P Q : Functor Γ (Setoids ℓ ℓ)}
  → NaturalTransformation
      (SetA.-×- ∘F (P ※ SetA.-×- ∘F (Q ※ Φ)))
      (SetA.-×- ∘F (P ※ Φ))
helper-project-simple {Φ = Φ} {P = P} {Q = Q} = ntHelper record
  { η = λ X → < proj₁ₛ , proj₂ₛ [⨾] proj₂ₛ >ₛ
  ; commute = λ { _ (x , y , m) → Func.cong (F₁ P _) x , Func.cong (F₁ Φ _) m }
  } where
  module P = Functor P
  module Φ = Functor Φ

-- Similarly as with other theorems, we need to duplicate one of the hypotheses because the cut rules
-- ask for the context Φ to be the same in both entailments. For this case the identity natural has as shape
--     P(x,y) x Φ′(¬x,x,¬z,z) → P(x,y) x
-- hence Φ := P(x,y) x Φ′(¬x,x,¬z,z) must be defined to include P, and γ must be weakened accordingly.
cut-din-idˡ : ∀ {Δ Γ : Category o ℓ e}
    {Φ Q : Functor (op (Δ ⊗ Γ) ⊗ Δ ⊗ Γ) (Setoids ℓ ℓ)}
    {P : Functor (op Δ ⊗ Δ) (Setoids ℓ ℓ)}
  → {γ : DinaturalTransformation {C = Δ ⊗ Γ} (SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)) Q}
  → cut-din {Φ = SetA.-×- ∘F (P ∘F (v1 ∘F contra ※ v1 ∘F cov) ※ Φ)} {Q = Q} {P = P}
           (π₁ ∘> helper-product-iso {Φ = Φ} {P = P})
           (γ ∘> helper-project-simple {Φ = Φ} {P = P ∘F (πˡ ∘F πˡ ※ πˡ ∘F πʳ)} {Q = P ∘F (πˡ ∘F πˡ ※ πˡ ∘F πʳ)})
  ≃ᵈ γ
cut-din-idˡ {Φ = Φ} {P} {γ = γ} = Func.cong (γ.α _)
  where
    module γ = DinaturalTransformation γ
