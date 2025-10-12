{-# OPTIONS --safe --without-K #-}

{-
  We validate the rules for coends, and prove that they are isomorphisms.

  We do not prove naturality here, although it is easy to
  check given the parametric way in which the maps below are defined.

  (This file is particularly slow to typecheck.)
-}

module Dinaturality.Coend where

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

open import Relation.Binary.Construct.Closure.Equivalence using (isEquivalence; EqClosure; setoid; return; join; map; gmap; fold; gfold)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

open import Dinaturality.CoendFunctor using (coendFunctor; Dinaturality; convert)

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

coendL : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {Φ : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → DinaturalTransformation Φ (P ∘F (Functor.op πʳ ∘F πˡ ※ πʳ ∘F πʳ))
    → DinaturalTransformation (coendFunctor (Φ ∘F F-reorder)) P
coendL {A = A} {Γ = Γ} {Φ = Φ} {P = P} α = dtHelper (record
      { α = λ X → record
        { to = λ { (A , p) → α.α (A , X) $ p }
        ; cong =
          λ { {A , px} {B , py} eq →
          gfold {S = Setoid._≈_ (P.F₀ (X , X)) } {R = Dinaturality (Φ ∘F F-reorder) (X , X)}
                (Setoid.isEquivalence (P.₀ (X , X)))
                (λ { (Y , p) → α.α (Y , X) $ p })
                (λ { {YY , yy} {XX , xx} (w1 , w2 , w3 , w4) →
                  let open RS (P.₀ (X , X)) in
                  begin α.α (YY , X) $ yy ≈⟨ Func.cong (α.α (YY , X)) w3 ⟩
                        α.α (YY , X) $ Φ.₁ ((w1 , Γ.id) , id , Γ.id) $ w2 ≈˘⟨ P.identity PS.refl ⟩
                        P.₁ (Γ.id , Γ.id) $ α.α (YY , X) $ Φ.₁ ((w1 , Γ.id) , id , Γ.id) $ w2 ≈⟨ α.commute (w1 , Γ.id) ZS.refl ⟩
                        P.₁ (Γ.id , Γ.id) $ α.α (XX , X) $ Φ.₁ ((id , Γ.id) , w1 , Γ.id) $ w2 ≈⟨ P.identity PS.refl ⟩
                        α.α (XX , X) $ Φ.F₁ ((id , Γ.id) , w1 , Γ.id) $ w2 ≈˘⟨ Func.cong (α.α (XX , X)) w4 ⟩
                        α.α (XX , X) $ xx ∎ }) eq
          }
        }
      ; commute =
      λ { {X} {Y} f {x , xp} {y , yp} eq →
          let congruence = gfold {R = Dinaturality (Φ ∘F F-reorder) (Y , X)}
                   (Setoid.isEquivalence (P.₀ (Y , Y)))
                   (λ { (Φ , zz) → α.α (Φ , Y) $ Φ.₁ ((id , Γ.id) , id , f) $ zz })
                   (λ { {YY , yy} {XX , xx} (w1 , w2 , w3 , w4) →
                       let open RS (P.₀ (Y , Y)) in
                        begin α.α (YY , Y) $ Φ.₁ ((id , Γ.id) , id , f) $ yy ≈⟨ Func.cong (α.α _) (Func.cong (Φ.₁ _) w3) ⟩
                              α.α (YY , Y) $ Φ.₁ ((id , Γ.id) , id , f) $ Φ.F₁ ((w1 , Γ.id) , id , Γ.id) $ w2 ≈⟨ Func.cong (α.α _) ([ Φ ]-commute ZS.refl) ⟩
                              α.α (YY , Y) $ Φ.₁ ((w1 , Γ.id) , id , Γ.id) $ Φ.F₁ ((id , Γ.id) , id , f) $ w2 ≈˘⟨ P.identity PS.refl ⟩
                              P.₁ (Γ.id , Γ.id) $ α.α (YY , Y) $ Φ.₁ ((w1 , Γ.id) , id , Γ.id) $ Φ.F₁ ((id , Γ.id) , id , f) $ w2 ≈⟨ α.commute (w1 , Γ.id) ZS.refl ⟩
                              P.₁ (Γ.id , Γ.id) $ α.α (XX , Y) $ Φ.₁ ((id , Γ.id) , w1 , Γ.id) $ Φ.₁ ((id , Γ.id) , id , f) $ w2 ≈⟨ P.identity PS.refl ⟩
                              α.α (XX , Y) $ Φ.₁ ((id , Γ.id) , w1 , Γ.id) $ Φ.₁ ((id , Γ.id) , id , f) $ w2 ≈˘⟨ Func.cong (α.α _) ([ Φ ]-resp-square ((Equiv.refl , Γ.refl) , sym-id-swap , Γ.id-swap) ZS.refl) ⟩
                              α.α (XX , Y) $ Φ.₁ ((id , Γ.id) , id , f) $ Φ.₁ ((id , Γ.id) , w1 , Γ.id) $ w2 ≈˘⟨ Func.cong (α.α _) (Func.cong (Φ.₁ _) w4) ⟩
                              α.α (XX , Y) $ Φ.₁ ((id , Γ.id) , id , f) $ xx ∎ }) eq in
            let open RS (P.F₀ (X , Y)) in
            begin P.₁ (Γ.id , f) $ α.α (x , X) $ Φ.₁ ((id , f) , id , Γ.id) $ xp
                     ≈⟨ α.commute {X = x , X} {Y = x , Y} (id , f) {xp} {xp} ZS.refl ⟩
                  P.₁ (f , Γ.id) $ α.α (x , Y) $ Φ.₁ ((id , Γ.id) , id , f) $ xp ≈⟨ Func.cong (P.₁ (f , Γ.id)) congruence ⟩
                  P.₁ (f , Γ.id) $ α.α (y , Y) $ Φ.₁ ((id , Γ.id) , id , f) $ yp ∎
        }
      })
  where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module P = Functor P
    module Φ = Functor Φ
    module ZS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)
    open Reason A

coendR : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {Φ : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → DinaturalTransformation (coendFunctor (Φ ∘F F-reorder)) P
    → DinaturalTransformation Φ (P ∘F (Functor.op πʳ ∘F πˡ ※ πʳ ∘F πʳ))
coendR {A = A} {Γ = Γ} {Φ = Φ} {P = P} α = dtHelper (record
      { α = λ { (X , G) → record
        { to = λ { p → α.α G $ (X , p) }
        ; cong = λ { {x} {y} eq → Func.cong (α.α G) (convert (Φ ∘F F-reorder) eq) }
        } }
      ; commute =
      λ { {X , XG} {Y , YG} (f1 , f2) {x} {y} eq →
        let open RS (P.F₀ (XG , YG)) in
           begin
              P.₁ (Γ.id , f2) $ α.α XG $ (X , Φ.₁ ((f1 , f2) , id , Γ.id) $ x) ≈⟨ Func.cong (P.₁ (Γ.id , f2)) (Func.cong (α.α XG) (convert (Φ ∘F F-reorder) (ZS.sym ([ Φ ]-merge (id-1 , Γ.id-0) (id-1 , Γ.id-0) ZS.refl)))) ⟩
              P.₁ (Γ.id , f2) $ α.α XG $ (X , Φ.₁ ((id , f2) , id , Γ.id) $ Φ.₁ ((f1 , Γ.id) , id , Γ.id) $ x) ≈⟨ α.commute f2 (return (f1 , x , ZS.refl , ZS.refl)) ⟩
              P.₁ (f2 , Γ.id) $ α.α YG $ (Y , Φ.₁ ((id , Γ.id) , id , f2) $ Φ.₁ ((id , Γ.id) , f1 , Γ.id) $ x) ≈⟨ Func.cong (P.₁ (f2 , Γ.id)) (Func.cong (α.α YG) (convert (Φ ∘F F-reorder) ([ Φ ]-merge (id-0 , Γ.id-0) (id-0 , Γ.id-1) eq))) ⟩
              P.₁ (f2 , Γ.id) $ α.α YG $ (Y , Φ.₁ ((id , Γ.id) , f1 , f2) $ y) ∎
        }
      })
  where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module P = Functor P
    module Φ = Functor Φ
    module ZS {A} = Setoid (F₀ Φ A)
    module PS {A} = Setoid (F₀ P A)
    open Reason A

-- The two maps above are isomorphisms (in Set).

coendL⨟coendR-iso : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {Φ : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → (α : DinaturalTransformation Φ (P ∘F (Functor.op πʳ ∘F πˡ ※ πʳ ∘F πʳ)))
    → coendR {A = A} {Γ = Γ} {Φ = Φ} {P = P} (coendL α) ≃ᵈ α
coendL⨟coendR-iso α eq = Func.cong (DinaturalTransformation.α α _) eq

coendR⨟coendL-iso : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {Φ : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → (α : DinaturalTransformation (coendFunctor (Φ ∘F F-reorder)) P)
    → coendL {A = A} {Γ = Γ} {Φ = Φ} {P = P} (coendR α) ≃ᵈ α
coendR⨟coendL-iso α eq = Func.cong (DinaturalTransformation.α α _) eq
