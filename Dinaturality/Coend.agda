module Dinaturality.Coend where

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
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong₂; trans; cong; sym)
open import Relation.Binary.Construct.Closure.Equivalence using (isEquivalence; EqClosure; setoid; return; join; map; gmap; fold; gfold)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

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

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt

coendAdjL : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {Z : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → DinaturalTransformation Z (P ∘F (Functor.op πʳ ∘F πˡ ※ πʳ ∘F πʳ))
    → DinaturalTransformation (coendFunctor (Z ∘F F-reorder)) P
coendAdjL {A = A} {Γ = Γ} {P = P} {Z = Z} α = dtHelper (record
      { α = λ X → record
        { to = λ { (A , p) → α.α (A , X) $ p }
        ; cong =
          λ { {A , px} {B , py} eq →
          gfold {S = Setoid._≈_ (P.F₀ (X , X)) } {R = Dinaturality (Z ∘F F-reorder) (X , X)}
                (Setoid.isEquivalence (P.₀ (X , X)))
                (λ { (Y , p) → α.α (Y , X) $ p })
                (λ { {YY , yy} {XX , xx} (w1 , w2 , w3 , w4) →
                  let open RS (P.₀ (X , X)) in
                  begin α.α (YY , X) $ yy ≈⟨ Func.cong (α.α (YY , X)) w3 ⟩
                        α.α (YY , X) $ Z.₁ ((w1 , Γ.id) , id , Γ.id) $ w2 ≈˘⟨ P.identity PS.refl ⟩
                        P.₁ (Γ.id , Γ.id) $ α.α (YY , X) $ Z.₁ ((w1 , Γ.id) , id , Γ.id) $ w2 ≈⟨ α.commute (w1 , Γ.id) ZS.refl ⟩
                        P.₁ (Γ.id , Γ.id) $ α.α (XX , X) $ Z.₁ ((id , Γ.id) , w1 , Γ.id) $ w2 ≈⟨ P.identity PS.refl ⟩
                        α.α (XX , X) $ Z.F₁ ((id , Γ.id) , w1 , Γ.id) $ w2 ≈˘⟨ Func.cong (α.α (XX , X)) w4 ⟩
                        α.α (XX , X) $ xx ∎ }) eq
          }
        }
      ; commute =
      λ { {X} {Y} f {x , xp} {y , yp} eq →
          let congruence = gfold {R = Dinaturality (Z ∘F F-reorder) (Y , X)}
                   (Setoid.isEquivalence (P.₀ (Y , Y)))
                   (λ { (Z , zz) → α.α (Z , Y) $ Z.₁ ((id , Γ.id) , id , f) $ zz })
                   (λ { {YY , yy} {XX , xx} (w1 , w2 , w3 , w4) →
                       let open RS (P.₀ (Y , Y)) in
                        begin α.α (YY , Y) $ Z.₁ ((id , Γ.id) , id , f) $ yy ≈⟨ Func.cong (α.α _) (Func.cong (Z.₁ _) w3) ⟩
                              α.α (YY , Y) $ Z.₁ ((id , Γ.id) , id , f) $ Z.F₁ ((w1 , Γ.id) , id , Γ.id) $ w2 ≈⟨ Func.cong (α.α _) ([ Z ]-commute ZS.refl) ⟩
                              α.α (YY , Y) $ Z.₁ ((w1 , Γ.id) , id , Γ.id) $ Z.F₁ ((id , Γ.id) , id , f) $ w2 ≈˘⟨ P.identity PS.refl ⟩
                              P.₁ (Γ.id , Γ.id) $ α.α (YY , Y) $ Z.₁ ((w1 , Γ.id) , id , Γ.id) $ Z.F₁ ((id , Γ.id) , id , f) $ w2 ≈⟨ α.commute (w1 , Γ.id) ZS.refl ⟩
                              P.₁ (Γ.id , Γ.id) $ α.α (XX , Y) $ Z.₁ ((id , Γ.id) , w1 , Γ.id) $ Z.₁ ((id , Γ.id) , id , f) $ w2 ≈⟨ P.identity PS.refl ⟩
                              α.α (XX , Y) $ Z.₁ ((id , Γ.id) , w1 , Γ.id) $ Z.₁ ((id , Γ.id) , id , f) $ w2 ≈˘⟨ Func.cong (α.α _) ([ Z ]-resp-square ((Equiv.refl , Γ.refl) , sym-id-swap , Γ.id-swap) ZS.refl) ⟩
                              α.α (XX , Y) $ Z.₁ ((id , Γ.id) , id , f) $ Z.₁ ((id , Γ.id) , w1 , Γ.id) $ w2 ≈˘⟨ Func.cong (α.α _) (Func.cong (Z.₁ _) w4) ⟩
                              α.α (XX , Y) $ Z.₁ ((id , Γ.id) , id , f) $ xx ∎ }) eq in
            let open RS (P.F₀ (X , Y)) in
            begin P.₁ (Γ.id , f) $ α.α (x , X) $ Z.₁ ((id , f) , id , Γ.id) $ xp
                     ≈⟨ α.commute {X = x , X} {Y = x , Y} (id , f) {xp} {xp} ZS.refl ⟩
                  P.₁ (f , Γ.id) $ α.α (x , Y) $ Z.₁ ((id , Γ.id) , id , f) $ xp ≈⟨ Func.cong (P.₁ (f , Γ.id)) congruence ⟩
                  P.₁ (f , Γ.id) $ α.α (y , Y) $ Z.₁ ((id , Γ.id) , id , f) $ yp ∎
        }
      })
  where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module P = Functor P
    module Z = Functor Z
    module ZS {A} = Setoid (F₀ Z A)
    module PS {A} = Setoid (F₀ P A)
    open Reason A

coendAdjR : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {Z : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    → DinaturalTransformation (coendFunctor (Z ∘F F-reorder)) P
    → DinaturalTransformation Z (P ∘F (Functor.op πʳ ∘F πˡ ※ πʳ ∘F πʳ))
coendAdjR {A = A} {Γ = Γ} {P = P} {Z = Z} α = dtHelper (record
      { α = λ { (X , G) → record
        { to = λ { p → α.α G $ (X , p) }
        ; cong = λ { {x} {y} eq → Func.cong (α.α G) (convert (Z ∘F F-reorder) eq) }
        } }
      ; commute =
      λ { {X , XG} {Y , YG} (f1 , f2) {x} {y} eq →
        let open RS (P.F₀ (XG , YG)) in
           begin
              P.₁ (Γ.id , f2) $ α.α XG $ (X , Z.₁ ((f1 , f2) , id , Γ.id) $ x) ≈⟨ Func.cong (P.₁ (Γ.id , f2)) (Func.cong (α.α XG) (convert (Z ∘F F-reorder) (ZS.sym ([ Z ]-merge (id-1 , Γ.id-0) (id-1 , Γ.id-0) ZS.refl)))) ⟩
              P.₁ (Γ.id , f2) $ α.α XG $ (X , Z.₁ ((id , f2) , id , Γ.id) $ Z.₁ ((f1 , Γ.id) , id , Γ.id) $ x) ≈⟨ α.commute f2 (return (f1 , x , ZS.refl , ZS.refl)) ⟩
              P.₁ (f2 , Γ.id) $ α.α YG $ (Y , Z.₁ ((id , Γ.id) , id , f2) $ Z.₁ ((id , Γ.id) , f1 , Γ.id) $ x) ≈⟨ Func.cong (P.₁ (f2 , Γ.id)) (Func.cong (α.α YG) (convert (Z ∘F F-reorder) ([ Z ]-merge (id-0 , Γ.id-0) (id-0 , Γ.id-1) eq))) ⟩
              P.₁ (f2 , Γ.id) $ α.α YG $ (Y , Z.₁ ((id , Γ.id) , f1 , f2) $ y) ∎
        }
      })
  where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module P = Functor P
    module Z = Functor Z
    module ZS {A} = Setoid (F₀ Z A)
    module PS {A} = Setoid (F₀ P A)
    open Reason A

{-
coendProjection : ∀ {o ℓ e} {A Γ : Category o ℓ e}
    {P : Functor (op Γ ⊗ Γ) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    {Z : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))}
    (F : Functor (op Γ ⊗ Γ) A)
  → DinaturalTransformation (coendFunctor (Z ∘F F-reorder)) P
  → DinaturalTransformation (Z ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ)) P
coendProjection {A = A} {Γ = Γ} {P = P} {Z = Z} F α = dtHelper (record
  { α = λ X → record
    { to = λ fxx → α.α X $ (_ , fxx)
    ; cong = λ eq → Func.cong (α.α X) (CoendCalculus.Coend.convert (Z ∘F F-reorder) eq)
    }
  ; commute = λ {X} {Y} m {x} {y} eq →
    let open RS (P.F₀ (X , Y)) in
    begin P.₁ (Γ.id , m) $ α.α X $ (F.₀ (X , X) , Z.₁ ((F.₁ (Γ.id , m) , m) , F.₁ (m , Γ.id) , Γ.id) $ x)
            ≈⟨ Func.cong (P.₁ _) (Func.cong (α.α X) (return (F.₁ (Γ.id , m)
                                                            , Z.₁ ((id , m) , F.₁ (m , Γ.id) , Γ.id) $ x
                                                            , ZS.sym ([ Z ]-merge (id-0 , Γ.id-1) (id-0 , Γ.id-1) ZS.refl)
                                                            , [ Z ]-resp-square ((Equiv.refl , Γ.sym-id-swap) , id-0 , Γ.refl) ZS.refl))) ⟩
          P.₁ (Γ.id , m) $ α.α X $ (F.₀ (X , Y) , Z.₁ ((id , m) , id , Γ.id) $ Z.₁ ((id , Γ.id) , F.₁ (Γ.id , m) ∘ F.₁ (m , Γ.id) , Γ.id) $ x)
            ≈⟨ α.commute m (Dinaturality.sym (Z ∘F F-reorder) (return (F.₁ (m , Γ.id)
                                                                      , Z.₁ ((id , Γ.id) , F.₁ (Γ.id , m) , Γ.id) $ x
                                                                      , ZS.sym ([ Z ]-merge (id-0 , Γ.id-0) (id-0 , Γ.id-0) ZS.refl)
                                                                      , ZS.sym ([ Z ]-merge (id-0 , Γ.id-0) (Equiv.sym [ F ]-commute , Γ.id-0) ZS.refl)))) ⟩
          P.F₁ (m , Γ.id) $ α.α Y $ (F.₀ (Y , Y) , Z.₁ ((id , Γ.id) , id , m) $ Z.₁ ((F.₁ (m , Γ.id) , Γ.id) , F.₁ (Γ.id , m) , Γ.id) $ x)
            ≈⟨ Func.cong (P.₁ _) (Func.cong (α.α Y) (CoendCalculus.Coend.convert (Z ∘F F-reorder) ([ Z ]-merge (id-1 , Γ.id-0) (id-0 , Γ.id-1) eq))) ⟩
          P.₁ (m , Γ.id) $ α.α Y $ (F.₀ (Y , Y) , Z.₁ ((F.F₁ (m , Γ.id) , Γ.id) , F.₁ (Γ.id , m) , m) $ y) ∎
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
