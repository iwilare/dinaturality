module Dinaturality.J where

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
open import Categories.NaturalTransformation.StrongDinatural using (StrongDinaturalTransformation; _≃ˢ_)
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

open Functor using (F₀; ₁; homomorphism; F-resp-≈)
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
    F G H I K L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt


-- modifier on a single variable
pos = πʳ
neg = πˡ

-- series of variables
positives = πʳ
negatives = πˡ

-- variables out of 2-tuple

va = πˡ
vb = πʳ

-- variables out of 3-tuple

v1 = πˡ

v2 : Functor (Product A (Product B C)) B
v2 = πˡ ∘F πʳ

v3 : Functor (Product A (Product B C)) C
v3 = πʳ ∘F πʳ

------------------------------------------------------------------------------------------

J :
  ∀ {o} {A C : Category o ℓ ℓ}
    (let module A = Category A)
    {Γ P : Functor (op (A ⊗ C) ⊗ (A ⊗ C)) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = A ⊗ C}
      Γ
      P
  → DinaturalTransformation {C = A.op ⊗ A ⊗ C}
      (SetA.-×- ∘F ((Hom[ A ][-,-] ∘F (v1 ∘F pos ※ v2 ∘F pos))
                 ※ (Γ ∘F ((v2 ∘F neg ※ v3 ∘F neg) ※ v1 ∘F neg ※ v3 ∘F pos))))
      (P ∘F ((v1 ∘F pos ※ v3 ∘F neg) ※ v2 ∘F pos ※ v3 ∘F pos))
J {A = A} {C = C} {Γ = Γ} {P = P} h = dtHelper (record
  { α = λ { (A , B , X) → record
    { to = λ { (f , k) → P.₁ ((f , C.id) , A.id , C.id) $ h.α (B , X) $ Γ.₁ ((A.id , C.id) , f , C.id) $ k }
    ; cong = λ { (feq , eq) → P.F-resp-≈ ((feq , C.refl) , A.refl , C.refl) (Func.cong (h.α _) (Γ.F-resp-≈ ((A.refl , C.refl) , feq , C.refl ) eq)) }
    } }
  ; commute = λ { {X1 , X2 , X3} {Y1 , Y2 , Y3} (f1 , f2 , f3) {e1 , k1} {e2 , k2} (eq1 , eq2) →
      let open RS (P.F₀ ((Y1 , X3) , Y2 , Y3)) in
      begin P.₁ ((f1 , C.id) , f2 , f3)
             $ P.₁ ((id ∘ e1 ∘ id , C.id) , id , C.id)
             $ h.α (X2 , X3)
             $ Γ.F₁ ((id , C.id) , id ∘ e1 ∘ id , C.id)
             $ Γ.F₁ ((f2 , f3) , f1 , C.id)
             $ k1 ≈⟨ [ P ]-resp-square ((((assoc-3 ∙ idm-2) , C.refl) , A.id-swap , C.id-swap)) (Func.cong (h.α _) ([ Γ ]-resp-square ((A.id-swap , C.id-swap) , (assoc-3 ∙ idm-2) , C.refl) eq2)) ⟩
            P.₁ ((e1 ∘ f1 , C.id) , id , C.id)
             $ P.₁ ((id , C.id) , f2 , f3)
             $ h.α (X2 , X3)
             $ Γ.₁ ((f2 , f3) , id , C.id)
             $ Γ.₁ ((id , C.id) , e1 ∘ f1 , C.id)
             $ k2 ≈⟨ Func.cong (P.₁ _) (h.commute _ ΓS.refl) ⟩
            P.₁ ((e1 ∘ f1 , C.id) , id , C.id)
            $ P.₁ ((f2 , f3) , id , C.id)
            $ h.α (Y2 , Y3)
            $ Γ.₁ ((id , C.id) , f2 , f3)
            $ Γ.₁ ((id , C.id) , e1 ∘ f1 , C.id)
            $ k2 ≈⟨ [ P ]-resp-square (((skip (rw eq1) ∙ sym-id-1) , C.id-swap) , A.refl , C.refl) (Func.cong (h.α _) ([ Γ ]-resp-square ((A.refl , C.refl) , ((skip (rw eq1) ∙ sym-id-1) , C.id-swap)) ΓS.refl)) ⟩
            P.₁ ((id , f3) , id , C.id)
            $ P.₁ ((f2 ∘ e2 ∘ f1 , C.id) , id , C.id)
            $ h.α (Y2 , Y3)
            $ Γ.₁ ((id , C.id) , f2 ∘ e2 ∘ f1 , C.id)
            $ Γ.₁ ((id , C.id) , id , f3)
            $ k2 ∎
      }
  }) where
    module Γ = Functor Γ
    module P = Functor P
    open module A = Reason A
    module C = Reason C
    module h = DinaturalTransformation h
    module ΓS {A} = Setoid (F₀ Γ A)
    module PS {A} = Setoid (F₀ P A)

J⁻¹ :
  ∀ {o} {A C : Category o ℓ ℓ}
    (let module A = Category A)
    {Γ P : Functor (op (A ⊗ C) ⊗ (A ⊗ C)) (Setoids ℓ ℓ)}
  → DinaturalTransformation {C = A.op ⊗ A ⊗ C}
      (SetA.-×- ∘F ((Hom[ A ][-,-] ∘F (v1 ∘F pos ※ v2 ∘F pos))
                 ※ (Γ ∘F ((v2 ∘F neg ※ v3 ∘F neg) ※ v1 ∘F neg ※ v3 ∘F pos))))
      (P ∘F ((v1 ∘F pos ※ v3 ∘F neg) ※ v2 ∘F pos ※ v3 ∘F pos))
  → DinaturalTransformation {C = A ⊗ C}
      Γ
      P
J⁻¹ {A = A} {C = C} {Γ = Γ} {P = P} h = dtHelper (record
  { α = λ { (A , X) → record
    { to = λ { k → h.α (A , A , X) $ (id , k) }
    ; cong = λ eq → Func.cong (h.α _) (A.refl , eq)
    } }
  ; commute =
  λ { {X1 , X2} {Y1 , Y2} (f1 , f2) {k1} {k2} eq → let open RS (P.F₀ ((X1 , X2) , Y1 , Y2)) in
    begin P.₁ ((id , C.id) , f1 , f2)
           $ h.α (X1 , X1 , X2)
           $ (id , Γ.F₁ ((f1 , f2) , id , C.id) $ k1) ≈⟨ Func.cong (P.₁ _) (Func.cong (h.α _) (A.sym-id-1 ∙ A.sym-id-2 , ΓS.refl)) ⟩
          P.₁ ((id , C.id) , f1 , f2)
           $ h.α (X1 , X1 , X2)
           $ (id ∘ id ∘ id , Γ.₁ ((f1 , f2) , id , C.id) $ k1) ≈⟨ h.commute (id , f1 , f2) (A.refl , eq) ⟩
          P.₁ ((id , f2) , id , C.id)
           $ h.α _
           $ (f1 ∘ id ∘ id , Γ.F₁ ((id , C.id) , id , f2) $ _) ≈˘⟨ [ P ]-merge (A.id-0 , C.id-0) (A.id-0 , C.id-0) (Func.cong (h.α _) (A.sym-id-swap-2 , [ Γ ]-merge (A.id-0 , C.id-0) (A.id-0 , C.id-0) ΓS.refl)) ⟩
          P.₁ ((id , f2) , id , C.id)
          $ P.₁ ((id , C.id) , id , C.id)
           $ h.α _
           $ (id ∘ id ∘ f1 , Γ.F₁ ((id , C.id) , id , C.id) $ Γ.F₁ ((id , C.id) , id , f2) $ _) ≈⟨ Func.cong (P.₁ _) (h.op-commute (f1 , id , C.id) (A.refl , ΓS.refl)) ⟩
          P.₁ ((id , f2) , id , C.id)
           $ P.₁ ((f1 , C.id) , id , C.id)
           $ h.α (Y1 , Y1 , Y2)
           $ (id ∘ id ∘ id , Γ.₁ ((id , C.id) , f1 , C.id) $ Γ.₁ ((id , C.id) , id , f2) $ k2) ≈⟨ [ P ]-merge (A.id-1 , C.id-0) (A.id-1 , C.id-0) (Func.cong (h.α _) ((A.id-0 ∙ A.id-0) , [ Γ ]-merge (A.id-1 , C.id-0) (A.id-1 , C.id-0) ΓS.refl)) ⟩
          P.F₁ ((f1 , f2) , id , C.id)
           $ h.α (Y1 , Y1 , Y2)
           $ (id , Γ.F₁ ((id , C.id) , f1 , f2) $ k2) ∎
      }
  }) where
    module Γ = Functor Γ
    module P = Functor P
    open module A = Reason A
    module C = Reason C
    module h = DinaturalTransformation h
    module ΓS {A} = Setoid (F₀ Γ A)
    module PS {A} = Setoid (F₀ P A)
