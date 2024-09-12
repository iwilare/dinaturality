

module Dinaturality.J-Compose where

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
    A B C D Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

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

-- J is the minimal definition (in terms of variable context) of J that
-- allows `e` to be the first projection.

J :
  ∀ {o} {A C : Category o ℓ ℓ}
    (let module A = Category A)
                     -- a , b , x
    {Γ P : Functor (op (A.op ⊗ A ⊗ C) ⊗ (A.op ⊗ A ⊗ C)) (Setoids ℓ ℓ)}
                              -- z , a , b , x
  → DinaturalTransformation {C = A ⊗ A.op ⊗ A ⊗ C}
         -- z+, z-, c-, (a+, b+, c+)
      (Γ ∘F ((va ∘F pos ※ va ∘F neg ※ v3 ∘F vb ∘F neg) ※ vb ∘F pos))
         -- (a-, b-, c-), z-, z+, c+
      (P ∘F (vb ∘F neg ※ (va ∘F neg ※ va ∘F pos ※ v3 ∘F vb ∘F pos)))
  → DinaturalTransformation {C = A.op ⊗ A ⊗ C}
      Γ
      (Hom[ A ][-,-] ∘F (v1 ∘F pos ※ v2 ∘F pos))
  → DinaturalTransformation {C = A.op ⊗ A ⊗ C}
      Γ
      P
J {A = A} {C = C} {Γ = Γ} {P = P} h e = dtHelper record
  { α = λ { (a , b , x) → record
    { to = λ p → P.₁ (M.id , ((A.id , e.α (a , b , x) $ p , C.id)))
               $ h.α (a , a , b , x)
               $ Γ.₁ ((A.id , e.α (a , b , x) $ p , C.id) , M.id)
               $ p
    ; cong = λ eq →
      P.F-resp-≈ (M.refl , (A.refl , Func.cong (e.α _) eq , C.refl))
      (Func.cong (h.α _)
      (Γ.F-resp-≈ ((A.refl , Func.cong (e.α _) eq , C.refl) , M.refl)
      eq))
    } }
  ; commute = λ { {X1 , X2 , X3} {Y1 , Y2 , Y3} (f , o , g) {x} {y} eq →
    let open RS (P.F₀ ((X1 , X2 , X3) , Y1 , Y2 , Y3)) in
    begin   P.₁ (M.id , f , o , g)
          $ P.₁ (M.id , (A.id , e.α _ $ Γ.₁ ((f , o , g) , M.id) $ x , C.id))
          $ h.α (X1 , X1 , X2 , X3)
          $ Γ.₁ ((A.id , e.α _ $ Γ.₁ ((f , o , g) , M.id) $ x , C.id) , M.id)
          $ Γ.₁ ((f , o , g) , M.id)
          $ x ≈⟨ [ P ]-resp-square (M.refl , A.refl , A.sym-id-0 , C.id-swap)
                 (Func.cong (h.α _)
                 ([ Γ ]-resp-square ((A.refl , A.sym-id-0 , C.id-swap) , M.refl) eq)) ⟩
            P.₁ (M.id , f , id , C.id)
          $ P.₁ (M.id , id , o ∘ (e.α (X1 , X2 , X3) $ Γ.₁ ((f , o , g) , M.id) $ x) , g)
          $ h.α (X1 , X1 , X2 , X3)
          $ Γ.₁ ((id , o ∘ (e.α (X1 , X2 , X3) $ Γ.₁ ((f , o , g) , M.id) $ x) , g) , M.id)
          $ Γ.₁ ((f , id , C.id) , M.id)
          $ y  ≈⟨ Func.cong (P.₁ _) (h.commute _ ΓS.refl) ⟩
            P.₁ (M.id , f , id , C.id)
          $ P.₁ ((f , o , g) , o ∘ (e.α (X1 , X2 , X3) $ Γ.F₁ ((f , o , g) , M.id) $ x) , id , C.id)
          $ h.α (Y2 , Y1 , Y2 , Y3)
          $ Γ.₁ ((o ∘ (e.α (X1 , X2 , X3) $ Γ.₁ ((f , o , g) , M.id) $ x) , id , C.id) , f , o , g)
          $ Γ.₁ ((f , id , C.id) , M.id)
          $ y ≈⟨ [ P ]-resp-square (M.id-swap , (assoc ∙ e.commute (f , o , g) eq ∙ id-0 , A.refl , C.refl))
                      (Func.cong (h.α _)
                      ([ Γ ]-resp-square ((assoc ∙ e.commute (f , o , g) eq ∙ id-0 , A.refl , C.refl) , M.id-swap) ΓS.refl)) ⟩
            P.₁ ((f , o , g) , M.id)
            $ P.₁ (M.id , (e.α (Y1 , Y2 , Y3) $ Γ.F₁ (M.id , f , o , g) $ y) , id , C.id)
            $ h.α (Y2 , _ , _ , Y3)
            $ Γ.₁ (((e.α (Y1 , Y2 , Y3) $ Γ.₁ (M.id , f , o , g) $ y) , id , C.id) , M.id)
            $ Γ.₁ (M.id , f , o , g)
            $ y  ≈⟨ Func.cong (P.₁ _) (h.op-commute _ ΓS.refl) ⟩
         P.₁ ((f , o , g) , M.id)
          $ P.₁ (M.id , id , (e.α (Y1 , Y2 , Y3) $ Γ.₁ (M.id , f , o , g) $ y) , C.id)
          $ h.α (Y1 , Y1 , Y2 , Y3)
          $ Γ.₁ ((id , (e.α (Y1 , Y2 , Y3) $ Γ.₁ (M.id , f , o , g) $ y) , C.id) , M.id)
          $ Γ.₁ (M.id , f , o , g)
          $ y ∎
           }
  } where
    module e = DinaturalTransformation e
    module h = DinaturalTransformation h
    module C = Reason C
    module A = Reason A
    module Γ = Functor Γ
    module P = Functor P
    module ΓS {A} = Setoid (F₀ Γ A)
    module PS {A} = Setoid (F₀ P A)
    open A
    module M = Reason (A.op ⊗ A ⊗ C)
