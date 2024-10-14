{-# OPTIONS --safe --without-K #-}

{-
  We define the parametric coend of a functor F : A × Aᵒᵖ × Γ → Set, taking the coend in A.

  The action on morphisms (i.e., on natural transformations) is not required in the rest of the formalization.
-}

module Dinaturality.CoendFunctor where

open import Level using (Level; _⊔_) renaming (zero to zeroℓ; suc to sucℓ)

import Categories.Functor.Hom as Hom
import Relation.Binary.Reasoning.Setoid as RS

open import Categories.Category using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Morphism as P using (_≅_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation)
open import Categories.Object.Terminal using (Terminal)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Function using () renaming (id to idf; _∘_ to _∘′_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Construct.Closure.Equivalence using (isEquivalence; EqClosure; setoid; return; join; map; gmap; fold; gfold)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; trans)

import Reason

module _ {o ℓ e} {A Γ : Category o ℓ e}
       (F : Functor (Product (Category.op A) (Product A Γ)) (Setoids (o ⊔ ℓ) (o ⊔ ℓ))) where

  private
    module F = Functor F
    module Γ = Reason Γ
    open module A = Reason A hiding (_≈_)
    open module FS {A} {B} {Γ} = Setoid (F.₀ (A , B , Γ))
    open module MRS {A} {B} {Γ} = RS (F.₀ (A , B , Γ))

  -- The dinaturality relation for a fixed G : Γ.Obj, coending in the first variable.
  Dinaturality : (G : Γ.Obj) → Rel (Σ[ X ∈ Obj ] Setoid.Carrier (F.₀ (X , X , G))) (o ⊔ ℓ)
  Dinaturality G = λ (X , p₁) (Y , p₂) →
    Σ[ f ∈ X ⇒ Y ]
    Σ[ z ∈ Setoid.Carrier (F.₀ (Y , X , G)) ]
      (p₁ ≈ F.₁ (f , id , Γ.id) ⟨$⟩ z)
    × (p₂ ≈ F.₁ (id , f , Γ.id) ⟨$⟩ z)

  module Dinaturality {G} = Setoid (setoid (Dinaturality G))

  -- Helper function to lift equality in Setoids to equality in the transitive
  -- reflexive closure of the relation Dinaturality.
  convert : ∀ {G} {X} {a b : FS.Carrier {X} {X} {G}}
          → a ≈ b
          → EqClosure (Dinaturality G) (_ , a) (_ , b)
  convert eq = return (id , _ , FS.sym (F.identity (FS.sym eq))
                              , FS.sym (F.identity FS.refl))

  -- Output functor.
  coendFunctor : Functor Γ (Setoids (o ⊔ ℓ) (o ⊔ ℓ))
  coendFunctor = record
    { F₀ = λ G → setoid (Dinaturality G)
    ; F₁ = λ {B} {C} f → record
      { to = λ { (_ , p) → _ , F.₁ (id , id , f) ⟨$⟩ p }
      ; cong = gmap _ (λ { {z , zp} {x , xp} (k , p , eq1 , eq2)
                      → k , F.₁ (id , id , f) ⟨$⟩ p
                      , (begin F.F₁ (id , id , f) ⟨$⟩ zp ≈⟨ Func.cong (F.₁ (id , id , f)) eq1 ⟩
                                F.F₁ (id , id , f) ⟨$⟩ (F.F₁ (k , id , Γ.id) ⟨$⟩ p) ≈⟨ [ F ]-resp-square (id-swap , A.refl , Γ.id-swap) FS.refl ⟩
                                F.F₁ (k , id , Γ.id) ⟨$⟩ (F.F₁ (id , id , f) ⟨$⟩ p) ∎)
                      , (begin F.F₁ (id , id , f) ⟨$⟩ xp ≈⟨ Func.cong (F.₁ (id , id , f)) eq2 ⟩
                                F.F₁ (id , id , f) ⟨$⟩ (F.F₁ (id , k , Γ.id) ⟨$⟩ p) ≈⟨ [ F ]-resp-square (A.refl , sym-id-swap , Γ.id-swap) FS.refl ⟩
                                F.F₁ (id , k , Γ.id) ⟨$⟩ (F.F₁ (id , id , f) ⟨$⟩ p) ∎) })
      }
    ; identity = Dinaturality.trans (return (id , _ , FS.refl , FS.sym (F.identity (FS.refl))))
    ; homomorphism = λ { {_} {_} {_} {f} {g} {h} eq →
      Dinaturality.trans
        (gmap _ (λ { {X , pX} {Y , pY} (p , z , q2 , q3) → p , _ ,
          (begin F.₁ (id , id , g Γ.∘ f) ⟨$⟩ pX ≈⟨ Func.cong (F.₁ (id , id , g Γ.∘ f)) q2 ⟩
                F.₁ (id , id , g Γ.∘ f) ⟨$⟩ (F.₁ (p , id , Γ.id) ⟨$⟩ z) ≈⟨ [ F ]-resp-square (id-swap , A.refl , Γ.id-swap) FS.refl ⟩
                F.₁ (p , id , Γ.id) ⟨$⟩ (F.₁ (id , id , g Γ.∘ f) ⟨$⟩ z) ∎) ,
          (begin F.₁ (id , id , g Γ.∘ f) ⟨$⟩ pY ≈⟨ Func.cong (F.₁ (id , id , g Γ.∘ f)) q3 ⟩
                F.₁ (id , id , g Γ.∘ f) ⟨$⟩ (F.₁ (id , p , Γ.id) ⟨$⟩ z) ≈⟨ [ F ]-resp-square (A.refl , sym-id-swap , Γ.id-swap) FS.refl ⟩
                F.₁ (id , p , Γ.id) ⟨$⟩ (F.₁ (id , id , g Γ.∘ f) ⟨$⟩ z) ∎) }) eq)
        (convert (FS.trans (F.F-resp-≈ (Equiv.sym identity² , Equiv.sym identity² , Γ.Equiv.refl) FS.refl) (F.homomorphism FS.refl))) }
    ; F-resp-≈ = λ { {_} {_} {f} {g} f≈g eq →
      Dinaturality.trans
        (gmap _ (λ { {X , pX} {Y , pY} (p , z , q2 , q3) → p , _ ,
          (begin F.₁ (id , id , f) ⟨$⟩ pX ≈⟨ Func.cong (F.₁ (id , id , f)) q2 ⟩
                F.₁ (id , id , f) ⟨$⟩ (F.₁ (p , id , Γ.id) ⟨$⟩ z) ≈⟨ [ F ]-resp-square (id-swap , A.refl , Γ.id-swap) FS.refl ⟩
                F.₁ (p , id , Γ.id) ⟨$⟩ (F.₁ (id , id , f) ⟨$⟩ z) ∎) ,
          (begin F.₁ (id , id , f) ⟨$⟩ pY ≈⟨ Func.cong (F.₁ (id , id , f)) q3 ⟩
                F.₁ (id , id , f) ⟨$⟩ (F.₁ (id , p , Γ.id) ⟨$⟩ z) ≈⟨ [ F ]-resp-square (A.refl , sym-id-swap , Γ.id-swap) FS.refl ⟩
                F.₁ (id , p , Γ.id) ⟨$⟩ (F.₁ (id , id , f) ⟨$⟩ z) ∎)
                }) eq)
        (convert (F.F-resp-≈ (Equiv.refl , Equiv.refl , f≈g) FS.refl)) }
    }
