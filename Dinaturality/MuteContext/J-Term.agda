

module Dinaturality.MuteContext.J-Term where

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
    F G K P I J L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt

-- version of J with terms where the context does not depend on the negative variable
J-mutectx-term : ∀ {o} {A Γ : Category o ℓ ℓ}
  {K : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
  {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
    (F : Functor (op Γ ⊗ Γ) (op A))
  → (G : Functor (op Γ ⊗ Γ) A)
  → DinaturalTransformation (K ∘F (πʳ ∘F πˡ ※ πʳ ∘F πʳ)) P
  → DinaturalTransformation K (Hom[ A ][-,-] ∘F (F ※ G))
  → DinaturalTransformation K (P ∘F ((F ※ πˡ) ※ G ※ πʳ))
J-mutectx-term {A = A} {Γ = Γ} {K = K} {P = P} F G α β = dtHelper record
  { α = λ X → record
    { to = λ pxx → P.₁ (((β.α X $ pxx) , Γ.id) , (id , Γ.id)) $ α.α (G.₀ (X , X) , X) $ pxx
    ; cong = λ eq → P.F-resp-≈ ((Func.cong (β.α X) eq , Γ.refl) , A.refl , Γ.refl) (Func.cong (α.α _) eq)
    }
  ; commute = λ { {X} {Y} f eq → let open RS (P.F₀ ((F.F₀ (X , Y) , X) , G.F₀ (X , Y) , Y)) in
    begin   P.₁ ((F.₁ (Γ.id , f) , Γ.id) , G.₁ (Γ.id , f) , f)
          $ P.₁ ((β.α X $ K.₁ (f , Γ.id) $ _ , Γ.id) , id , Γ.id)
          $ α.α _ $ K.₁ (f , Γ.id) $ _ ≈⟨ [ P ]-resp-square ((A.sym-id-0 , Γ.refl) , A.id-swap , Γ.id-swap) HS.refl ⟩
            P.₁ ((((β.α X $ K.₁ (f , Γ.id) $ _) ∘ F.₁ (Γ.id , f)) , Γ.id) , id , Γ.id)
          $ P.₁ ((id , Γ.id) , G.₁ (Γ.id , f) , f)
          $ α.α _ $ K.₁ (f , Γ.id) $ _ ≈⟨ Func.cong (P.₁ _) (α.commute (G.₁ (Γ.id , f) , f) eq) ⟩
            P.₁ (((β.α X $ K.₁ (f , Γ.id) $ _) ∘ F.₁ (Γ.id , f) , Γ.id) , id , Γ.id)
          $ P.₁ ((G.₁ (Γ.id , f) , f) , id , Γ.id)
          $ α.α _ $ K.₁ (Γ.id , f) $ _ ≈⟨ [ P ]-resp-square ((β.commute f eq , Γ.id-swap) , A.refl , Γ.refl) HS.refl ⟩
            P.₁ (((β.α Y $ K.₁ (Γ.id , f) $ _) ∘ F.₁ (f , Γ.id) , f) , id , Γ.id)
          $ P.₁ ((G.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
          $ α.α _ $ K.₁ (Γ.id , f) $ _ ≈˘⟨ Func.cong (P.₁ _) (Func.cong (P.₁ _) (Func.cong (α.α _) (K.identity PS.refl))) ⟩
            P.₁ (((β.α Y $ K.₁ (Γ.id , f) $ _) ∘ F.₁ (f , Γ.id) , f) , id , Γ.id)
          $ P.₁ ((G.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
          $ α.α _ $ K.₁ (Γ.id , Γ.id) $ K.₁ (Γ.id , f) $ _
           ≈⟨ Func.cong (P.₁ _) (α.op-commute (G.₁ (f , Γ.id) , Γ.id) PS.refl) ⟩
            P.₁ (((β.α Y $ K.₁ (Γ.id , f) $ _) ∘ F.₁ (f , Γ.id) , f) , id , Γ.id)
          $ P.₁ ((id , Γ.id) , G.₁ (f , Γ.id) , Γ.id)
          $ α.α (G.F₀ (Y , Y) , Y) $ K.₁ (Γ.id , Γ.id) $ K.₁ (Γ.id , f)
          $ _  ≈⟨ Func.cong (P.₁ _) (Func.cong (P.₁ _) (Func.cong (α.α _) (K.identity PS.refl))) ⟩
            P.₁ (((β.α Y $ K.₁ (Γ.id , f) $ _) ∘ F.₁ (f , Γ.id) , f) , id , Γ.id)
          $ P.₁ ((id , Γ.id) , G.₁ (f , Γ.id) , Γ.id)
          $ α.α (G.F₀ (Y , Y) , Y) $ K.₁ (Γ.id , f) $ _ ≈⟨ [ P ]-resp-square ((A.id-0 , Γ.refl) , A.sym-id-swap , Γ.refl) HS.refl ⟩
            P.₁ ((F.₁ (f , Γ.id) , f) , G.₁ (f , Γ.id) , Γ.id)
          $ P.₁ ((β.α Y $ K.₁ (Γ.id , f) $ _ , Γ.id) , id , Γ.id)
          $ α.α _ $ K.₁ (Γ.id , f) $ _ ∎ }
  } where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module Γ = Reason Γ
    module HS {A} = Setoid (F₀ P A)
    module PS {A} = Setoid (F₀ K A)
    module P = Functor P
    module K = Functor K
    module F = Functor F
    module G = Functor G
    open module A = Reason A

{-
J-term-lawvere-⊤ : ∀ {o} {A Γ : Category o ℓ ℓ} {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
           (F : Functor (op Γ ⊗ Γ) A)
         → (G : Functor (op Γ ⊗ Γ) A)
         → DinaturalTransformation (const SetT.⊤) P
         → DinaturalTransformation (Hom[ A ][-,-] ∘F (Functor.op F ∘F Swap ※ G))
                                   (P ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ G ※ πʳ))
J-term-lawvere-⊤ {A = A} {Γ = Γ} {P = P} F G α = dtHelper (record
  { α = λ X → record
    { to = λ m → P.₁ ((m , Γ.id) , id , Γ.id) $ (α.α (F₀ G (X , X) , X) $ *)
    ; cong = λ eq → F-resp-≈ P ((eq , Γ.refl) , Equiv.refl , Γ.refl)  (Setoid.refl (F₀ P ((F₀ G (X , X) , X) , F₀ G (X , X) , X)))
    }
  ; commute = λ { {X} {Y} m {x} {y} eq →
    let open RS (F₀ P ((F₀ F (Y , X) , X) , F₀ G (X , Y) , Y)) in
    begin
        P.₁ ((F.₁ (m , Γ.id) , Γ.id) , G.₁ (Γ.id , m) , m)
      $ P.₁ ((G.₁ (m , Γ.id) ∘ x ∘ F.₁ (Γ.id , m) , Γ.id) , id , Γ.id)
      $ α.α (F₀ G (X , X) , X) $ * ≈⟨ [ P ]-resp-square ((((assoc-3 ∙ skip (rw eq) ∙ (skip-2 ([ F ]-merge Γ.ids-1 Γ.ids-1) ∙ sym-id-1))) , Γ.refl) , Equiv.refl , Γ.refl)  (Setoid.refl (F₀ P ((F₀ G (X , X) , X) , F₀ G (X , X) , X))) ⟩
        P.₁ ((id , Γ.id) , G.₁ (Γ.id , m) , m)
      $ P.₁ ((G.₁ (m , Γ.id) ∘ y ∘ F.₁ (m , m) , Γ.id) , id , Γ.id)
      $ α.α (F₀ G (X , X) , X) $ * ≈⟨ Func.cong (P.₁ _) (α.op-commute _ *) ⟩
        P.₁ ((id , Γ.id) , G.₁ (Γ.id , m) , m)
      $ P.₁ ((id , Γ.id) , G.₁ (m , Γ.id) ∘ y ∘ F.₁ (m , m) , Γ.id)
      $ α.α (F₀ F (Y , X) , X) $ * ≈⟨ [ P ]-resp-square ((Equiv.refl , Γ.refl) , rw-2 [ G ]-commute , Γ.id-swap) (Setoid.refl (F₀ P ((F₀ F (Y , X) , X) , F₀ F (Y , X) , X))) ⟩
        P.₁ ((id , Γ.id) , G.₁ (m , Γ.id) , Γ.id)
      $ P.₁ ((id , Γ.id) , G.₁ (Γ.id , m) ∘ y ∘ F.₁ (m , m) , m)
      $ α.α (F₀ F (Y , X) , X) $ * ≈⟨ Func.cong (P.₁ _) (α.commute _ *) ⟩
        P.₁ ((id , Γ.id) , G.₁ (m , Γ.id) , Γ.id)
      $ P.₁ ((G.₁ (Γ.id , m) ∘ y ∘ F.₁ (m , m) , m) , id , Γ.id)
      $ α.α (F₀ G (Y , Y) , Y) $ * ≈˘⟨ [ P ]-resp-square  ((assoc-3 ∙ skip-2 ([ F ]-merge Γ.id-0 Γ.id-0) ∙ sym-id-1 , Γ.sym-id-swap) , Equiv.refl , Γ.refl) (Setoid.refl (F₀ P ((F₀ G (Y , Y) , Y) , F₀ G (Y , Y) , Y))) ⟩
        P.₁ ((F.₁ (Γ.id , m) , m) , G.₁ (m , Γ.id) , Γ.id)
      $ P.₁ ((G.₁ (Γ.id , m) ∘ y ∘ F.₁ (m , Γ.id) , Γ.id) , id , Γ.id)
      $ α.α (F₀ G (Y , Y) , Y) $ * ∎
    }
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module P = Functor P
    module F = Functor F
    module G = Functor G
    open Reason A
-}

{-
-- a variation of the above in which F and G have the same variance
J-term-Fop : ∀ {o} {A Γ : Category o ℓ ℓ}
  {K : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
  {P : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
    (F G : Functor (op Γ ⊗ Γ) A)
  → DinaturalTransformation (K ∘F (πʳ ∘F πˡ ※ πʳ ∘F πʳ)) P
  → DinaturalTransformation K (Hom[ A ][-,-] ∘F (Functor.op F ∘F Swap ※ G))
  → DinaturalTransformation K (P ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ G ※ πʳ))
J-term-Fop {A = A} {Γ = Γ} {K = K} {P = P} F G α β = dtHelper record
  { α = λ X → record
    { to = λ pxx → P.₁ (((β.α X $ pxx) , Γ.id) , (id , Γ.id)) $ α.α (G.₀ (X , X) , X) $ pxx
    ; cong = λ eq → P.F-resp-≈ ((Func.cong (β.α X) eq , Γ.refl) , A.refl , Γ.refl) (Func.cong (α.α _) eq)
    }
  ; commute = λ { {X} {Y} f eq → let open RS (P.F₀ ((F.F₀ (Y , X) , X) , G.F₀ (X , Y) , Y)) in
    begin   P.₁ ((F.₁ (f , Γ.id) , Γ.id) , G.₁ (Γ.id , f) , f)
          $ P.₁ ((β.α X $ K.₁ (f , Γ.id) $ _ , Γ.id) , id , Γ.id)
          $ α.α _ $ K.₁ (f , Γ.id) $ _ ≈⟨ [ P ]-resp-square ((A.sym-id-0 , Γ.refl) , A.id-swap , Γ.id-swap) HS.refl ⟩
            P.₁ ((((β.α X $ K.₁ (f , Γ.id) $ _) ∘ F.₁ (f , Γ.id)) , Γ.id) , id , Γ.id)
          $ P.₁ ((id , Γ.id) , G.₁ (Γ.id , f) , f)
          $ α.α _ $ K.₁ (f , Γ.id) $ _ ≈⟨ Func.cong (P.₁ _) (α.commute (G.₁ (Γ.id , f) , f) eq) ⟩
            P.₁ (((β.α X $ K.₁ (f , Γ.id) $ _) ∘ F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
          $ P.₁ ((G.₁ (Γ.id , f) , f) , id , Γ.id)
          $ α.α _ $ K.₁ (Γ.id , f) $ _ ≈⟨ [ P ]-resp-square ((β.commute f eq , Γ.id-swap) , A.refl , Γ.refl) HS.refl ⟩
            P.₁ (((β.α Y $ K.₁ (Γ.id , f) $ _) ∘ F.₁ (Γ.id , f) , f) , id , Γ.id)
          $ P.₁ ((G.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
          $ α.α _ $ K.₁ (Γ.id , f) $ _ ≈˘⟨ Func.cong (P.₁ _) (Func.cong (P.₁ _) (Func.cong (α.α _) (K.identity PS.refl))) ⟩
            P.₁ (((β.α Y $ K.₁ (Γ.id , f) $ _) ∘ F.₁ (Γ.id , f) , f) , id , Γ.id)
          $ P.₁ ((G.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
          $ α.α _ $ K.₁ (Γ.id , Γ.id) $ K.₁ (Γ.id , f) $ _
           ≈⟨ Func.cong (P.₁ _) (α.op-commute (G.₁ (f , Γ.id) , Γ.id) PS.refl) ⟩
            P.₁ (((β.α Y $ K.₁ (Γ.id , f) $ _) ∘ F.₁ (Γ.id , f) , f) , id , Γ.id)
          $ P.₁ ((id , Γ.id) , G.₁ (f , Γ.id) , Γ.id)
          $ α.α (G.F₀ (Y , Y) , Y) $ K.₁ (Γ.id , Γ.id) $ K.₁ (Γ.id , f)
          $ _  ≈⟨ Func.cong (P.₁ _) (Func.cong (P.₁ _) (Func.cong (α.α _) (K.identity PS.refl))) ⟩
            P.₁ (((β.α Y $ K.₁ (Γ.id , f) $ _) ∘ F.₁ (Γ.id , f) , f) , id , Γ.id)
          $ P.₁ ((id , Γ.id) , G.₁ (f , Γ.id) , Γ.id)
          $ α.α (G.F₀ (Y , Y) , Y) $ K.₁ (Γ.id , f) $ _ ≈⟨ [ P ]-resp-square ((A.id-0 , Γ.refl) , A.sym-id-swap , Γ.refl) HS.refl ⟩
            P.₁ ((F.₁ (Γ.id , f) , f) , G.₁ (f , Γ.id) , Γ.id)
          $ P.₁ ((β.α Y $ K.₁ (Γ.id , f) $ _ , Γ.id) , id , Γ.id)
          $ α.α _ $ K.₁ (Γ.id , f) $ _ ∎ }
  } where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module Γ = Reason Γ
    module HS {A} = Setoid (F₀ P A)
    module PS {A} = Setoid (F₀ K A)
    module P = Functor P
    module K = Functor K
    module F = Functor F
    module G = Functor G
    open module A = Reason A
-}
