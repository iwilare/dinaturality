

module Dinaturality.Reindexing where

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
    F G H I J K L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt

reindexing : ∀ {o} {A Γ Δ : Category o ℓ ℓ}
    {H : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    {H′ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
    (F : Functor (op Δ ⊗ Δ) Γ)
  → DinaturalTransformation H H′
  → DinaturalTransformation (H ∘F ((Functor.op F ∘F Swap) ※ F)) (H′ ∘F ((Functor.op F ∘F Swap) ※ F))
reindexing {A = A} {Γ = Γ} {Δ = Δ} {H = H} {H′ = H′} F α = dtHelper (record
  { α = λ X → record { to = λ p → α.α (F.₀ (X , X)) $ p ; cong = Func.cong (α.α (F.₀ (X , X))) }
  ; commute = λ { {X} {Y} f {x} {y} eq →
    let open RS (H′.₀ (F.₀ (Y , X) , F.₀ (X , Y))) in begin
      H′.₁ (F.₁ (f , Δ.id) , F.₁ (Δ.id , f)) $ α.α (F.₀ (X , X)) $ H.₁ (F.₁ (Δ.id , f) , F.₁ (f , Δ.id)) $ x
        ≈⟨ [ H′ ]-decompose₁ (Func.cong (α.α _) ([ H ]-decompose₁ eq)) ⟩
      H′.₁ (F.₁ (f , Δ.id) , Γ.id) $ H′.₁ (Γ.id , F.₁ (Δ.id , f)) $ α.α (F.₀ (X , X)) $ H.₁ (F.₁ (Δ.id , f) , Γ.id) $ H.₁ (Γ.id , F.₁ (f , Δ.id)) $ y
        ≈⟨ Func.cong (H′.₁ _) (α.commute (F.₁ (Δ.id , f)) HS.refl) ⟩
      H′.₁ (F.₁ (f , Δ.id) , Γ.id) $ H′.₁ (F.₁ (Δ.id , f) , Γ.id) $ α.α (F.₀ (X , Y)) $ H.₁ (Γ.id , F.₁ (Δ.id , f)) $ H.₁ (Γ.id , F.₁ (f , Δ.id)) $ y
        ≈⟨ [ H′ ]-resp-square ([ F ]-commute , Γ.refl) (Func.cong (α.α _) ([ H ]-resp-square (Γ.refl , [ F ]-commute) HS.refl)) ⟩
      H′.₁ (F.₁ (Δ.id , f) , Γ.id) $ H′.₁ (F.₁ (f , Δ.id) , Γ.id) $ α.α (F.₀ (X , Y)) $ H.₁ (Γ.id , F.₁ (f , Δ.id)) $ H.₁ (Γ.id , F.₁ (Δ.id , f)) $ y
        ≈⟨ Func.cong (H′.₁ _) (α.op-commute (F.₁ (f , Δ.id)) HS.refl) ⟩
      H′.₁ (F.₁ (Δ.id , f) , Γ.id) $ H′.₁ (Γ.id , F.₁ (f , Δ.id)) $ α.α (F.F₀ (Y , Y)) $ H.₁ (F.₁ (f , Δ.id) , Γ.id) $ H.₁ (Γ.id , F.₁ (Δ.id , f)) $ y
        ≈⟨ [ H′ ]-merge Γ.id-0 Γ.id-0 (Func.cong (α.α (F.F₀ (Y , Y))) ([ H ]-merge Γ.id-0 Γ.id-0 HS.refl)) ⟩
      H′.₁ (F.₁ (Δ.id , f) , F.₁ (f , Δ.id)) $ α.α (F.₀ (Y , Y)) $ H.₁ (F.₁ (f , Δ.id) , F.₁ (Δ.id , f)) $ y ∎
    }
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module Δ = Reason Δ
    module F = Functor F
    module H = Functor H
    module H′ = Functor H′
    module HS {A} = Setoid (F₀ H A)
    module H′S {A} = Setoid (F₀ H′ A)
    open Reason A

-- derivable in terms of reindexing for F = Swap, given here for a cleaner statement
squash :
    DinaturalTransformation {C = A ⊗ op A} F G
  → DinaturalTransformation {C = A} (F ∘F (idF ※ Swap)) (G ∘F (idF ※ Swap))
squash {A = A} {F = F} {G = G} α = dtHelper record
  { α = λ X → α.α (X , X)
  ; commute = λ { {X} {Y} f eq → let open RS (G.F₀ ((X , Y) , Y , X)) in
      begin    G.₁ ((A.id , f) , f , A.id)
               $ α.α (X , X)
               $ F.₁ ((f , A.id) , A.id , f)
               $ _  ≈˘⟨ [ G ]-merge (A.id-0 , A.id-1) (A.id-0 , A.id-0) (Func.cong (α.α _) ([ F ]-merge (A.id-0 , A.id-0) (A.id-0 , A.id-1) FS.refl)) ⟩
                G.₁ ((A.id , f) , A.id , A.id)
               $ G.₁ ((A.id , A.id) , f , A.id)
               $ α.α (X , X)
               $ F.₁ ((f , A.id) , A.id , A.id)
               $ F.₁ ((A.id , A.id) , A.id , f)
               $ _ ≈⟨ Func.cong (G.₁ _) (α.commute (f , A.id) (Func.cong (F.₁ _) eq)) ⟩
               G.₁ ((A.id , f) , A.id , A.id)
                $ G.₁ ((f , A.id) , A.id , A.id)
                $ α.α (Y , X)
                $ F.₁ ((A.id , A.id) , f , A.id)
                $ F.₁ ((A.id , A.id) , A.id , f)
                $ _ ≈⟨ [ G ]-resp-square (((A.id-swap , A.id-swap) , A.refl , A.refl)) (Func.cong (α.α _) ([ F ]-resp-square ((A.refl , A.refl) , A.id-swap , A.id-swap) FS.refl)) ⟩
               G.₁ ((f , A.id) , A.id , A.id)
                $ G.₁ ((A.id , f) , A.id , A.id)
                $ α.α (Y , X)
                $ F.₁ ((A.id , A.id) , A.id , f)
                $ F.₁ ((A.id , A.id) , f , A.id)
                $ _ ≈⟨ Func.cong (G.₁ _) (α.op-commute (A.id , f) FS.refl)  ⟩
               G.₁ ((f , A.id) , A.id , A.id)
                $ G.₁ ((A.id , A.id) , A.id , f)
                $ α.α (Y , Y)
                $ F.₁ ((A.id , f) , A.id , A.id)
                $ F.₁ ((A.id , A.id) , f , A.id)
                $ _ ≈⟨ [ G ]-merge (A.id-0 , A.id-0) (A.id-0 , A.id-1) (Func.cong (α.α _) ([ F ]-merge (A.id-0 , A.id-1) (A.id-0 , A.id-0) FS.refl)) ⟩
               G.₁ ((f , A.id) , A.id , f)
                $ α.α (Y , Y)
                $ F.₁ ((A.id , f) , f , A.id)
                $ _ ∎ }
  } where
  module F = Functor F
  module G = Functor G
  module α = DinaturalTransformation α
  module A = Reason A
  module FS {A} = Setoid (F₀ F A)


-- special case of reindexing combined with weakening
reindexing+weakening : ∀ {o} {A Γ : Category o ℓ ℓ}
         {H : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
         {G : Functor ((op (A ⊗ Γ)) ⊗ (A ⊗ Γ)) (Setoids ℓ ℓ)}
           (F : Functor (op Γ ⊗ Γ) A)
  → DinaturalTransformation H G
  → DinaturalTransformation (H ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ))
                            (G ∘F ((Functor.op F ∘F Swap ※ πˡ) ※ F ※ πʳ))
reindexing+weakening {A = A} {Γ = Γ} {H = H} {G = G} F α = dtHelper (record
  { α = λ X → record { to = λ p → α.α (_ , X) $ p ; cong = Func.cong (α.α (F₀ F (X , X) , X)) }
  ; commute = λ { {X} {Y} f {x} {y} eq →
    let open RS (F₀ G ((F₀ F (Y , X) , X) , F₀ F (X , Y) , Y)) in
      begin   G.₁ ((F.₁ (f , Γ.id) , Γ.id) , F.₁ (Γ.id , f) , f)
            $ α.α _
            $ H.₁ ((F.₁ (Γ.id , f) , f) , F.₁ (f , Γ.id) , Γ.id)
            $ x
              ≈˘⟨ [ G ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) (Func.cong (α.α _) ([ H ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) HS.refl)) ⟩
              G.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ G.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ α.α _
            $ H.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ H.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ x ≈⟨ Func.cong (G.₁ _) (α.commute (F.₁ (Γ.id , f) , f) HS.refl) ⟩
              G.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ G.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ α.α _
            $ H.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ H.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ x ≈⟨ [ G ]-resp-square (([ F ]-commute , Γ.id-swap) , A.refl , Γ.refl)
                  (Func.cong (α.α _)
                  ([ H ]-resp-square ((A.refl , Γ.refl) , [ F ]-commute , Γ.id-swap) eq)) ⟩
              G.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ G.₁ ((F.₁ (f , Γ.id) , Γ.id) , id , Γ.id)
            $ α.α _
            $ H.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ H.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ≈⟨ Func.cong (G.₁ _) (α.op-commute (F.F₁ (f , Γ.id) , Γ.id) HS.refl) ⟩
              G.₁ ((F.₁ (Γ.id , f) , f) , id , Γ.id)
            $ G.₁ ((id , Γ.id) , F.₁ (f , Γ.id) , Γ.id)
            $ α.α _
            $ H.₁ ((F.₁ (f , Γ.id)  , Γ.id) , id , Γ.id)
            $ H.₁ ((id , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ≈⟨ [ G ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) (Func.cong (α.α _) ([ H ]-merge (A.id-0 , Γ.id-0) (A.id-0 , Γ.id-0) HS.refl)) ⟩
              G.₁ ((F.₁ (Γ.id , f) , f) , F.₁ (f , Γ.id) , Γ.id)
            $ α.α _
            $ H.₁ ((F.₁ (f , Γ.id) , Γ.id) , F.₁ (Γ.id , f) , f)
            $ y ∎ }
  }) where
    module α = DinaturalTransformation α
    module Γ = Reason Γ
    module H = Functor H
    module GS {X} = Setoid (F₀ G X)
    module HS {X} = Setoid (F₀ H X)
    module G = Functor G
    module F = Functor F
    open module A = Reason A
