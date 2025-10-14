{-
  This file lists all relevant files of the formalization.
-}

--------------------- Common ------------------------

-- Helper library to quickly reason in agda-categories.
open import Reason

-- Definition of ends and coends.
open import Dinaturality.CoendFunctor
open import Dinaturality.EndFunctor

-- Definition of functor of dinaturals, used in the example for naturality.
open import Dinaturality.DinaturalsFunctor

--------------------- Theorems ------------------------

-- Bijection between dinatural transformations between presheaves and certain natural transformations with hom.
open import Dinaturality.NaturalDinatural

-- Dinatural transformations where the domain is a groupoid always compose.
open import Dinaturality.GroupoidCompose

--------------------- Rules ------------------------

-- Naturality example using the functor of dinaturals. [Rules: (exp)]
open import Dinaturality.NaturalityExample

-- Identity dinatural transformation. [Rules: (var)]
open import Dinaturality.Identity

-- Rules for coends. [Rules: (coend)]
open import Dinaturality.Coend

-- Rules for ends. [Rules: (end)]
open import Dinaturality.End

-- Rules for cuts. [Rules: (cut-din), (cut-nat)]
open import Dinaturality.Cut

-- Rules for cuts in the equational theory.
-- [Rules: (assoc-nat-din-nat), (cut-coherence), (cut-nat-id-l), (cut-nat-id-r), (cut-din-id-l), (cut-din-id-r)]
open import Dinaturality.CutAssociativity
open import Dinaturality.CutCoherence
open import Dinaturality.CutIdentities

------ Directed equality ------

-- Rules for J elimination and its inverse, and the isomorphism between them.
-- [Rules: (J), (J-comp), (J-eq)]
open import Dinaturality.J
open import Dinaturality.J-Inverse
open import Dinaturality.J-Iso     -- both directions showing that J is an isomorphism
open import Dinaturality.J-IsoA    -- top-bottom-top    direction of the isomorphism
open import Dinaturality.J-IsoB    -- bottom-top-bottom direction of the isomorphism

open import Dinaturality.Refl

------ Propositional rules ------

-- Rules for exponentials. [Rules: (exp)]
open import Dinaturality.Exponential

-- Rules for conjunction and terminal. [Rules: (prod), (⊤)]
open import Dinaturality.Product

-- Rules for reindexing with a diterm. [Rules: (idx)]
open import Dinaturality.Reindexing

-- Structural rules for conjunction. [Rules: (wk), (ctr), (exch)]
open import Dinaturality.Structural
