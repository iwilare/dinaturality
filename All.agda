{-
  This file lists all relevant files of the formalization.
-}

--------------------- Common ------------------------

-- Helper library to quickly reason in agda-categories.
open import Reason

-- Definition of parametric (co)ends.
open import Dinaturality.EndFunctor
open import Dinaturality.CoendFunctor

-- Definition of functor of dinaturals, used in the example for naturality.
open import Dinaturality.DinaturalsFunctor

--------------------- Theorems ------------------------

-- Bijection between dinatural transformations between presheaves and certain natural transformations with hom.
open import Dinaturality.NaturalDinatural

-- Dinatural transformations where the domain is a groupoid always compose.
open import Dinaturality.GroupoidCompose

--------------------- Rules ------------------------

-- Naturality example using the functor of dinaturals, focusing on rule (exp).
open import Dinaturality.NaturalityExample

-- Identity dinatural transformation. [Rules: (var)]
-- (Semantically, this captures the situation in which the context
-- has a single hypothesis. In practice, the variable case is modeled using
-- projections in Dinaturality.Product, since we work with propositional contexts
-- which have a list of hypotheses and the var case simply projects away the correct one.)
open import Dinaturality.Identity

-- Rules for ends and coends. [Rules: (coend), (end)]
open import Dinaturality.End
open import Dinaturality.Coend
open import Dinaturality.Quantifiers

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

-- Rules for polarized implication. [Rules: (exp)]
open import Dinaturality.Implication

-- Rules for conjunction and terminal. [Rules: (prod), (⊤)]
open import Dinaturality.Product

-- Rules for reindexing with a diterm. [Rules: (idx)]
open import Dinaturality.Reindexing

-- Structural rules for conjunction. [Rules: (wk), (ctr), (exch)]
open import Dinaturality.Structural
