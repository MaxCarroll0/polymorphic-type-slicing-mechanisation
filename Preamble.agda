module Preamble where

-- Data types
open import Data.Nat public using (ℕ; _≟_)
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Sum public using (_⊎_; inj₁; inj₂)
open import Data.Product public using (_×_; _,_; proj₁; proj₂; ∃-syntax; curry; uncurry)

-- Relations
open import Relation.Binary public
  using (Poset; IsPartialOrder; IsPreorder; IsEquivalence)
open import Relation.Binary.Definitions public
  using (Reflexive; Symmetric; Transitive; Antisymmetric; Maximum; Minimum)
open import Relation.Binary.PropositionalEquality as Eq public
open Eq.≡-Reasoning public
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

-- Lattices
open import Relation.Binary.Lattice.Structures public
  using (IsMeetSemilattice; IsJoinSemilattice; IsLattice; IsBoundedLattice)
open import Relation.Binary.Lattice.Definitions public
  using (Infimum; Supremum)

-- Decidability
open import Relation.Nullary public using (Dec; yes; no; ¬_; map′)
open import Relation.Nullary.Decidable public using (_×-dec_)

-- Functions
open import Function public using (_∘_; _⇔_; _on_)
