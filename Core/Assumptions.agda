module Core.Assumptions where

open import Core.Assumptions.Base public

open import Core.Assumptions.Equality public

-- Precision: rename relation, slices, and records
open import Core.Assumptions.Precision public
  hiding (⊤ₛ; ⊤ₛ-max)

-- Lattice: rename operators and records
open import Core.Assumptions.Lattice public
