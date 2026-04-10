module Core.Assms where

open import Core.Assms.Base public
open import Core.Assms.Equality public hiding (_≟_)
open import Core.Assms.Precision public
  hiding (⊤ₛ; ⊤ₛ-max; module LiftMeetSemilattice;
          _⊑_; _⊑?_; SliceOf; ↓; _isSlice_; ↑; weaken; weaken-identity;
          _≈ₛ_; _≈ₛ?_; _⊑ₛ_; _⊑ₛ?_;
          module ⊑; module ≈ₛ; module ⊑ₛ)
open import Core.Assms.Lattice public
  hiding (_⊓_; _⊔_; _⊓ₛ_; _⊔ₛ_;
          module ⊑ₛLat)
