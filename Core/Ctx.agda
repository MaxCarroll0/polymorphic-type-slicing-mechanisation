module Core.Ctx where

open import Core.Ctx.Base public hiding (_kind?_; diag; shallow-disequality)
open import Core.Ctx.Equality public hiding (_≟_)
open import Core.Ctx.Precision public
  hiding (⊤ₛ; ⊤ₛ-max; module LiftMeetSemilattice;
          _⊑_; _⊑?_; SliceOf; ↓; _isSlice_; ↑; weaken; weaken-identity;
          _≈ₛ_; _≈ₛ?_; _⊑ₛ_; _⊑ₛ?_;
          module ⊑; module ≈ₛ; module ⊑ₛ)
open import Core.Ctx.Lattice public
  hiding (_⊓_; _⊔_; _⊓ₛ_; _⊔ₛ_;
          module ⊑ₛLat)
