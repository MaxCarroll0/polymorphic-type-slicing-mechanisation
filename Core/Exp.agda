module Core.Exp where

open import Core.Exp.Base public hiding (_kind?_; diag; shallow-disequality)
open import Core.Exp.Equality public hiding (_≟_)
open import Core.Exp.Precision public
  hiding (⊤ₛ; ⊤ₛ-max; module LiftMeetSemilattice;
          _⊑_; _⊑?_; SliceOf; ↓; _isSlice_; ↑; weaken; weaken-identity;
          _≈ₛ_; _≈ₛ?_; _⊑ₛ_; _⊑ₛ?_;
          module ⊑; module ≈ₛ; module ⊑ₛ)
open import Core.Exp.Lattice public
  hiding (module ⊓ₛ; _⊓_; _⊔_; _⊓ₛ_; _⊔ₛ_;
          module ⊑Lat; module ⊑ₛLat)
