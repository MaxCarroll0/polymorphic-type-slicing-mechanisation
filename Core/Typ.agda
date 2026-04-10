module Core.Typ where
open import Agda.Builtin.FromNat using (Number; fromNat)

open import Core.Typ.Base public hiding (_kind?_; diag; shallow-disequality)
open import Core.Typ.Consistency public
open import Core.Typ.Equality public hiding (_≟_)
open import Core.Typ.Precision public
  hiding (⊤ₛ; ⊤ₛ-max; module LiftMeetSemilattice;
          _⊑_; _⊑?_; SliceOf; ↓; _isSlice_; ↑; weaken; weaken-identity;
          _≈ₛ_; _≈ₛ?_; _⊑ₛ_; _⊑ₛ?_;
          module ⊑; module ≈ₛ; module ⊑ₛ)
open import Core.Typ.Lattice public
  hiding (module ⊓ₛ; _⊓_; _⊔_; _⊓ₛ_; _⊔ₛ_;
          module ⊑Lat; module ⊑ₛLat)
open import Core.Typ.Properties public
open import Core.Typ.Substitution public
