module Core.Typ where
open import Agda.Builtin.FromNat using (Number; fromNat)

open import Core.Typ.Base public hiding (_kind?_; diag; shallow-disequality)
open import Core.Typ.Consistency public
open import Core.Typ.Properties public
open import Core.Typ.Substitution public

-- Import sub-modules; re-export instances + selected non-names
open import Core.Typ.Equality
open import Core.Typ.Precision
open import Core.Typ.Lattice

open Core.Typ.Equality public using (typ-decEq)
open Core.Typ.Precision public
  using (⊑□; ⊑*; ⊑Var; ⊑+; ⊑×; ⊑⇒; ⊑∀;
         ⊑to~; ⊑-consistent;
         typ-precision; typ-slice)
open Core.Typ.Lattice public
  using (module ~;
         typ-meet; typ-join; typ-meetSemilattice; typ-sliceLattice)
