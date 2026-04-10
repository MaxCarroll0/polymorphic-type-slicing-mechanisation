module Core.Typ where
open import Agda.Builtin.FromNat using (Number; fromNat)

open import Core.Typ.Base public hiding (_kind?_; diag; shallow-disequality)
open import Core.Typ.Consistency public
open import Core.Typ.Equality public
open import Core.Typ.Precision public
open import Core.Typ.Lattice public
open import Core.Typ.Properties public
open import Core.Typ.Substitution public
