module Core.Exp where

open import Core.Exp.Base public hiding (_kind?_; diag; shallow-disequality)

open import Core.Exp.Equality
open import Core.Exp.Precision
open import Core.Exp.Lattice

open Core.Exp.Equality public using (exp-decEq)
open Core.Exp.Precision public
  using (⊑□; ⊑*; ⊑Var; ⊑λ; ⊑λu; ⊑∘; ⊑<>; ⊑&; ⊑ι₁; ⊑ι₂; ⊑case; ⊑π₁; ⊑π₂; ⊑Λ; ⊑def;
         exp-precision; exp-slice)
open Core.Exp.Lattice public
  using (exp-meet; exp-join; exp-meetSemilattice; exp-sliceLattice)
