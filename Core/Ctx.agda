module Core.Ctx where

open import Core.Ctx.Base public hiding (_kind?_; diag; shallow-disequality)

open import Core.Ctx.Equality
open import Core.Ctx.Precision
open import Core.Ctx.Lattice

open Core.Ctx.Equality public using (ctx-decEq)
open Core.Ctx.Precision public
  using (⊑○; ⊑λ; ⊑λu; ⊑∘₁; ⊑∘₂; ⊑<>₁; ⊑&₁; ⊑&₂; ⊑ι₁; ⊑ι₂; ⊑case₁; ⊑case₂; ⊑π₁; ⊑π₂; ⊑Λ; ⊑def₁; ⊑def₂;
         plug-preserves-⊑;
         ctx-precision; ctx-slice)
open Core.Ctx.Lattice public
  using (ctx-meet; ctx-join; ctx-sliceLattice)
