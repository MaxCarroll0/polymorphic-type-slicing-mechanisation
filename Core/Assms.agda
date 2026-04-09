module Core.Assms where

open import Core.Assms.Base public

open import Core.Assms.Equality
open import Core.Assms.Precision
open import Core.Assms.Lattice

open Core.Assms.Equality public using (assms-decEq)
open Core.Assms.Precision public
  using (⊑[]; ⊑∷;
         assms-precision; assms-slice)
open Core.Assms.Lattice public
  using (assms-meet; assms-join; assms-sliceLattice)
