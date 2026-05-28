-- Dissertation: §4.1 Syntax & Relations, §4.2 Lattice Properties.
module Core.Exp where

open import Core.Exp.Base public hiding (_kind?_; diag; shallow-disequality)
open import Core.Exp.Equality public
open import Core.Exp.Precision public
open import Core.Exp.Lattice public
open import Core.Exp.Lift public
