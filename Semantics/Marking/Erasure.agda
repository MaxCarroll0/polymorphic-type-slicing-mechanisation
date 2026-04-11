module Semantics.Marking.Erasure where

open import Data.Nat using (ℕ)
open import Core.Typ using (Typ)
open import Core.Exp.Base as Exp
open import Core.MExp as M

erase : MExp → Exp
erase M.□                     = Exp.□
erase M.*                     = Exp.*
erase M.⟨ n ⟩                 = Exp.⟨ n ⟩
erase (M.λ: τ ⇒ ě)           = Exp.λ: τ ⇒ erase ě
erase (M.λ⇒ ě)               = Exp.λ⇒ erase ě
erase (ě₁ M.∘ ě₂)            = erase ě₁ Exp.∘ erase ě₂
erase (ě M.< τ >)             = erase ě Exp.< τ >
erase (ě₁ M.& ě₂)            = erase ě₁ Exp.& erase ě₂
erase (M.ι₁ ě)               = Exp.ι₁ (erase ě)
erase (M.ι₂ ě)               = Exp.ι₂ (erase ě)
erase (M.case ě of ě₁ · ě₂)  = Exp.case erase ě of erase ě₁ · erase ě₂
erase (M.π₁ ě)               = Exp.π₁ (erase ě)
erase (M.π₂ ě)               = Exp.π₂ (erase ě)
erase (M.Λ ě)                = Exp.Λ (erase ě)
erase (M.def ě₁ ⊢ ě₂)       = Exp.def erase ě₁ ⊢ erase ě₂
erase (M.⟨ n ⟩⇑)             = Exp.⟨ n ⟩
erase (ě ⦅≁ _ ⦆)             = erase ě
erase (ě ⦅▸⇒⦆)               = erase ě
erase (ě ⦅▸+⦆)               = erase ě
erase (ě ⦅▸×⦆)               = erase ě
erase (ě ⦅▸∀⦆)               = erase ě
erase (ě ⦅~⇒⦆)               = erase ě
erase (ě ⦅~+⦆)               = erase ě
erase (ě ⦅~×⦆)               = erase ě
