-- Lifts context constructors to context slices, producing a sliced context
-- from sliced sub-contexts, sub-expressions, and annotation types.
module Core.Ctx.Lift where

open import Core.Typ
open import Core.Exp.Base
open import Core.Exp.Precision
open import Core.Ctx.Base
open import Core.Ctx.Precision
open import Core.Instances

○ₖ : ⌊ ○ ⌋
○ₖ = ○ isSlice ⊑○

λ:ₖ : ∀ {τ₁ : Typ} {C : Ctx} → ⌊ τ₁ ⌋ → ⌊ C ⌋ → ⌊ λ: τ₁ ⇒ C ⌋
λ:ₖ (τ isSlice τ⊑τ₁) (κ isSlice κ⊑C) = (λ: τ ⇒ κ) isSlice (⊑λ τ⊑τ₁ κ⊑C)

λ⇒ₖ : ∀ {C : Ctx} → ⌊ C ⌋ → ⌊ λ⇒ C ⌋
λ⇒ₖ (κ isSlice κ⊑C) = (λ⇒ κ) isSlice (⊑λu κ⊑C)

_∘₁ₖ_ : ∀ {C : Ctx} {e : Exp} → ⌊ C ⌋ → ⌊ e ⌋ → ⌊ C ∘₁ e ⌋
(κ isSlice κ⊑C) ∘₁ₖ (σ isSlice σ⊑e) = (κ ∘₁ σ) isSlice (⊑∘₁ κ⊑C σ⊑e)

_∘₂ₖ_ : ∀ {e : Exp} {C : Ctx} → ⌊ e ⌋ → ⌊ C ⌋ → ⌊ e ∘₂ C ⌋
(σ isSlice σ⊑e) ∘₂ₖ (κ isSlice κ⊑C) = (σ ∘₂ κ) isSlice (⊑∘₂ σ⊑e κ⊑C)

_<>₁ₖ_ : ∀ {C : Ctx} {τ : Typ} → ⌊ C ⌋ → ⌊ τ ⌋ → ⌊ C < τ >₁ ⌋
(κ isSlice κ⊑C) <>₁ₖ (τ' isSlice τ'⊑τ) = (κ < τ' >₁) isSlice (⊑<>₁ κ⊑C τ'⊑τ)

_&₁ₖ_ : ∀ {C : Ctx} {e : Exp} → ⌊ C ⌋ → ⌊ e ⌋ → ⌊ C &₁ e ⌋
(κ isSlice κ⊑C) &₁ₖ (σ isSlice σ⊑e) = (κ &₁ σ) isSlice (⊑&₁ κ⊑C σ⊑e)

_&₂ₖ_ : ∀ {e : Exp} {C : Ctx} → ⌊ e ⌋ → ⌊ C ⌋ → ⌊ e &₂ C ⌋
(σ isSlice σ⊑e) &₂ₖ (κ isSlice κ⊑C) = (σ &₂ κ) isSlice (⊑&₂ σ⊑e κ⊑C)

ι₁ₖ : ∀ {C : Ctx} → ⌊ C ⌋ → ⌊ ι₁ C ⌋
ι₁ₖ (κ isSlice κ⊑C) = (ι₁ κ) isSlice (⊑ι₁ κ⊑C)

ι₂ₖ : ∀ {C : Ctx} → ⌊ C ⌋ → ⌊ ι₂ C ⌋
ι₂ₖ (κ isSlice κ⊑C) = (ι₂ κ) isSlice (⊑ι₂ κ⊑C)

case₀ₖ : ∀ {C : Ctx} {e f : Exp} → ⌊ C ⌋ → ⌊ e ⌋ → ⌊ f ⌋ → ⌊ case₀ C of e · f ⌋
case₀ₖ (κ isSlice κ⊑C) (σ isSlice σ⊑e) (σ' isSlice σ'⊑f) =
  (case₀ κ of σ · σ') isSlice (⊑case₀ κ⊑C σ⊑e σ'⊑f)

case₁ₖ : ∀ {e : Exp} {C : Ctx} {f : Exp} → ⌊ e ⌋ → ⌊ C ⌋ → ⌊ f ⌋ → ⌊ case e of C ·₁ f ⌋
case₁ₖ (σ isSlice σ⊑e) (κ isSlice κ⊑C) (σ' isSlice σ'⊑f) =
  (case σ of κ ·₁ σ') isSlice (⊑case₁ σ⊑e κ⊑C σ'⊑f)

case₂ₖ : ∀ {e f : Exp} {C : Ctx} → ⌊ e ⌋ → ⌊ f ⌋ → ⌊ C ⌋ → ⌊ case e of₂ f · C ⌋
case₂ₖ (σ isSlice σ⊑e) (σ' isSlice σ'⊑f) (κ isSlice κ⊑C) =
  (case σ of₂ σ' · κ) isSlice (⊑case₂ σ⊑e σ'⊑f κ⊑C)

π₁ₖ : ∀ {C : Ctx} → ⌊ C ⌋ → ⌊ π₁ C ⌋
π₁ₖ (κ isSlice κ⊑C) = (π₁ κ) isSlice (⊑π₁ κ⊑C)

π₂ₖ : ∀ {C : Ctx} → ⌊ C ⌋ → ⌊ π₂ C ⌋
π₂ₖ (κ isSlice κ⊑C) = (π₂ κ) isSlice (⊑π₂ κ⊑C)

Λₖ : ∀ {C : Ctx} → ⌊ C ⌋ → ⌊ Λ C ⌋
Λₖ (κ isSlice κ⊑C) = (Λ κ) isSlice (⊑Λ κ⊑C)

def₁ₖ : ∀ {C : Ctx} {e : Exp} → ⌊ C ⌋ → ⌊ e ⌋ → ⌊ def C ⊢₁ e ⌋
def₁ₖ (κ isSlice κ⊑C) (σ isSlice σ⊑e) = (def κ ⊢₁ σ) isSlice (⊑def₁ κ⊑C σ⊑e)

def₂ₖ : ∀ {e : Exp} {C : Ctx} → ⌊ e ⌋ → ⌊ C ⌋ → ⌊ def e ⊢₂ C ⌋
def₂ₖ (σ isSlice σ⊑e) (κ isSlice κ⊑C) = (def σ ⊢₂ κ) isSlice (⊑def₂ σ⊑e κ⊑C)
