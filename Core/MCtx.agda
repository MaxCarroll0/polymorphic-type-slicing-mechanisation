-- Marked expression contexts: an MExp with exactly one hole, used by the marking-side
-- classification judgement in Semantics.Marking.CtxMarking.
-- Dissertation: §6.3 Marking (parallel to Core.Ctx for unmarked expressions).
module Core.MCtx where

open import Data.Nat using (ℕ)
open import Core.Typ using (Typ)
open import Core.Exp.Base using (Exp)
import Core.Exp.Base as E
open import Core.MExp

-- Marked context: a marked expression with exactly one hole ○ to plug an
-- MExp into. Mirrors the regular Ctx structure but allows mark-wrappers
-- along the path from root to hole.
data MCtx : Set where
  -- Hole
  ○                : MCtx

  -- Standard MExp constructor contexts (mirror Ctx with MExp-typed siblings)
  λ:_⇒_            : Typ → MCtx → MCtx          -- Annotated lambda; hole in body
  λ⇒_              : MCtx → MCtx                  -- Unannotated lambda; hole in body
  _∘₁_             : MCtx → MExp → MCtx          -- Application; hole on left
  _∘₂_             : MExp → MCtx → MCtx          -- Application; hole on right
  _<_>₁            : MCtx → Typ → MCtx           -- Type application; hole in expression
  _&₁_             : MCtx → MExp → MCtx          -- Pair; hole on left
  _&₂_             : MExp → MCtx → MCtx          -- Pair; hole on right
  ι₁               : MCtx → MCtx                  -- Left injection
  ι₂               : MCtx → MCtx                  -- Right injection
  case₀_of_·_      : MCtx → MExp → MExp → MCtx   -- Case; hole in scrutinee
  case_of_·₁_      : MExp → MCtx → MExp → MCtx   -- Case; hole in left branch
  case_of₂_·_      : MExp → MExp → MCtx → MCtx   -- Case; hole in right branch
  π₁               : MCtx → MCtx                  -- First projection
  π₂               : MCtx → MCtx                  -- Second projection
  Λ                : MCtx → MCtx                  -- Type abstraction
  def_⊢₁_          : MCtx → MExp → MCtx          -- Let; hole in definition
  def_⊢₂_          : MExp → MCtx → MCtx          -- Let; hole in body

  -- Mark wrappers: each represents an error mark on the path to the hole.
  -- These mirror the mark constructors in MExp; the structural context
  -- classification (Semantics/Marking/CtxMarking.agda) restricts where each
  -- mark may appear (e.g. ⦅▸⇒⦆ is only valid in the function position of
  -- an application).
  _⦅≁_⦆            : MCtx → Typ → MCtx           -- Type inconsistency (mark⇓sub⇑)
  _⦅▸⇒⦆            : MCtx → MCtx                  -- Expected arrow type   (mark⇑∘⇑)
  _⦅▸+⦆            : MCtx → MCtx                  -- Expected sum type     (mark⇑case⇑, mark⇓case⇑)
  _⦅▸×⦆            : MCtx → MCtx                  -- Expected product type (mark⇑π₁⇑, mark⇑π₂⇑)
  _⦅▸∀⦆            : MCtx → MCtx                  -- Expected ∀ type       (mark⇑<>⇑)
  _⦅~⇒⦆            : MCtx → MCtx                  -- Lambda in non-arrow   (mark⇑λ⇒, mark⇓λ⇑)
  _⦅~+⦆            : MCtx → MCtx                  -- Injection in non-sum  (mark⇑ι₁, mark⇑ι₂)

infixr 5  λ:_⇒_
infixr 5  λ⇒_
infixr 5  def_⊢₁_ def_⊢₂_
infixl 22 _∘₁_    _∘₂_
infixl 22 _<_>₁
infixl 23 _&₁_    _&₂_

-- Plug an MExp focus into the hole of an MCtx.
mplug : MCtx → MExp → MExp
mplug ○                  ě = ě
mplug (λ: τ ⇒ C)         ě = λ: τ ⇒ mplug C ě
mplug (λ⇒ C)             ě = λ⇒ mplug C ě
mplug (C ∘₁ ě')          ě = mplug C ě ∘ ě'
mplug (ě' ∘₂ C)          ě = ě' ∘ mplug C ě
mplug (C < τ >₁)         ě = mplug C ě < τ >
mplug (C &₁ ě')          ě = mplug C ě & ě'
mplug (ě' &₂ C)          ě = ě' & mplug C ě
mplug (ι₁ C)             ě = ι₁ (mplug C ě)
mplug (ι₂ C)             ě = ι₂ (mplug C ě)
mplug (case₀ C of ě' · ě'') ě = case mplug C ě of ě' · ě''
mplug (case ě' of C ·₁ ě'') ě = case ě' of mplug C ě · ě''
mplug (case ě' of₂ ě'' · C) ě = case ě' of ě'' · mplug C ě
mplug (π₁ C)             ě = π₁ (mplug C ě)
mplug (π₂ C)             ě = π₂ (mplug C ě)
mplug (Λ C)              ě = Λ (mplug C ě)
mplug (def C ⊢₁ ě')      ě = def mplug C ě ⊢ ě'
mplug (def ě' ⊢₂ C)      ě = def ě' ⊢ mplug C ě
mplug (C ⦅≁ τ ⦆)         ě = (mplug C ě) ⦅≁ τ ⦆
mplug (C ⦅▸⇒⦆)           ě = (mplug C ě) ⦅▸⇒⦆
mplug (C ⦅▸+⦆)           ě = (mplug C ě) ⦅▸+⦆
mplug (C ⦅▸×⦆)           ě = (mplug C ě) ⦅▸×⦆
mplug (C ⦅▸∀⦆)           ě = (mplug C ě) ⦅▸∀⦆
mplug (C ⦅~⇒⦆)           ě = (mplug C ě) ⦅~⇒⦆
mplug (C ⦅~+⦆)           ě = (mplug C ě) ⦅~+⦆
