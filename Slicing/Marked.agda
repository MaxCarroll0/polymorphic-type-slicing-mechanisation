-- Marked representatives of every slice family used by interaction slicing.
-- The order is deliberately inherited from the already-proved unmarked
-- slice: marks are explanatory decoration, not additional program content.
module Slicing.Marked where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; Σ-syntax; ∃-syntax) renaming (_×_ to _∧_)
open import Function using (_on_)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Core
open import Core.MExp using (MExp)
open import Core.MCtx using (MCtx)
open import Semantics.Statics
open import Semantics.Marking.Judgment
open import Semantics.Marking.CtxMarking
open import Semantics.Marking.Erasure
open import Semantics.Marking.Embedding
open import Slicing.Synthesis.Synthesis
import Slicing.Synthesis.Synthesis as SS
open import Slicing.Analysis.Analysis
import Slicing.Analysis.Analysis as AS
open import Slicing.Full.Full

record MarkedSynSlice
    {n : ℕ} {Γ : Assms} {e : Exp} {τ : Typ}
    (D : n , Γ ⊢ e ⇑ τ) (u : ⌊ τ ⌋) : Set where
  field
    slice        : SynSlice D ◂ u
    marked-exp   : MExp
    erase-exp    : erase marked-exp ≡ SynSlice_◂_.↓σ slice
    marked-syn   :
      n , SynSlice_◂_.↓γ slice ⊢ SynSlice_◂_.↓σ slice
        ↬ marked-exp ⇑ SynSlice_◂_.↓ϕ slice
open MarkedSynSlice public

mark-syn-slice : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {u}
  → SynSlice D ◂ u → MarkedSynSlice D u
mark-syn-slice s = record
  { slice = s
  ; marked-exp = embed (SynSlice_◂_.↓σ s)
  ; erase-exp = erase-embed _
  ; marked-syn = mark-typing-syn (SynSlice_◂_.syn s)
  }

instance
  marked-syn-slice-precision : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {u}
    → HasPrecision (MarkedSynSlice D u)
  marked-syn-slice-precision = record
    { _≈_ = _≈_ on slice
    ; _⊑_ = _⊑_ on slice
    ; isDecPartialOrder = On.isDecPartialOrder slice
        (HasPrecision.isDecPartialOrder syn-slice-precision)
    }

mark-syn-minimal : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {u}
  → (s : SynSlice D ◂ u) → SS.IsMinimal s → SS.IsMinimal (mark-syn-slice s)
mark-syn-minimal s minimal r r⊑ = minimal (slice r) r⊑

record MarkedAnaSlice
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms} {τ τₚ : Typ}
    (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ])
    (u : ⌊ τ ⌋) : Set where
  field
    ana-slice      : AnaSlice Cls u
    marked-context : MCtx
    erase-context  : eraseCtx marked-context ≡ AnaSlice.κ ana-slice .↓
    marked-valid   : ∃[ n'' ] ∃[ Γ' ]
      n , AnaSlice.γ ana-slice .↓ ⊢ AnaSlice.κ ana-slice .↓ ↬ marked-context
        at synPos (AnaSlice.type ana-slice .↓) ▷ n'' , Γ'
        [ ⇐mode (AnaSlice.focus ana-slice .↓) ]
open MarkedAnaSlice public

mark-ana-slice : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
  → AnaSlice Cls u → MarkedAnaSlice Cls u
mark-ana-slice s with AnaSlice.valid s
... | n'' , Γ' , cls = record
  { ana-slice = s
  ; marked-context = embedCtx (AnaSlice.κ s .↓)
  ; erase-context = erase-embedCtx _
  ; marked-valid = n'' , Γ' , mark-syn-cls cls
  }

instance
  marked-ana-slice-precision : ∀ {n Γ₀ C n' Γ τ τₚ}
    {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
    → HasPrecision (MarkedAnaSlice Cls u)
  marked-ana-slice-precision = record
    { _≈_ = _≈_ on ana-slice
    ; _⊑_ = _⊑_ on ana-slice
    ; isDecPartialOrder = On.isDecPartialOrder ana-slice
        (HasPrecision.isDecPartialOrder anaSlice-precision)
    }

MarkedAnaMinimal : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
  → MarkedAnaSlice Cls u → Set
MarkedAnaMinimal s = ∀ r → r ⊑ s → s ⊑ r

mark-ana-minimal : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
  → (s : AnaSlice Cls u) → AS.IsMinimal s → MarkedAnaMinimal (mark-ana-slice s)
mark-ana-minimal s minimal r r⊑ = minimal (ana-slice r) r⊑

record MarkedAnaPosSlice
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms} {τ τₚ : Typ}
    (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ])
    (u : ⌊ τ ⌋) : Set where
  field
    ana-pos-slice       : AnaPosSlice Cls u
    marked-pos-context  : MCtx
    erase-pos-context   : eraseCtx marked-pos-context ≡ ana-κ ana-pos-slice .↓
    marked-pos-valid    : ∃[ n'' ] ∃[ Γ' ]
      n , ana-γ ana-pos-slice .↓ ⊢ ana-κ ana-pos-slice .↓ ↬ marked-pos-context
        at anaPos (ana-υ_outer ana-pos-slice .↓) ▷ n'' , Γ'
        [ ⇐mode (ana-focus ana-pos-slice .↓) ]
open MarkedAnaPosSlice public

mark-ana-pos-slice : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
  → AnaPosSlice Cls u → MarkedAnaPosSlice Cls u
mark-ana-pos-slice s with ana-valid s
... | n'' , Γ' , cls = record
  { ana-pos-slice = s
  ; marked-pos-context = embedCtx (ana-κ s .↓)
  ; erase-pos-context = erase-embedCtx _
  ; marked-pos-valid = n'' , Γ' , mark-ana-cls cls
  }

instance
  marked-ana-pos-slice-precision : ∀ {n Γ₀ C n' Γ τ τₚ}
    {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
    → HasPrecision (MarkedAnaPosSlice Cls u)
  marked-ana-pos-slice-precision = record
    { _≈_ = _≈_ on ana-pos-slice
    ; _⊑_ = _⊑_ on ana-pos-slice
    ; isDecPartialOrder = On.isDecPartialOrder ana-pos-slice
        (HasPrecision.isDecPartialOrder anaPosSlice-precision)
    }

MarkedAnaPosMinimal : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
  → MarkedAnaPosSlice Cls u → Set
MarkedAnaPosMinimal s = ∀ r → r ⊑ s → s ⊑ r

mark-ana-pos-minimal : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
  → (s : AnaPosSlice Cls u) → AS.IsMinimalPos s → MarkedAnaPosMinimal (mark-ana-pos-slice s)
mark-ana-pos-minimal s minimal r r⊑ = minimal (ana-pos-slice r) r⊑

record MarkedSynTypeSlice
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms}
    {e : Exp} {τ τₚ : Typ}
    (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ])
    (D : n' , Γ ⊢ e ⇑ τ) (u : ⌊ τ ⌋) : Set where
  field
    full-slice          : SynTypeSlice Cls D u
    marked-full-context : MCtx
    marked-full-focus   : MExp
    erase-full-context  : eraseCtx marked-full-context ≡ SynTypeSlice.κ full-slice .↓
    erase-full-focus    : erase marked-full-focus ≡ SynSlice_◂_.↓σ (SynTypeSlice.focus-slice full-slice)
    marked-powered      :
      Σ[ n'' ∈ ℕ ] Σ[ Γᶠ ∈ ⌊ Γ ⌋ ] Σ[ φᶠ ∈ ⌊ τ ⌋ ]
        (SynSlice_◂_.↓γₛ (SynTypeSlice.focus-slice full-slice) ⊑ₛ Γᶠ) ∧
        (n , SynTypeSlice.γ full-slice .↓ ⊢ SynTypeSlice.κ full-slice .↓
          ↬ marked-full-context at synPos (SynTypeSlice.outer full-slice .↓)
          ▷ n'' , Γᶠ .↓ [ ⇒mode (φᶠ .↓) ]) ∧
        (n'' , Γᶠ .↓ ⊢ SynSlice_◂_.↓σ (SynTypeSlice.focus-slice full-slice)
          ↬ marked-full-focus ⇑ φᶠ .↓)
open MarkedSynTypeSlice public

mark-syn-type-slice : ∀ {n Γ₀ C n' Γ e τ τₚ}
  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
  {D : n' , Γ ⊢ e ⇑ τ} {u}
  → SynTypeSlice Cls D u → MarkedSynTypeSlice Cls D u
mark-syn-type-slice s with SynTypeSlice.powered s
... | n'' , Γᶠ , φᶠ , γ⊑ , cls , d = record
  { full-slice = s
  ; marked-full-context = embedCtx (SynTypeSlice.κ s .↓)
  ; marked-full-focus = embed (SynSlice_◂_.↓σ (SynTypeSlice.focus-slice s))
  ; erase-full-context = erase-embedCtx _
  ; erase-full-focus = erase-embed _
  ; marked-powered = n'' , Γᶠ , φᶠ , γ⊑ , mark-syn-cls cls , mark-typing-syn d
  }

instance
  marked-syn-type-slice-precision : ∀ {n Γ₀ C n' Γ e τ τₚ}
    {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
    {D : n' , Γ ⊢ e ⇑ τ} {u} → HasPrecision (MarkedSynTypeSlice Cls D u)
  marked-syn-type-slice-precision = record
    { _≈_ = _≈_ on full-slice
    ; _⊑_ = _⊑_ on full-slice
    ; isDecPartialOrder = On.isDecPartialOrder full-slice
        (HasPrecision.isDecPartialOrder syn-type-slice-precision)
    }

mark-syn-type-minimal : ∀ {n Γ₀ C n' Γ e τ τₚ}
  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
  {D : n' , Γ ⊢ e ⇑ τ} {u}
  → (s : SynTypeSlice Cls D u) → SS.IsMinimal s → SS.IsMinimal (mark-syn-type-slice s)
mark-syn-type-minimal s minimal r r⊑ = minimal (full-slice r) r⊑

record MarkedSynPosTypeSlice
    {n : ℕ} {Γ₀ : Assms} {C : Ctx} {n' : ℕ} {Γ : Assms}
    {e : Exp} {τ τₚ : Typ}
    (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ])
    (D : n' , Γ ⊢ e ⇑ τ) (u : ⌊ τ ⌋) : Set where
  field
    full-pos-slice          : SynPosTypeSlice Cls D u
    marked-full-pos-context : MCtx
    marked-full-pos-focus   : MExp
    erase-full-pos-context  : eraseCtx marked-full-pos-context ≡ SynPosTypeSlice.pos-κ full-pos-slice .↓
    erase-full-pos-focus    : erase marked-full-pos-focus ≡ SynSlice_◂_.↓σ (SynPosTypeSlice.pos-focus-slice full-pos-slice)
    marked-pos-powered      :
      Σ[ n'' ∈ ℕ ] Σ[ Γᶠ ∈ ⌊ Γ ⌋ ] Σ[ φᶠ ∈ ⌊ τ ⌋ ]
        (SynSlice_◂_.↓γₛ (SynPosTypeSlice.pos-focus-slice full-pos-slice) ⊑ₛ Γᶠ) ∧
        (n , SynPosTypeSlice.pos-γ full-pos-slice .↓ ⊢ SynPosTypeSlice.pos-κ full-pos-slice .↓
          ↬ marked-full-pos-context at anaPos (SynPosTypeSlice.pos-outer full-pos-slice .↓)
          ▷ n'' , Γᶠ .↓ [ ⇒mode (φᶠ .↓) ]) ∧
        (n'' , Γᶠ .↓ ⊢ SynSlice_◂_.↓σ (SynPosTypeSlice.pos-focus-slice full-pos-slice)
          ↬ marked-full-pos-focus ⇑ φᶠ .↓)
open MarkedSynPosTypeSlice public

mark-syn-pos-type-slice : ∀ {n Γ₀ C n' Γ e τ τₚ}
  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
  {D : n' , Γ ⊢ e ⇑ τ} {u}
  → SynPosTypeSlice Cls D u → MarkedSynPosTypeSlice Cls D u
mark-syn-pos-type-slice s with SynPosTypeSlice.pos-powered s
... | n'' , Γᶠ , φᶠ , γ⊑ , cls , d = record
  { full-pos-slice = s
  ; marked-full-pos-context = embedCtx (SynPosTypeSlice.pos-κ s .↓)
  ; marked-full-pos-focus = embed (SynSlice_◂_.↓σ (SynPosTypeSlice.pos-focus-slice s))
  ; erase-full-pos-context = erase-embedCtx _
  ; erase-full-pos-focus = erase-embed _
  ; marked-pos-powered = n'' , Γᶠ , φᶠ , γ⊑ , mark-ana-cls cls , mark-typing-syn d
  }

instance
  marked-syn-pos-type-slice-precision : ∀ {n Γ₀ C n' Γ e τ τₚ}
    {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
    {D : n' , Γ ⊢ e ⇑ τ} {u} → HasPrecision (MarkedSynPosTypeSlice Cls D u)
  marked-syn-pos-type-slice-precision = record
    { _≈_ = _≈_ on full-pos-slice
    ; _⊑_ = _⊑_ on full-pos-slice
    ; isDecPartialOrder = On.isDecPartialOrder full-pos-slice
        (HasPrecision.isDecPartialOrder syn-pos-type-slice-precision)
    }

mark-syn-pos-type-minimal : ∀ {n Γ₀ C n' Γ e τ τₚ}
  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
  {D : n' , Γ ⊢ e ⇑ τ} {u}
  → (s : SynPosTypeSlice Cls D u) → SS.IsMinimal s → SS.IsMinimal (mark-syn-pos-type-slice s)
mark-syn-pos-type-minimal s minimal r r⊑ = minimal (full-pos-slice r) r⊑

MinMarkedSynSlice : ∀ {n Γ e τ} (D : n , Γ ⊢ e ⇑ τ) → ⌊ τ ⌋ → Set
MinMarkedSynSlice D u = Σ[ s ∈ MarkedSynSlice D u ] SS.IsMinimal s

MinMarkedAnaSlice : ∀ {n Γ₀ C n' Γ τ τₚ}
  (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set
MinMarkedAnaSlice Cls u = Σ[ s ∈ MarkedAnaSlice Cls u ] MarkedAnaMinimal s

MinMarkedAnaPosSlice : ∀ {n Γ₀ C n' Γ τ τₚ}
  (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ]) → ⌊ τ ⌋ → Set
MinMarkedAnaPosSlice Cls u = Σ[ s ∈ MarkedAnaPosSlice Cls u ] MarkedAnaPosMinimal s

MinMarkedSynTypeSlice : ∀ {n Γ₀ C n' Γ e τ τₚ}
  (Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ])
  (D : n' , Γ ⊢ e ⇑ τ) → ⌊ τ ⌋ → Set
MinMarkedSynTypeSlice Cls D u = Σ[ s ∈ MarkedSynTypeSlice Cls D u ] SS.IsMinimal s

MinMarkedSynPosTypeSlice : ∀ {n Γ₀ C n' Γ e τ τₚ}
  (Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ])
  (D : n' , Γ ⊢ e ⇑ τ) → ⌊ τ ⌋ → Set
MinMarkedSynPosTypeSlice Cls D u = Σ[ s ∈ MarkedSynPosTypeSlice Cls D u ] SS.IsMinimal s

mark-min-syn-slice : ∀ {n Γ e τ} {D : n , Γ ⊢ e ⇑ τ} {u}
  → MinSynSlice D ◂ u → MinMarkedSynSlice D u
mark-min-syn-slice (s , minimal) = mark-syn-slice s , mark-syn-minimal s minimal

mark-min-ana-slice : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
  → MinAnaSlice Cls u → MinMarkedAnaSlice Cls u
mark-min-ana-slice (s , minimal) = mark-ana-slice s , mark-ana-minimal s minimal

mark-min-ana-pos-slice : ∀ {n Γ₀ C n' Γ τ τₚ}
  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇐mode τ ]} {u}
  → MinAnaPosSlice Cls u → MinMarkedAnaPosSlice Cls u
mark-min-ana-pos-slice (s , minimal) = mark-ana-pos-slice s , mark-ana-pos-minimal s minimal

mark-min-syn-type-slice : ∀ {n Γ₀ C n' Γ e τ τₚ}
  {Cls : n , Γ₀ ⊢ C at synPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
  {D : n' , Γ ⊢ e ⇑ τ} {u}
  → MinSynTypeSlice Cls D u → MinMarkedSynTypeSlice Cls D u
mark-min-syn-type-slice (s , minimal) =
  mark-syn-type-slice s , mark-syn-type-minimal s minimal

mark-min-syn-pos-type-slice : ∀ {n Γ₀ C n' Γ e τ τₚ}
  {Cls : n , Γ₀ ⊢ C at anaPos τₚ ▷ n' , Γ [ ⇒mode τ ]}
  {D : n' , Γ ⊢ e ⇑ τ} {u}
  → MinSynPosTypeSlice Cls D u → MinMarkedSynPosTypeSlice Cls D u
mark-min-syn-pos-type-slice (s , minimal) =
  mark-syn-pos-type-slice s , mark-syn-pos-type-minimal s minimal
