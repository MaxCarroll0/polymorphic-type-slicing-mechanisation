# Debugging marks with type slicing

This document maps each error mark form (defined in `Core/MExp.agda` and
introduced by the marking judgment in `Semantics/Marking/Judgment.agda`)
to a debugging strategy that uses the type-slicing infrastructure
(`Slicing/Synthesis/`, `Slicing/Analysis/`).

The marked context classification in `Semantics/Marking/CtxMarking.agda`
formalises *where* each mark may appear in a marked program; this
document describes *how* slicing helps the user understand each mark.

The premise: each error mark is the marking algorithm's record of a
local incompatibility between a focus's type and the surrounding
context's expectation. Type slicing isolates the *minimal subterms* —
both within the focus and within the surrounding context — responsible
for the incompatibility, giving a precise, actionable error report.

> **Note**: this assumes type slicing has been lifted to marked
> expressions (MExp). The unmarked-side slicing infrastructure can be
> applied to the *erasure* of an MExp, then re-projected; lifting the
> slice records directly to MExp is straightforward but is left as
> follow-up work.

---

## Type-driven marks (slicing applies)

### `_⦅≁_⦆` — Type inconsistency in subsumption

Inserted by `mark↤sub⇑` when an expression's synthesis type `τ'` is
inconsistent with the analysis-target type `τ`.

**Slicing strategy**:

1. **Slice the focus's syn type `τ'`** — `BoundedMinSynSlice` queried at
   the *minimal incompatibility witness* between `τ` and `τ'`. This
   gives the smallest subterm of the focus whose synthesis type is still
   inconsistent with `τ`.
2. **Slice the analysis context** — `AnaSlice` of the surrounding
   context `C`, queried at the same incompatibility. This produces a
   minimal `κ`-slice of `C` and a minimal outer-type slice `ψ ⊑ τ` that
   still enforces the inconsistency.
3. **Combine** — the user sees only the source-level fragments of the
   focus and the surrounding code that mutually fail consistency.

This is the *paradigmatic* case for slicing: the user gets an
explanation of "why these two types don't match" reduced to a small
explainable kernel.

### `_⦅▸⇒⦆` — Expected arrow type

Inserted by `mark↦∘⇑` (focus on function in an application) when the
function position synthesises a non-arrow type.

**Slicing strategy**:

1. **Slice the function's syn type** down to a `MinSynSlice` queried at
   "fails the `τ ⊔ □⇒□ ≡ τ₁ ⇒ τ₂` match" — i.e. a slice that still has
   a non-arrow head.
2. The `MinSynSlice` precisely identifies the smallest subterm of the
   function whose synthesised type is the wrong shape — typically a
   sub-expression of a larger composite (e.g. a tuple component, the
   wrong field of a record), letting the user fix it without reading
   the rest of the function.

### `_⦅▸+⦆` — Expected sum type

Inserted by `mark↦case⇑`/`mark↤case⇑` when a case scrutinee
synthesises a non-sum type.

**Slicing strategy**: same shape as `_⦅▸⇒⦆` but with the join target
`□+□`. Slice the scrutinee's synthesis type to find the smallest
subterm with a non-sum head.

### `_⦅▸×⦆` — Expected product type

Inserted by `mark↦π₁⇑`/`mark↦π₂⇑` when a projection's argument
synthesises a non-product type.

**Slicing strategy**: same shape as `_⦅▸⇒⦆` with join target `□×□`.

### `_⦅▸∀⦆` — Expected ∀ type

Inserted by `mark↦<>⇑` when a type application's expression
synthesises a non-`∀` type.

**Slicing strategy**: same shape as `_⦅▸⇒⦆` with join target `∀· □`.

### `_⦅~⇒⦆` — Lambda against non-arrow

Inserted by `mark↤λ⇑` when an unannotated lambda is analysed against a
non-arrow type, and by `mark↦λ⇒` when a bare unannotated lambda appears
in synthesis position.

**Slicing strategy** (analysis variant):

1. **Slice the analysis type `τ`** to find a minimal slice `τ-min ⊑ τ`
   that still has a non-arrow head.
2. **Slice the surrounding analysis context** (via `AnaSlice` on `C`)
   to identify which enclosing operation imposed this `τ`-shape — a
   manual annotation, a `def`-body, an injection's expected type, etc.

The synthesis variant is partially type-driven (the lambda has no syn
type), so type slicing only helps via the surrounding consumer's
expected type.

### `_⦅~+⦆` — Injection against non-sum / in synthesis

Inserted by `mark↦ι₁`/`mark↦ι₂` when a bare injection appears in
synthesis position.

**Slicing strategy**: similar to `_⦅~⇒⦆` synthesis variant — type
slicing helps via the surrounding consumer's expected type, not the
injection itself.

### `_⦅~×⦆` — Pair against non-product

Defined in `Core/MExp.agda` but **not currently used by any marking
rule**. Reserved for future expansion (e.g. analysing a pair against a
non-product type). The slicing strategy would mirror `_⦅~⇒⦆` analysis
variant.

---

## Non-type-driven marks (slicing does NOT apply)

### `⟨_⟩⇑` — Free / unbound variable

Inserted by `mark↦Var⇑` when a variable lookup fails (the variable is
not bound in scope).

**Why slicing doesn't help**: the mark is a *scope* error, not a *type*
error. The variable's type is undefined precisely because there's no
binding to look up. There is no incompatible-types pair to slice; no
sub-derivation explains "why the variable is missing".

**What tooling should do instead**: report `unbound variable k` with
the source location, and suggest:
- nearby in-scope variables (Levenshtein distance);
- the closest enclosing `def`/`λ` that *could* bind it (so the user can
  add a binding);
- the import structure if the language has one.

Type slicing has nothing useful to contribute and should not be
invoked.

---

## Summary table

| Mark         | Inserted by                        | Type-driven? | Slicing strategy |
|--------------|------------------------------------|:------------:|------------------|
| `⦅≁ τ ⦆`     | `mark↤sub⇑`                        | ✓            | Focus syn-slice + AnaSlice on context, queried at incompatibility |
| `⦅▸⇒⦆`       | `mark↦∘⇑`                          | ✓            | MinSynSlice on focus at "fails ⊔□⇒□" |
| `⦅▸+⦆`       | `mark↦case⇑` / `mark↤case⇑`        | ✓            | MinSynSlice on scrutinee at "fails ⊔□+□" |
| `⦅▸×⦆`       | `mark↦π₁⇑` / `mark↦π₂⇑`            | ✓            | MinSynSlice on focus at "fails ⊔□×□" |
| `⦅▸∀⦆`       | `mark↦<>⇑`                         | ✓            | MinSynSlice on focus at "fails ⊔∀·□" |
| `⦅~⇒⦆`       | `mark↤λ⇑` / `mark↦λ⇒`              | ✓ (partial)  | Slice analysis target τ + AnaSlice on enclosing context (analysis variant only) |
| `⦅~+⦆`       | `mark↦ι₁` / `mark↦ι₂`              | ✓ (partial)  | AnaSlice on enclosing consumer (synthesis variant) |
| `⦅~×⦆`       | (unused)                           | n/a          | (would mirror `⦅~⇒⦆`) |
| `⟨ k ⟩⇑`     | `mark↦Var⇑`                        | ✗            | **Slicing does not apply.** Report scope error with source location and binding suggestions. |
