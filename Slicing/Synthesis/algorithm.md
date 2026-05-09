This is how the mincase slice algorithm should work:

If \upsilon = \square, then return \square as slice. Else:

# Phase 1: (Branch Fixed point)
Calculate fixed point satisfying *exactly* the following conditions:
- D₁ ◂ υ₁ ⤳ σ₁ ↦ ψ₁ ⊣ γ₁ // (calculated recursively)
- D₂ ◂ υ₂ ⤳ σ₂ ↦ ψ₂ ⊣ γ₂
- ⊔-inlₛ c υ₁ ⊑ₛ (υ \\ₛ ⊔-inrₛ c ψ₂)
- ⊔-inrₛ c υ₂ ⊑ₛ (υ \\ₛ ⊔-inlₛ c ψ₁)
- υ .↓ ⊑ ψ₁ .↓ ⊔ ψ₂ .↓

Set \upsilon\_1 = L \upsilon
Then iterate \upsilon\_1 ==> \psi\_1

Coverage is trivially satisfies as \upsilon\_1 \sqsubseteq \psi\_1 and \upsilon\_2 \sqsubseteq \psi\_2. (By co-heyting join rule)

Set \upsilon\_2 = \upsilon \\\_s \psi\_1 ==> \psi\_2
Re-slice \upsilon\_1 = \upsilon \\\_s \psi\_2 ==> \psi\_1'
etc.

By anti-monotonicity, as \psi\_1 decreases \upsilon\_2 increases and as \psi\_2 increases \upsilon\_1 decreases. By reslicing the \sigma at each step (similarly to phase 2) we get that as \upsilon\_1 decreases so do \psi\_1. However, this does not necessarily hold for \psi\_2 increasing as \upsilon\_2 increases (see counterexamples.agda).

For now: just do a decidability check on whether \psi\_2 increases, and fail (return None) otherwise.

Termination by well-foundedness of \sqsubset\x\sqsupset

# Phase 2: (Strict Scrutinee Descent)
Tracking Invariant: \upsilon \sqsubseteq \phi\_1 \sqcup \phi\_2
Key idea, from D ◂ \upsilon ⤳ σ ↦ ψ ⊣ γ we can construct a derivation d : \Gamma \vdash \sigma \mapsto \phi with \upsilon \sqsubseteq \phi \sqsubseteq \psi. Then we can select \upsilon' \sqsubseteq \upsilon (\sqsubseteq \phi) on this constructed derivation to get \phi' \sqsubseteq \phi and \sigma' \sqsubseteq \sigma. Then we can weaken the slice on d to a slice on the original derivation D (postulate this transform). This effectively means as we strictly descend on \upsilon we monotonically descend on \phi. This is the descent we perform on the scrutinee

1) Slice scrutinee by \tau\_1 + \tau\_2 (i.e. maximum assumption)
2) Get \tau\_1 + \tau\_2 \sqsubseteq \phi\_0, hence fst \phi\_0 \:: \Gamma \vdash \sigma \mapsto \phi\_1 and snd :: \phi\_1 \:: \Gamma \vdash \maspto \phi\_2 with \phi\_1 and \phi\_2 respectively larger than \psi\_1 \psi\_2 (graduality), hence coverage (\upsilon \sqsubseteq \phi\_1 \sqcup \phi\_2) is satisfied. Note: in fact \phi\_0 = \tau\_1 + \tau\_2 here.
3) Loop through each '1-step' strict slice of \tau\_1 + \tau\_2 (i.e. a maximal \tau\_1' + \tau\_2' \sqsubset \tau\_1 + \tau\_2)
4) Calculate \phi\_1 and \phi\_2 for each, i.e. \tau\_1' :: \Gamma \vdash \sigma\_1 \mapsto \phi\_1, similarly for \phi\_2.
5a) For the first pair \phi\_1, \phi\_2 s.t. coverage is satisfied (\upsilon \sqsubseteq \phi\_1 \sqcup \phi\_2), loop from step 1 with \tau\_1' and \tau\_2' (coverage holding by the check we just made)
5b) Otherwise, if no strict slices satisfy coverage, then we have a minimal scrutinee slice.
6) The above is sufficient to establish the minimal term for the FixedAssmsSlice. Since the rule's branch typings are now pinned at \psi\_0's natural projections (`fst+ₛ' ψ₀ m`, `snd+ₛ' ψ₀ m`) directly, no separate `m-scr` match equation needs to be discharged: `match+ₛ ψ₀ m` derives it inline.

# Phase 3: (Minimal Branch Context)
The rule's \gamma-out is `γ_0 ⊔ γ-tail`, where γ\_0 is the scrutinee's used context (already minimal from the scrutinee slice) and γ-tail is the joint minimal context supporting both branches' typing at the chosen heads. We need to find γ-tail s.t.

- (\varsigma\_1 :: γ-tail) ⊢ σ\_1 ↦ τ-c\_1
- (\varsigma\_2 :: γ-tail) ⊢ σ\_2 ↦ τ-c\_2
- υ ⊑ τ-c\_1 ⊔ τ-c\_2

with γ-tail ⊑ Γ' for any (Γ', τ\_a ⊑ τ\_1, τ\_b ⊑ τ\_2) refinement that admits the same coverage (joint head + tail minimality).

This is `MinBranchPairCover D₁ D₂ σ₁ σ₂ ς₁ ς₂ υ` from the `BranchPair` module. **Postulated for now** as `min-branch-pair-cover`, taking the per-branch starting minimal contexts (Phase-1's `ς_i ∷ₛ γ_i'`) as efficiency hints. The algorithm uses this existence postulate to supply the rule's `mbpc` premise; only the context-minimality aspect is non-trivially axiomatised.