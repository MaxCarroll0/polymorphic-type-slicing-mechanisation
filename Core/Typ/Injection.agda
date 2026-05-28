-- Left/right injections L, R lifting slices of τ₁ (resp. τ₂) into slices of τ₁ ⊔ τ₂ when τ₁ ~ τ₂,
-- with monotonicity and distributivity over ⊓ₛ / ⊔ₛ.
module Core.Typ.Injection where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Typ.Base using (Typ)
open import Core.Typ.Precision
open import Core.Typ.Consistency using (_~_)
open import Core.Typ.Lattice using (module ~)
open import Core.Instances

-- L: lift a slice of τ₁ into ⌊ τ₁ ⊔ τ₂ ⌋
L : ∀ {τ₁ τ₂ : Typ} → (c : τ₁ ~ τ₂) → ⌊ τ₁ ⌋ → ⌊ τ₁ ⊔ τ₂ ⌋
L c s = ↑ (⊑.trans {Typ} (s .proof) (~.⊔-ub₁ c))

-- R: lift a slice of τ₂ into ⌊ τ₁ ⊔ τ₂ ⌋
R : ∀ {τ₁ τ₂ : Typ} → (c : τ₁ ~ τ₂) → ⌊ τ₂ ⌋ → ⌊ τ₁ ⊔ τ₂ ⌋
R c s = ↑ (⊑.trans {Typ} (s .proof) (~.⊔-ub₂ c))

-- Monotonicity
L-mono : ∀ {τ₁ τ₂ : Typ} (c : τ₁ ~ τ₂) {a b : ⌊ τ₁ ⌋} → a ⊑ₛ b → L c a ⊑ₛ L c b
L-mono c p = p

R-mono : ∀ {τ₁ τ₂ : Typ} (c : τ₁ ~ τ₂) {a b : ⌊ τ₂ ⌋} → a ⊑ₛ b → R c a ⊑ₛ R c b
R-mono c p = p

-- Distributivity over ⊔ₛ
L-⊔ₛ : ∀ {τ₁ τ₂ : Typ} (c : τ₁ ~ τ₂) (a b : ⌊ τ₁ ⌋) → L c (a ⊔ₛ b) ≈ₛ (L c a ⊔ₛ L c b)
L-⊔ₛ c a b = refl

R-⊔ₛ : ∀ {τ₁ τ₂ : Typ} (c : τ₁ ~ τ₂) (a b : ⌊ τ₂ ⌋) → R c (a ⊔ₛ b) ≈ₛ (R c a ⊔ₛ R c b)
R-⊔ₛ c a b = refl

-- Distributivity over ⊓ₛ
L-⊓ₛ : ∀ {τ₁ τ₂ : Typ} (c : τ₁ ~ τ₂) (a b : ⌊ τ₁ ⌋) → L c (a ⊓ₛ b) ≈ₛ (L c a ⊓ₛ L c b)
L-⊓ₛ c a b = refl

R-⊓ₛ : ∀ {τ₁ τ₂ : Typ} (c : τ₁ ~ τ₂) (a b : ⌊ τ₂ ⌋) → R c (a ⊓ₛ b) ≈ₛ (R c a ⊓ₛ R c b)
R-⊓ₛ c a b = refl
