-- Well-foundedness postulates for strict precision on type slices.
-- The type slice lattice ⌊ τ ⌋ is finite, so both strict orders are well-founded.
module Core.Typ.WellFounded where

open import Induction.WellFounded using (WellFounded; Acc; acc)
import Induction.WellFounded as WF
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Relation.Nullary using (¬_)
open import Function.Base using (_on_)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  renaming (sym to ≡sym; trans to ≡trans; subst to ≡subst)
open import Relation.Nullary using (yes; no)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Core.Typ.Base using (Typ)
open import Core.Typ.Precision
open import Core.Instances

postulate
  ⊏ₛ-wf : ∀ {τ : Typ} → WellFounded (λ (a b : ⌊ τ ⌋) → a .↓ ⊏ b .↓)

postulate
  ⊐ₛ-wf : ∀ {τ : Typ} → WellFounded (λ (a b : ⌊ τ ⌋) → a .↓ ⊐ b .↓)

-- ⊏×⊐ is contained in "first proj's ⊏" — well-founded by InverseImage of ⊏ₛ-wf.
⊏×⊐-wf : ∀ {τ₁ τ₂ : Typ}
  → WellFounded (λ (p q : ⌊ τ₁ ⌋ × ⌊ τ₂ ⌋) →
      proj₁ p .↓ ⊏ proj₁ q .↓
    × proj₂ p .↓ ⊐ proj₂ q .↓)
⊏×⊐-wf {τ₁} {τ₂} =
  WF.Subrelation.wellFounded (λ (p , _) → p)
    (On.wellFounded proj₁ ⊏ₛ-wf)

⊐×⊐×⊐-rel
  : ∀ {τ₁ τ₂ τ₃ : Typ}
  → ⌊ τ₁ ⌋ × ⌊ τ₂ ⌋ × ⌊ τ₃ ⌋
  → ⌊ τ₁ ⌋ × ⌊ τ₂ ⌋ × ⌊ τ₃ ⌋ → Set
⊐×⊐×⊐-rel (a₁ , b₁ , c₁) (a₂ , b₂ , c₂) =
    ((a₁ .↓ ⊐ a₂ .↓) × (b₂ .↓ ⊑ b₁ .↓) × (c₂ .↓ ⊑ c₁ .↓))
  ⊎ ((a₂ .↓ ⊑ a₁ .↓) × (b₁ .↓ ⊐ b₂ .↓) × (c₂ .↓ ⊑ c₁ .↓))
  ⊎ ((a₂ .↓ ⊑ a₁ .↓) × (b₂ .↓ ⊑ b₁ .↓) × (c₁ .↓ ⊐ c₂ .↓))

⊐×⊐×⊐-wf : ∀ {τ₁ τ₂ τ₃ : Typ} → WellFounded (⊐×⊐×⊐-rel {τ₁} {τ₂} {τ₃})
⊐×⊐×⊐-wf {τ₁} {τ₂} {τ₃} =
  WF.Subrelation.wellFounded
    (λ {x y} → sub-proof x y)
    (×-wellFounded' ≡trans
                    (λ {x = x} y≡z x⊐y → ≡subst (x .↓ ⊐_) y≡z x⊐y)
                    ⊐ₛ-wf
                    (×-wellFounded' ≡trans
                                    (λ {x = x} y≡z x⊐y → ≡subst (x .↓ ⊐_) y≡z x⊐y)
                                    ⊐ₛ-wf ⊐ₛ-wf))
  where
    open import Data.Product.Relation.Binary.Lex.Strict using (×-wellFounded')

    sub-proof : ∀ (x y : ⌊ τ₁ ⌋ × ⌊ τ₂ ⌋ × ⌊ τ₃ ⌋) → ⊐×⊐×⊐-rel x y →
                ×-Lex _≈ₛ_ _⊐ₛ_ (×-Lex _≈ₛ_ _⊐ₛ_ _⊐ₛ_) x y
    sub-proof _ _ (inj₁ (a₁⊐a₂ , _ , _)) = inj₁ a₁⊐a₂
    sub-proof (a₁ , _) (a₂ , _) (inj₂ (inj₁ (a₂⊑a₁ , b₁⊐b₂ , _)))
      with a₂ .↓ ≈? a₁ .↓
    ... | yes a₂≡a₁ = inj₂ (≡sym a₂≡a₁ , inj₁ b₁⊐b₂)
    ... | no  a₂≢a₁ = inj₁ (⊑.⊒∧≉⇒⊐ a₂⊑a₁ (λ a₁≡a₂ → a₂≢a₁ (≡sym a₁≡a₂)))
    sub-proof (a₁ , b₁ , _) (a₂ , b₂ , _) (inj₂ (inj₂ (a₂⊑a₁ , b₂⊑b₁ , c₁⊐c₂)))
      with a₂ .↓ ≈? a₁ .↓
    ... | no  a₂≢a₁ = inj₁ (⊑.⊒∧≉⇒⊐ a₂⊑a₁ (λ a₁≡a₂ → a₂≢a₁ (≡sym a₁≡a₂)))
    ... | yes a₂≡a₁
        with b₂ .↓ ≈? b₁ .↓
    ...   | yes b₂≡b₁ = inj₂ (≡sym a₂≡a₁ , inj₂ (≡sym b₂≡b₁ , c₁⊐c₂))
    ...   | no  b₂≢b₁ = inj₂ (≡sym a₂≡a₁ ,
                              inj₁ (⊑.⊒∧≉⇒⊐ b₂⊑b₁ (λ b₁≡b₂ → b₂≢b₁ (≡sym b₁≡b₂))))

-- Enumerate the slices exactly one step below the current slice
postulate
  max-strict-slices : ∀ {τ : Typ} → ⌊ τ ⌋ → List ⌊ τ ⌋

  max-strict-slices-valid
    : ∀ {τ : Typ} (ψ : ⌊ τ ⌋)
      → All (λ ψ' → ψ' .↓ ⊏ ψ .↓) (max-strict-slices ψ)

  max-strict-slices-complete
    : ∀ {τ : Typ} (ψ ψ' : ⌊ τ ⌋)
      → ψ' .↓ ⊏ ψ .↓
      → Any (λ ψ-max → ψ' .↓ ⊑ ψ-max .↓) (max-strict-slices ψ)

  max-strict-slices-maximal
    : ∀ {τ : Typ} (ψ : ⌊ τ ⌋)
      → AllPairs (λ ψ₁ ψ₂ → (ψ₁ .↓ ⊏̸ ψ₂ .↓) × (ψ₂ .↓ ⊏̸ ψ₁ .↓))
                 (max-strict-slices ψ)
