module core.Ctx.Base where

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import core.Typ using (Typ; □)
open import core.Exp using (Exp; □e; λ·_⇒_; _∘_; _&_; ιₗ; ιᵣ; Λ; def_⊢_)

-- Expression contexts with exactly one mark ○
-- Note: Do not confuse with the typing assumptions (often referred to as contexts)
data Ctx : Set where
  ○       : Ctx                      -- Identity context (the mark)
  λ·_⇒_   : Typ → Ctx → Ctx          -- Lambda: mark in body
  _∘ₗ_    : Ctx → Exp → Ctx          -- App: mark on left
  _∘ᵣ_    : Exp → Ctx → Ctx          -- App: mark on right
  _&ₗ_    : Ctx → Exp → Ctx          -- Pair: mark on left
  _&ᵣ_    : Exp → Ctx → Ctx          -- Pair: mark on right
  ιₗ      : Ctx → Ctx                -- Left injection
  ιᵣ      : Ctx → Ctx                -- Right injection
  Λ       : Ctx → Ctx                -- Type abstraction
  def_⊢ₗ_ : Ctx → Exp → Ctx          -- Let: mark in definition
  def_⊢ᵣ_ : Exp → Ctx → Ctx          -- Let: mark in body

infixl 22 _∘ₗ_ _∘ᵣ_
infixl 23 _&ₗ_ _&ᵣ_

-- Plug an expression into a context
plug : Ctx → Exp → Exp
plug ○             e = e
plug (λ· τ ⇒ C)    e = λ· τ ⇒ plug C e
plug (C ∘ₗ e')     e = plug C e ∘ e'
plug (e' ∘ᵣ C)     e = e' ∘ plug C e
plug (C &ₗ e')     e = plug C e & e'
plug (e' &ᵣ C)     e = e' & plug C e
plug (ιₗ C)        e = ιₗ (plug C e)
plug (ιᵣ C)        e = ιᵣ (plug C e)
plug (Λ C)         e = Λ (plug C e)
plug (def C ⊢ₗ e') e = def plug C e ⊢ e'
plug (def e' ⊢ᵣ C) e = def e' ⊢ plug C e

-- Bottom constructor: replace all Exp/Typ with □e/□
□Ctx : Ctx → Ctx
□Ctx ○             = ○
□Ctx (λ· _ ⇒ C)    = λ· □ ⇒ □Ctx C
□Ctx (C ∘ₗ _)      = □Ctx C ∘ₗ □e
□Ctx (_ ∘ᵣ C)      = □e ∘ᵣ □Ctx C
□Ctx (C &ₗ _)      = □Ctx C &ₗ □e
□Ctx (_ &ᵣ C)      = □e &ᵣ □Ctx C
□Ctx (ιₗ C)        = ιₗ (□Ctx C)
□Ctx (ιᵣ C)        = ιᵣ (□Ctx C)
□Ctx (Λ C)         = Λ (□Ctx C)
□Ctx (def C ⊢ₗ _)  = def □Ctx C ⊢ₗ □e
□Ctx (def _ ⊢ᵣ C)  = def □e ⊢ᵣ □Ctx C

-- Classify contexts by their 'kinds' i.e. the kind of their top-most constructor
data _kind?_ : Ctx → Ctx → Set where
  kind○    :                                 ○               kind? ○
  kindλ    : ∀ {τ τ' C C'}                 → (λ· τ ⇒ C)     kind? (λ· τ' ⇒ C')
  kind∘ₗ   : ∀ {C C' e e'}                 → (C ∘ₗ e)       kind? (C' ∘ₗ e')
  kind∘ᵣ   : ∀ {e e' C C'}                 → (e ∘ᵣ C)       kind? (e' ∘ᵣ C')
  kind&ₗ   : ∀ {C C' e e'}                 → (C &ₗ e)       kind? (C' &ₗ e')
  kind&ᵣ   : ∀ {e e' C C'}                 → (e &ᵣ C)       kind? (e' &ᵣ C')
  kindιₗ   : ∀ {C C'}                      → ιₗ C           kind? ιₗ C'
  kindιᵣ   : ∀ {C C'}                      → ιᵣ C           kind? ιᵣ C'
  kindΛ    : ∀ {C C'}                      → Λ C            kind? Λ C'
  kinddefₗ : ∀ {C C' e e'}                 → (def C ⊢ₗ e)   kind? (def C' ⊢ₗ e')
  kinddefᵣ : ∀ {e e' C C'}                 → (def e ⊢ᵣ C)   kind? (def e' ⊢ᵣ C')
  diff     : ∀ {C C'}                      → C              kind? C'

diag : (C C' : Ctx) → C kind? C'
diag ○             ○               = kind○
diag (λ· _ ⇒ _)    (λ· _ ⇒ _)      = kindλ
diag (_ ∘ₗ _)      (_ ∘ₗ _)        = kind∘ₗ
diag (_ ∘ᵣ _)      (_ ∘ᵣ _)        = kind∘ᵣ
diag (_ &ₗ _)      (_ &ₗ _)        = kind&ₗ
diag (_ &ᵣ _)      (_ &ᵣ _)        = kind&ᵣ
diag (ιₗ _)        (ιₗ _)          = kindιₗ
diag (ιᵣ _)        (ιᵣ _)          = kindιᵣ
diag (Λ _)         (Λ _)           = kindΛ
diag (def _ ⊢ₗ _)  (def _ ⊢ₗ _)    = kinddefₗ
diag (def _ ⊢ᵣ _)  (def _ ⊢ᵣ _)    = kinddefᵣ
diag _             _               = diff

shallow-disequality : {C : Ctx} → ¬(diag C C ≡ diff)
shallow-disequality {○}           = λ ()
shallow-disequality {λ· _ ⇒ _}    = λ ()
shallow-disequality {_ ∘ₗ _}      = λ ()
shallow-disequality {_ ∘ᵣ _}      = λ ()
shallow-disequality {_ &ₗ _}      = λ ()
shallow-disequality {_ &ᵣ _}      = λ ()
shallow-disequality {ιₗ _}        = λ ()
shallow-disequality {ιᵣ _}        = λ ()
shallow-disequality {Λ _}         = λ ()
shallow-disequality {def _ ⊢ₗ _}  = λ ()
shallow-disequality {def _ ⊢ᵣ _}  = λ ()
