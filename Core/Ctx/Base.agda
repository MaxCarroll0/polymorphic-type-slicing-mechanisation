module Core.Ctx.Base where

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Core.Typ using (Typ) renaming (□ to □t)
open import Core.Exp renaming (□ to □e; _kind?_ to _kind?e_; diag to diag-e; shallow-disequality to shallow-disequality-e)

-- Expression contexts with exactly one mark ○ to plug expressions into
-- Note: Do not confuse with the typing assumptions (often referred to as contexts)
data Ctx : Set where
  ○       : Ctx              -- Identity context (the mark)
  λ·_⇒_   : Typ → Ctx → Ctx  -- Lambda: mark in body
  _∘₁_    : Ctx → Exp → Ctx  -- App: mark on left
  _∘₂_    : Exp → Ctx → Ctx  -- App: mark on right
  _&₁_    : Ctx → Exp → Ctx  -- Pair: mark on left
  _&₂_    : Exp → Ctx → Ctx  -- Pair: mark on right
  ι₁      : Ctx → Ctx        -- Left injection
  ι₂      : Ctx → Ctx        -- Right injection
  Λ       : Ctx → Ctx        -- Type abstraction
  def_⊢₁_ : Ctx → Exp → Ctx  -- Let: mark in definition
  def_⊢₂_ : Exp → Ctx → Ctx  -- Let: mark in body

infixr 5  λ·_⇒_
infixr 5  def_⊢₁_ def_⊢₂_
infixl 22 _∘₁_    _∘₂_
infixl 23 _&₁_    _&₂_
infix 4   _kind?_

plug : Ctx → Exp → Exp
plug ○             e = e
plug (λ· τ ⇒ C)    e = λ· τ ⇒ plug C e
plug (C ∘₁ e')     e = plug C e ∘ e'
plug (e' ∘₂ C)     e = e' ∘ plug C e
plug (C &₁ e')     e = plug C e & e'
plug (e' &₂ C)     e = e' & plug C e
plug (ι₁ C)        e = ι₁ (plug C e)
plug (ι₂ C)        e = ι₂ (plug C e)
plug (Λ C)         e = Λ (plug C e)
plug (def C ⊢₁ e') e = def plug C e ⊢ e'
plug (def e' ⊢₂ C) e = def e' ⊢ plug C e

-- 'purely structural' context
□ : Ctx → Ctx
□ ○             = ○
□ (λ· _ ⇒ C)    = λ· □t ⇒ □ C
□ (C ∘₁ _)      = □ C ∘₁ □e
□ (_ ∘₂ C)      = □e ∘₂ □ C
□ (C &₁ _)      = □ C &₁ □e
□ (_ &₂ C)      = □e &₂ □ C
□ (ι₁ C)        = ι₁(□ C)
□ (ι₂ C)        = ι₂ (□ C)
□ (Λ C)         = Λ (□ C)
□ (def C ⊢₁ _)  = def □ C ⊢₁ □e
□ (def _ ⊢₂ C)  = def □e ⊢₂ □ C

-- Classify contexts by their 'kinds' i.e. the kind of their top-most constructor
data _kind?_ : Ctx → Ctx → Set where
  kind○    :                   ○           kind?  ○
  kindλ    : ∀ {τ τ' C C'}  →  λ· τ ⇒ C    kind?  λ· τ' ⇒ C'
  kind∘₁   : ∀ {C C' e e'}  →  C ∘₁ e      kind?  C' ∘₁ e'
  kind∘₂   : ∀ {e e' C C'}  →  e ∘₂ C      kind?  e' ∘₂ C'
  kind&₁   : ∀ {C C' e e'}  →  C &₁ e      kind?  C' &₁ e'
  kind&₂   : ∀ {e e' C C'}  →  e &₂ C      kind?  e' &₂ C'
  kindι₁   : ∀ {C C'}       →  ι₁ C        kind?  ι₁ C'
  kindι₂   : ∀ {C C'}       →  ι₂ C        kind?  ι₂ C'
  kindΛ    : ∀ {C C'}       →  Λ C         kind?  Λ C'
  kinddef₁ : ∀ {C C' e e'}  →  def C ⊢₁ e  kind?  def C' ⊢₁ e'
  kinddef₂ : ∀ {e e' C C'}  →  def e ⊢₂ C  kind?  def e' ⊢₂ C'
  diff     : ∀ {C C'}       →  C           kind?  C'

diag : (C C' : Ctx) → C kind? C'
diag ○             ○             =  kind○
diag (λ· _ ⇒ _)    (λ· _ ⇒ _)    =  kindλ
diag (_ ∘₁ _)      (_ ∘₁ _)      =  kind∘₁
diag (_ ∘₂ _)      (_ ∘₂ _)      =  kind∘₂
diag (_ &₁ _)      (_ &₁ _)      =  kind&₁
diag (_ &₂ _)      (_ &₂ _)      =  kind&₂
diag (ι₁ _)        (ι₁ _)        =   kindι₁
diag (ι₂ _)        (ι₂ _)        =  kindι₂
diag (Λ _)         (Λ _)         =  kindΛ
diag (def _ ⊢₁ _)  (def _ ⊢₁ _)  =  kinddef₁
diag (def _ ⊢₂ _)  (def _ ⊢₂ _)  =  kinddef₂
diag _             _             =  diff

shallow-disequality : {C : Ctx} → ¬(diag C C ≡ diff)
shallow-disequality {○}           = λ ()
shallow-disequality {λ· _ ⇒ _}    = λ ()
shallow-disequality {_ ∘₁ _}      = λ ()
shallow-disequality {_ ∘₂ _}      = λ ()
shallow-disequality {_ &₁ _}      = λ ()
shallow-disequality {_ &₂ _}      = λ ()
shallow-disequality {ι₁ _}        = λ ()
shallow-disequality {ι₂ _}        = λ ()
shallow-disequality {Λ _}         = λ ()
shallow-disequality {def _ ⊢₁ _}  = λ ()
shallow-disequality {def _ ⊢₂ _}  = λ ()
