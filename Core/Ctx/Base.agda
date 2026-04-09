module Core.Ctx.Base where

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Core.Typ using (Typ) renaming (□ to □t)
open import Core.Exp.Base renaming (□ to □e; _kind?_ to _kind?e_; diag to diag-e; shallow-disequality to shallow-disequality-e)

-- Expression contexts with exactly one mark ○ to plug expressions into
-- Note: Do not confuse with the typing assumptions (often referred to as contexts)
data Ctx : Set where
  ○              : Ctx                        -- Identity context (the mark)
  λ:_⇒_          : Typ → Ctx → Ctx            -- Annotated lambda: mark in body
  λ⇒_            : Ctx → Ctx                  -- Unannotated lambda: mark in body
  _∘₁_           : Ctx → Exp → Ctx            -- App: mark on left
  _∘₂_           : Exp → Ctx → Ctx            -- App: mark on right
  _<_>₁          : Ctx → Typ → Ctx            -- Type app: mark on expression
  _&₁_           : Ctx → Exp → Ctx            -- Pair: mark on left
  _&₂_           : Exp → Ctx → Ctx            -- Pair: mark on right
  ι₁             : Ctx → Ctx                  -- Left injection
  ι₂             : Ctx → Ctx                  -- Right injection
  case_of_·₁_    : Exp → Ctx → Exp → Ctx      -- Case: mark in left branch  (scrutinee fixed)
  case_of₂_·_    : Exp → Exp → Ctx → Ctx      -- Case: mark in right branch (scrutinee fixed)
  π₁             : Ctx → Ctx                  -- First projection
  π₂             : Ctx → Ctx                  -- Second projection
  Λ              : Ctx → Ctx                  -- Type abstraction
  def_⊢₁_        : Ctx → Exp → Ctx            -- Let: mark in definition
  def_⊢₂_        : Exp → Ctx → Ctx            -- Let: mark in body

infixr 5  λ:_⇒_
infixr 5  λ⇒_
infixr 5  def_⊢₁_ def_⊢₂_
infixl 22 _∘₁_    _∘₂_
infixl 22 _<_>₁
infixl 23 _&₁_    _&₂_
infix 4   _kind?_

plug : Ctx → Exp → Exp
plug ○                  e = e
plug (λ: τ ⇒ C)         e = λ: τ ⇒ plug C e
plug (λ⇒ C)             e = λ⇒ plug C e
plug (C ∘₁ e')          e = plug C e ∘ e'
plug (e' ∘₂ C)          e = e' ∘ plug C e
plug (C < τ >₁)         e = plug C e < τ >
plug (C &₁ e')          e = plug C e & e'
plug (e' &₂ C)          e = e' & plug C e
plug (ι₁ C)             e = ι₁ (plug C e)
plug (ι₂ C)             e = ι₂ (plug C e)
plug (case e' of C ·₁ e'') e = case e' of plug C e · e''
plug (case e' of₂ e'' · C) e = case e' of e'' · plug C e
plug (π₁ C)             e = π₁ (plug C e)
plug (π₂ C)             e = π₂ (plug C e)
plug (Λ C)              e = Λ (plug C e)
plug (def C ⊢₁ e')      e = def plug C e ⊢ e'
plug (def e' ⊢₂ C)      e = def e' ⊢ plug C e

-- 'purely structural' context
□ : Ctx → Ctx
□ ○                    = ○
□ (λ: _ ⇒ C)           = λ: □t ⇒ □ C
□ (λ⇒ C)               = λ⇒ □ C
□ (C ∘₁ _)             = □ C ∘₁ □e
□ (_ ∘₂ C)             = □e ∘₂ □ C
□ (C < _ >₁)           = □ C < □t >₁
□ (C &₁ _)             = □ C &₁ □e
□ (_ &₂ C)             = □e &₂ □ C
□ (ι₁ C)               = ι₁ (□ C)
□ (ι₂ C)               = ι₂ (□ C)
□ (case _ of C ·₁ _)   = case □e of □ C ·₁ □e
□ (case _ of₂ _ · C)   = case □e of₂ □e · □ C
□ (π₁ C)               = π₁ (□ C)
□ (π₂ C)               = π₂ (□ C)
□ (Λ C)                = Λ (□ C)
□ (def C ⊢₁ _)         = def □ C ⊢₁ □e
□ (def _ ⊢₂ C)         = def □e ⊢₂ □ C

-- Classify contexts by their 'kinds' i.e. the kind of their top-most constructor
data _kind?_ : Ctx → Ctx → Set where
  kind○      :                      ○               kind?  ○
  kindλ      : ∀ {τ τ' C C'}     →  λ: τ ⇒ C        kind?  λ: τ' ⇒ C'
  kindλu     : ∀ {C C'}          →  λ⇒ C            kind?  λ⇒ C'
  kind∘₁     : ∀ {C C' e e'}     →  C ∘₁ e          kind?  C' ∘₁ e'
  kind∘₂     : ∀ {e e' C C'}     →  e ∘₂ C          kind?  e' ∘₂ C'
  kind<>₁    : ∀ {C C' τ τ'}     →  C < τ >₁        kind?  C' < τ' >₁
  kind&₁     : ∀ {C C' e e'}     →  C &₁ e          kind?  C' &₁ e'
  kind&₂     : ∀ {e e' C C'}     →  e &₂ C          kind?  e' &₂ C'
  kindι₁     : ∀ {C C'}          →  ι₁ C            kind?  ι₁ C'
  kindι₂     : ∀ {C C'}          →  ι₂ C            kind?  ι₂ C'
  kindcase₁  : ∀ {e e' C C' f f'} → case e of C ·₁ f  kind?  case e' of C' ·₁ f'
  kindcase₂  : ∀ {e e' f f' C C'} → case e of₂ f · C  kind?  case e' of₂ f' · C'
  kindπ₁     : ∀ {C C'}          →  π₁ C            kind?  π₁ C'
  kindπ₂     : ∀ {C C'}          →  π₂ C            kind?  π₂ C'
  kindΛ      : ∀ {C C'}          →  Λ C             kind?  Λ C'
  kinddef₁   : ∀ {C C' e e'}     →  def C ⊢₁ e      kind?  def C' ⊢₁ e'
  kinddef₂   : ∀ {e e' C C'}     →  def e ⊢₂ C      kind?  def e' ⊢₂ C'
  diff       : ∀ {C C'}          →  C               kind?  C'

diag : (C C' : Ctx) → C kind? C'
diag ○                    ○                    =  kind○
diag (λ: _ ⇒ _)           (λ: _ ⇒ _)           =  kindλ
diag (λ⇒ _)               (λ⇒ _)               =  kindλu
diag (_ ∘₁ _)             (_ ∘₁ _)             =  kind∘₁
diag (_ ∘₂ _)             (_ ∘₂ _)             =  kind∘₂
diag (_ < _ >₁)           (_ < _ >₁)           =  kind<>₁
diag (_ &₁ _)             (_ &₁ _)             =  kind&₁
diag (_ &₂ _)             (_ &₂ _)             =  kind&₂
diag (ι₁ _)               (ι₁ _)               =  kindι₁
diag (ι₂ _)               (ι₂ _)               =  kindι₂
diag (case _ of _ ·₁ _)   (case _ of _ ·₁ _)   =  kindcase₁
diag (case _ of₂ _ · _)   (case _ of₂ _ · _)   =  kindcase₂
diag (π₁ _)               (π₁ _)               =  kindπ₁
diag (π₂ _)               (π₂ _)               =  kindπ₂
diag (Λ _)                (Λ _)                =  kindΛ
diag (def _ ⊢₁ _)         (def _ ⊢₁ _)         =  kinddef₁
diag (def _ ⊢₂ _)         (def _ ⊢₂ _)         =  kinddef₂
diag _                    _                    =  diff

shallow-disequality : {C : Ctx} → ¬(diag C C ≡ diff)
shallow-disequality {○}                = λ ()
shallow-disequality {λ: _ ⇒ _}         = λ ()
shallow-disequality {λ⇒ _}             = λ ()
shallow-disequality {_ ∘₁ _}           = λ ()
shallow-disequality {_ ∘₂ _}           = λ ()
shallow-disequality {_ < _ >₁}         = λ ()
shallow-disequality {_ &₁ _}           = λ ()
shallow-disequality {_ &₂ _}           = λ ()
shallow-disequality {ι₁ _}             = λ ()
shallow-disequality {ι₂ _}             = λ ()
shallow-disequality {case _ of _ ·₁ _} = λ ()
shallow-disequality {case _ of₂ _ · _} = λ ()
shallow-disequality {π₁ _}             = λ ()
shallow-disequality {π₂ _}             = λ ()
shallow-disequality {Λ _}              = λ ()
shallow-disequality {def _ ⊢₁ _}       = λ ()
shallow-disequality {def _ ⊢₂ _}       = λ ()
