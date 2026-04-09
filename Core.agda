module Core where

  open import Core.Instances public

  open import Core.Typ public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_;
              ⊑-isDecPartialOrder; _⊑ₛ_; _⊓ₛ_; _⊔ₛ_;
              SliceOf; ↓; _isSlice_; ↑; weaken; weaken-identity;
              _≈ₛ_; _≈ₛ?_; _⊑ₛ?_;
              module ⊑; module ⊑Lat; module ⊑ₛLat; module ≈ₛ; module ⊑ₛ)

  open import Core.Exp public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_;
              ⊑-isDecPartialOrder; _⊑ₛ_; _⊓ₛ_; _⊔ₛ_;
              SliceOf; ↓; _isSlice_; ↑; weaken; weaken-identity;
              _≈ₛ_; _≈ₛ?_; _⊑ₛ?_;
              module ⊑; module ⊑Lat; module ⊑ₛLat; module ≈ₛ; module ⊑ₛ)

  open import Core.Assms public
    hiding (_⊑_; _⊑?_; _⊓_; _⊔_; _≟_;
            ⊑-isDecPartialOrder; _⊑ₛ_; _⊓ₛ_; _⊔ₛ_;
            SliceOf; ↓; _isSlice_; ↑; weaken; weaken-identity;
            _≈ₛ_; _≈ₛ?_; _⊑ₛ?_;
            module ⊑; module ⊑ₛLat; module ≈ₛ; module ⊑ₛ)
    renaming (□ to □Assm)

  open import Core.Ctx public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_;
              ⊑-isDecPartialOrder; _⊑ₛ_; _⊓ₛ_; _⊔ₛ_;
              SliceOf; ↓; _isSlice_; ↑; weaken; weaken-identity;
              _≈ₛ_; _≈ₛ?_; _⊑ₛ?_;
              module ⊑; module ⊑ₛLat; module ≈ₛ; module ⊑ₛ)
    renaming (□ to □Ctx)
