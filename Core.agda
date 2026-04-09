module Core where

  open import Core.Instances public

  open import Core.Typ public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_;
              ⊑-isDecPartialOrder; _⊑ₛ_; _⊓ₛ_; _⊔ₛ_;
              module ⊑; module ⊑Lat; module ⊑ₛLat)
    renaming (_⊑ₛ?_ to _⊑tₛ?_;
              _≈ₛ_ to _≈tₛ_; _≈ₛ?_ to _≈ₛt?_; SliceOf to SliceOfTyp;
              weaken to weaken-t; weaken-identity to weaken-identity-t; ↑ to ↑t;
              module ≈ₛ to ≈tₛ; module ⊑ₛ to ⊑tₛ)

  open import Core.Exp public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_;
              ⊑-isDecPartialOrder; _⊑ₛ_; _⊓ₛ_; _⊔ₛ_;
              module ⊑; module ⊑Lat; module ⊑ₛLat)
    renaming (_⊑ₛ?_ to _⊑eₛ?_;
              _≈ₛ_ to _≈eₛ_; _≈ₛ?_ to _≈ₛe?_; SliceOf to SliceOfExp;
              weaken to weaken-e; weaken-identity to weaken-identity-e; ↑ to ↑e;
              module ≈ₛ to ≈eₛ; module ⊑ₛ to ⊑eₛ)

  open import Core.Assms public
    hiding (_⊑_; _⊑?_; _⊓_; _⊔_; _≟_;
            ⊑-isDecPartialOrder; _⊑ₛ_; _⊓ₛ_; _⊔ₛ_;
            module ⊑; module ⊑ₛLat)
    renaming (□ to □Assm;
              _⊑ₛ?_ to _⊑Assmₛ?_;
              _≈ₛ_ to _≈Assmₛ_; _≈ₛ?_ to _≈ₛAssm?_; SliceOf to SliceOfAssms;
              weaken to weaken-Assm; weaken-identity to weaken-identity-Assm; ↑ to ↑Assm;
              module ≈ₛ to ≈Assmₛ; module ⊑ₛ to ⊑Assmₛ)

  open import Core.Ctx public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_;
              ⊑-isDecPartialOrder; _⊑ₛ_; _⊓ₛ_; _⊔ₛ_;
              module ⊑; module ⊑ₛLat)
    renaming (□ to □Ctx;
              _⊑ₛ?_ to _⊑Ctxₛ?_;
              _≈ₛ_ to _≈Ctxₛ_; _≈ₛ?_ to _≈ₛCtx?_; SliceOf to SliceOfCtx;
              weaken to weaken-Ctx; weaken-identity to weaken-identity-Ctx; ↑ to ↑Ctx;
              module ≈ₛ to ≈Ctxₛ; module ⊑ₛ to ⊑Ctxₛ)
