module Core where

  open import Core.Instances public

  open import Core.Typ public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_)
    renaming (_⊑ₛ_ to _⊑tₛ_; _⊑ₛ?_ to _⊑tₛ?_;
              _≈ₛ_ to _≈tₛ_; _≈ₛ?_ to _≈ₛt?_; SliceOf to SliceOfTyp;
              _⊓ₛ_ to _⊓tₛ_; _⊔ₛ_ to _⊔tₛ_;
              weaken to weaken-t; weaken-identity to weaken-identity-t; ↑ to ↑t;
              module ≈ₛ to ≈tₛ; module ⊑ to ⊑t; module ⊑ₛ to ⊑tₛ; module ⊑Lat to ⊑tLat; module ⊑ₛLat to ⊑tₛLat)

  open import Core.Exp public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_)
    renaming (_⊑ₛ_ to _⊑eₛ_; _⊑ₛ?_ to _⊑eₛ?_;
              _≈ₛ_ to _≈eₛ_; _≈ₛ?_ to _≈ₛe?_; SliceOf to SliceOfExp;
              _⊓ₛ_ to _⊓eₛ_; _⊔ₛ_ to _⊔eₛ_;
              weaken to weaken-e; weaken-identity to weaken-identity-e; ↑ to ↑e;
              module ≈ₛ to ≈eₛ; module ⊑ to ⊑e; module ⊑ₛ to ⊑eₛ; module ⊑Lat to ⊑eLat; module ⊑ₛLat to ⊑eₛLat)

  open import Core.Assms public
    hiding (_⊑_; _⊑?_; _⊓_; _⊔_; _≟_)
    renaming (□ to □Assm;
              _⊑ₛ_ to _⊑Assmₛ_; _⊑ₛ?_ to _⊑Assmₛ?_;
              _≈ₛ_ to _≈Assmₛ_; _≈ₛ?_ to _≈ₛAssm?_; SliceOf to SliceOfAssms;
              _⊓ₛ_ to _⊓Assmₛ_; _⊔ₛ_ to _⊔Assmₛ_;
              weaken to weaken-Assm; weaken-identity to weaken-identity-Assm; ↑ to ↑Assm;
              module ≈ₛ to ≈Assmₛ; module ⊑ to ⊑Assm; module ⊑ₛ to ⊑Assmₛ; module ⊑ₛLat to ⊑AssmₛLat)

  open import Core.Ctx public
    hiding   (_kind?_; diag; shallow-disequality; _⊑_; _⊑?_; _⊓_; _⊔_; _≟_)
    renaming (□ to □Ctx;
              _⊑ₛ_ to _⊑Ctxₛ_; _⊑ₛ?_ to _⊑Ctxₛ?_;
              _≈ₛ_ to _≈Ctxₛ_; _≈ₛ?_ to _≈ₛCtx?_; SliceOf to SliceOfCtx;
              _⊓ₛ_ to _⊓Ctxₛ_; _⊔ₛ_ to _⊔Ctxₛ_;
              weaken to weaken-Ctx; weaken-identity to weaken-identity-Ctx; ↑ to ↑Ctx;
              module ≈ₛ to ≈Ctxₛ; module ⊑ to ⊑Ctx; module ⊑ₛ to ⊑Ctxₛ; module ⊑ₛLat to ⊑CtxₛLat)
