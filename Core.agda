module Core where
  open import Core.Typ public
    hiding   (_kind?_; diag; shallow-disequality)
    renaming (_⊑_ to _⊑t_; _⊑?_ to _⊑t?_; _⊑ₛ_ to _⊑tₛ_; _⊑ₛ?_ to _⊑tₛ?_;
              _≈ₛ_ to _≈tₛ_; _≈ₛ?_ to _≈ₛt?_; _≟_ to _≟t_; SliceOf to SliceOfTyp;
              _⊓_ to _⊓t_; _⊔_ to _⊔t_; _⊓ₛ_ to _⊓tₛ_; _⊔ₛ_ to _⊔tₛ_; 
              weaken to weaken-t; weaken-identity to weaken-identity-t; ↑ to ↑t;
              module ≈ₛ to ≈tₛ; module ⊑ to ⊑t; module ⊑ₛ to ⊑tₛ; module ⊑Lat to ⊑tLat; module ⊑ₛLat to ⊑ₛtLat)

  open import Core.Exp public
    hiding   (_kind?_; diag; shallow-disequality)
    renaming (_⊑_ to _⊑e_; _⊑?_ to _⊑e?_; _⊑ₛ_ to _⊑eₛ_; _⊑ₛ?_ to _⊑eₛ?_;
              _≈ₛ_ to _≈eₛ_; _≈ₛ?_ to _≈ₛe?_; _≟_ to _≟e_; SliceOf to SliceOfExp;
              _⊓_ to _⊓e_; _⊔_ to _⊔e_; _⊓ₛ_ to _⊓eₛ_; _⊔ₛ_ to _⊔eₛ_; 
              weaken to weaken-e; weaken-identity to weaken-identity-e; ↑ to ↑e;
              module ≈ₛ to ≈eₛ; module ⊑ to ⊑e; module ⊑ₛ to ⊑eₛ; module ⊑Lat to ⊑eLat; module ⊑ₛLat to ⊑ₛeLat)

  open import Core.Assms public
    renaming (□ to □Assm;
              _⊑_ to _⊑Assm_; _⊑?_ to _⊑Assm?_; _⊑ₛ_ to _⊑Assmₛ_; _⊑ₛ?_ to _⊑Assmₛ?_;
              _≈ₛ_ to _≈Assmₛ_; _≈ₛ?_ to _≈ₛAssm?_; _≟_ to _≟Assm_; SliceOf to SliceOfAssms;
              _⊓_ to _⊓Assm_; _⊔_ to _⊔Assm_; _⊓ₛ_ to _⊓Assmₛ_; _⊔ₛ_ to _⊔Assmₛ_; 
              weaken to weaken-Assm; weaken-identity to weaken-identity-Assm; ↑ to ↑Assm;
              module ≈ₛ to ≈Assmₛ; module ⊑ to ⊑Assm; module ⊑ₛ to ⊑Assmₛ; module ⊑ₛLat to ⊑ₛAssmLat)
              
  open import Core.Ctx public
    hiding   (_kind?_; diag; shallow-disequality)
    renaming (□ to □Ctx;
              _⊑_ to _⊑Ctx_; _⊑?_ to _⊑Ctx?_; _⊑ₛ_ to _⊑Ctxₛ_; _⊑ₛ?_ to _⊑Ctxₛ?_;
              _≈ₛ_ to _≈Ctxₛ_; _≈ₛ?_ to _≈ₛCtx?_; _≟_ to _≟Ctx_; SliceOf to SliceOfCtx;
              _⊓_ to _⊓Ctx_; _⊔_ to _⊔Ctx_; _⊓ₛ_ to _⊓Ctxₛ_; _⊔ₛ_ to _⊔Ctxₛ_; 
              weaken to weaken-Ctx; weaken-identity to weaken-identity-Ctx; ↑ to ↑Ctx;
              module ≈ₛ to ≈Ctxₛ; module ⊑ to ⊑Ctx; module ⊑ₛ to ⊑Ctxₛ; module ⊑ₛLat to ⊑ₛCtxLat)
