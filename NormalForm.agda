{-# OPTIONS --without-K #-}

module NormalForm where

open import Lib
open import Syntax
open import Embedding

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne  : Ne Γ ι → Nf Γ ι
    lam : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var : ∀ {A} → A ∈ Γ → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

-- Context embeddings
--------------------------------------------------------------------------------

mutual
  Nfₑ : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
  Nfₑ σ (ne n)  = ne (Neₑ σ n)
  Nfₑ σ (lam n) = lam (Nfₑ (keep σ) n)

  Neₑ : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
  Neₑ σ (var v)   = var (∈ₑ σ v)
  Neₑ σ (app f a) = app (Neₑ σ f) (Nfₑ σ a)

mutual
  Nf-∘ₑ :
    ∀ {Γ Δ Σ A}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Nf Σ A)
    → Nfₑ (σ ∘ₑ δ) t ≡ Nfₑ δ (Nfₑ σ t)
  Nf-∘ₑ  σ δ (ne n)  = ne & Ne-∘ₑ σ δ n
  Nf-∘ₑ  σ δ (lam t) = lam & Nf-∘ₑ (keep σ) (keep δ) t
    
  Ne-∘ₑ :
    ∀ {Γ Δ Σ A}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Ne Σ A)
    → Neₑ (σ ∘ₑ δ) t ≡ Neₑ δ (Neₑ σ t)
  Ne-∘ₑ σ δ (var v)   = var & ∈-∘ₑ σ δ v
  Ne-∘ₑ σ δ (app f a) = app & Ne-∘ₑ σ δ f ⊗ Nf-∘ₑ σ δ a

mutual
  Nf-idₑ : ∀ {Γ A}(t : Nf Γ A) → Nfₑ idₑ t ≡ t
  Nf-idₑ (ne n)  = ne & Ne-idₑ n
  Nf-idₑ (lam t) = lam & Nf-idₑ t

  Ne-idₑ : ∀ {Γ A}(t : Ne Γ A) → Neₑ idₑ t ≡ t
  Ne-idₑ (var v)   = var & ∈-idₑ v
  Ne-idₑ (app f a) = app & Ne-idₑ f ⊗ Nf-idₑ a

-- Embedding into Tm
--------------------------------------------------------------------------------

mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n  ⌝ = ⌜ n ⌝Ne
  ⌜ lam t ⌝ = lam ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v   ⌝Ne = var v
  ⌜ app n t ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝

mutual
  ⌜⌝Ne-nat : ∀ {Γ Δ A}(σ : OPE Δ Γ)(n : Ne Γ A) → ⌜ Neₑ σ n ⌝Ne ≡ Tmₑ σ ⌜ n ⌝Ne
  ⌜⌝Ne-nat σ (var v)   = refl
  ⌜⌝Ne-nat σ (app f a) = app & ⌜⌝Ne-nat σ f ⊗ ⌜⌝Nf-nat σ a

  ⌜⌝Nf-nat : ∀ {Γ Δ A}(σ : OPE Δ Γ)(n : Nf Γ A) → ⌜ Nfₑ σ n ⌝ ≡ Tmₑ σ ⌜ n ⌝
  ⌜⌝Nf-nat σ (ne n)  = ⌜⌝Ne-nat σ n
  ⌜⌝Nf-nat σ (lam n) = lam & ⌜⌝Nf-nat (keep σ) n


-- Decidable equality
--------------------------------------------------------------------------------

∈≡? :
  ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ Γ) → Dec (Σ (A ≡ B) λ p → coe ((_∈ Γ) & p) v ≡ v')
∈≡? vz     vz      = inj₁ (refl , refl)
∈≡? vz     (vs v') = inj₂ (λ {(refl , ())})
∈≡? (vs v) vz      = inj₂ (λ {(refl , ())})
∈≡? (vs v) (vs v') with ∈≡? v v'
... | inj₁ (refl , refl) = inj₁ (refl , refl)
... | inj₂ p = inj₂ (λ {(refl , refl) → p (refl , refl)})

Ty-set : {A : Ty}(p : A ≡ A) → p ≡ refl
Ty-set {ι}     refl = refl
Ty-set {A ⇒ B} p = fg p ⁻¹
                 ◾ lem (⇒-≡ p) (Ty-set (proj₁ (⇒-≡ p))) (Ty-set (proj₂ (⇒-≡ p)))
  where
    ⇒-≡ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → (A ≡ C) × (B ≡ D)
    ⇒-≡ refl = refl , refl
    
    ⇒-≡' : ∀ {A B C D} → (A ≡ C) × (B ≡ D) → (A ⇒ B) ≡ (C ⇒ D)
    ⇒-≡' (refl , refl) = refl
    
    fg : ∀ {A B C D} (p : (A ⇒ B) ≡ (C ⇒ D)) → ⇒-≡' (⇒-≡ p) ≡ p
    fg refl = refl
    
    lem : ∀ {A B} (p : (A ≡ A) × (B ≡ B)) → proj₁ p ≡ refl → proj₂ p ≡ refl → ⇒-≡' p ≡ refl
    lem _ refl refl = refl

mutual
  Nf≡? : ∀ {Γ A}(n n' : Nf Γ A) → Dec (n ≡ n')
  Nf≡? (ne n)  (ne n')  with Ne≡? n n'
  ... | inj₁ (refl , refl) = inj₁ refl
  ... | inj₂ p             = inj₂ (λ {refl → p (refl , refl)})
  Nf≡? (lam n) (lam n') with Nf≡? n n'
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ p    = inj₂ (λ {refl → p refl})
  
  Ne≡? : ∀ {Γ A B}(n : Ne Γ A)(n' : Ne Γ B) → Dec (Σ (A ≡ B) λ p → coe (Ne Γ & p) n ≡ n')
  Ne≡? (var v) (var v')      with ∈≡? v v'
  ... | inj₁ (refl , refl) = inj₁ (refl , refl)
  ... | inj₂ p             = inj₂ (λ {(refl , refl) → p (refl , refl)})
  Ne≡? (var _) (app _ _)     = inj₂ (λ {(refl , ())})
  Ne≡? (app _ _) (var _)     = inj₂ (λ {(refl , ())})
  Ne≡? (app n x) (app n' x') with Ne≡? n n'
  Ne≡? (app n x) (app n' x') | inj₁ (refl , refl) with Nf≡? x x'
  ... | inj₁ refl = inj₁ (refl , refl)
  ... | inj₂ p    = inj₂ (λ {(q , r)
     → p (let foo = coe ((λ p → coe (Ne _ & p ) (app n x) ≡ app n x') & Ty-set q) r
              s , t = app-≡₂ foo
          in coe ((λ p → coe (Nf _ & p) x ≡ x') & Ty-set s) t)})
     where
       app-≡₂ :
         ∀ {Γ A A' B}{n : Ne Γ (A ⇒ B)}{n' : Ne Γ (A' ⇒ B)}{x x'}
         → Ne.app n x ≡ app n' x' → Σ (A ≡ A') λ p → coe (Nf Γ & p) x ≡ x'
       app-≡₂ refl = refl , refl
  
  Ne≡? (app n x) (app n' x') | inj₂ p = inj₂ (λ {(refl , refl) → p (refl , refl)})

