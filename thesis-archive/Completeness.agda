{-# OPTIONS --without-K #-}

module Completeness where

open import Lib
open import Syntax
open import NormalForm
open import Normalization
open import Embedding
open import Substitution
open import Conversion

_≈_ : ∀ {A Γ} → Tm Γ A → Tyᴺ A Γ → Set
_≈_ {ι}        t tᴺ = t ~ ⌜ tᴺ ⌝Nf
_≈_ {A ⇒ B}{Γ} t tᴺ = ∀ {Δ}(σ : OPE Δ Γ){a aᴺ} → a ≈ aᴺ → app (Tmₑ σ t) a ≈ tᴺ σ aᴺ

infix 3 _≈_ _≈ᶜ_

data _≈ᶜ_ {Γ} : ∀ {Δ} → Sub Γ Δ → Conᴺ Δ Γ → Set where
  ∙   : _≈ᶜ_ ∙ ∙
  _,_ : ∀ {A Δ σ δ}{t : Tm Γ A}{t' : Tyᴺ A Γ} → _≈ᶜ_ {Γ}{Δ} σ δ → t ≈ t' → (σ , t) ≈ᶜ (δ , t')

≈ₑ : ∀ {A Γ Δ}(σ : OPE Δ Γ){t}{tᴺ : Tyᴺ A Γ} → t ≈ tᴺ → Tmₑ σ t ≈ Tyᴺₑ σ tᴺ
≈ₑ {ι}     σ {t}{tᴺ} t≈tᴺ = coe ((_ ~_) & (⌜⌝Nf-nat σ tᴺ ⁻¹)) (~ₑ σ t≈tᴺ)
≈ₑ {A ⇒ B} σ {t}{tᴺ} t≈tᴺ δ rewrite Tm-∘ₑ σ δ t ⁻¹ = t≈tᴺ (σ ∘ₑ δ)

≈ᶜₑ : ∀ {Γ Δ Σ}(σ : OPE Σ Γ){δ}{νᴺ : Conᴺ Δ Γ} → δ ≈ᶜ νᴺ → δ ₛ∘ₑ σ ≈ᶜ Conᴺₑ σ νᴺ
≈ᶜₑ σ ∙              = ∙
≈ᶜₑ σ (δ≈ᶜνᴺ , t≈tᴺ) = ≈ᶜₑ σ δ≈ᶜνᴺ , ≈ₑ σ t≈tᴺ

_~◾≈_ : ∀ {Γ A}{t t'}{tᴺ : Tyᴺ A Γ} → t ~ t' → t' ≈ tᴺ → t ≈ tᴺ
_~◾≈_ {A = ι}     p q = p ~◾ q
_~◾≈_ {A = A ⇒ B} p q = λ σ a≈aᴺ → app (~ₑ σ p) ~refl ~◾≈ q σ a≈aᴺ

∈≈ : ∀ {Γ Δ A}(v : A ∈ Γ){σ}{δᴺ : Conᴺ Γ Δ} → σ ≈ᶜ δᴺ → ∈ₛ σ v ≈ ∈ᴺ v δᴺ
∈≈ vz     (σ≈δᴺ , t≈tᴺ) = t≈tᴺ
∈≈ (vs v) (σ≈δᴺ , _   ) = ∈≈ v σ≈δᴺ

Tm≈ : ∀ {Γ Δ A}(t : Tm Γ A){σ}{δᴺ : Conᴺ Γ Δ} → σ ≈ᶜ δᴺ → Tmₛ σ t ≈ Tmᴺ t δᴺ
Tm≈ (var v) σ≈δᴺ = ∈≈ v σ≈δᴺ

Tm≈ (lam t) {σ}{δᴺ} σ≈δᴺ ν {a} {aᴺ} a≈aᴺ =
  coe ((app (lam (Tmₑ (keep ν) (Tmₛ (keepₛ σ) t))) a ~_ ) &
    ( Tm-ₑ∘ₛ (keep ν) (idₛ , a) (Tmₛ (keepₛ σ) t) ⁻¹
    ◾ Tm-∘ₛ (keepₛ σ) (keep ν ₑ∘ₛ (idₛ , a)) t ⁻¹
    ◾ (λ x → Tmₛ (x , a) t) &
        (assₛₑₛ σ wk ((ν ₑ∘ₛ idₛ) , a)
      ◾ (σ ∘ₛ_) & idlₑₛ (ν ₑ∘ₛ idₛ)
      ◾ assₛₑₛ σ ν idₛ ⁻¹
      ◾ idrₛ _)))
  (β (Tmₑ (keep ν) (Tmₛ (keepₛ σ) t)) a)
  ~◾≈
  Tm≈ t (≈ᶜₑ ν σ≈δᴺ , a≈aᴺ)

Tm≈ (app f a) {σ} σ≈δᴺ
  rewrite Tm-idₑ (Tmₛ σ f) ⁻¹ = Tm≈ f σ≈δᴺ idₑ (Tm≈ a σ≈δᴺ)

mutual
  q≈ : ∀ {A Γ}{t}{tᴺ : Tyᴺ A Γ} → t ≈ tᴺ → t ~ ⌜ qᴺ tᴺ ⌝Nf
  q≈ {ι}     t≈tᴺ = t≈tᴺ
  q≈ {A ⇒ B} t≈tᴺ = η _ ~◾ lam (q≈ (t≈tᴺ wk (u≈ (var vz))))

  u≈ : ∀ {A Γ}(n : Ne Γ A) → ⌜ n ⌝Ne ≈ uᴺ n
  u≈ {ι}     n = ~refl
  u≈ {A ⇒ B} n σ {a} {aᴺ} a≈aᴺ
    rewrite ⌜⌝Ne-nat σ n ⁻¹ = app ~refl (q≈ a≈aᴺ) ~◾≈ u≈ (app (Neₑ σ n) (qᴺ aᴺ))

uᶜ≈  : ∀ {Γ} → idₛ {Γ} ≈ᶜ uᶜᴺ
uᶜ≈ {∙}     = ∙
uᶜ≈ {Γ , A} = ≈ᶜₑ wk uᶜ≈ , u≈ (var vz)

complete : ∀ {Γ A}(t : Tm Γ A) → t ~ ⌜ nf t ⌝Nf
complete t = coe ((_~ ⌜ qᴺ (Tmᴺ t uᶜᴺ) ⌝Nf) & Tm-idₛ t) (q≈ (Tm≈ t uᶜ≈))

