{-# OPTIONS --without-K #-}

module Completeness where

open import Lib
open import Syntax
open import Nf
open import Normalization
open import Presheaf
open import Embedding
open import Substitution
open import Conversion

_≈_ : ∀ {A Γ} → Tm Γ A → Tyᴺ A Γ → Set
_≈_ {Ty.⊤}  {Γ} t tᴺ        = t ~ ⌜ tᴺ ⌝
_≈_ {Ty.⊥}  {Γ} t tᴺ        = t ~ ⌜ tᴺ ⌝Ne
_≈_ {A ⇒ B} {Γ} t (tᴺ , _)  = ∀ {Δ}(σ : OPE Δ Γ){a aᴺ} → a ≈ aᴺ → app (Tmₑ σ t) a ≈ tᴺ σ aᴺ
_≈_ {A * B} {Γ} t (tᴺ , uᴺ) = (π₁ t ≈ tᴺ) × (π₂ t ≈ uᴺ)
_≈_ {A + B} {Γ} t (ne+ n)   = t ~ ⌜ n ⌝Ne
_≈_ {A + B} {Γ} t (inj₁ tᴺ) = Σ (Tm Γ A) λ t' → (t ~ inj₁ t') × (t' ≈ tᴺ)
_≈_ {A + B} {Γ} t (inj₂ tᴺ) = Σ (Tm Γ B) λ t' → (t ~ inj₂ t') × (t' ≈ tᴺ)

infix 3 _≈_ _≈ᶜ_

data _≈ᶜ_ {Γ} : ∀ {Δ} → Sub Γ Δ → Conᴺ Δ Γ → Set where
  ∙   : _≈ᶜ_ ∙ ∙
  _,_ : ∀ {A Δ σ δ}{t : Tm Γ A}{t' : Tyᴺ A Γ} → _≈ᶜ_ {Γ}{Δ} σ δ → t ≈ t' → (σ , t) ≈ᶜ (δ , t')

≈ₑ : ∀ {A Γ Δ}(σ : OPE Δ Γ){t : Tm Γ A}{tᴺ : Tyᴺ A Γ} → t ≈ tᴺ → Tmₑ σ t ≈ Tyᴺₑ {A} σ tᴺ
≈ₑ {Ty.⊤}  σ {t} {tᴺ} t≈tᴺ = coe ((_ ~_) & (⌜⌝Nf-nat σ tᴺ ⁻¹)) (~ₑ σ t≈tᴺ)
≈ₑ {Ty.⊥}  σ {t} {tᴺ} t≈tᴺ = coe ((_ ~_) & (⌜⌝Ne-nat σ tᴺ ⁻¹)) (~ₑ σ t≈tᴺ)
≈ₑ {A ⇒ B} σ {t} {tᴺ} t≈tᴺ δ rewrite Tm-∘ₑ σ δ t ⁻¹ = t≈tᴺ (σ ∘ₑ δ)
≈ₑ {A * B} σ {t} {tᴺ} t≈tᴺ = ≈ₑ {A} σ (proj₁ t≈tᴺ) , ≈ₑ {B} σ (proj₂ t≈tᴺ)
≈ₑ {A + B} σ {t} {ne+ n}   t≈tᴺ            = coe ((_ ~_) & (⌜⌝Ne-nat σ n ⁻¹)) (~ₑ σ t≈tᴺ)
≈ₑ {A + B} σ {t} {inj₁ tᴺ} (t' , t~t' , p) = Tmₑ σ t' , ~ₑ σ t~t' , ≈ₑ {A} σ p
≈ₑ {A + B} σ {t} {inj₂ tᴺ} (t' , t~t' , p) = Tmₑ σ t' , ~ₑ σ t~t' , ≈ₑ {B} σ p

≈ᶜₑ : ∀ {Γ Δ Σ}(σ : OPE Σ Γ){δ}{νᴺ : Conᴺ Δ Γ} → δ ≈ᶜ νᴺ → δ ₛ∘ₑ σ ≈ᶜ Conᴺₑ σ νᴺ
≈ᶜₑ σ ∙                    = ∙
≈ᶜₑ σ (_,_ {A} δ≈ᶜνᴺ t≈tᴺ) = ≈ᶜₑ σ δ≈ᶜνᴺ , ≈ₑ {A} σ t≈tᴺ

_~≈◾_ : ∀ {A Γ}{t t' : Tm Γ A}{tᴺ : Tyᴺ A Γ} → t ~ t' → t' ≈ tᴺ → t ≈ tᴺ
_~≈◾_ {Ty.⊤}  p q = p ~◾ q
_~≈◾_ {Ty.⊥}  p q = p ~◾ q
_~≈◾_ {A ⇒ B} p q = λ σ a≈aᴺ → app (~ₑ σ p) ~refl ~≈◾ q σ a≈aᴺ
_~≈◾_ {A * B} p q = (π₁ p ~≈◾ proj₁ q) , (π₂ p ~≈◾ proj₂ q)
_~≈◾_ {A + B} {tᴺ = ne+ n}   p q           = p ~◾ q
_~≈◾_ {A + B} {tᴺ = inj₁ tᴺ} p (q , r , s) = q , (p ~◾ r) , s
_~≈◾_ {A + B} {tᴺ = inj₂ tᴺ} p (q , r , s) = q , (p ~◾ r) , s

mutual
  q≈ : ∀ {A Γ}{t : Tm Γ A}{tᴺ : Tyᴺ A Γ} → t ≈ tᴺ → t ~ ⌜ qᴺ tᴺ ⌝
  q≈ {Ty.⊤}  t≈tᴺ = ⊤η _
  q≈ {A ⇒ B} t≈tᴺ = ⇒η _ ~◾ lam (q≈ (t≈tᴺ wk (u≈ {A} (var vz))))
  q≈ {Ty.⊥}  t≈tᴺ = t≈tᴺ
  q≈ {A * B} {Γ} {t} {tᴺ , uᴺ}  (p , q) = πη t ~⁻¹ ~◾ q≈ p , q≈ q
  q≈ {A + B} {Γ} {t} {ne+ n}   t≈tᴺ = t≈tᴺ
  q≈ {A + B} {Γ} {t} {inj₁ tᴺ} (p , q , r) = q ~◾ inj₁ (q≈ r)
  q≈ {A + B} {Γ} {t} {inj₂ tᴺ} (p , q , r) = q ~◾ inj₂ (q≈ r)

  u≈ : ∀ {A Γ}(n : Ne Γ A) → ⌜ n ⌝Ne ≈ uᴺ n
  u≈ {Ty.⊤}  n = ⊤η ⌜ n ⌝Ne
  u≈ {A ⇒ B} n σ {a} {aᴺ} a≈aᴺ rewrite ⌜⌝Ne-nat σ n ⁻¹ =
    app {B = B} ~refl (q≈ {A} a≈aᴺ) ~≈◾ u≈ {B} (Ne.app (Neₑ σ n) (qᴺ {A} aᴺ))
  u≈ {Ty.⊥}  n = ~refl
  u≈ {A * B} n = u≈ (π₁ n) , u≈ (π₂ n)
  u≈ {A + B} n = ~refl

⟦∈⟧ : ∀ {A Γ Δ}(v : A ∈ Γ){σ}{Γᴺ : Conᴺ Γ Δ} → σ ≈ᶜ Γᴺ → ∈ₛ σ v ≈ ∈ᴺ v Γᴺ
⟦∈⟧ vz     (σ≈Γᴺ , t≈tᴺ) = t≈tᴺ
⟦∈⟧ (vs v) (σ≈Γᴺ , _   ) = ⟦∈⟧ v σ≈Γᴺ

⟦Tm⟧ : ∀ {A Γ Δ}(t : Tm Γ A){σ}{δᴺ : Conᴺ Γ Δ} → σ ≈ᶜ δᴺ → Tmₛ σ t ≈ Tmᴺ t δᴺ
⟦Tm⟧ (var v) σ≈δᴺ = ⟦∈⟧ v σ≈δᴺ

⟦Tm⟧ (lam t) {σ} {δ} σ≈δᴺ ν {a} {aᴺ} a≈aᴺ
  = coe ((app (lam (Tmₑ (keep ν) (Tmₛ (keepₛ σ) t))) a ~_ ) & (βₑₛ σ ν t a ⁻¹))
    (⇒β (Tmₑ (keep ν) (Tmₛ (keepₛ σ) t)) a)
  ~≈◾ ⟦Tm⟧ t (≈ᶜₑ ν σ≈δᴺ , a≈aᴺ)

⟦Tm⟧ (app f a) {σ} {δ} σ≈δᴺ
  rewrite Tm-idₑ (Tmₛ σ f) ⁻¹ = ⟦Tm⟧ f σ≈δᴺ idₑ (⟦Tm⟧ a σ≈δᴺ)
⟦Tm⟧ tt σ≈δᴺ = ~refl
⟦Tm⟧ (π₁ t) σ≈δᴺ = proj₁ (⟦Tm⟧ t σ≈δᴺ)
⟦Tm⟧ (π₂ t) σ≈δᴺ = proj₂ (⟦Tm⟧ t σ≈δᴺ)
⟦Tm⟧ (t , u) {σ} σ≈δᴺ = (π₁β (Tmₛ σ t) (Tmₛ σ u) ~≈◾ ⟦Tm⟧ t σ≈δᴺ) ,
                        ((π₂β (Tmₛ σ t) (Tmₛ σ u) ~≈◾ ⟦Tm⟧ u σ≈δᴺ))
⟦Tm⟧ (inj₁ {A} {B} t) {σ} {δᴺ} σ≈δᴺ = Tmₛ σ t , ~refl , ⟦Tm⟧ t σ≈δᴺ
⟦Tm⟧ (inj₂ {A} {B} t) {σ} {δᴺ} σ≈δᴺ = Tmₛ σ t , ~refl , ⟦Tm⟧ t σ≈δᴺ
⟦Tm⟧ {C} {Γ} {Δ} (case {A} {B} l r t) {σ} {δᴺ} σ≈δᴺ with Tmᴺ t δᴺ | ⟦Tm⟧ t σ≈δᴺ
... | ne+  n  | tp =
  let up = u≈ {C} (case (qᴺ (Tmᴺ l (Conᴺₑ wk δᴺ , uᴺ {A} (var vz))))
                        (qᴺ (Tmᴺ r (Conᴺₑ wk δᴺ , uᴺ {B} (var vz)))) n)
      lp = ⟦Tm⟧ l {keepₛ σ} (≈ᶜₑ wk σ≈δᴺ , u≈ {A} _)
      rp = ⟦Tm⟧ r {keepₛ σ} (≈ᶜₑ wk σ≈δᴺ , u≈ {B} _)
  in case (q≈ {C} lp) (q≈ {C} rp) tp ~≈◾ up
... | inj₁ tᴺ | (t' , p , q) =
      (case ~refl ~refl p
   ~◾ case₁β (Tmₛ (keepₛ σ) l) (Tmₛ (keepₛ σ) r) t'
   ~◾ coe ((Tmₛ (idₛ , t') (Tmₛ (keepₛ σ) l) ~_) &
          (Tm-∘ₛ (keepₛ σ) (idₛ , t') l ⁻¹
        ◾ (λ x → Tmₛ (x , t') l) & (assₛₑₛ σ wk (idₛ , t') ◾ (σ ∘ₛ_) & idlₑₛ idₛ ◾ idrₛ σ)))
        ~refl)
   ~≈◾ ⟦Tm⟧ l {σ , t'} {δᴺ , tᴺ} (σ≈δᴺ , q)
... | inj₂ tᴺ | (t' , p , q) =
      (case ~refl ~refl p
   ~◾ case₂β (Tmₛ (keepₛ σ) l) (Tmₛ (keepₛ σ) r) t'
   ~◾ coe ((Tmₛ (idₛ , t') (Tmₛ (keepₛ σ) r) ~_) &
          (Tm-∘ₛ (keepₛ σ) (idₛ , t') r ⁻¹
        ◾ (λ x → Tmₛ (x , t') r) & (assₛₑₛ σ wk (idₛ , t') ◾ (σ ∘ₛ_) & idlₑₛ idₛ ◾ idrₛ σ)))
        ~refl)
   ~≈◾ ⟦Tm⟧ r {σ , t'} {δᴺ , tᴺ} (σ≈δᴺ , q)

⟦Tm⟧ (⊥-rec {A} t) {σ} {δᴺ} σ≈δᴺ =
  ⊥-rec {_}{A} (⟦Tm⟧ t σ≈δᴺ) ~≈◾ u≈ {A} (Ne.⊥-rec {_}{A} (Tmᴺ t δᴺ))

u≈ᶜ  : ∀ {Γ} → idₛ {Γ} ≈ᶜ uConᴺ
u≈ᶜ {∙}     = ∙
u≈ᶜ {Γ , A} = ≈ᶜₑ wk u≈ᶜ , u≈ {A} (var vz)

complete : ∀ {Γ A}(t : Tm Γ A) → t ~ ⌜ nf t ⌝
complete t = coe ((_~ ⌜ qᴺ (Tmᴺ t uConᴺ) ⌝) & Tm-idₛ t) (q≈ (⟦Tm⟧ t u≈ᶜ))
