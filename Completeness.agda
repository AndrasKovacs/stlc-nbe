{-# OPTIONS --without-K #-}

module Completeness where

open import Lib
open import Syntax
open import Renaming
open import Substitution
open import Conversion
open import Nf

infix 3 _≈_ _≈ₛ_

Norm₂ : ∀ {A Γ} → Tm Γ A → Tm Γ A → Set
Norm₂ {A}{Γ} t t' = Σ (Nf Γ A) λ n → (t ~ ⌜ n ⌝) × (t' ~ ⌜ n ⌝)

_≈_ : ∀ {A Γ} → Tm Γ A → Tm Γ A → Set
_≈_ {ι}        t t' = Norm₂ t t'
_≈_ {A ⇒ B}{Γ} t t' = ∀ {Δ}(σ : Ren Δ Γ){a a'} → a ≈ a' → app (t [ σ ]ᵣ) a ≈ app (t' [ σ ]ᵣ) a'

_≈ₛ_ : ∀ {Δ Γ} → Tms Γ Δ → Tms Γ Δ → Set
_≈ₛ_ {∙}     σ       δ        = ⊤
_≈ₛ_ {Δ , A} (σ , t) (δ , t') = (σ ≈ₛ δ) × (t ≈ t')

≈ᵣ : ∀ {A Γ Δ}{t t' : Tm Γ A} → (σ : Ren Δ Γ) → t ≈ t' → t [ σ ]ᵣ ≈ t' [ σ ]ᵣ
≈ᵣ {ι}     σ (n , t~n , t'~n) = let p = ⌜⌝ᵣ n σ ⁻¹ in
  (n [ σ ]ₙᵣ) , coe ((_ ~_) & p) (~ᵣ σ t~n) , coe ((_ ~_) & p) (~ᵣ σ t'~n)
≈ᵣ {A ⇒ B} σ t≈t' = λ δ {a a'} a≈a' →
  coe ((λ t t' → app t a ≈ app t' a') & (∘ᵣTm _ σ δ ⁻¹) ⊗ ((∘ᵣTm _ σ δ ⁻¹)))(t≈t' (σ ∘ᵣ δ) a≈a')

≈ₛᵣ : ∀ {Σ Γ Δ}(σ : Ren Δ Γ){δ ν : Tms Γ Σ} → δ ≈ₛ ν → (δ ₛ∘ᵣ σ) ≈ₛ (ν ₛ∘ᵣ σ)
≈ₛᵣ σ {δ = ∙}             δ≈ν          = tt
≈ₛᵣ σ {δ = _ , _} {_ , _} (δ≈ν , t≈t') = ≈ₛᵣ σ δ≈ν , ≈ᵣ σ t≈t'

infix 6 _≈⁻¹ _≈ₛ⁻¹

_≈⁻¹ : ∀ {A Γ}{t t' : Tm Γ A} → t ≈ t' → t' ≈ t
_≈⁻¹ {ι}     (n , p , q) = n , q , p
_≈⁻¹ {A ⇒ B} t≈t'        = λ σ a≈a' → t≈t' σ (a≈a' ≈⁻¹) ≈⁻¹

_≈ₛ⁻¹ : ∀ {Γ Δ}{σ δ : Tms Γ Δ} → σ ≈ₛ δ → δ ≈ₛ σ
_≈ₛ⁻¹ {σ = ∙}     {∙}      σ≈δ          = tt
_≈ₛ⁻¹ {σ = σ , t} {δ , t'} (σ≈δ , t≈t') = σ≈δ ≈ₛ⁻¹ , t≈t' ≈⁻¹

infixr 4 _≈◾_ _≈ₛ◾_ _~≈◾_

_≈◾_ : ∀ {A Γ}{t t' t'' : Tm Γ A} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {ι} (n , p , q) (n' , p' , q') = n , p , (q' ~◾ (p' ~⁻¹ ~◾ q))
_≈◾_ {A ⇒ B} p q = λ σ a≈a' → p σ (a≈a' ≈◾ a≈a' ≈⁻¹) ≈◾ q σ a≈a'

_≈ₛ◾_ : ∀ {Δ Γ}{σ δ ν : Tms Γ Δ} → σ ≈ₛ δ → δ ≈ₛ ν → σ ≈ₛ ν
_≈ₛ◾_ {σ = ∙}     {∙}      {∙}       p          q            = tt
_≈ₛ◾_ {σ = σ , t} {δ , t'} {ν , t''} (p , t≈t') (q , t'≈t'') = (p ≈ₛ◾ q) , (t≈t' ≈◾ t'≈t'')

_~≈◾_ : ∀ {A Γ}{t t' t'' : Tm Γ A} → t ~ t' → t' ≈ t'' → t ≈ t''
_~≈◾_ {ι}     p (n , s , t) = n , (p ~◾ s) , t
_~≈◾_ {A ⇒ B} p q           = λ σ a≈a' → app₁ (~ᵣ σ p) ~≈◾ q σ a≈a'

_≈~◾_ : ∀ {A Γ}{t t' t'' : Tm Γ A} → t ≈ t' → t' ~ t'' → t ≈ t''
p ≈~◾ q = (q ~⁻¹ ~≈◾ p ≈⁻¹) ≈⁻¹

⟦∈⟧ : ∀ {Γ Δ A}(v : A ∈ Γ){σ δ : Tms Δ Γ} → σ ≈ₛ δ → v [ σ ]∈ ≈ v [ δ ]∈
⟦∈⟧ vz     {σ , _}{δ , _} (σ≈δ , p) = p
⟦∈⟧ (vs v) {σ , _}{δ , _} (σ≈δ , _) = ⟦∈⟧ v σ≈δ

⟦Tm⟧ : ∀ {Γ Δ A}(t : Tm Γ A){σ δ : Tms Δ Γ} → σ ≈ₛ δ → t [ σ ] ≈ t [ δ ]
⟦Tm⟧ (var v) σ≈δ = ⟦∈⟧ v σ≈δ

⟦Tm⟧ {Γ}{Δ}{A ⇒ B}(lam t) {σ}{δ} σ≈δ {Σ} ν {a}{a'} a≈a' =
      coe ((app (lam (t [ keepₛ σ ] [ keep ν ]ᵣ)) a ~_) & βᵣ σ ν t a)
        (β (t [ keepₛ σ ] [ keep ν ]ᵣ) a)
  ~≈◾ (⟦Tm⟧ t {σ ₛ∘ᵣ ν , a}{δ ₛ∘ᵣ ν , a'}(≈ₛᵣ ν σ≈δ , a≈a'))
  ≈~◾ coe ((_~ app (lam (t [ keepₛ δ ] [ keep ν ]ᵣ)) a') & βᵣ δ ν t a')
        (β (t [ keepₛ δ ] [ keep ν ]ᵣ) a' ~⁻¹)

⟦Tm⟧ (app f a) {σ}{δ} σ≈δ =
  coe ((λ t t' → app t (a [ σ ]) ≈ app t' (a [ δ ]))
       & idᵣTm (f [ σ ]) ⊗ idᵣTm (f [ δ ]))
    (⟦Tm⟧ f σ≈δ idᵣ (⟦Tm⟧ a σ≈δ))


⟦~⟧ : ∀ {Γ Δ A}{t t' : Tm Γ A} → t ~ t' → ∀ {σ δ : Tms Δ Γ} → σ ≈ₛ δ → t [ σ ] ≈ t' [ δ ]
⟦~⟧ (~refl {t = t} ) σ≈δ = ⟦Tm⟧ t σ≈δ
⟦~⟧ (t'~t ~⁻¹      ) σ≈δ = ⟦~⟧ t'~t (σ≈δ ≈ₛ⁻¹) ≈⁻¹
⟦~⟧ (t~t' ~◾ t'~t'') σ≈δ = ⟦~⟧ t~t' (σ≈δ ≈ₛ◾ σ≈δ ≈ₛ⁻¹) ≈◾ ⟦~⟧ t'~t'' σ≈δ

⟦~⟧ (app₁ {f = f} {f'} {a} f~f') {σ} {δ} σ≈δ =
  coe ((λ t t' → app t (a [ σ ]) ≈ app t' (a [ δ ]))
      & idᵣTm (f [ σ ]) ⊗ idᵣTm (f' [ δ ]))
   (⟦~⟧ f~f' σ≈δ idᵣ (⟦Tm⟧ a σ≈δ))

⟦~⟧ (app₂ {f = f} {a} {a'} a~a') {σ} {δ} σ≈δ =
  coe (((λ t t' → app t (a [ σ ]) ≈ app t' (a' [ δ ]))
      & idᵣTm (f [ σ ]) ⊗ idᵣTm (f [ δ ])))
  (⟦Tm⟧ f σ≈δ idᵣ (⟦~⟧ a~a' σ≈δ))

⟦~⟧ (lam {t = t}{t'} t~t') {σ}{δ} σ≈δ = λ ν {a a'} a≈a' →
      coe ((app (lam (t [ keepₛ σ ] [ keep ν ]ᵣ)) a ~_) & βᵣ σ ν t a)
        (β (t [ keepₛ σ ] [ keep ν ]ᵣ) a)
  ~≈◾ ⟦~⟧ t~t' (≈ₛᵣ ν σ≈δ , a≈a')
  ≈~◾ coe ((_~ app (lam (t' [ keepₛ δ ] [ keep ν ]ᵣ)) a') & βᵣ δ ν t' a')
        (β (t' [ keepₛ δ ] [ keep ν ]ᵣ) a' ~⁻¹)

⟦~⟧ (η t) {σ} {δ} σ≈δ ν {a}{a'} a≈a' =
      ⟦Tm⟧ t σ≈δ ν a≈a'
  ≈~◾ (coe
    ((λ t' → app t' a' ~ app (lam (app (t [ wk ]ᵣ [ keepₛ δ ] [ keep ν ]ᵣ) (var vz))) a') &
        (βᵣ δ ν (t [ wk ]ᵣ) a'
      ◾ ᵣ∘ₛTm t wk ((δ ₛ∘ᵣ ν) , a')
      ◾ (t [_]) & idlᵣₛ (δ ₛ∘ᵣ ν)
      ◾ ₛ∘ᵣTm t δ ν ⁻¹))
    (β (app (t [ wk ]ᵣ [ keepₛ δ ] [ keep ν ]ᵣ) (var vz)) a' ~⁻¹))

⟦~⟧ (β t t') {σ} {δ} σ≈δ =
      ⟦Tm⟧ (app (lam t) t') σ≈δ
  ≈~◾ coe ((app (lam (t [ keepₛ δ ])) (t' [ δ ]) ~_) &
        (∘ₛTm t (keepₛ δ) (idₛ , (t' [ δ ]))
      ◾ (λ x → t [ x , (t' [ δ ]) ]) &
          (assₛᵣₛ δ (drop idᵣ) (idₛ , (t' [ δ ]))
        ◾ (δ ∘ₛ_) & idlᵣₛ idₛ
        ◾ idrₛ δ
        ◾ idlₛ δ ⁻¹)
      ◾ ∘ₛTm t (idₛ , t') δ ⁻¹))
      (β (t [ keepₛ δ ]) (t' [ δ ]))

-- binary logical predicate = unary predicate on relation?

mutual
  q : ∀ A {Γ}{t t' : Tm Γ A} → t ≈ t' → Norm₂ t t'
  q ι       t≈t' = t≈t'
  q (A ⇒ B) t≈t' =
    let (n , t~n , t'~n) = q B (t≈t' wk (u A (var vz)))
    in (lam n) , (η _ ~◾ lam t~n) , (η _ ~◾ lam t'~n)

  u : ∀ A {Γ}(n : Ne Γ A) → ⌜ n ⌝Ne ≈ ⌜ n ⌝Ne
  u ι       n                    = ne n , ~refl , ~refl
  u (A ⇒ B) n {Δ} σ {a}{a'} a≈a' =
    let (aₙ , a~aₙ , a'~aₙ) = q A a≈a'
    in    coe ((λ x → app (⌜ n ⌝Ne [ σ ]ᵣ) a ~ app x ⌜ aₙ ⌝) & (⌜⌝Neᵣ n σ ⁻¹)) (app₂ a~aₙ)
      ~≈◾ u B (n [ σ ]ₙₑᵣ $ₙ aₙ)
      ≈~◾ coe ((λ x → app x ⌜ aₙ ⌝ ~ app (⌜ n ⌝Ne [ σ ]ᵣ) a') & (⌜⌝Neᵣ n σ ⁻¹)) (app₂ a'~aₙ ~⁻¹)

uCon : ∀ Γ → idₛ {Γ} ≈ₛ idₛ
uCon ∙       = tt
uCon (Γ , A) = ≈ₛᵣ wk (uCon Γ) , u A (var vz)

norm₂ : ∀ {Γ A} (t t' : Tm Γ A) → t ~ t' → Norm₂ t t'
norm₂ t t' t~t' = q _ (coe (_≈_ & idₛTm t ⊗ idₛTm t') (⟦~⟧ t~t' (uCon _)))

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = proj₁ (norm₂ t t ~refl)

