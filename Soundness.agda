{-# OPTIONS --without-K #-}

module Soundness where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Nf
open import Normalization

infix 3 _≈_ -- _≈ᶜ_

_≈_ : ∀ {A Γ} → Tyᴺ A Γ → Tyᴺ A Γ → Set
_≈_ {ι}    {Γ} tᴺ tᴺ' = tᴺ ≡ tᴺ'
_≈_ {A ⇒ B}{Γ} tᴺ tᴺ' =
  ∀ {Δ}(σ : OPE Δ Γ) {aᴺ aᴺ' : Tyᴺ A Δ} → aᴺ ≈ aᴺ' →
     (∀ {Σ}(δ : OPE Σ Δ) → (tᴺ  (σ ∘ₑ δ) (Tyᴺₑ δ aᴺ) ≡ Tyᴺₑ δ (tᴺ  σ aᴺ))
                         × (tᴺ' (σ ∘ₑ δ) (Tyᴺₑ δ aᴺ) ≡ Tyᴺₑ δ (tᴺ' σ aᴺ)))
     × (tᴺ σ aᴺ ≈ tᴺ' σ aᴺ')

data _≈ᶜ_ : ∀ {Γ Δ} → Conᴺ Γ Δ → Conᴺ Γ Δ → Set where
  ∙   : ∀ {Γ} → _≈ᶜ_ {∙}{Γ} ∙ ∙
  _,_ : ∀ {A Γ Δ σ δ}{t t' : Tyᴺ A Δ} → _≈ᶜ_ {Γ}{Δ} σ δ → t ≈ t' → (σ , t) ≈ᶜ (δ , t')

_≈⁻¹ : ∀ {Γ A}{t t' : Tyᴺ A Γ} → t ≈ t' → t' ≈ t
_≈⁻¹ {A = ι}     t≈t' = t≈t' ⁻¹
_≈⁻¹ {A = A ⇒ B} t≈t' = λ σ a≈a' →
  (λ δ → let nat₁ , nat₂ = proj₁ (t≈t' σ a≈a') δ in nat₂ , nat₁) ,
  (proj₂ (t≈t' σ (a≈a' ≈⁻¹)) ≈⁻¹)

_≈ᶜ⁻¹ : ∀ {Γ Δ}{σ δ : Conᴺ Γ Δ} → σ ≈ᶜ δ → δ ≈ᶜ σ
∙            ≈ᶜ⁻¹ = ∙
(σ≈δ , t≈t') ≈ᶜ⁻¹ = (σ≈δ ≈ᶜ⁻¹) , (t≈t' ≈⁻¹)

_≈◾_ : ∀ {Γ A}{t t' t'' : Tyᴺ A Γ} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {A = ι}     p q = p ◾ q
_≈◾_ {A = A ⇒ B} p q = λ σ a≈a' →
  (λ δ → proj₁ (proj₁ (p σ a≈a') δ) , proj₂ (proj₁ (q σ a≈a') δ)) ,
  (proj₂ (p σ (a≈a' ≈◾ (a≈a' ≈⁻¹))) ≈◾ proj₂ (q σ a≈a'))

≈refl : ∀ {A Γ}{t t' : Tyᴺ A Γ} → t ≈ t' → t ≈ t
≈refl p = p ≈◾ (p ≈⁻¹)

_≈ᶜ◾_ : ∀ {Γ Δ}{σ δ ν : Conᴺ Γ Δ} → σ ≈ᶜ δ → δ ≈ᶜ ν → σ ≈ᶜ ν
∙          ≈ᶜ◾ q            = q
(p , t≈t') ≈ᶜ◾ (q , t'≈t'') = (p ≈ᶜ◾ q) , (t≈t' ≈◾ t'≈t'')

≈ᶜrefl : ∀ {A Γ}{Γᴺ Γᴺ' : Conᴺ A Γ} → Γᴺ ≈ᶜ Γᴺ' → Γᴺ ≈ᶜ Γᴺ
≈ᶜrefl p = p ≈ᶜ◾ (p ≈ᶜ⁻¹)

≈ₑ : ∀ {Γ Δ A}(σ : OPE Δ Γ){t t' : Tyᴺ A Γ} → t ≈ t' → Tyᴺₑ σ t ≈ Tyᴺₑ σ t'
≈ₑ {A = ι}     σ t≈t' = Nfₑ σ & t≈t'
≈ₑ {A = A ⇒ B} σ {t}{t'} t≈t' = λ δ {aᴺ}{aᴺ'} a≈a' →
  (λ ν → let p = λ (t : Tyᴺ (A ⇒ B) _) x → t x (Tyᴺₑ ν aᴺ) ≡ Tyᴺₑ ν (t (σ ∘ₑ δ) aᴺ)
         in coe ((λ x → p t x × p t' x) & assₑ σ δ ν) (proj₁ (t≈t' (σ ∘ₑ δ) a≈a') ν)) ,
  proj₂ (t≈t' (σ ∘ₑ δ) a≈a')

≈ᶜₑ : ∀ {Γ Δ Σ}(σ : OPE Σ Γ){δ ν : Conᴺ Δ Γ} → δ ≈ᶜ ν → Conᴺₑ σ δ ≈ᶜ Conᴺₑ σ ν
≈ᶜₑ σ ∙          = ∙
≈ᶜₑ σ (p , t≈t') = ≈ᶜₑ σ p , ≈ₑ σ t≈t'

∈≈ : ∀ {Γ Δ A}(v : A ∈ Γ){σ δ : Conᴺ Γ Δ} → σ ≈ᶜ δ → ∈ᴺ v σ ≈ ∈ᴺ v δ
∈≈ vz     (σ≈δ , t≈t') = t≈t'
∈≈ (vs v) (σ≈δ , _   ) = ∈≈ v σ≈δ

∈ᴺ-nat : ∀ {Γ Δ Σ A}(v : A ∈ Γ)(σ : OPE Σ Δ) Γᴺ → ∈ᴺ v (Conᴺₑ σ Γᴺ) ≡ Tyᴺₑ σ (∈ᴺ v Γᴺ)
∈ᴺ-nat vz     σ (Γᴺ , _) = refl
∈ᴺ-nat (vs v) σ (Γᴺ , _) = ∈ᴺ-nat v σ Γᴺ

mutual
  Tm≈ : ∀ {Γ Δ A}(t : Tm Γ A){Γᴺ Γᴺ' : Conᴺ Γ Δ} →  Γᴺ ≈ᶜ Γᴺ' → Tmᴺ t Γᴺ ≈ Tmᴺ t Γᴺ'
  Tm≈ (var v)   p = ∈≈ v p
  Tm≈ (lam t)   p = λ σ a≈a' →
      (λ δ → let eq = λ {Γᴺ} (p : Γᴺ ≈ᶜ Γᴺ) → (λ x → Tmᴺ t (x , _)) & Conᴺ-∘ₑ σ δ _
                       ◾ Tmᴺ-nat t δ (≈ᶜₑ σ p , ≈refl a≈a')
             in eq (≈ᶜrefl p) , eq (≈ᶜrefl (p ≈ᶜ⁻¹))) ,
      Tm≈ t (≈ᶜₑ σ p , a≈a')
  Tm≈ (app f x) p = proj₂ (Tm≈ f p idₑ (Tm≈ x p))

  Tmᴺ-nat :
    ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : OPE Σ Δ) {Γᴺ} → Γᴺ ≈ᶜ Γᴺ → Tmᴺ t (Conᴺₑ σ Γᴺ) ≡ Tyᴺₑ σ (Tmᴺ t Γᴺ)
  Tmᴺ-nat (var v)   σ p = ∈ᴺ-nat v σ _
  Tmᴺ-nat (lam t)   σ p = funexti λ Σ → funext λ δ → funext λ aᴺ →
    (λ x → Tmᴺ t (x , aᴺ)) & (Conᴺ-∘ₑ σ δ _ ⁻¹)
  Tmᴺ-nat (app f x) σ p rewrite
      Tmᴺ-nat f σ p | Tmᴺ-nat x σ p
    | proj₁ (proj₁ (Tm≈ f p idₑ (Tm≈ x (≈ᶜrefl p))) σ) ⁻¹
    | idrₑ σ | idlₑ σ = refl

uᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(n : Ne Γ A) → Tyᴺₑ σ (uᴺ n) ≡ uᴺ (Neₑ σ n)
uᴺ-nat {ι}     σ n = refl
uᴺ-nat {A ⇒ B} σ n = funexti λ Σ → funext λ δ → funext λ aᴺ →
  (λ x → uᴺ (app x (qᴺ aᴺ))) & Ne-∘ₑ σ δ n

mutual
  uᴺ≈ : ∀ {A Γ}{n n' : Ne Γ A} → n ≡ n' → uᴺ n ≈ uᴺ n'
  uᴺ≈ {ι}     n≡n' = ne & n≡n'
  uᴺ≈ {A ⇒ B} n≡n' = λ σ a≈a' →
    (λ δ → let eq = λ {n : Ne _ (A ⇒ B)} →
                 ((λ x y → uᴺ (app x y)) & (Ne-∘ₑ σ δ n ⁻¹) ⊗ qᴺ-nat δ _ (≈refl a≈a') ⁻¹
                ◾ uᴺ-nat δ (app (Neₑ σ n) (qᴺ _)) ⁻¹)
           in eq , eq ) ,
    uᴺ≈ (app & (Neₑ σ & n≡n') ⊗ qᴺ≈ a≈a')

  qᴺ≈ : ∀ {A Γ}{t t' : Tyᴺ A Γ} → t ≈ t' → qᴺ t ≡ qᴺ t'
  qᴺ≈ {ι}     t≈t' = t≈t'
  qᴺ≈ {A ⇒ B} t≈t' = lam & qᴺ≈ (proj₂ (t≈t' wk (uᴺ≈ refl)))

  qᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(tᴺ : Tyᴺ A Γ) → tᴺ ≈ tᴺ → Nfₑ σ (qᴺ tᴺ) ≡ qᴺ (Tyᴺₑ σ tᴺ)
  qᴺ-nat {ι}     σ tᴺ t≈t = refl
  qᴺ-nat {A ⇒ B} σ tᴺ t≈t =
    let tᴺ-nat , ta≈ = t≈t wk (uᴺ≈ {n = var vz} refl) in
    lam & (qᴺ-nat (keep σ) (tᴺ wk (uᴺ (var vz))) ta≈
        ◾ qᴺ & (proj₁ (tᴺ-nat (keep σ)) ⁻¹
              ◾ tᴺ & (drop & (idlₑ σ ◾ (idrₑ σ ⁻¹))) ⊗ uᴺ-nat (keep σ) (var vz)))

Tmₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(t : Tm Γ A){Γᴺ Γᴺ' : Conᴺ Δ Σ} → Γᴺ ≈ᶜ Γᴺ'
 → Tmᴺ (Tmₛ σ t) Γᴺ ≈ Tmᴺ t (Subᴺ σ Γᴺ')
Tmₛᴺ σ (var v) {Γᴺ' = Γᴺ'} p rewrite ∈ₛᴺ σ v Γᴺ' ⁻¹ = Tm≈ (∈ₛ σ v) p
Tmₛᴺ σ (lam t)   p δ a≈a' = {!Sub!}
Tmₛᴺ σ (app f x) p = proj₂ (Tmₛᴺ σ f p idₑ (Tmₛᴺ σ x p))

-- Tmₛᴺ :
--  ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(t : Tm Γ A)(δᴺ : Conᴺ Δ Σ) → δᴺ ≈ᶜ δᴺ
--  → Tmᴺ (Tmₛ σ t) δᴺ ≈ Tmᴺ t (Subᴺ σ δᴺ)
-- Tmₛᴺ σ (var v) {Γᴺ' = Γᴺ'} p rewrite ∈ₛᴺ σ v Γᴺ' ⁻¹ = Tm≈ (∈ₛ σ v) p
-- Tmₛᴺ σ (lam t)   δᴺ δᴾ δᴺ≈* ν {a}{a'} aᴾ aᴾ' a≈a'
--   rewrite Subᴺ-nat σ ν δᴺ δᴾ ⁻¹
--   = let δᴾ' = Conᴾₑ ν δᴾ in
--     Tmₛᴺ (keepₛ σ) t (Conᴺₑ ν δᴺ , a) (Conᴾₑ ν δᴾ , aᴾ) (≈*ₑ ν δᴺ≈* , (a≈a' ≈◾ (a≈a' ≈⁻¹)))
--   ≈◾ coe ((λ x → Tmᴺ t (x , a) ≈ _) & (Subᴺ-ₛ∘ₑ σ wk (Conᴺₑ ν δᴺ , a) ◾ Subᴺ σ & OPEᴺ-idₑ (Conᴺₑ ν δᴺ)) ⁻¹)
--      (⟦Tm⟧ t (Subᴺᴾ σ δᴾ' , aᴾ) (Subᴺᴾ σ δᴾ' , aᴾ') (Subᴺ≈* σ δᴾ' δᴾ' (≈*ₑ ν δᴺ≈*) , a≈a'))
-- Tmₛᴺ σ (app f x) δᴺ δᴾ δᴺ≈* =
--   Tmₛᴺ σ f δᴺ δᴾ δᴺ≈* idₑ (Tmᴾ (Tmₛ σ x) δᴾ) (Tmᴾ x (Subᴺᴾ σ δᴾ)) (Tmₛᴺ σ x δᴺ δᴾ δᴺ≈*)

⟦~⟧ :
  ∀ {Γ A}{t t' : Tm Γ A} → t ~ t'
  → ∀ {Δ}{Γᴺ Γᴺ' : Conᴺ Γ Δ} → Γᴺ ≈ᶜ Γᴺ' → Tmᴺ t Γᴺ ≈ Tmᴺ t' Γᴺ'

⟦~⟧ (η t) {Γᴺ = Γᴺ}{Γᴺ'} Γ≈Γ' σ {aᴺ}{aᴺ'} a≈a'
  rewrite
    Tmₑᴺ wk t (Conᴺₑ σ Γᴺ' , aᴺ')
  | OPEᴺ-idₑ (Conᴺₑ σ Γᴺ')
  | Tmᴺ-nat t σ (≈ᶜrefl (Γ≈Γ' ≈ᶜ⁻¹))
  | idrₑ σ
  = (λ δ → proj₁ (proj₁ (Tm≈ t (≈ᶜrefl Γ≈Γ') σ a≈a') δ) ,
           -- TODO: reduce this clutter
           ((λ x → x idₑ (Tyᴺₑ δ aᴺ)) & Tmₑᴺ wk t (Conᴺₑ (σ ∘ₑ δ) Γᴺ' , Tyᴺₑ δ aᴺ)
           ◾ (λ x → Tmᴺ t x idₑ (Tyᴺₑ δ aᴺ)) & OPEᴺ-idₑ (Conᴺₑ (σ ∘ₑ δ) Γᴺ')
           ◾ (λ x → x idₑ (Tyᴺₑ δ aᴺ)) & Tmᴺ-nat t (σ ∘ₑ δ) (≈ᶜrefl (Γ≈Γ' ≈ᶜ⁻¹))
           ◾ (λ x → Tmᴺ t Γᴺ' x (Tyᴺₑ δ aᴺ)) & idrₑ (σ ∘ₑ δ)
           ◾ proj₁ (proj₁ (Tm≈ t (≈ᶜrefl (Γ≈Γ' ≈ᶜ⁻¹)) σ a≈a') δ)
           ◾ Tyᴺₑ δ & (
                (λ x → Tmᴺ t Γᴺ' x aᴺ) & idrₑ σ ⁻¹
              ◾ (λ x → x idₑ aᴺ) & Tmᴺ-nat t σ (≈ᶜrefl (Γ≈Γ' ≈ᶜ⁻¹)) ⁻¹
              ◾ (λ x → Tmᴺ t x idₑ aᴺ) & OPEᴺ-idₑ (Conᴺₑ σ Γᴺ') ⁻¹
              ◾ (λ x → x idₑ aᴺ) & Tmₑᴺ wk t (Conᴺₑ σ Γᴺ' , aᴺ) ⁻¹))
           ) ,
    proj₂ (Tm≈ t Γ≈Γ' σ a≈a')

⟦~⟧ (β t t') {Γᴺ = Γᴺ} Γ≈Γ' =
     coe ((λ x y → Tmᴺ t (x , Tmᴺ t' Γᴺ) ≈ Tmᴺ t (y , Tmᴺ t' Γᴺ)) &
           (Conᴺ-idₑ Γᴺ ⁻¹) ⊗ (Subᴺ-idₛ Γᴺ ⁻¹))
         (Tm≈ t (≈ᶜrefl Γ≈Γ' , Tm≈ t' (≈ᶜrefl Γ≈Γ')))
  ≈◾ (Tmₛᴺ (idₛ , t') t (Γ≈Γ' ≈ᶜ⁻¹) ≈⁻¹)

⟦~⟧ (lam {t = t}{t'} t~t') Γ≈Γ' = λ σ a≈a' →
  (λ δ → proj₁ (proj₁ (Tm≈ (lam t) Γ≈Γ' σ a≈a') δ) ,
         proj₁ (proj₁ (Tm≈ (lam t') (Γ≈Γ' ≈ᶜ⁻¹) σ a≈a') δ)) ,
  (⟦~⟧ t~t' (≈ᶜₑ σ Γ≈Γ' , a≈a'))

⟦~⟧ (app₁ {x = x} t~t') Γ≈Γ' = proj₂ (⟦~⟧ t~t' Γ≈Γ' idₑ (Tm≈ x Γ≈Γ'))
⟦~⟧ (app₂ {f = f} t~t') Γ≈Γ' = proj₂ (Tm≈ f Γ≈Γ' idₑ (⟦~⟧ t~t' Γ≈Γ'))
⟦~⟧ (~refl {t = t})     Γ≈Γ' = Tm≈ t Γ≈Γ'
⟦~⟧ (t'~t ~⁻¹)          Γ≈Γ' = ⟦~⟧ t'~t (Γ≈Γ' ≈ᶜ⁻¹) ≈⁻¹
⟦~⟧ (t~t' ~◾ t'~t'')    Γ≈Γ' = ⟦~⟧ t~t' (≈ᶜrefl Γ≈Γ') ≈◾ ⟦~⟧ t'~t'' Γ≈Γ'

uCon≈ : ∀ {Γ} → uConᴺ {Γ} ≈ᶜ uConᴺ
uCon≈ {∙}     = ∙
uCon≈ {Γ , A} = ≈ᶜₑ wk uCon≈ , uᴺ≈ refl

sound : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
sound t~t' = qᴺ≈ (⟦~⟧ t~t' uCon≈)

