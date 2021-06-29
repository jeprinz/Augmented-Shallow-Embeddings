\begin{code}
{-# OPTIONS --cumulativity #-}

open import Data.Product
open import Agda.Primitive
open import Data.Unit

import Dep-Thy-shallow as DTS

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
mutual
  data Context : DTS.Ctx → Set j where
    ∅ : Context DTS.∅
    _,_ : ∀{sΓ} → (ctx : Context sΓ) → (T : sΓ → Set i) → Context (DTS.cons sΓ T)

  data Var : {sΓ : DTS.Ctx} → (Γ : Context sΓ) → (T : DTS.Type sΓ)
    → ((γ : sΓ) → T γ) → Set j where
    same : ∀{sΓ T} → {Γ : Context sΓ} → Var (Γ , T) (DTS.weakenT T) DTS.same
    next : ∀{sΓ Γ T A s} → Var {sΓ} Γ A s → Var (Γ , T) (DTS.weakenT A) (DTS.next s)

mutual
  data Exp : {sΓ : DTS.Ctx} → (Γ : Context sΓ) → (T : DTS.Type sΓ)
    → DTS.Exp sΓ T → Set j where
    lambda : {sΓ : DTS.Ctx} → {Γ : Context sΓ} → {A : DTS.Type sΓ} → {B : DTS.Type (DTS.cons sΓ A)} → ∀{s}
      → Exp (Γ , A) B s → Exp Γ (DTS.Π A B) (DTS.lambda s)
    var : {sΓ : DTS.Ctx} → {Γ : Context sΓ} → {T : DTS.Type sΓ} → {s : DTS.Exp sΓ T}
      → Var Γ T s → Exp {sΓ} Γ T s
    app : {sΓ : DTS.Ctx} → {Γ : Context sΓ} → {A : DTS.Type sΓ} → {B : DTS.Type (DTS.cons sΓ A)} → ∀{s₁ s₂}
        → Exp Γ (DTS.Π A B) s₁ → (x : Exp Γ A s₂)
        → Exp Γ (λ γ → B (γ , s₂ γ)) (DTS.app s₁ s₂)
    Π : {sΓ : DTS.Ctx} → {Γ : Context sΓ} → {s₁ : DTS.Type sΓ} → {s₂ : DTS.Type (DTS.cons sΓ s₁)}
      → (A : Exp Γ (λ _ → Set) s₁)
      → (B : Exp (Γ , (λ γ → s₁ γ)) (λ _ → Set) s₂)
      → Exp Γ (λ _ → Set) (λ γ → (x : s₁ γ) → s₂ (γ , x))
    The solution here is to put Π₀, Π₁, ... in Dep-Thy-shallow,  and then mirror them here.
    𝓤₀ : {sΓ : Set i} → {Γ : Context sΓ} → Exp {sΓ} Γ (λ _ → Set₁) (λ _ → Set₀)
\end{code}
