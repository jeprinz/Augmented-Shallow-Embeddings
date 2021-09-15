First, some initial setup

\begin{code}
{-# OPTIONS --cumulativity #-}

open import Data.Product
open import Agda.Primitive
open import Data.Unit

import Dep-Thy-shallow as S

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
\end{code}

Next, the code that shows in the paper:

\begin{code}
data Context : S.Ctx → Set j where
  ∅ : Context S.∅
  _,_ : ∀{sΓ} → Context sΓ → (T : S.Type sΓ) → Context (S.cons sΓ T)

data Var : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → (S.Term sΓ T) → Set j where
  same : ∀{sΓ T} → {Γ : Context sΓ} → Var (Γ , T) (S.weakenT T) S.same
  next : ∀{sΓ Γ T A s} → Var {sΓ} Γ A s → Var (Γ , T) (S.weakenT A) (S.next s)

data Term : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → S.Term sΓ T → Set j where
  lambda : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s}
    → Term (Γ , A) B s → Term Γ (S.Π A B) (S.lambda s)
  var : {sΓ : S.Ctx} → {Γ : Context sΓ} → {T : S.Type sΓ} → {s : S.Term sΓ T}
    → Var Γ T s → Term {sΓ} Γ T s
  app : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
      → Term Γ (S.Π A B) s₁ → (x : Term Γ A s₂)
      → Term Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
  Π₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
    → (A : Term Γ S.U₀ s₁)
    → (B : Term (Γ , s₁) S.U₀ s₂)
    → Term Γ S.U₀ (S.Π₀ s₁ s₂)
  Π : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
    → (A : Term Γ S.U₀ s₁)
    → (B : Term (Γ , s₁) S.U₀ s₂)
    → Term Γ S.U₀ (S.Π₀ s₁ s₂)
  Π₁ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₁ sΓ} → {s₂ : S.Type₁ (S.cons sΓ s₁)}
    → (A : Term Γ S.U₁ s₁)
    → (B : Term (Γ , s₁) S.U₁ s₂)
    → Term Γ S.U₁ (S.Π₁ s₁ s₂)
  U₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → Term {sΓ} Γ S.U₁ S.U₀
  U : {sΓ : S.Ctx} → {Γ : Context sΓ} → Term {sΓ} Γ S.U₁ S.U₀
\end{code}
