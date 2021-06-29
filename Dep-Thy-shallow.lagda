\begin{code}
{-# OPTIONS --cumulativity #-}
open import Data.Unit
open import Agda.Primitive
open import Data.Product

module Dep-Thy-shallow where

-- arbitrarily pick some type levels to work with.
i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

Ctx : Set j
Type : Ctx → Set j
Var : (Γ : Ctx) → Type Γ → Set i
Exp : (Γ : Ctx) → Type Γ → Set i

Ctx = Set i
Type Γ = Γ → Set i
Var Γ T = (γ : Γ) → T γ
Exp Γ T = (γ : Γ) → T γ

∅ : Ctx
∅ = ⊤
cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ {i} {i} Γ T

Π : ∀{Γ} → (A : Type Γ) → Type (cons Γ A) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

U₀ : ∀{Γ} → Type Γ
U₀ γ = Set₀

U₁ : ∀{Γ} → Type Γ
U₁ γ = Set₁

U₂ : ∀{Γ} → Type Γ
U₂ γ = Set₂

weakenT : ∀{Γ T} → Type Γ → Type (cons Γ T)
weakenT T (γ , _) = T γ

same : ∀{Γ T} → Var (cons Γ T) (weakenT T)
same = λ (γ , t) → t
next : ∀{Γ T A} → Var Γ A → Var (cons Γ T) (weakenT A)
next x = λ (γ , t) → x γ

var : ∀{Γ T} → (icx : Var Γ T) → Exp Γ T
var x = x

lambda : ∀{Γ A B} → Exp (cons Γ A) B → Exp Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app : ∀{Γ A B} → Exp Γ (Π A B) → (a : Exp Γ A) → Exp Γ (λ γ → B (γ , a γ))
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)
\end{code}
