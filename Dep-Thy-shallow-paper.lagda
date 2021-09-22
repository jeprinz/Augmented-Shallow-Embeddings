\begin{code}
{-# OPTIONS --cumulativity #-}
open import Data.Unit
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import variables

module Dep-Thy-shallow-paper where

\end{code}

POINTER - Dep thy shallow

\begin{code}

Ctx : Set
Type : Ctx → Set
Var : (Γ : Ctx) → Type Γ → Set
Term : (Γ : Ctx) → Type Γ → Set

Π : ∀{Γ} → (A : Type Γ) → Type (Σ Γ A) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

U : ∀{Γ} → Type Γ
U γ = Set

lambda : ∀{Γ A B} → Term (Σ Γ A) B → Term Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app : ∀{Γ A B} → Term Γ (Π A B) → (a : Term Γ A) → Term Γ (λ γ → B (γ , a γ))
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)
\end{code}

POINTER - substitutions
\begin{code}
Sub : Ctx → Ctx → Set
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

extend : Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
extend sub e γ₂ = sub γ₂ , e (sub γ₂)

subType : Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
subType sub T = λ γ₂ → T (sub γ₂)

lift : (sub : Sub Γ₁ Γ₂) → (T : Type Γ₁)
  → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
lift sub T (γ , t) = sub γ , t

subExp : (sub : Sub Γ₁ Γ₂)
  → Term Γ₁ T → Term Γ₂ (subType sub T)
subExp sub e = λ γ₂ → e (sub γ₂)
\end{code}

POINTER - end
