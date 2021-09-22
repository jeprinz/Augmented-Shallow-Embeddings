\begin{code}
{-# OPTIONS --cumulativity #-}
open import Data.Unit hiding(⊤)
open import Agda.Primitive
open import Data.Product
-- open import Relation.Binary.PropositionalEquality
-- open import Function
open import variables

module Dep-Thy-shallow-paper-full where

-- arbitrarily pick some type levels to work with.
i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

\end{code}

POINTER - start

\begin{code}

Ctx = Set
Type : Ctx → Set
Type Γ = Γ → Set

∅ : Ctx
∅ = ⊤
cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ Γ T


Var : (Γ : Ctx) → Type Γ → Set
Var Γ T = (γ : Γ) → T γ
same : ∀{Γ T} → Var (cons Γ T) (T ∘ proj₁)
same = λ (γ , t) → t
next : ∀{Γ T A} → Var Γ A → Var (cons Γ T) (A ∘ proj₁)
next x = λ (γ , t) → x γ

Term : (Γ : Ctx) → Type Γ → Set
Term Γ T = (γ : Γ) → T γ

Π : ∀{Γ} → (A : Type Γ) → Type (cons Γ A) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

U : ∀{Γ} → Type Γ
U γ = Set

var : ∀{Γ T} → (icx : Var Γ T) → Term Γ T
var x = x

lambda : ∀{Γ A B} → Term (cons Γ A) B → Term Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app : ∀{Γ A B} → Term Γ (Π A B) → (a : Term Γ A)
  → Term Γ (λ γ → B (γ , a γ))
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

subTerm : (sub : Sub Γ₁ Γ₂)
  → Term Γ₁ T → Term Γ₂ (subType sub T)
subTerm sub e = λ γ₂ → e (sub γ₂)
\end{code}

POINTER - end
