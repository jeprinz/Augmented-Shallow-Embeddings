\begin{code}
{-# OPTIONS --cumulativity #-}
open import Data.Unit
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality

module Dep-Thy-shallow-paper where

\end{code}

POINTER - Dep thy shallow

\begin{code}

Ctx : Set
Type : Ctx → Set
Var : (Γ : Ctx) → Type Γ → Set
Exp : (Γ : Ctx) → Type Γ → Set

Π : ∀{Γ} → (A : Type Γ) → Type (Σ Γ A) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

U : ∀{Γ} → Type Γ
U γ = Set

lambda : ∀{Γ A B} → Exp (Σ Γ A) B → Exp Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app : ∀{Γ A B} → Exp Γ (Π A B) → (a : Exp Γ A) → Exp Γ (λ γ → B (γ , a γ))
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)
\end{code}

POINTER - substitutions

\begin{code}

--------------------------------------------------------------------------------

{-
Sub : Ctx → Ctx → Set j
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

weaken1ren : ∀{Γ} → (T : Type Γ) → Sub Γ (Σ Γ T)
weaken1ren T (γ , _) = γ

-- append1ren : ∀{Γ₁ Γ₂} → {T : GSemT Γ₂} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
append1sub : ∀{Γ₁ Γ₂} → {T : Type Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (Σ Γ₂ T)
append1sub sub (γ₂ , t) = sub γ₂

idSub : ∀{Γ} → Sub Γ Γ
idSub γ = γ

subType : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
subType sub T = λ γ₂ → T (sub γ₂)

subExp : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → (T : Type Γ₁)
  → Exp Γ₁ T → Exp Γ₂ (subType sub T)
subExp sub T t γ = t (sub γ)

test : ∀{Γ₁ Γ₂} → {T : Type Γ₁} → {A : Type Γ₂} → (sub : Sub Γ₁ Γ₂)
  → subType {Γ₁} {Σ Γ₂ A} (append1sub sub) T ≡ subType (append1sub idSub) (subType sub T)
test sub = refl
-}

\end{code}
