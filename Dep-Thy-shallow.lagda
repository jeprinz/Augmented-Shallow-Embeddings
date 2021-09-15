\begin{code}
{-# OPTIONS --cumulativity #-}
open import Data.Unit
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality

module Dep-Thy-shallow where

-- arbitrarily pick some type levels to work with.
i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i

Ctx : Set j
Type : Ctx → Set j
Var : (Γ : Ctx) → Type Γ → Set i
Term : (Γ : Ctx) → Type Γ → Set i

Ctx = Set i
Type Γ = Γ → Set i
Type₀ = λ (Γ : Ctx) → Γ → Set₀
Type₁ = λ (Γ : Ctx) → Γ → Set₁
Type₂ = λ (Γ : Ctx) → Γ → Set₂
Var Γ T = (γ : Γ) → T γ
Term Γ T = (γ : Γ) → T γ

∅ : Ctx
∅ = ⊤
cons : (Γ : Ctx) → Type Γ → Ctx
cons Γ T = Σ {i} {i} Γ T

Π : ∀{Γ} → (A : Type Γ) → Type (cons Γ A) → Type Γ
Π A B = λ γ → (a : A γ) → B (γ , a)

Π₀ : ∀{Γ} → (A : Type₀ Γ) → Type₀ (cons Γ A) → Type₀ Γ
Π₀ A B = λ γ → (a : A γ) → B (γ , a)

Π₁ : ∀{Γ} → (A : Type₁ Γ) → Type₁ (cons Γ A) → Type₁ Γ
Π₁ A B = λ γ → (a : A γ) → B (γ , a)

Π₂ : ∀{Γ} → (A : Type₂ Γ) → Type₂ (cons Γ A) → Type₂ Γ
Π₂ A B = λ γ → (a : A γ) → B (γ , a)

U₀ : ∀{Γ} → Type₁ Γ
U₀ γ = Set₀

U : ∀{Γ} → Type₁ Γ
U γ = Set₀

U₁ : ∀{Γ} → Type₂ Γ
U₁ γ = Set₁

weakenT : ∀{Γ T} → Type Γ → Type (cons Γ T)
weakenT T (γ , _) = T γ

same : ∀{Γ T} → Var (cons Γ T) (weakenT T)
same = λ (γ , t) → t
next : ∀{Γ T A} → Var Γ A → Var (cons Γ T) (weakenT A)
next x = λ (γ , t) → x γ

var : ∀{Γ T} → (icx : Var Γ T) → Term Γ T
var x = x

lambda : ∀{Γ A B} → Term (cons Γ A) B → Term Γ (Π A B)
lambda e = λ γ a → e (γ , a)

app : ∀{Γ A B} → Term Γ (Π A B) → (a : Term Γ A) → Term Γ (λ γ → B (γ , a γ))
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

cumu : ∀{Γ} → Term Γ U₀ → Term Γ U₁
cumu T = T
\end{code}

\begin{code}

--------------------------------------------------------------------------------

-- NOTE : should put renamings and substitutions in here.

{-

Because no Γ in SemT, some things work out definitionally. For example,
renType (append1ren ren) T ≡ renType (append1ren idRen) (renType ren T)

-}

-- Ren : Ctx → Ctx → Set j
-- Ren Γ₁ Γ₂ = ∀{T} → Var Γ₁ T → Var Γ₂ {! T  !}

Sub : Ctx → Ctx → Set j
Sub Γ₁ Γ₂ = Γ₂ → Γ₁

weaken1ren : ∀{Γ} → (T : Type Γ) → Sub Γ (cons Γ T)
weaken1ren T (γ , _) = γ

-- append1ren : ∀{Γ₁ Γ₂} → {T : GSemT Γ₂} → Ren Γ₁ Γ₂ → Ren Γ₁ (Γ₂ , T)
append1sub : ∀{Γ₁ Γ₂} → {T : Type Γ₂} → Sub Γ₁ Γ₂ → Sub Γ₁ (cons Γ₂ T)
append1sub sub (γ₂ , t) = sub γ₂

idSub : ∀{Γ} → Sub Γ Γ
idSub γ = γ

subType : ∀{Γ₁ Γ₂} → Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
subType sub T = λ γ₂ → T (sub γ₂)

subExp : ∀{Γ₁ Γ₂} → (sub : Sub Γ₁ Γ₂) → (T : Type Γ₁)
  → Term Γ₁ T → Term Γ₂ (subType sub T)
subExp sub T t γ = t (sub γ)

test : ∀{Γ₁ Γ₂} → {T : Type Γ₁} → {A : Type Γ₂} → (sub : Sub Γ₁ Γ₂)
  → subType {Γ₁} {cons Γ₂ A} (append1sub sub) T ≡ subType (append1sub idSub) (subType sub T)
test sub = refl

\end{code}
