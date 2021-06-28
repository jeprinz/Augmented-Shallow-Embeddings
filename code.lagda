This is the code associated with the paper "Name of paper here"

\begin{code}
module code where
open import Data.Unit
open import Data.Product
\end{code}

Deep embedding of Simply Typed Lambda Calculus
\begin{code}
module STLC-deep where
  data Type : Set where
    _⇒_ : Type → Type → Type
    base : Type

  data Ctx : Set where
    ∅ : Ctx
    _,_ : Ctx → Type → Ctx

  data Var : (Γ : Ctx) → Type → Set where
    same : ∀{Γ T} → Var (Γ , T) T
    next : ∀{Γ T A} → Var Γ A → Var (Γ , T) A

  data Exp : Ctx → Type → Set where
    var : ∀{Γ T} → (icx : Var Γ T) → Exp Γ T
    lambda : ∀{Γ A B} → Exp (Γ , A) B → Exp Γ (A ⇒ B)
    app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
    ⋆ : ∀{Γ} → Exp Γ base
\end{code}

Shallow embedding of Simply Typed Lambda Calculus
\begin{code}
module STLC-shallow where
  Ctx : Set₁
  Type : Set₁
  Var : Ctx → Type → Set
  Exp : Ctx → Type → Set

  Ctx = Set
  Type = Set
  Var Γ T = Γ → T
  Exp Γ T = Γ → T

  ∅ : Ctx
  ∅ = ⊤
  cons : Ctx → Type → Ctx
  cons Γ T = Γ × T

  _⇒_ : Type → Type → Type
  A ⇒ B = A → B
  base : Type
  base = ⊤

  same : ∀{Γ T} → Var (cons Γ T) T
  same = λ (γ , t) → t
  next : ∀{Γ T A} → Var Γ A → Var (cons Γ T) A
  next x = λ (γ , t) → x γ


  var : ∀{Γ T} → (icx : Var Γ T) → Exp Γ T
  var x = x
  lambda : ∀{Γ A B} → Exp (cons Γ A) B → Exp Γ (A ⇒ B)
  lambda e = λ γ a → e (γ , a)
  app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
  app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)
  ⋆ : ∀{Γ} → Exp Γ base
  ⋆ = λ _ → tt
\end{code}

Shallow embedding of Dependent Type Theory
\begin{code}
module Dep-Thy-shallow where
  Ctx : Set₁
  Type : Ctx → Set₁
  Var : (Γ : Ctx) → Type Γ → Set
  Exp : (Γ : Ctx) → Type Γ → Set

  Ctx = Set
  Type Γ = Γ → Set
  Var Γ T = (γ : Γ) → T γ
  Exp Γ T = (γ : Γ) → T γ

  ∅ : Ctx
  ∅ = ⊤
  cons : (Γ : Ctx) → Type Γ → Ctx
  cons Γ T = Σ Γ T

  Π : ∀{Γ} → (A : Type Γ) → Type (cons Γ A) → Type Γ
  Π A B = λ γ → (a : A γ) → B (γ , a)

  

  -- same : ∀{Γ T} → Var (cons Γ T) T
  -- same = λ (γ , t) → t
  -- next : ∀{Γ T A} → Var Γ A → Var (cons Γ T) A
  -- next x = λ (γ , t) → x γ
  --
  --
  -- var : ∀{Γ T} → (icx : Var Γ T) → Exp Γ T
  -- var x = x
  -- lambda : ∀{Γ A B} → Exp (cons Γ A) B → Exp Γ (A ⇒ B)
  -- lambda e = λ γ a → e (γ , a)
  -- app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
  -- app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)
  -- ⋆ : ∀{Γ} → Exp Γ base
  -- ⋆ = λ _ → tt
\end{code}
