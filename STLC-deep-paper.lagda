\begin{code}
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
  var : ∀{Γ T} → Var Γ T → Exp Γ T
  lambda : ∀{Γ A B} → Exp (Γ , A) B
    → Exp Γ (A ⇒ B)
  app : ∀{Γ A B} → Exp Γ (A ⇒ B)
    → Exp Γ A → Exp Γ B
  tt : ∀{Γ} → Exp Γ base
\end{code}
