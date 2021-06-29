\begin{code}
open import Data.Unit
open import Data.Product

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
