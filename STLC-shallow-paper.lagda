\begin{code}
open import Data.Unit hiding (⊤)
open import Data.Product
open import variables
\end{code}

POINTER

\begin{code}
Type = Set
_⇒_ : Type → Type → Type
A ⇒ B = A → B
base : Type
base = ⊤

Ctx = Set
∅ : Ctx
∅ = ⊤
cons : Ctx → Type → Ctx
cons Γ T = Γ × T

Var : Ctx → Type → Set
Var Γ T = Γ → T
same : ∀{Γ T} → Var (Γ × T) T
same = λ (γ , t) → t
next : ∀{Γ T A} → Var Γ A → Var (Γ × T) A
next x = λ (γ , t) → x γ

Exp : Ctx → Type → Set
Exp Γ T = Γ → T
var : ∀{Γ T} → (icx : Var Γ T) → Exp Γ T
var x = x
lambda : ∀{Γ A B} → Exp (Γ × A) B → Exp Γ (A ⇒ B)
lambda e = λ γ a → e (γ , a)
app : ∀{Γ A B} → Exp Γ (A ⇒ B) → Exp Γ A → Exp Γ B
app e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)
⋆ : ∀{Γ} → Exp Γ base
⋆ = λ _ → tt
\end{code}
