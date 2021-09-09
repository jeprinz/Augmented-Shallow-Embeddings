\begin{code}
{-# OPTIONS --cumulativity #-}
open import Data.Nat
open import Data.Nat.Show
open import Augmented-Shallow-Embedding
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.String hiding (show)
open import Data.Fin hiding (_+_ ; _-_)
import Dep-Thy-shallow as S
\end{code}

\begin{code}
lambdaCount : ∀{sΓ Γ T s} → Exp {sΓ} Γ T s → ℕ
lambdaCount (lambda e) = 1 + (lambdaCount e)
lambdaCount (var x) = 0
lambdaCount (app e₁ e₂) = (lambdaCount e₁) + (lambdaCount e₂)
lambdaCount (Π₀ A B) = (lambdaCount A) + (lambdaCount B)
lambdaCount (Π₁ A B) = (lambdaCount A) + (lambdaCount B)
lambdaCount U₀ = 0
\end{code}

\begin{code}
extract : ∀{sΓ Γ T t} → Exp {sΓ} Γ T t → S.Exp sΓ T
extract {sΓ} {Γ} {T} {t} e = t
\end{code}

\begin{code}
consistency : ∀{t} → Exp {S.∅} ∅ (λ _ → ⊥) t → ⊥
consistency e = (extract e) tt
\end{code}

\begin{code}
ctxLength : ∀{sΓ} → Context sΓ → ℕ
ctxLength ∅ = 0
ctxLength (Γ , T) = 1 + (ctxLength Γ)

varIndex : ∀{sΓ T t} → {Γ : Context sΓ} → Var Γ T t → Fin (ctxLength Γ)
varIndex same = zero
varIndex (next x) = suc (varIndex x)

_-_ : (n : ℕ) → Fin n → ℕ
n - zero = n
(suc n) - suc f = n - f

compileToJs : ∀{sΓ Γ T s} → Exp {sΓ} Γ T s → String
compileToJs {sΓ} {Γ} (lambda e) = "function(x" ++ (show (ctxLength Γ)) ++ "){" ++ compileToJs e ++ "}"
compileToJs {sΓ} {Γ} (var x) = "x" ++ (show ((ctxLength Γ) - (varIndex x)))
compileToJs (app e₁ e₂) = "(" ++ (compileToJs e₁) ++ " " ++ (compileToJs e₂) ++ ")"
compileToJs (Π₀ e₁ e₂) = "null"
compileToJs (Π₁ e₁ e₂) = "null"
compileToJs U₀ = "null"

example : Exp ∅ (λ _ → (X Y : Set) → (X → Y) → X → Y) _
example = lambda (lambda (lambda (lambda (app (var (next same)) (var same)))))

test : String
test = compileToJs example

bla = {! test  !}
\end{code}
