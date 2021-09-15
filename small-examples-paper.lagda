\begin{code}
{-# OPTIONS --cumulativity #-}
open import Data.Nat
open import Data.Nat.Show
open import Augmented-Shallow-Embedding
open import Data.Product
-- open import Data.Empty
open import Data.Unit
open import Data.String hiding (show)
open import Data.Fin hiding (_+_ ; _-_)
import Dep-Thy-shallow as S
open import variables
\end{code}

POINTER - lambdaCount

\begin{code}
lambdaCount : ∀{sΓ Γ T s} → Term {sΓ} Γ T s → ℕ
lambdaCount (lambda e) = 1 + (lambdaCount e)
lambdaCount (var x) = 0
lambdaCount (app e₁ e₂) = (lambdaCount e₁) + (lambdaCount e₂)
lambdaCount (Π₀ A B) = (lambdaCount A) + (lambdaCount B)
lambdaCount (Π₁ A B) = (lambdaCount A) + (lambdaCount B)
lambdaCount U₀ = 0
\end{code}

POINTER - extract

\begin{code}
extract : ∀{sΓ Γ T t} → Term {sΓ} Γ T t → S.Term sΓ T
extract {sΓ} {Γ} {T} {t} e = t
\end{code}

POINTER - consistency

\begin{code}
consistency : ∀{t} → Term {S.∅} ∅ (λ _ → ⊥) t → ⊥
consistency e = (extract e) tt
\end{code}

POINTER - compileToJs helper functions

\begin{code}
len : Context sΓ → ℕ
index : Var Γ T t → Fin (len Γ)
\end{code}

POINTER - compileToJs

\begin{code}
compileToJs : Term Γ T s → String
compileToJs {Γ} (lambda e)
  = "function(x" ++ (show (len Γ)) ++ ")"
    ++ "{" ++ compileToJs e ++ "}"
compileToJs {Γ} (var x)
  = "x" ++ (show ((len Γ) - (index x)))
compileToJs (app e₁ e₂)
  = "(" ++ (compileToJs e₁) ++ "
    " ++ (compileToJs e₂) ++ ")"
compileToJs (Π e₁ e₂) = "null"
compileToJs U = "null"
\end{code}

POINTER - example "two"

\begin{code}
two : Term ∅ (λ _ → (X Y : Set) → (X → Y) → X → Y) _
two = lambda (lambda (lambda (lambda
    (app (var (next same)) (var same)))))
\end{code}

POINTER - example identity

\begin{code}
id : Term ∅ (λ _ → (X : Set) → X → X) _
id = lambda (lambda (var same))
\end{code}

POINTER - shallow embedding U -> U identity

\begin{code}
piece1 : Ty
piece1 = S.lambda (S.var S.same)
piece2 : Ty
piece2 = S.Term S.∅ (S.Π S.U S.U)
piece3 : Ty
piece3 = λ y x → x

\end{code}
