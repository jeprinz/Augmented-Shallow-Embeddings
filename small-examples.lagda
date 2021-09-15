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
-- church numeral 2
-- Type = (X : U) → (X → X) → X → X
-- Term = λ X f x . f (f x)
Nat : Exp ∅ (S.Π₁ S.U₀
            (S.Π₀ (S.Π₀ (S.var S.same) (S.var (S.next S.same)))
              (S.Π₀ (S.var (S.next S.same)) (S.var (S.next (S.next S.same)))))) _
Nat = lambda (lambda (lambda (app (var (next same))
                                    (app (var (next same)) (var same)))))
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

example : Exp ∅ (λ _ → (X Y : Set) → (X → Y) → X → Y) _
example = lambda (lambda (lambda (lambda (app (var (next same)) (var same)))))

-- Leibniz equality
-- leibniz : ∀{Γ} → (T : S.Type Γ) → (a b : S.Exp Γ T) → S.Type Γ
-- leibniz T a b = λ γ → (P : (T γ) →
leibniz : (T : Set) → T → T → Set₁
leibniz T a b = (P : T → Set) → P a → P b

trans : Exp ∅ (λ _ → (T : Set) → (a b c : T)
  → leibniz T a b → leibniz T b c → leibniz T a c) _
trans = lambda (lambda (lambda (lambda (lambda (lambda
  (app (var (next same) ) (app {! var (next (next same))  !} (var same))))))))


\end{code}
