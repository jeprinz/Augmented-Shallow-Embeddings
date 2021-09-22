--------------------------------------------------------------------------------
\begin{code}
{-# OPTIONS --cumulativity #-}

open import Data.Product
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Bool hiding (T)
open import Data.Maybe
open import variables

open import Augmented-Shallow-Embedding
import Dep-Thy-shallow as S
\end{code}

--------------------------------------------------------------------------------
Initial definitions

POINTER: vardata and check

\begin{code}
data VarData : Context sΓ → Set where
  ∅ : VarData ∅
  _,_ : VarData Γ → Bool → VarData (Γ , T)

data Check : VarData Γ → VarData Γ → VarData Γ
  → Set j where
  ∅ : Check ∅ ∅ ∅
  consLeft : (T : S.Type sΓ) → Check Γ₁ Γ₂ Γ₃
    → Check (Γ₁ , true) (Γ₂ , false) (Γ₃ , true)
  consRight : (T : S.Type sΓ) → Check Γ₁ Γ₂ Γ₃
    → Check (Γ₁ , false) (Γ₂ , true) (Γ₃ , true)
  consNeither : (T : S.Type sΓ) → Check Γ₁ Γ₂ Γ₃
    → Check (Γ₁ , false) (Γ₂ , false) (Γ₃ , false)

\end{code}


POINTER

\begin{code}

noneVars : ∀{Γ} → VarData Γ
oneVars : (Γ : Context aΓ) → Var Γ T t → VarData Γ
check : (vd₁ vd₂ : VarData Γ)
  → Maybe (Σ {j} {j} (VarData Γ) (λ vd₃ → Check vd₁ vd₂ vd₃))
\end{code}

--------------------------------------------------------------------------------
Some boring implementations

\begin{code}

check ∅ ∅ = just (∅ , ∅)
check (vd₁ , x) (vd₂ , x₁) with check vd₁ vd₂
check (vd₁ , b₁) (vd₂ , b₂) | nothing = nothing
check (vd₁ , false) (vd₂ , false) | just (vd₃ , c) = just ((vd₃ , false) , consNeither _ c)
check (vd₁ , false) (vd₂ , true) | just (vd₃ , c) = just ((vd₃ , true) , consRight _ c)
check (vd₁ , true) (vd₂ , false) | just (vd₃ , c) = just ((vd₃ , true) , consLeft _ c)
check (vd₁ , true) (vd₂ , true) | just (vd₃ , c) = nothing

noneVars {_}  {∅} = ∅
noneVars {_}  {Γ , T} = noneVars , false

oneVars .(_ , _) same = noneVars , true
oneVars .(_ , _) (next x) = oneVars _ x , false
\end{code}

--------------------------------------------------------------------------------
POINTER - Main definition

\begin{code}
data AffineTerm : (Γ : Context sΓ) → VarData Γ
  → (T : S.Type sΓ) → S.Term sΓ T → Set j where
  app : AffineTerm Γ Γ₁ (S.Π A B) s₁
      → (x : AffineTerm Γ Γ₂ A s₂) → Check Γ₁ Γ₂ Γ₃
      → AffineTerm Γ Γ₃ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
  Π : AffineTerm Γ Γ₁ S.U s₁
    → AffineTerm (Γ , s₁) (Γ₂ , b) S.U s₂ → Check Γ₁ Γ₂ Γ₃
    → AffineTerm Γ Γ₃ S.U (S.Π s₁ s₂)
  -- ...
\end{code}
POINTER
\begin{code}
  lambda : AffineTerm (Γ , A) (vd , b) B s
    → AffineTerm Γ vd (S.Π A B) (S.lambda s)
  var : (x : Var Γ T s) → AffineTerm {sΓ} Γ (oneVars Γ x) T s
  Π₁ : AffineTerm Γ Γ₁ S.U₁ s₁
    → AffineTerm (Γ , s₁) (Γ₂ , b) S.U₁ s₂ → Check Γ₁ Γ₂ Γ₃
    → AffineTerm Γ Γ₃ S.U₁ (S.Π₁ s₁ s₂)
  U₀ : AffineTerm {sΓ} Γ (noneVars) S.U₁ S.U₀
\end{code}


POINTER checkAffine declaration

\begin{code}
checkAffine : Term Γ T t
  → Maybe (Σ (VarData Γ) (λ vd → AffineTerm Γ vd T t))
\end{code}

POINTER - checkAffine definition

\begin{code}
checkAffine (lambda e) with checkAffine e
... | nothing = nothing
... | just ((vd , false) , Ae) = just (vd , lambda Ae)
... | just ((vd , true) , Ae) = just (vd , lambda Ae)
checkAffine (var icx) = just (oneVars _ icx , var icx)
checkAffine (app e₁ e₂) with checkAffine e₁ | checkAffine e₂
... | nothing | res2 = nothing
... | just x | nothing = nothing
... | just (vd₁ , Ae₁) | just (vd₂ , Ae₂) with check vd₁ vd₂
... | nothing = nothing
... | just (vd₃ , c) = just (vd₃ , app Ae₁ Ae₂ c)
checkAffine (Π₀ e₁ e₂) with checkAffine e₁ | checkAffine e₂
... | nothing | res2 = nothing
... | just x | nothing = nothing
... | just (vd₁ , ae₁) | just ((vd₂ , b) , ae₂) with check vd₁ vd₂
... | nothing = nothing
... | just (vd , c) = just (vd , Π₀ ae₁ ae₂ c)
checkAffine (Π₁ e₁ e₂) with checkAffine e₁ | checkAffine e₂
... | nothing | res2 = nothing
... | just x | nothing = nothing
... | just (vd₁ , ae₁) | just ((vd₂ , b) , ae₂) with check vd₁ vd₂
... | nothing = nothing
... | just (vd , c) = just (vd , Π₁ ae₁ ae₂ c)
checkAffine U₀ = just (noneVars ,  U₀)

\end{code}

POINTER - Examples
\begin{code}
ex1 : AffineTerm ∅ ∅ (λ _ → (Set → Set)) _
ex1 = lambda (var same)

ex1' : Term ∅ (λ _ → (Set → Set)) _
ex1' = lambda (var same)

test1 : checkAffine ex1' ≡ just (_ , ex1)
test1 = refl

ex2 : Term ∅ (λ _ → (X : Set) → X → X) _
ex2 = lambda (lambda (var same))

test2 : checkAffine ex2 ≡ just (_ , lambda (lambda (var same)))
test2 = refl
\end{code}
