First, some initial setup

\begin{code}
{-# OPTIONS --cumulativity #-}

open import Data.Product hiding (map)
open import Agda.Primitive
open import Data.Unit hiding (_≟_ ; ⊤)
open import Data.String
open import Data.Maybe
open import Data.Bool hiding (_≟_ ; T)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import variables

import Dep-Thy-shallow as S

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
\end{code}

POINTER: Context

\begin{code}
data Context : S.Ctx → Set j where
  ∅ : Context S.∅
  _,_∷_ : Context sΓ → String
    → (T : S.Type sΓ) → Context (S.cons sΓ T)

\end{code}

POINTER: Var type

\begin{code}

data Var : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → (S.Exp sΓ T) → Set j where
  same : Var (Γ , name ∷ T) (S.weakenT T) S.same
  next : Var {sΓ} Γ A s
    → Var (Γ , name ∷ T) (S.weakenT A) (S.next s)

\end{code}
\begin{code}

data Exp : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → S.Exp sΓ T → Set j where

\end{code}

POINTER: lambda and pi constructors

\begin{code}
  lambda : (name : String)
    → Exp (Γ , name ∷ A) B s → Exp Γ (S.Π A B) (S.lambda s)
  Π₀ : (name : String)
    → (A : Exp Γ S.U₀ s₁)
    → (B : Exp (Γ , name ∷ s₁) S.U₀ s₂)
    → Exp Γ S.U₀ (S.Π₀ s₁ s₂)
\end{code}
\begin{code}
  var : Var Γ T s → Exp {sΓ} Γ T s

\end{code}

POINTER: app constructor

\begin{code}
  app : Exp Γ (S.Π A B) s₁ → (x : Exp Γ A s₂)
      → Exp Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)

\end{code}
\begin{code}
  Π₁ : (name : String)
    → (A : Exp Γ S.U₁ s₁)
    → (B : Exp (Γ , name ∷ s₁) S.U₁ s₂)
    → Exp Γ S.U₁ (S.Π₁ s₁ s₂)
  U₀ : Exp {sΓ} Γ S.U₁ S.U₀
  ⋆ : Exp Γ (λ _ → ⊤) (λ _ → tt)

\end{code}

POINTER: var'

\begin{code}

findVar : (Γ : Context sΓ) → String → Maybe
  (Σ (Σ (S.Type sΓ) (S.Exp sΓ)) (λ (T , t) → Var Γ T t))

resultType : (Γ : Context sΓ) → String → S.Type sΓ
resultType Γ name with findVar Γ name
... | nothing = λ _ → ⊤
... | just ((T , t) , x) = T

resultTerm : (Γ : Context sΓ)
  → (name : String) → S.Exp sΓ (resultType Γ name)
resultTerm Γ name with findVar Γ name
... | nothing = λ _ → tt
... | just ((T , t) , x) = t

var' : (name : String)
  → Exp Γ (resultType Γ name) (resultTerm Γ name)
var' {Γ} name with findVar Γ name
... | nothing = ⋆
... | just ((T , t) , x) = var x

\end{code}
\begin{code}

\end{code}

POINTER: Example

\begin{code}

example2 : Exp ∅ (λ _ → (X : Set) → X → X) _
example2 = lambda "X" (lambda "x" (var' "x"))

\end{code}
\begin{code}

\end{code}
