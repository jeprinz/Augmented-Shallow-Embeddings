First, some initial setup

\begin{code}
{-# OPTIONS --cumulativity #-}

open import Data.Product hiding (map)
open import Agda.Primitive
open import Data.Unit hiding (_≟_)
open import Data.String
open import Data.Maybe
open import Data.Bool hiding (_≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function

import Dep-Thy-shallow as S

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
\end{code}

Next, the code that shows in the paper:

\begin{code}
data Context : S.Ctx → Set j where
  ∅ : Context S.∅
  _,_∷_ : ∀{sΓ} → Context sΓ → String → (T : S.Type sΓ) → Context (S.cons sΓ T)

data Var : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → (S.Exp sΓ T) → Set j where
  same : ∀{sΓ T name} → {Γ : Context sΓ} → Var (Γ , name ∷ T) (S.weakenT T) S.same
  next : ∀{sΓ Γ T A s name} → Var {sΓ} Γ A s → Var (Γ , name ∷ T) (S.weakenT A) (S.next s)

data Exp : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → S.Exp sΓ T → Set j where
  lambda : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)}
    → ∀{s} → (name : String) → Exp (Γ , name ∷ A) B s → Exp Γ (S.Π A B) (S.lambda s)
  var : {sΓ : S.Ctx} → {Γ : Context sΓ} → {T : S.Type sΓ} → {s : S.Exp sΓ T}
    → Var Γ T s → Exp {sΓ} Γ T s
  app : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
      → Exp Γ (S.Π A B) s₁ → (x : Exp Γ A s₂)
      → Exp Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
  Π₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
    → (name : String)
    → (A : Exp Γ S.U₀ s₁)
    → (B : Exp (Γ , name ∷ s₁) S.U₀ s₂)
    → Exp Γ S.U₀ (S.Π₀ s₁ s₂)
  Π₁ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₁ sΓ} → {s₂ : S.Type₁ (S.cons sΓ s₁)}
    → (name : String)
    → (A : Exp Γ S.U₁ s₁)
    → (B : Exp (Γ , name ∷ s₁) S.U₁ s₂)
    → Exp Γ S.U₁ (S.Π₁ s₁ s₂)
  U₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → Exp {sΓ} Γ S.U₁ S.U₀
  ⋆ : ∀{sΓ} → {Γ : Context sΓ} → Exp Γ (λ _ → ⊤) (λ _ → tt)
  cumu : ∀{sΓ} → {Γ : Context sΓ} → ∀{T}
    → Exp Γ S.U₀ T → Exp Γ S.U₁ (S.cumu T)

findVar : ∀{sΓ} → (Γ : Context sΓ) → String
  → Maybe (Σ {j} {j} (Σ {j} {i} (S.Type sΓ) (S.Exp sΓ)) (λ (T , t) → Var Γ T t))
findVar ∅ name = nothing
findVar (Γ , a ∷ A) name
  = if  ⌊ name ≟ a ⌋
    then just {j} ((S.subType (S.weaken1ren A) A , S.same) , same)
    else map
      (λ ((T , t) , x) → (S.subType (S.weaken1ren A) T , S.subExp (S.weaken1ren A) T t) , next x)
      (findVar Γ name)

resultType : ∀{sΓ} → (Γ : Context sΓ) → String → S.Type sΓ
resultType Γ name with findVar Γ name
... | nothing = λ _ → ⊤
... | just ((T , t) , x) = T

resultTerm : ∀{sΓ} → (Γ : Context sΓ) → (name : String) → S.Exp sΓ (resultType Γ name)
resultTerm Γ name with findVar Γ name
... | nothing = λ _ → tt
... | just ((T , t) , x) = t

var' : ∀{sΓ} → {Γ : Context sΓ} → (name : String) → Exp Γ (resultType Γ name) (resultTerm Γ name)
var' {_} {Γ} name with findVar Γ name
... | nothing = ⋆
... | just ((T , t) , x) = var x

example2 : Exp ∅ (λ _ → (X : Set) → X → X) _
example2 = lambda "X" (lambda "x" (var' "x"))

-- Π₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ}
--   → {s₂ : S.Type₀ (S.cons sΓ s₁)}
--   → (name : String)
--   → (A : Exp Γ S.U₀ s₁)
--   → (B : Exp (Γ , name ∷ s₁) S.U₀ s₂)
--   → Exp Γ S.U₀ (S.Π₀ s₁ s₂)

infixr 10 _⇒_
_⇒_ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ}
  → {s₂ : S.Type₀ (S.cons sΓ s₁)}
  → (A : Exp Γ S.U₀ s₁) → (B : Exp (Γ , "_" ∷ s₁) S.U₀ s₂)
  → Exp Γ S.U₀ (S.Π₀ s₁ s₂)
A ⇒ B = Π₀ "_" A B

`_` = var'

infixl 10 _^_
_^_ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
    → Exp Γ (S.Π A B) s₁ → (x : Exp Γ A s₂)
    → Exp Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
_^_ = app

Nat : Exp ∅ S.U₁ _
Nat = Π₁ "X" U₀ (cumu ((`"X"` ⇒ `"X"` ) ⇒ `"X"` ⇒ `"X"`))

extract : ∀{sΓ Γ T t} → Exp {sΓ} Γ T t → S.Exp sΓ T
extract {sΓ} {Γ} {T} {t} e = t

two : Exp ∅ (extract Nat) _
two = lambda "X" (lambda "f" (lambda "x"
  (`"f"` ^ (`"f"` ^ `"x"`))))

leibniz : (T : Set) → T → T → Set₁
leibniz T a b = (P : T → Set) → P a → P b

trans' : (T : Set) → (a b c : T)
  → leibniz T a b → leibniz T b c → leibniz T a c
trans' T a b c p₁ p₂ P x = p₂ P (p₁ P x)

-- lambda : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)}
  -- → ∀{s} → (name : String) → Exp (Γ , name ∷ A) B s → Exp Γ (S.Π A B) (S.lambda s)
fun :
{-
IDEA: lambda that takes list of strings, maps to a bunch of lambdas. This
is not just for fun, it really is something that can't be done with
shallow embeddings.
-}

trans : Exp ∅ (λ _ → (T : Set) → (a b c : T)
  → leibniz T a b → leibniz T b c → leibniz T a c) _
trans = lambda "T" (lambda "a" (lambda "b" (lambda "c"
  (lambda "p₁" (lambda "p₂" (lambda "P" (lambda "x"
  (`"p₂"` ^ `"P"` ^ (`"p₁"` ^ `"P"` ^ `"x"`)))))))))

-- Λ "X" - Λ "x" - var "x"
--
-- -- Λ
-- -- λ X . λ x . x

-- example3 : Exp ∅ (λ _ → Set₁)
-- example3 = Π₁ "X" 𝓤₀ (Cumu₀ (Π₀ "_" (var' "X") (var' "X")) )

\end{code}
