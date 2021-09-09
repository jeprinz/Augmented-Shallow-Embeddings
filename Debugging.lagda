\begin{code}
{-# OPTIONS --cumulativity #-}

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Bool
open import Data.Maybe

-- open import Augmented-Shallow-Embedding
import Dep-Thy-shallow as S

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
\end{code}

\begin{code}
data Context : S.Ctx → Set j where
  ∅ : Context S.∅
  _,_ : ∀{sΓ} → Context sΓ → (T : S.Type sΓ) → Context (S.cons sΓ T)

data Var : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → (S.Exp sΓ T) → Set j where
  same : ∀{sΓ T} → {Γ : Context sΓ} → Var (Γ , T) (S.weakenT T) S.same
  next : ∀{sΓ Γ T A s} → Var {sΓ} Γ A s → Var (Γ , T) (S.weakenT A) (S.next s)

data DebugType : S.Ctx → Set j where
  ∅ : ∀{sΓ} → DebugType sΓ
  _,_ : ∀{sΓ} → DebugType sΓ → (T : S.Type sΓ) → DebugType sΓ

data DebugData : {sΓ : S.Ctx} → DebugType sΓ → Set j where
  ∅ : ∀{sΓ} → DebugData {sΓ} ∅
  _,_ : ∀{sΓ} → {dt : DebugType sΓ} → {T : S.Type sΓ} → DebugData dt
    → S.Exp sΓ T → DebugData (dt , T)

Sub : S.Ctx → S.Ctx → Set j
Sub sΓ₁ sΓ₂ = sΓ₂ → sΓ₁

subDebugType : ∀{sΓ₁ sΓ₂} → Sub sΓ₁ sΓ₂ → DebugType sΓ₁ → DebugType sΓ₂
subDebugType sub ∅ = ∅
subDebugType sub (dt , T) = subDebugType sub dt , (λ γ → T (sub γ))

subDebugData : ∀{sΓ₁ sΓ₂} → (sub : Sub sΓ₁ sΓ₂) → {dt : DebugType sΓ₁}
  → DebugData dt → DebugData (subDebugType sub dt)
subDebugData sub ∅ = ∅
subDebugData sub (dd , t) = subDebugData sub dd , (λ γ → t (sub γ))

subEnd : {sΓ : S.Ctx} → {T : S.Type sΓ} → S.Exp sΓ T → Sub (S.cons sΓ T) sΓ
subEnd t γ = γ , t γ

data DebugExp : {sΓ : S.Ctx} → (Γ : Context sΓ) → (T : S.Type sΓ)
  → S.Exp sΓ T
  → (dd : DebugType sΓ) → DebugData dd
  → Set j where
  breakpoint : ∀{sΓ Γ T t dt dd} → DebugExp {sΓ} Γ T t dt dd → DebugExp {sΓ} Γ T t (dt , T) (dd , t)
  lambda : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s dt dd}
    → DebugExp (Γ , A) B s dt dd
    → DebugExp Γ (S.Π A B) (S.lambda s) (subDebugType (subEnd {!   !} ) dt) {!   !}
  -- var : {sΓ : S.Ctx} → {Γ : Context sΓ} → {T : S.Type sΓ} → {s : S.Exp sΓ T}
  --   → Var Γ T s → DebugExp {sΓ} Γ T s
  -- app : {sΓ : S.Ctx} → {Γ : Context sΓ} → {A : S.Type sΓ} → {B : S.Type (S.cons sΓ A)} → ∀{s₁ s₂}
  --     → DebugExp Γ (S.Π A B) s₁ → (x : DebugExp Γ A s₂)
  --     → DebugExp Γ (λ γ → B (γ , s₂ γ)) (S.app s₁ s₂)
  -- Π₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₀ sΓ} → {s₂ : S.Type₀ (S.cons sΓ s₁)}
  --   → (A : DebugExp Γ S.U₀ s₁)
  --   → (B : DebugExp (Γ , s₁) S.U₀ s₂)
  --   → DebugExp Γ S.U₀ (S.Π₀ s₁ s₂)
  -- Π₁ : {sΓ : S.Ctx} → {Γ : Context sΓ} → {s₁ : S.Type₁ sΓ} → {s₂ : S.Type₁ (S.cons sΓ s₁)}
  --   → (A : DebugExp Γ S.U₁ s₁)
  --   → (B : DebugExp (Γ , s₁) S.U₁ s₂)
  --   → DebugExp Γ S.U₁ (S.Π₁ s₁ s₂)
  -- U₀ : {sΓ : S.Ctx} → {Γ : Context sΓ} → DebugExp {sΓ} Γ S.U₁ S.U₀
\end{code}
