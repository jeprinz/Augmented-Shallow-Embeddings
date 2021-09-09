\begin{code}

open import variables
open import Data.Nat
open import Data.Product
open import Data.Maybe

\end{code}

\begin{code}

postulate
  funExt : ((x : A) → f x ≡ g x) → f ≡ g
  funExtElim : funExt (λ x → refl) ≡ refl

{-# REWRITE funExtElim #-}

happly : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
            → f ≡ g → ((x : A) → f x ≡ g x)
happly refl x = refl

data TypeCode₀ : Set where
⟦_⟧₀ : TypeCode₀ → Set
⟦_⟧₀ ()

module Universe {TypeCode : Set} {⟦_⟧ : TypeCode → Set} where
  mutual
    data TypeCodeₙ₊₁ : Set where
        `U : TypeCodeₙ₊₁
        `Π : (A : TypeCodeₙ₊₁) → (⟦_⟧ₙ₊₁ A → TypeCodeₙ₊₁) → TypeCodeₙ₊₁
        `raise : TypeCode → TypeCodeₙ₊₁

    ⟦_⟧ₙ₊₁ : TypeCodeₙ₊₁ → Set
    ⟦ `U ⟧ₙ₊₁ = TypeCode
    ⟦ `Π A B ⟧ₙ₊₁ = (a : ⟦ A ⟧ₙ₊₁) → ⟦ B a ⟧ₙ₊₁
    ⟦ `raise T ⟧ₙ₊₁ = ⟦ T ⟧

open Universe

mutual
  TypeCode : ℕ → Set
  TypeCode zero = TypeCode₀
  TypeCode (suc n) = TypeCodeₙ₊₁ {TypeCode n} {⟦_⟧}

  ⟦_⟧ : {n : ℕ} → TypeCode n → Set
  ⟦_⟧ {zero} T = ⟦ T ⟧₀
  ⟦_⟧ {suc n} T = ⟦ T ⟧ₙ₊₁

------------------------  "Shallow" embedding   --------------------------------
module S where

  Ctx = Set
  Type : ℕ → Ctx → Set
  Type n Γ = Γ → TypeCode n
  Term : ∀{n} → (Γ : Ctx) → Type n Γ → Set
  Term Γ T = (γ : Γ) → ⟦ T γ ⟧
  Var : ∀{n} → (Γ : Ctx) → Type n Γ → Set
  Var Γ T = (γ : Γ) → ⟦ T γ ⟧
  nil : Ctx
  nil = ⊤
  cons : ∀{n} → (Γ : Ctx) → Type n Γ → Ctx
  cons Γ T = Σ Γ (λ γ → ⟦ T γ ⟧)

  U : ∀{n} → Type (suc n) Γ
  U = λ _ → `U

  Π : (A : Type (suc n) Γ) → Type (suc n) (cons Γ A) → Type (suc n) Γ
  Π A B = λ γ → `Π (A γ) ((λ a → B (γ , a)))

  lambda : Term (cons Γ A) B → Term Γ (Π A B)
  lambda e = λ γ → λ a → e (γ , a)

  app : Term Γ (Π A B) → (e₂ : Term Γ A) → Term Γ (λ γ → B (γ , e₂ γ))
  app A B e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

  weakenT : Type n Γ → Type n (cons Γ T)
  weakenT T A (γ , _) = A γ

  same : Var {n} (cons Γ T) (weakenT T T)
  same = λ (γ , t) → t

  next : Var Γ A → Var (cons Γ T) (weakenT A)
  next x = λ (γ , t) → x γ

  weaken : Term Γ T → Term (cons Γ A) (weakenT T)
  weaken e = λ γ → e (proj₁ γ)

  cumuT : Type n Γ → Type (suc n) Γ
  cumuT T = λ γ → `raise (T γ)

  raise : Term Γ T → Term Γ (cumuT T)
  raise e = e

\end{code}

POINTER - Sub in shallow embedding - no typecodes

\begin{code}

  Sub : Ctx → Ctx → Set
  Sub Γ₁ Γ₂ = Γ₂ → Γ₁

  extend : Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
  extend sub e γ₂ = sub γ₂ , e (sub γ₂)

  idSub : Sub Γ Γ
  idSub γ = γ

  weaken1Ren : Sub Γ (cons {n} Γ T)
  weaken1Ren = proj₁

  subType : Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
  subType sub T = λ γ₂ → T (sub γ₂)

  lift : (sub : Sub Γ₁ Γ₂) → (T : Type Γ₁)
    → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
  lift sub T (γ , t) = sub γ , t

  subExp : (sub : Sub Γ₁ Γ₂)
    → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
  subExp sub e = λ γ₂ → e (sub γ₂)

\end{code}

POINTER - Sub in shallow embedding - with typecodes

\begin{code}

  Sub : Ctx → Ctx → Set
  Sub Γ₁ Γ₂ = Γ₂ → Γ₁

  extend : Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
  extend sub e γ₂ = sub γ₂ , e (sub γ₂)

  idSub : Sub Γ Γ
  idSub γ = γ

  weaken1Ren : Sub Γ (cons {n} Γ T)
  weaken1Ren = proj₁

  subType : Sub Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
  subType sub T = λ γ₂ → T (sub γ₂)

  lift : (sub : Sub Γ₁ Γ₂) → (T : Type n Γ₁)
    → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
  lift sub T (γ , t) = sub γ , t

  subExp : (sub : Sub Γ₁ Γ₂)
    → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
  subExp sub e = λ γ₂ → e (sub γ₂)

\end{code}
POINTER - Augmented Shallow Embedding with Type Codes
\begin{code}

-------------------- Augmented "shallow" embedding -----------------------------

data Context : S.Ctx → Set₁ where
  ∅ : Context S.nil
  _,_ : (ctx : Context SΓ) → (T : S.Type n SΓ) → Context (S.cons SΓ T)

data Var : ∀{n} → {SΓ : S.Ctx} → (Γ : Context SΓ) → (T : S.Type n SΓ)
  → S.Term SΓ T → Set₁ where
  same : Var {n} (Γ , T) (S.weakenT T T) (S.same T)
  next : Var (Γ , T) (S.weakenT T A) (S.next A T a)

data Exp : ∀{n} → {SΓ : S.Ctx} → (Γ : Context SΓ) → (T : S.Type n SΓ)
  → S.Term SΓ T → Set₁ where
  lambda : Exp (Γ , A) B a → Exp Γ (S.Π A B) (S.lambda a)
  var : (icx : Var Γ T a) → Exp Γ T a
  app : Exp Γ (S.Π A B) a₁ → (x : Exp Γ A a₂)
      → Exp Γ (λ γ → B (γ , a₂ γ)) (S.app A B a₁ a₂)
  Π : (A : Exp Γ S.U a)
    → (B : Exp (Γ , a) S.U b)
    → Exp Γ S.U(S.Π a b)
  U : Exp Γ (S.U {suc n}) (S.U {n})
  raise : Exp Γ T a → Exp Γ (S.cumuT T) (S.raise a)
  lower : Exp Γ (S.cumuT T) (S.raise T a) → Exp Γ T a
  cumuT : Exp Γ (S.U {n}) a → Exp Γ (S.U {suc n}) (S.cumuT a)

\end{code}

POINTER - Renamings and substitutions for Augmented shallow embeddings

\begin{code}

Ren : ∀{sΓ₁ sΓ₂} → S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
Ren sub Γ₁ Γ₂ = Var Γ₁ T t → Var Γ₂ (S.subType sub T) (S.subExp sub t)

idRen : Ren S.idSub Γ Γ
idRen x = x

lift : Ren sub Γ₁ Γ₂ → Ren (S.lift sub T) (Γ₁ , T) (Γ₂ , S.subType sub T)
lift ren same = same
lift ren (next x) = next (ren x)

weaken1Ren : Ren S.weaken1Ren Γ (Γ , T)
weaken1Ren = next

renExp : Ren sub Γ₁ Γ₂ → Exp Γ₁ T t → Exp Γ₂ (S.subType sub T) (S.subExp sub t)
renExp ren (lambda e) = lambda (renExp (lift ren) e)
renExp ren (var x) = var (ren x)
renExp ren (app e₁ e₂) = app (renExp ren e₁) (renExp ren e₂)
renExp ren (Π A B) = Π (renExp ren A) (renExp (lift ren) B)
renExp ren U = U
renExp ren (cumuT e) = cumuT (renExp ren e)
renExp ren (raise e) = raise (renExp ren e)
renExp ren (lower e) = lower (renExp ren e)

Sub : S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
Sub sub Γ₁ Γ₂ = Var Γ₁ T t → Exp Γ₂ (S.subType sub T) (S.subExp sub t)

idSub : Sub S.idSub Γ Γ
idSub x = var x

liftSub : Sub sub Γ₁ Γ₂ → Sub (S.lift sub) (Γ₁ , T) (Γ₂ , S.subType sub T)
liftSub sub same = var same
liftSub sub (next x) = renExp weaken1Ren (sub x)

subExp : Sub sub Γ₁ Γ₂ → Exp {n} Γ₁ T t → Exp Γ₂ (S.subType sub T) (S.subExp sub t)
subExp sub (lambda e) = lambda (subExp (liftSub sub) e)
subExp sub (var x) = sub x
subExp sub (app e₁ e₂) = app (subExp sub e₁) (subExp sub e₂)
subExp sub (Π A B) = Π (subExp sub A) (subExp (liftSub sub) B)
subExp sub U = U
subExp sub (cumuT e) = cumuT (subExp sub e)
subExp sub (raise e) = raise (subExp sub e)
subExp sub (lower e) = lower (subExp sub e)

extend : Sub sub Γ₁ Γ₂ → Exp Γ₁ T t → Sub (S.extend sub t) (Γ₁ , T) Γ₂
extend sub e same = subExp sub e
extend sub e (next x) = sub x

\end{code}
POINTER - maybeLamImpl
\begin{code}

--------------------------------------------------------------------------------

maybeLamImpl : ∀{n SΓ Γ T t} → Exp {suc n} {SΓ} Γ T t
  → Maybe (Σ (S.Type (suc n) SΓ)
          (λ A → Σ (S.Type (suc n) (S.cons SΓ A))
          (λ B → Σ (S.Term (S.cons SΓ A) B)
          (λ t' → Σ (_≡_ {_} {(γ : SΓ) → Σ (TypeCode (suc n)) ⟦_⟧}
            (λ γ → (T γ , t γ))
            (λ γ → ((S.Π A B) γ , λ a → t' (γ , a))))
          (λ p → Exp (Γ , A) B t')))))
maybeLamImpl (lambda e) = just (_ , _ , _ , refl , e)
maybeLamImpl _ = nothing

\end{code}
POINTER - lemma
\begin{code}

lemma : ((`Π A B) , t) ≡ ((`Π A' B') , t')
  → (A , B , t) ≡ (A' , B' , t')
lemma refl = refl

\end{code}
POINTER - theorem
\begin{code}

theorem :
  (λ γ → ((S.Π A B) γ , λ a → t (γ , a)))
  ≡ (λ γ → ((S.Π A' B') γ , λ a → t' (γ , a)))
  → (A , B , t) ≡ (A' , B' , t')
theorem p
   = cong (λ f → (proj₁ ∘ f , (λ (γ , a) → proj₁ (proj₂ (f γ)) a) , λ (γ , a) → proj₂ (proj₂ (f γ)) a))
      (funExt (λ γ → lemma (happly p γ)))

\end{code}
POINTER - maybeLam
\begin{code}

maybeLam : Exp Γ (S.Π A B) t
  → Maybe (Exp (Γ , A) B (λ (γ , a) → t γ a))
maybeLam e with maybeLamImpl e
... | nothing = nothing
... | just (A , B , t' , p , e') with (theorem p)
... | refl = just e'

\end{code}
POINTER - β-reduce
\begin{code}

βreduce : Exp Γ T t → Exp Γ T t
βreduce (lambda e) = lambda (βreduce e)
βreduce (var icx) = var icx
βreduce (Π A B) = Π (βreduce A) (βreduce B)
βreduce U = U
βreduce (raise e) = raise (βreduce e)
βreduce (lower e) = lower (βreduce e)
βreduce (cumuT e) = cumuT (βreduce e)
βreduce (app e₁ e₂) with maybeLam e₁
... | nothing = app (βreduce e₁) (βreduce e₂)
... | just e = subExp (extend idSub e₂) e

\end{code}
POINTER
\begin{code}

term1 : Exp {2} ∅ S.U S.U
term1 = app (lambda (var same)) U

test : βreduce term1 ≡ U
test = refl
\end{code}

Some examples for paper:

\begin{code}
e : Exp Γ (S.Π A B)
\end{code}

\begin{code}
maybeLam2 : Exp Γ (S.Π A B) t
  → Maybe (Exp (Γ , A) B (λ (γ , a) → t γ a))
\end{code}

\begin{code}
theorem2 :
  (λ γ → ((S.Π A B) γ , λ a → t (γ , a))) ≡ (λ γ → ((S.Π A' B') γ , λ a → t' (γ , a)))
  → (A , B , t) ≡ (A' , B' , t')
\end{code}

\begin{code}
maybeLam' : ∀{n SΓ Γ T t} → Exp {suc n} {SΓ} Γ T t
  → Maybe (Σ (S.Type (suc n) SΓ)
          (λ A → Σ (S.Type (suc n) (S.cons SΓ A))
          (λ B → Σ (S.Term (S.cons SΓ A) B)
          (λ t' → Σ (_≡_ {_} {(γ : SΓ) → Σ (TypeCode (suc n)) ⟦_⟧}
            (λ γ → (T γ , t γ))
            (λ γ → ((S.Π A B) γ , λ a → t' (γ , a))))
          (λ p → Exp (Γ , A) B t')))))
\end{code}
