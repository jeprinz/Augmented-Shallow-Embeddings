\begin{code}

open import variables
open import Data.Nat
open import Data.Product
open import Data.Maybe

\end{code}

POINTER - function extentionality

\begin{code}

postulate
  funExt : ((x : A) → f x ≡ g x) → f ≡ g
  funExtElim : funExt (λ x → refl) ≡ refl

{-# REWRITE funExtElim #-}

happly : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
            → f ≡ g → ((x : A) → f x ≡ g x)
happly refl x = refl

\end{code}

POINTER - new typecodes

\begin{code}
mutual
  data TypeCode : ℕ → Set where
    `U : TypeCode (suc n)
    `Π : (A : TypeCode n)
      → (⟦ A ⟧ → TypeCode n) → TypeCode n
    `raise : TypeCode n → TypeCode (suc n)

  ⟦_⟧ : TypeCode n → Set
  ⟦ `U ⟧ = TypeCode n
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `raise T ⟧ = ⟦ T ⟧
\end{code}

POINTER - TypeCode -old

\begin{code}
--
-- data TypeCode₀ : Set where
-- ⟦_⟧₀ : TypeCode₀ → Set
-- ⟦_⟧₀ ()
--
-- module Universe {TypeCode : Set} {⟦_⟧ : TypeCode → Set} where
--   mutual
--     data TypeCodeₙ₊₁ : Set where
--         `U : TypeCodeₙ₊₁
--         `Π : (A : TypeCodeₙ₊₁) → (⟦_⟧ₙ₊₁ A → TypeCodeₙ₊₁) → TypeCodeₙ₊₁
--         `raise : TypeCode → TypeCodeₙ₊₁
--
--     ⟦_⟧ₙ₊₁ : TypeCodeₙ₊₁ → Set
--     ⟦ `U ⟧ₙ₊₁ = TypeCode
--     ⟦ `Π A B ⟧ₙ₊₁ = (a : ⟦ A ⟧ₙ₊₁) → ⟦ B a ⟧ₙ₊₁
--     ⟦ `raise T ⟧ₙ₊₁ = ⟦ T ⟧
--
-- open Universe
--
-- mutual
--   TypeCode : ℕ → Set
--   TypeCode zero = TypeCode₀
--   TypeCode (suc n) = TypeCodeₙ₊₁ {TypeCode n} {⟦_⟧}
--
--   ⟦_⟧ : {n : ℕ} → TypeCode n → Set
--   ⟦_⟧ {zero} T = ⟦ T ⟧₀
--   ⟦_⟧ {suc n} T = ⟦ T ⟧ₙ₊₁
--
\end{code}

------------------------  "Shallow" embedding   --------------------------------

POINTER

\begin{code}
module S where
\end{code}

POINTER - shallow embedding with typecodes

\begin{AgdaSuppressSpace}
\begin{code}
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

  Π : (A : Type (suc n) Γ)
    → Type (suc n) (cons Γ A) → Type (suc n) Γ
  Π A B = λ γ → `Π (A γ) ((λ a → B (γ , a)))
\end{code}
\end{AgdaSuppressSpace}

POINTER - Sub in shallow embedding - no typecodes

\begin{code}

  {-
  Sub : Ctx → Ctx → Set
  Sub Γ₁ Γ₂ = Γ₂ → Γ₁

  extend : Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
  extend sub e γ₂ = sub γ₂ , e (sub γ₂)

  subType : Sub Γ₁ Γ₂ → Type Γ₁ → Type Γ₂
  subType sub T =   λ γ₂ → T (sub γ₂)

  lift : (sub : Sub Γ₁ Γ₂) → (T : Type Γ₁)
    → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
  lift sub T (γ , t) = sub γ , t

  subTerm : (sub : Sub Γ₁ Γ₂)
    → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
  subTerm sub e = λ γ₂ → e (sub γ₂)
  -}

\end{code}

POINTER - parts of shallow embedding with typecodes not included in paper:

\begin{code}
  lambda : ∀{n Γ} → {A : Type (suc n) Γ} → {B : Type (suc n) (cons Γ A)}
    → Term (cons Γ A) B → Term Γ (Π A B)
  lambda e = λ γ → λ a → e (γ , a)

  app : ∀{n Γ} → (A : Type (suc n) Γ) → (B : Type (suc n) (cons Γ A))
    → Term Γ (Π A B) → (e₂ : Term Γ A) → Term Γ (λ γ → B (γ , e₂ γ))
  app A B e₁ e₂ = λ γ → (e₁ γ) (e₂ γ)

  weakenT : ∀{n m Γ} → (T : Type m Γ) → Type n Γ → Type n (cons Γ T)
  weakenT T A (γ , _) = A γ

  same : ∀{n Γ} → (T : Type n Γ) → Var {n} (cons Γ T) (weakenT T T)
  same T = λ (γ , t) → t
  next : ∀{n m Γ} → (A : Type n Γ) → (T : Type m Γ)
    → Var {n} Γ A → Var {n} (cons Γ T) (weakenT T A)
  next A T x = λ (γ , t) → x γ

  weaken : ∀{n Γ} → {T A : Type n Γ} → Term Γ T
    → Term (cons Γ A) (weakenT A T)
  weaken e = λ γ → e (proj₁ γ)

  cumuT : ∀{n Γ} → (T : Type n Γ) → Type (suc n) Γ
  cumuT T = λ γ → `raise (T γ)

  raise : ∀{n Γ} → (T : Type n Γ) → Term Γ T → Term Γ (cumuT T)
  raise T e = e

  Sub : Ctx → Ctx → Set
  Sub Γ₁ Γ₂ = Γ₂ → Γ₁

  extend : ∀{n Γ₁ Γ₂} → (T : Type n Γ₁)
    → Sub Γ₁ Γ₂ → Term Γ₁ T → Sub (cons Γ₁ T) Γ₂
  extend T sub e γ₂ = sub γ₂ , e (sub γ₂)

  -- idSub : ∀{Γ} → Sub Γ Γ
  -- idSub γ = γ

  weaken1Ren : ∀{Γ n T} → Sub Γ (cons {n} Γ T)
  weaken1Ren = proj₁

  subType : ∀{Γ₁ Γ₂ n} → Sub Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
  subType sub T = λ γ₂ → T (sub γ₂)

  lift : ∀{Γ₁ Γ₂ n} → (sub : Sub Γ₁ Γ₂) → (T : Type n Γ₁)
    → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
  lift sub T (γ , t) = sub γ , t

  subTerm : ∀{Γ₁ Γ₂ n} → (T : Type n Γ₁) → (sub : Sub Γ₁ Γ₂)
    → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
  subTerm T sub e = λ γ₂ → e (sub γ₂)
\end{code}

POINTER - Augmented Shallow Embedding with Type Codes - parts included in paper

\begin{code}
data Context : S.Ctx → Set
data Var : ∀{n} → {SΓ : S.Ctx} → (Γ : Context SΓ)
  → (T : S.Type n SΓ) → S.Term SΓ T → Set
data Term : ∀{n} → {SΓ : S.Ctx} → (Γ : Context SΓ)
  → (T : S.Type n SΓ) → S.Term SΓ T → Set
\end{code}

POINTER - Augmented Shallow Embedding with Type Codes - parts not included in paper
\begin{code}

-------------------- Augmented "shallow" embedding -----------------------------

data Context where
  ∅ : Context S.nil
  _,_ : (ctx : Context SΓ) → (T : S.Type n SΓ) → Context (S.cons SΓ T)

data Var where
  same : Var (Γ , T) (T ∘ proj₁) (S.same T)
  next : Var Γ A a
    → Var (Γ , T) (A ∘ proj₁) (a ∘ proj₁)

data Term where
  lambda : Term (Γ , A) B a → Term Γ (S.Π A B) (S.lambda a)
  var : (icx : Var Γ T a) → Term Γ T a
  app : Term Γ (S.Π A B) a₁ → (x : Term Γ A a₂)
      → Term Γ (λ γ → B (γ , a₂ γ)) (S.app A B a₁ a₂)
  Π : (A : Term Γ S.U a)
    → (B : Term (Γ , a) S.U b)
    → Term Γ S.U(S.Π a b)
  U : Term Γ (S.U {suc n}) (S.U {n})
  raise : Term Γ T a → Term Γ (S.cumuT T) (S.raise a)
  lower : Term Γ (S.cumuT T) (S.raise T a) → Term Γ T a
  cumuT : Term Γ (S.U {n}) a → Term Γ (S.U {suc n}) (S.cumuT a)

\end{code}

POINTER - Renamings for augmented shallow

\begin{code}

Ren : S.Sub sΓ₁ sΓ₂ → Context sΓ₁
  → Context sΓ₂ → Set₁
Ren sub Γ₁ Γ₂ = Var Γ₁ T t
  → Var Γ₂ (S.subType sub T) (S.subTerm sub t)

lift : Ren sub Γ₁ Γ₂
  → Ren (S.lift sub T) (Γ₁ , T) (Γ₂ , S.subType sub T)

renTerm : Ren sub Γ₁ Γ₂ → Term Γ₁ T t
  → Term Γ₂ (S.subType sub T) (S.subTerm sub t)
renTerm ren (lambda e) = lambda (renTerm (lift ren) e)
renTerm ren (var x) = var (ren x)
renTerm ren (app e₁ e₂)
  = app (renTerm ren e₁) (renTerm ren e₂)
renTerm ren (Π A B)
  = Π (renTerm ren A) (renTerm (lift ren) B)
renTerm ren U = U

\end{code}

POINTER - sub for aug shal

\begin{code}
Sub : S.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
Sub sub Γ₁ Γ₂ = Var Γ₁ T t
  → Term Γ₂ (S.subType sub T) (S.subTerm sub t)

liftSub : Sub sub Γ₁ Γ₂
  → Sub (S.lift sub) (Γ₁ , T) (Γ₂ , S.subType sub T)
liftSub sub same = var same
liftSub sub (next x) = renTerm next (sub x)

subTerm : Sub sub Γ₁ Γ₂ → Term Γ₁ T t
  → Term Γ₂ (S.subType sub T) (S.subTerm sub t)
subTerm sub (lambda e) = lambda (subTerm (liftSub sub) e)
subTerm sub (var x) = sub x
subTerm sub (app e₁ e₂)
  = app (subTerm sub e₁) (subTerm sub e₂)
subTerm sub (Π A B)
  = Π (subTerm sub A) (subTerm (liftSub sub) B)
subTerm sub U = U
\end{code}

POINTER - extend

\begin{code}
extend : Sub sub Γ₁ Γ₂ → Term Γ₁ T t
  → Sub (S.extend sub t) (Γ₁ , T) Γ₂
extend sub e same = subTerm sub e
extend sub e (next x) = sub x
\end{code}

POINTER - maybeLamImpl (remember to delete ᵀs before putting in latex)
\begin{code}
maybeLamImpl : Term Γ T t
  → Maybe (Σ (S.Type (suc n) SΓ)
          (λ A → Σ (S.Type (suc n) (S.cons SΓ A))
          (λ B → Σ (S.Term (S.cons SΓ A) B)
          (λ t' → Σ ((λ γ → (T γ , t γ)) ≡
            (λ γ → ((S.Π A B) γ , λ a → t' (γ , a))))
          (λ p → Term (Γ , A) B t')))))
maybeLamImpl (lambda e) = just (_ , _ , _ , refl , e)
maybeLamImpl _ = nothing
\end{code}

POINTER - lemma

\begin{code}

lemma : ((`Π A B) , t) ≡ ((`Π A' B') , t')
  → (A , B , t) ≡ (A' , B' , t')
lemma refl = refl

\end{code}

POINTER - theorem statement

\begin{code}
theorem :
  (λ γ → ((S.Π A B) γ , λ a → t (γ , a)))
  ≡ (λ γ → ((S.Π A' B') γ , λ a → t' (γ , a)))
  → (A , B , t) ≡ (A' , B' , t')
\end{code}

POINTER - theorem definition

\begin{code}
theorem p
   = cong
      (λ f
          → (proj₁ ∘ f
            , (λ (γ , a) → proj₁ (proj₂ (f γ)) a)
            , λ (γ , a) → proj₂ (proj₂ (f γ)) a))
      (funExt (λ γ → lemma (happly p γ)))
\end{code}

POINTER - term in proof of theorem

\begin{code}
piece :
  (λ z → (A z , (λ a → B (z , a)) , (λ a → t (z , a))))
  ≡ (λ z → (A' z , (λ a → B' (z , a)) , (λ a → t' (z , a))))
piece = funExt  (λ γ → lemma (happly p γ))
\end{code}

POINTER - maybeLam

\begin{code}

maybeLam : Term Γ (S.Π A B) t
  → Maybe (Term (Γ , A) B (λ (γ , a) → t γ a))
maybeLam e with maybeLamImpl e
... | nothing = nothing
... | just (A , B , t' , p , e') with (theorem p)
... | refl = just e'

\end{code}

POINTER - β-reduce

\begin{code}
βreduce : Term Γ T t → Term Γ T t
βreduce (lambda e) = lambda (βreduce e)
βreduce (var x) = var x
βreduce (Π A B) = Π (βreduce A) (βreduce B)
βreduce U = U
βreduce (app e₁ e₂) = ?
\end{code}

POINTER - app case of βreduce

\begin{code}
-- βreduce (app e₁ e₂) with maybeLam e₁
-- ... | nothing = app (βreduce e₁) (βreduce e₂)
-- ... | just e = subTerm (extend idSub e₂) e
\end{code}

POINTER

\begin{code}

term1 : Term {2} ∅ S.U S.U
term1 = app (lambda (var same)) U

test : βreduce term1 ≡ U
test = refl
\end{code}

Some examples for paper:

\begin{code}
e : Term Γ (S.Π A B)
\end{code}

\begin{code}
maybeLam2 : Term Γ (S.Π A B) t
  → Maybe (Term (Γ , A) B (λ (γ , a) → t γ a))
\end{code}

\begin{code}
theorem2 :
  (λ γ → ((S.Π A B) γ , λ a → t (γ , a))) ≡ (λ γ → ((S.Π A' B') γ , λ a → t' (γ , a)))
  → (A , B , t) ≡ (A' , B' , t')
\end{code}

\begin{code}
maybeLam' : ∀{n SΓ Γ T t} → Term {suc n} {SΓ} Γ T t
  → Maybe (Σ (S.Type (suc n) SΓ)
          (λ A → Σ (S.Type (suc n) (S.cons SΓ A))
          (λ B → Σ (S.Term (S.cons SΓ A) B)
          (λ t' → Σ (_≡_ {_} {(γ : SΓ) → Σ (TypeCode (suc n)) ⟦_⟧}
            (λ γ → (T γ , t γ))
            (λ γ → ((S.Π A B) γ , λ a → t' (γ , a))))
          (λ p → Term (Γ , A) B t')))))
\end{code}
