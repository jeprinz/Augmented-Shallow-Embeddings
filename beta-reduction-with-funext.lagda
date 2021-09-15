\begin{code}
{-# OPTIONS --without-K #-}
{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Unit
open import Data.Nat
open import Data.Maybe
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Agda.Primitive
open import Function
\end{code}

----------------------------- Function Extentionality --------------------------

In order to implement function extentionality, I use two postulates and a
rewrite rule. This gives the necessary computation for this particular purpose.

I have also turned off Axiom-K, just to ensure compatibility with any potential
type theory with computational univalence.


\begin{code}
postulate
  funExt : ∀{l} {A B : Set l} {f g : A → B}
     → ((x : A) → f x ≡ g x) → f ≡ g
  funExtElim : ∀{l} {A B : Set l} {f : A → B}
     → funExt {l} {A} {B} {f} {f} (λ x → refl) ≡ refl

{-# REWRITE funExtElim #-}

happly : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
            → f ≡ g → ((x : A) → f x ≡ g x)
happly refl x = refl

data TypeCode₀ : Set where
⟦_⟧₀ : TypeCode₀ → Set
⟦_⟧₀ ()

\end{code}

--------------------------------------------------------------------------------

\begin{code}
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
module Sᵀ where

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

  U : ∀{n Γ} → Type (suc n) Γ
  U = λ _ → `U

  Π : ∀{n Γ} → (A : Type (suc n) Γ) → Type (suc n) (cons Γ A) → Type (suc n) Γ
  Π A B = λ γ → `Π (A γ) ((λ a → B (γ , a)))

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

  idSub : ∀{Γ} → Sub Γ Γ
  idSub γ = γ

  weaken1Ren : ∀{Γ n T} → Sub Γ (cons {n} Γ T)
  weaken1Ren = proj₁

  subType : ∀{Γ₁ Γ₂ n} → Sub Γ₁ Γ₂ → Type n Γ₁ → Type n Γ₂
  subType sub T = λ γ₂ → T (sub γ₂)

  lift : ∀{Γ₁ Γ₂ n} → (sub : Sub Γ₁ Γ₂) → (T : Type n Γ₁)
    → Sub (cons Γ₁ T) (cons Γ₂ (subType sub T))
  lift sub T (γ , t) = sub γ , t

  subExp : ∀{Γ₁ Γ₂ n} → (T : Type n Γ₁) → (sub : Sub Γ₁ Γ₂)
    → Term Γ₁ T → Term Γ₂ (subType {_} {_} {n} sub T)
  subExp T sub e = λ γ₂ → e (sub γ₂)

-------------------- Augmented "shallow" embedding -----------------------------

data Context : Sᵀ.Ctx → Set₁ where
  ∅ : Context Sᵀ.nil
  _,_ : ∀{n SΓ} → (ctx : Context SΓ) → (T : Sᵀ.Type n SΓ) → Context (Sᵀ.cons SΓ T)

data Var : ∀{n} → {SΓ : Sᵀ.Ctx} → (Γ : Context SΓ) → (T : Sᵀ.Type n SΓ)
  → Sᵀ.Term SΓ T → Set₁ where
  same : ∀{n SΓ} → {T : Sᵀ.Type n SΓ} → {Γ : Context SΓ}
    → Var {n} (Γ , T) (Sᵀ.weakenT T T) (Sᵀ.same T)
  next : ∀{n m SΓ Γ A a} → {T : Sᵀ.Type n SΓ} → Var {m} {SΓ} Γ A a
    → Var (Γ , T) (Sᵀ.weakenT T A) (Sᵀ.next A T a)

data Exp : ∀{n} → {SΓ : Sᵀ.Ctx} → (Γ : Context SΓ) → (T : Sᵀ.Type n SΓ)
  → Sᵀ.Term SΓ T → Set₁ where
  lambda : ∀{n SΓ} → {Γ : Context SΓ} → {A : Sᵀ.Type (suc n) SΓ}
    → {B : Sᵀ.Type (suc n) (Sᵀ.cons SΓ A)} → ∀{a}
    → Exp (Γ , A) B a → Exp Γ (Sᵀ.Π A B) (Sᵀ.lambda {n} {SΓ} {A} {B} a)
  var : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ}
    → {a : Sᵀ.Term SΓ T} → (icx : Var Γ T a) → Exp {n} {SΓ} Γ T a
  app : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {A : Sᵀ.Type (suc n) SΓ}
      → {B : Sᵀ.Type (suc n) (Sᵀ.cons SΓ A)} → ∀{a₁ a₂}
      → Exp {suc n} Γ (Sᵀ.Π A B) a₁ → (x : Exp {suc n} Γ A a₂)
      → Exp {suc n} Γ (λ γ → B (γ , a₂ γ)) (Sᵀ.app A B a₁ a₂)
  Π : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {a₁ : Sᵀ.Term SΓ (Sᵀ.U {suc n})}
    → {a₂ : Sᵀ.Type (suc n) (Sᵀ.cons SΓ a₁)} → (A : Exp Γ (Sᵀ.U {suc n}) a₁)
    → (B : Exp (Γ , a₁) (Sᵀ.U {suc n}) a₂)
    → Exp Γ (Sᵀ.U {suc n}) (Sᵀ.Π {n} a₁ a₂)
  U : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → Exp {suc (suc n)} {SΓ} Γ Sᵀ.U Sᵀ.U
  -- Eweaken : ∀{n} → {SΓ : Ctx} → {Γ : Context SΓ} → {T : Type n SΓ}
    -- → {A : Type n SΓ} → ∀{a}
    -- → Exp Γ T a → Exp (Γ , A) (λ γ → (T (proj₁ γ))) (Sweaken {_} {_} {T} {A} a)
  raise : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ} → ∀{a}
    → Exp Γ T a → Exp Γ (Sᵀ.cumuT T) (Sᵀ.raise T a)
  lower : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → {T : Sᵀ.Type n SΓ} → ∀{a}
    → Exp Γ (Sᵀ.cumuT T) (Sᵀ.raise T a) → Exp Γ T a
  cumuT : ∀{n} → {SΓ : Sᵀ.Ctx} → {Γ : Context SΓ} → ∀{a}
    → Exp Γ (Sᵀ.U {n}) a → Exp Γ (Sᵀ.U {suc n}) (Sᵀ.cumuT a)

  -- Renamings and Substitutions on Exp

Ren : ∀{sΓ₁ sΓ₂} → Sᵀ.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
Ren sub Γ₁ Γ₂ = ∀{n T t} → Var {n} Γ₁ T t → Var Γ₂ (Sᵀ.subType sub T) (Sᵀ.subExp T sub t)

idRen : ∀{sΓ Γ} → Ren {sΓ} Sᵀ.idSub Γ Γ
idRen x = x

lift : ∀{n sΓ₁ sΓ₂ T} → {sub : Sᵀ.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₁ Γ₂ → Ren (Sᵀ.lift {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , Sᵀ.subType sub T)
lift ren same = same
lift ren (next x) = next (ren x)

weaken1Ren : ∀{sΓ Γ n T} → Ren {sΓ} (Sᵀ.weaken1Ren {sΓ} {n} {T}) Γ (Γ , T)
weaken1Ren = next

renExp : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sᵀ.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Ren sub Γ₁ Γ₂ → Exp {n} Γ₁ T t → Exp Γ₂ (Sᵀ.subType sub T) (Sᵀ.subExp T sub t)
renExp ren (lambda e) = lambda (renExp (lift ren) e)
renExp ren (var x) = var (ren x)
renExp ren (app e₁ e₂) = app (renExp ren e₁) (renExp ren e₂)
renExp ren (Π A B) = Π (renExp ren A) (renExp (lift ren) B)
renExp ren U = U
renExp ren (cumuT e) = cumuT (renExp ren e)
renExp ren (raise e) = raise (renExp ren e)
renExp ren (lower e) = lower (renExp ren e)

Sub : ∀{sΓ₁ sΓ₂} → Sᵀ.Sub sΓ₁ sΓ₂ → Context sΓ₁ → Context sΓ₂ → Set₁
Sub sub Γ₁ Γ₂ = ∀{n T t} → Var {n} Γ₁ T t → Exp Γ₂ (Sᵀ.subType sub T) (Sᵀ.subExp T sub t)

idSub : ∀{sΓ Γ} → Sub {sΓ} Sᵀ.idSub Γ Γ
idSub x = var x

liftSub : ∀{n sΓ₁ sΓ₂ T} → {sub : Sᵀ.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₁ Γ₂ → Sub (Sᵀ.lift {_} {_} {n} sub T) (Γ₁ , T) (Γ₂ , Sᵀ.subType sub T)
liftSub sub same = var same
liftSub sub (next x) = renExp weaken1Ren (sub x)

subExp : ∀{n sΓ₁ sΓ₂ T t} → {sub : Sᵀ.Sub sΓ₁ sΓ₂} → {Γ₁ : Context sΓ₁} → {Γ₂ : Context sΓ₂}
  → Sub sub Γ₁ Γ₂ → Exp {n} Γ₁ T t → Exp Γ₂ (Sᵀ.subType sub T) (Sᵀ.subExp T sub t)
subExp sub (lambda e) = lambda (subExp (liftSub sub) e)
subExp sub (var x) = sub x
subExp sub (app e₁ e₂) = app (subExp sub e₁) (subExp sub e₂)
subExp sub (Π A B) = Π (subExp sub A) (subExp (liftSub sub) B)
subExp sub U = U
subExp sub (cumuT e) = cumuT (subExp sub e)
subExp sub (raise e) = raise (subExp sub e)
subExp sub (lower e) = lower (subExp sub e)

extend : ∀{sΓ₁ sΓ₂ n Γ₁ Γ₂ sub} → {T : Sᵀ.Type n sΓ₁} → {t : Sᵀ.Term sΓ₁ T}
  → Sub {sΓ₁} {sΓ₂} sub Γ₁ Γ₂
  → Exp Γ₁ T t → Sub (Sᵀ.extend T sub t) (Γ₁ , T) Γ₂
extend sub e same = subExp sub e
extend sub e (next x) = sub x

--------------------------------------------------------------------------------

Eq2 : {l : Level} {P : Set l} {Q : P → Set l}
  → (a₁ a₂ : P) → Q a₁ → Q a₂ → Set l
Eq2 {l} {P} {Q} a₁ a₂ b₁ b₂
  = _≡_ {l} {Σ P Q} (a₁ , b₁) (a₂ , b₂)

-- The propositional equality type, specialized to triples for convenience
Eq3 : {l : Level} {P : Set l} {Q : P → Set l} {R : (p : P) → Q p → Set l}
  → (a₁ a₂ : P) → (b₁ : Q a₁) → (b₂ : Q a₂) → R a₁ b₁ → R a₂ b₂ → Set l
Eq3 {l} {P} {Q} {R} a₁ a₂ b₁ b₂ c₁ c₂
  = _≡_ {l} {Σ P (λ a → Σ (Q a) (R a))} (a₁ , b₁ , c₁) (a₂ , b₂ , c₂)

maybeLamImpl : ∀{n SΓ Γ T t} → Exp {suc n} {SΓ} Γ T t
  → Maybe (Σ (Sᵀ.Type (suc n) SΓ)
          (λ A → Σ (Sᵀ.Type (suc n) (Sᵀ.cons SΓ A))
          (λ B → Σ (Sᵀ.Term (Sᵀ.cons SΓ A) B)
          (λ t' → Σ (_≡_ {_} {(γ : SΓ) → Σ (TypeCode (suc n)) ⟦_⟧}
            (λ γ → (T γ , t γ))
            (λ γ → ((Sᵀ.Π A B) γ , λ a → t' (γ , a))))
          (λ p → Exp (Γ , A) B t')))))
maybeLamImpl (lambda e) = just (_ , _ , _ , refl , e)
maybeLamImpl _ = nothing

lemma : ∀{n} → {A A' : TypeCode (suc n)} → {B : ⟦ A ⟧ → TypeCode (suc n)}
  → {B' : ⟦ A' ⟧ → TypeCode (suc n)}
  → {t : ⟦ `Π A B ⟧} → {t' : ⟦ `Π A' B' ⟧ }
  → (_≡_ {_} {Σ (TypeCode (suc n)) ⟦_⟧}
      ((`Π A B) , t)
      ((`Π A' B') , t'))
  → Eq3 A A' B B' t t'
lemma refl = refl

theorem : ∀{n Γ} → {A A' : Sᵀ.Type (suc n) Γ}
  → {B : Sᵀ.Type (suc n) (Sᵀ.cons Γ A)}
  → {B' : Sᵀ.Type (suc n) (Sᵀ.cons Γ A')}
  → {t : Sᵀ.Term (Sᵀ.cons Γ A) B}
  → {t' : Sᵀ.Term (Sᵀ.cons Γ A') B'}
  → _≡_ {_} {(γ : Γ) → Σ (TypeCode (suc n)) ⟦_⟧}
      (λ γ → ((Sᵀ.Π A B) γ , λ a → t (γ , a)))
      (λ γ → ((Sᵀ.Π A' B') γ , λ a → t' (γ , a)))
  → Eq3 A A' B B' t t'
theorem p
   -- = cong (λ f → {!   !} )
      -- (funExt (λ γ → lemma (happly p γ)))
  = {! funExt  !}
   -- = cong (λ f → (proj₁ ∘ f , (λ (γ , a) → proj₁ (proj₂ (f γ)) a) , λ (γ , a) → proj₂ (proj₂ (f γ)) a))
      -- (funExt (λ γ → lemma (happly p γ)))

{-
maybeLam : ∀{n SΓ Γ A B t} → Exp {suc n} {SΓ} Γ (Sᵀ.Π A B) t
  → Maybe (Exp (Γ , A) B (λ (γ , a) → t γ a))
maybeLam {n} {SΓ} {Γ} e with maybeLamImpl e
... | nothing = nothing
... | just (A , B , t' , p , e') with (theorem p)
... | refl = just e'

βreduce : ∀{n sΓ Γ T t} → Exp {n} {sΓ} Γ T t → Exp {n} {sΓ} Γ T t
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

term1 : Exp {2} ∅ Sᵀ.U Sᵀ.U
term1 = app (lambda (var same)) U
-- (λ x . x) U

-- (λ x . x) U  =  U
test : βreduce term1 ≡ U
test = refl

-}

{-
NOTE: the presence of funext implies some wierd things with shallow embeddings.
e.g., take the context Γ = {ℕ, String, ⊥}.
This context cannot be instantiated, so I call it uninstantiable.

Any two types or terms in an uninstantiable context are equal by function extentionality.
Therefore, any combination of constructors for an Exp type can be validly put
together in an uninstantiable context.


-}
\end{code}
