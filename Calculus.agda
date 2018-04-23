module Calculus where


open import Delay

open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

--------------------------------------------------------------------------------
-- The calculus
--------------------------------------------------------------------------------
infixr 6 _⇒_

data Ty  : Set where
  ★      : Ty
  _⇒_    : (a b : Ty) →  Ty

data Cxt  : Set where
  ε       : Cxt
  _,_     : (Γ : Cxt) (a : Ty) →  Cxt

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero  : ∀{Γ a}                  → Var (Γ , a) a
  suc   : ∀{Γ a b} (x : Var Γ a)  → Var (Γ , b) a

data Tm (Ψ Γ : Cxt) : (a : Ty) → Set where
  var  : ∀{a}    (x : Var Γ a)                        → Tm Ψ Γ a
  con  : ∀{a}    (x : Var Ψ a)                        → Tm Ψ Γ a
  abs  : ∀{a b}  (t : Tm Ψ (Γ , a) b)                 → Tm Ψ Γ (a ⇒ b)
  app  : ∀{a b}  (t : Tm Ψ Γ (a ⇒ b)) (u : Tm Ψ Γ a)  → Tm Ψ Γ b

data Ne (Ξ : Cxt → Cxt → Ty → Set)(Ψ Γ : Cxt) : Ty → Set where
  var  : ∀{a}    → Var Γ a                     → Ne Ξ Ψ Γ a
  con  : ∀{a}    → Var Ψ a                     → Ne Ξ Ψ Γ a
  app  : ∀{a b}  → Ne Ξ Ψ Γ (a ⇒ b) → Ξ Ψ Γ a  → Ne Ξ Ψ Γ b
  app■ : ∀{a b}  → Ξ Ψ Γ (a ⇒ b)    → Ξ Ψ Γ a  → Ne Ξ Ψ Γ b

mutual
  data Val (Ψ Δ : Cxt) : (a : Ty) → Set where
    ne   : ∀{a}      (w : Ne Val Ψ Δ a)                    → Val Ψ Δ a
    lam  : ∀{Γ a b}  (t : Tm Ψ (Γ , a) b) (ρ : Env Ψ Δ Γ)  → Val Ψ Δ (a ⇒ b)

  data Env (Ψ Δ : Cxt) : (Γ : Cxt) → Set where
    ε    :                                            Env Ψ Δ ε
    _,_  : ∀ {Γ a} (ρ : Env Ψ Δ Γ) (v : Val Ψ Δ a) →  Env Ψ Δ (Γ , a)

lookup                   :  ∀ {Ψ Γ Δ a} → Var Γ a → Env Ψ Δ Γ → Val Ψ Δ a
lookup zero     (ρ , v)  =  v
lookup (suc x)  (ρ , v)  =  lookup x ρ

eval   :  ∀{i Ψ Γ Δ b}    → Tm Ψ Γ b         → Env Ψ Δ Γ               → Delay i (Val Ψ Δ b)
apply  :  ∀{i Ψ Δ a b}    → Val Ψ Δ (a ⇒ b)               → Val Ψ Δ a  → Delay i (Val Ψ Δ b)
beta   :  ∀{i Ψ Γ Δ a b}  → Tm Ψ (Γ , a) b   → Env Ψ Δ Γ  → Val Ψ Δ a  → ∞Delay i (Val Ψ Δ b)

eval (var x) e     = now (lookup x e)
eval (con x) e     = now (ne (con x))
eval (abs t) e     = now (lam t e)
eval (app t₁ t₂) e = eval t₁ e >>= λ v₁ → eval t₂ e >>= λ v₂ → apply v₁ v₂

apply (ne n) v₂   = now (ne (app n v₂))
apply (lam t ρ) v = later (beta t ρ v)

force (beta t ρ v) = eval t (ρ , v)

data Nf (Ψ Γ : Cxt) : Ty → Set where
  lam  : ∀{a b}  (n  : Nf Ψ (Γ , a) b)  → Nf Ψ Γ (a ⇒ b)
  ne   : ∀{a}    (m  : Ne Nf Ψ Γ a)     → Nf Ψ Γ a

data _≤_ : (Γ Δ : Cxt) → Set where
  id    : ∀{Γ}              → Γ ≤ Γ
  weak  : ∀{Γ Δ a} → Γ ≤ Δ  → (Γ , a) ≤ Δ
  lift  : ∀{Γ Δ a} → Γ ≤ Δ  → (Γ , a) ≤ (Δ , a)

_•_                :  ∀ {Γ Δ Δ′} (η : Γ ≤ Δ) (η′ : Δ ≤ Δ′) → Γ ≤ Δ′
id      • η′       =  η′
weak η  • η′       =  weak  (η • η′)
lift η  • id       =  lift  η
lift η  • weak η′  =  weak  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

η•id               :  ∀ {Γ Δ} (η : Γ ≤ Δ) → η • id ≡ η
η•id id       = refl
η•id (weak η) = cong weak (η•id η)
η•id (lift η) = refl

var≤  : ∀{Γ Δ}   → Γ ≤ Δ → ∀{a}  → Var Δ a       → Var Γ a
val≤  : ∀{Ψ Γ Δ} → Γ ≤ Δ → ∀{a}  → Val Ψ Δ a     → Val Ψ Γ a
env≤  : ∀{Ψ Γ Δ} → Γ ≤ Δ → ∀{E}  → Env Ψ Δ E     → Env Ψ Γ E
nev≤  : ∀{Ψ Γ Δ} → Γ ≤ Δ → ∀{a}  → Ne Val Ψ Δ a  → Ne Val Ψ Γ a
nf≤   : ∀{Ψ Γ Δ} → Γ ≤ Δ → ∀{a}  → Nf Ψ Δ a      → Nf Ψ Γ a
nen≤  : ∀{Ψ Γ Δ} → Γ ≤ Δ → ∀{a}  → Ne Nf Ψ Δ a   → Ne Nf Ψ Γ a

var≤ id        x      = x
var≤ (weak η)  x      = suc (var≤ η x)
var≤ (lift η)  zero   = zero
var≤ (lift η) (suc x) = suc (var≤ η x)

val≤ η (ne w)     = ne (nev≤ η w)
val≤ η (lam t ρ)  = lam t (env≤ η ρ)

env≤ η ε       = ε
env≤ η (ρ , v) = env≤ η ρ , val≤ η v

nev≤ η (var x)    = var (var≤ η x)
nev≤ η (con x)    = con x
nev≤ η (app  w v) = app  (nev≤ η w) (val≤ η v)
nev≤ η (app■ w v) = app■ (val≤ η w) (val≤ η v)

nf≤ η (ne m)   = ne (nen≤ η m)
nf≤ η (lam n)  = lam (nf≤ (lift η) n)

nen≤ η (var x)    = var (var≤ η x)
nen≤ η (con x)    = con x
nen≤ η (app  m n)  = app  (nen≤ η m) (nf≤ η n)
nen≤ η (app■ m n)  = app■ (nf≤ η m)  (nf≤ η n)

wk       :  ∀{Γ a} → (Γ , a) ≤ Γ
wk       =  weak id

weakVal : ∀{Ψ Δ a c} → Val Ψ Δ c → Val Ψ (Δ , a) c
weakVal  =  val≤ wk

readback    : ∀{i Ψ Γ a}      → Val Ψ Γ a                    →  Delay i (Nf Ψ Γ a)
nereadback  : ∀{i Ψ Γ a}      → Ne Val Ψ Γ a                 →  Delay i (Ne Nf Ψ Γ a)
lamreadback : ∀{i Ψ Γ Γ₁ a b} → Tm Ψ (Γ₁ , a) b → Env Ψ Γ Γ₁ → ∞Delay i (Nf Ψ (Γ , a) b)

readback (ne w)    = ne  <$> nereadback w
readback (lam t ρ) = lam <$> later (lamreadback t ρ)

nereadback (var x)       = now (var x)
nereadback (con x)       = now (con x)
nereadback (app  w v)    = nereadback w >>= λ m  → app m <$> readback v
nereadback (app■ w v)    = readback w   >>= λ nw → app■ nw <$> readback v

force (lamreadback t ρ)  = readback =<< eval t (env≤ wk ρ , ne (var zero))

ide            :  ∀ Ψ Γ → Env Ψ Γ Γ
ide Ψ ε        =  ε
ide Ψ (Γ , a)  =  env≤ wk (ide Ψ Γ) , ne (var zero)

nf            :  ∀{Ψ Γ a}(t : Tm Ψ Γ a) → Delay ∞ (Nf Ψ Γ a)
nf {Ψ} {Γ} t  =  eval t (ide Ψ Γ) >>= readback
