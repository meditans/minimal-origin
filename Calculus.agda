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

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var  : ∀{a}    (x : Var Γ a)                    → Tm Γ a
  abs  : ∀{a b}  (t : Tm (Γ , a) b)               → Tm Γ (a ⇒ b)
  app  : ∀{a b}  (t : Tm Γ (a ⇒ b)) (u : Tm Γ a)  → Tm Γ b


data Ne (Ξ : Cxt → Ty → Set)(Γ : Cxt) : Ty → Set where
  var  : ∀{a}    → Var Γ a                 → Ne Ξ Γ a
  app  : ∀{a b}  → Ne Ξ Γ (a ⇒ b) → Ξ Γ a  → Ne Ξ Γ b

mutual
  data Val (Δ : Cxt) : (a : Ty) → Set where
    ne   : ∀{a}      (w : Ne Val Δ a)                  → Val Δ a
    lam  : ∀{Γ a b}  (t : Tm (Γ , a) b) (ρ : Env Δ Γ)  → Val Δ (a ⇒ b)

  data Env (Δ : Cxt) : (Γ : Cxt) → Set where
    ε    :                                        Env Δ ε
    _,_  : ∀ {Γ a} (ρ : Env Δ Γ) (v : Val Δ a) →  Env Δ (Γ , a)

lookup                   :  ∀ {Γ Δ a} → Var Γ a → Env Δ Γ → Val Δ a
lookup zero     (ρ , v)  =  v
lookup (suc x)  (ρ , v)  =  lookup x ρ

eval   :  ∀{i Γ Δ b}    → Tm Γ b         → Env Δ Γ             → Delay i (Val Δ b)
apply  :  ∀{i Δ a b}    → Val Δ (a ⇒ b)             → Val Δ a  → Delay i (Val Δ b)
beta   :  ∀{i Γ Δ a b}  → Tm (Γ , a) b   → Env Δ Γ  → Val Δ a  → ∞Delay i (Val Δ b)

eval (var x) e     = now (lookup x e)
eval (abs t) e     = now (lam t e)
eval (app t₁ t₂) e = eval t₁ e >>= λ v₁ → eval t₂ e >>= λ v₂ → apply v₁ v₂

apply (ne n) v₂   = now (ne (app n v₂))
apply (lam t ρ) v = later (beta t ρ v)

force (beta t ρ v) = eval t (ρ , v)

data Nf (Γ : Cxt) : Ty → Set where
  lam  : ∀{a b}  (n  : Nf (Γ , a) b)  → Nf Γ (a ⇒ b)
  ne   : ∀{a}    (m  : Ne Nf Γ a)     → Nf Γ a

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

var≤  : ∀{Γ Δ} → Γ ≤ Δ → ∀{a}  → Var Δ a     → Var Γ a
val≤  : ∀{Γ Δ} → Γ ≤ Δ → ∀{a}  → Val Δ a     → Val Γ a
env≤  : ∀{Γ Δ} → Γ ≤ Δ → ∀{E}  → Env Δ E     → Env Γ E
nev≤  : ∀{Γ Δ} → Γ ≤ Δ → ∀{a}  → Ne Val Δ a  → Ne Val Γ a
nf≤   : ∀{Γ Δ} → Γ ≤ Δ → ∀{a}  → Nf Δ a      → Nf Γ a
nen≤  : ∀{Γ Δ} → Γ ≤ Δ → ∀{a}  → Ne Nf Δ a   → Ne Nf Γ a

var≤ id        x      = x
var≤ (weak η)  x      = suc (var≤ η x)
var≤ (lift η)  zero   = zero
var≤ (lift η) (suc x) = suc (var≤ η x)

val≤ η (ne w)     = ne (nev≤ η w)
val≤ η (lam t ρ)  = lam t (env≤ η ρ)

env≤ η ε       = ε
env≤ η (ρ , v) = env≤ η ρ , val≤ η v

nev≤ η (var x)   = var (var≤ η x)
nev≤ η (app w v) = app (nev≤ η w) (val≤ η v)

nf≤ η (ne m)   = ne (nen≤ η m)
nf≤ η (lam n)  = lam (nf≤ (lift η) n)

nen≤ η (var x)   = var (var≤ η x)
nen≤ η (app m n) = app (nen≤ η m) (nf≤ η n)

wk       :  ∀{Γ a} → (Γ , a) ≤ Γ
wk       =  weak id

weakVal : ∀{Δ a c} → Val Δ c → Val (Δ , a) c
weakVal  =  val≤ wk

readback    : ∀{i Γ a}      → Val Γ a                  →  Delay i (Nf Γ a)
nereadback  : ∀{i Γ a}      → Ne Val Γ a               →  Delay i (Ne Nf Γ a)
lamreadback : ∀{i Γ Γ₁ a b} → Tm (Γ₁ , a) b → Env Γ Γ₁ → ∞Delay i (Nf (Γ , a) b)

readback (ne w)    = ne  <$> nereadback w
readback (lam t ρ) = lam <$> later (lamreadback t ρ)

nereadback (var x)       = now (var x)
nereadback (app w v)     = nereadback w >>= λ m → app m <$> readback v

force (lamreadback t ρ)  = readback =<< eval t (env≤ wk ρ , ne (var zero))

ide          :  ∀ Γ → Env Γ Γ
ide ε        =  ε
ide (Γ , a)  =  env≤ wk (ide Γ) , ne (var zero)

nf        :  ∀{Γ a}(t : Tm Γ a) → Delay ∞ (Nf Γ a)
nf {Γ} t  =  eval t (ide Γ) >>= readback

