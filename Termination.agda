module Termination where

open import Delay
open import Calculus

open import Data.Unit  public
  using (⊤)

--------------------------------------------------------------------------------
-- Termination proof
--------------------------------------------------------------------------------

V : ∀{Ψ Γ a} → Val Ψ Γ a       → Set
C : ∀{Ψ Γ a}   → Delay ∞ (Val Ψ Γ a) → Set

V                 (ne w)    = nereadback w ⇓
V {Ψ} {a = a ⇒ b} (lam t ρ) = ∀{Δ}(η : Δ ≤ _)(u : Val Ψ Δ a) → V u → C (eval t (env≤ η ρ , u))

C v?      = ∃ λ v → v? ⇓ v × V v

E          :  ∀{Ψ Δ Γ} → Env Ψ Δ Γ → Set
E ε        =  ⊤
E (ρ , v)  =  E ρ × V v

val≤-id  : ∀{Ψ Δ a}  (v : Val Ψ Δ a)     → val≤ id v ≡ v

env≤-id  : ∀{Ψ Γ Δ}  (ρ : Env Ψ Δ Γ)     → env≤ id ρ ≡ ρ

nev≤-id  : ∀{Ψ Δ a}  (t : Ne Val Ψ Δ a)  → nev≤ id t ≡ t

env≤-id ε         = refl
env≤-id (ρ , v)   = cong₂ _,_ (env≤-id ρ) (val≤-id v)

val≤-id (ne t) = cong ne (nev≤-id t)
val≤-id (lam t ρ) = cong (lam t) (env≤-id ρ)

nev≤-id (var x)   = refl
nev≤-id (con x)   = refl
nev≤-id (app  t u) = cong₂ app  (nev≤-id t) (val≤-id u)
nev≤-id (app■ t u) = cong₂ app■ (val≤-id t) (val≤-id u)

var≤-•  :  ∀{Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (x : Var Δ″ a) →
           var≤ η (var≤ η′ x) ≡ var≤ (η • η′) x

val≤-•  :  ∀{Ψ Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (v : Val Ψ Δ″ a) →
           val≤ η (val≤ η′ v) ≡ val≤ (η • η′) v

env≤-•  :  ∀{Ψ Γ Δ Δ′ Δ″} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (ρ : Env Ψ Δ″ Γ) →
           env≤ η (env≤ η′ ρ) ≡ env≤ (η • η′) ρ

nev≤-•  :  ∀{Ψ Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (t : Ne Val Ψ Δ″ a) →
           nev≤ η (nev≤ η′ t) ≡ nev≤ (η • η′) t

var≤-• id       η′        x       = refl
var≤-• (weak η) η′        x       = cong suc (var≤-• η η′ x)
var≤-• (lift η) id        x       = refl
var≤-• (lift η) (weak η′) x       = cong suc (var≤-• η η′ x)
var≤-• (lift η) (lift η′) zero    = refl
var≤-• (lift η) (lift η′) (suc x) = cong suc (var≤-• η η′ x)

env≤-• η η′ ε       = refl
env≤-• η η′ (ρ , v) = cong₂ _,_ (env≤-• η η′ ρ) (val≤-• η η′ v)

val≤-• η η′ (ne w) = cong ne (nev≤-• η η′ w)
val≤-• η η′ (lam t ρ) = cong (lam t) (env≤-• η η′ ρ)

nev≤-• η η′ (var x)    = cong var (var≤-• η η′ x)
nev≤-• η η′ (con x)    = refl
nev≤-• η η′ (app w v)  = cong₂ app  (nev≤-• η η′ w) (val≤-• η η′ v)
nev≤-• η η′ (app■ w v) = cong₂ app■ (val≤-• η η′ w) (val≤-• η η′ v)

lookup≤  :  ∀ {Ψ Γ Δ Δ′ a} (x : Var Γ a) (ρ : Env Ψ Δ Γ) (η : Δ′ ≤ Δ) →
            val≤ η (lookup x ρ) ≡ lookup x (env≤ η ρ)

eval≤    :  ∀ {i Ψ Γ Δ Δ′ a} (t : Tm Ψ Γ a) (ρ : Env Ψ Δ Γ) (η : Δ′ ≤ Δ) →
            (val≤ η <$> (eval t ρ)) ∼⟨ i ⟩∼ (eval t (env≤ η ρ))

apply≤   :  ∀{i Ψ Γ Δ a b} (f : Val Ψ Γ (a ⇒ b))(v : Val Ψ Γ a)(η : Δ ≤ Γ) →
            (val≤ η <$> apply f v) ∼⟨ i ⟩∼ (apply (val≤ η f) (val≤ η v))

beta≤    :  ∀ {i Ψ Γ Δ E a b} (t : Tm Ψ (Γ , a) b)(ρ : Env Ψ Δ Γ) (v : Val Ψ Δ a) (η : E ≤ Δ) →
            (val≤ η ∞<$> (beta t ρ v)) ∞∼⟨ i ⟩∼ beta t (env≤ η ρ) (val≤ η v)

lookup≤ zero    (ρ , v) η = refl
lookup≤ (suc x) (ρ , v) η = lookup≤ x ρ η

eval≤ (var x)   ρ η rewrite lookup≤ x ρ η = ∼now _
eval≤ (con x)   ρ η = ∼now _
eval≤ (abs t)   ρ η = ∼now _
eval≤ (app t u) ρ η =
  proof
  ((eval t ρ >>=
    (λ f → eval u ρ >>= (λ v → apply f v)))
      >>= (λ x′ → now (val≤ η x′)))
  ∼⟨ bind-assoc (eval t ρ) ⟩
  (eval t ρ >>=
    λ f → eval u ρ >>= (λ v → apply f v)
      >>= (λ x′ → now (val≤ η x′)))
  ∼⟨ bind-cong-r (eval t ρ) (λ t₁ → bind-assoc (eval u ρ)) ⟩
  (eval t ρ >>=
    λ f → eval u ρ >>= λ v → apply f v
      >>= (λ x′ → now (val≤ η x′)))
  ∼⟨ bind-cong-r (eval t ρ)
                 (λ t₁ → bind-cong-r (eval u ρ)
                                     (λ u₁ → apply≤ t₁ u₁ η )) ⟩
  (eval t ρ >>=
   λ x′ → eval u ρ >>= (λ x′′ → apply (val≤ η x′) (val≤ η x′′)))
  ≡⟨⟩
  (eval t ρ >>= λ x′ →
      (eval u ρ >>= λ x′′ → now (val≤ η x′′) >>=
        λ v → apply (val≤ η x′) v))
  ∼⟨ bind-cong-r (eval t ρ) (λ a → ∼sym (bind-assoc (eval u ρ))) ⟩
  (eval t ρ >>= λ x′ →
      (eval u ρ >>= λ x′′ → now (val≤ η x′′)) >>=
        (λ v → apply (val≤ η x′) v))
  ∼⟨ bind-cong-r (eval t ρ) (λ x′ → bind-cong-l  (eval≤ u ρ η) (λ _ → _)) ⟩
  (eval t ρ >>= λ x′ →
      eval u (env≤ η ρ) >>= (λ v → apply (val≤ η x′) v))
  ≡⟨⟩
  (eval t ρ >>= λ x′ → now (val≤ η x′) >>=
    (λ f → eval u (env≤ η ρ) >>= (λ v → apply f v)))
  ∼⟨ ∼sym (bind-assoc (eval t ρ)) ⟩
  ((eval t ρ >>= (λ x′ → now (val≤ η x′))) >>=
    (λ f → eval u (env≤ η ρ) >>= (λ v → apply f v)))
  ∼⟨ bind-cong-l (eval≤ t ρ η) (λ _ → _) ⟩
  (eval t (env≤ η ρ) >>=
    (λ f → eval u (env≤ η ρ) >>= (λ v → apply f v)))
  ∎
  where open ∼-Reasoning

apply≤ (ne x)    v η = ∼refl _
apply≤ (lam t ρ) v η = ∼later (beta≤ t ρ v η)

∼force (beta≤ t ρ v η) = eval≤ t (ρ , v) η

nereadback≤  :  ∀{i Ψ Γ Δ a}(η : Δ ≤ Γ)(t : Ne Val Ψ Γ a) →
                (nen≤ η <$> nereadback t) ∼⟨ i ⟩∼ (nereadback (nev≤ η t))

readback≤    :  ∀{i Ψ Γ Δ a}(η : Δ ≤ Γ)(v : Val Ψ Γ a) →
                (nf≤ η <$> readback v) ∼⟨ i ⟩∼ (readback (val≤ η v))

lamreadback≤  :  ∀{i Ψ Γ Γ₁ Δ a b} (η : Δ ≤ Γ) (t : Tm Ψ (Γ₁ , a) b) (ρ : Env Ψ Γ Γ₁) →
                 (nf≤ (lift η) ∞<$> lamreadback t ρ) ∞∼⟨ i ⟩∼ (lamreadback t (env≤ η ρ))

nereadback≤ η (var x)   = ∼now _
nereadback≤ η (con x)   = ∼now _
nereadback≤ η (app t u) =
  proof
  ((nereadback t >>=
    (λ t₁ → readback u >>= (λ n → now (app t₁ n))))
                                 >>= (λ x′ → now (nen≤ η x′)))
  ∼⟨ bind-assoc (nereadback t) ⟩
  (nereadback t >>= (λ x →
    (readback u >>= (λ n → now (app x n)))
                                 >>= (λ x′ → now (nen≤ η x′))))
  ∼⟨ bind-cong-r (nereadback t) (λ x → bind-assoc (readback u)) ⟩
  (nereadback t >>= (λ x →
     readback u >>= (λ y → now (app x y) >>= (λ x′ → now (nen≤ η x′)))))
  ≡⟨⟩
  (nereadback t >>=
    (λ x → (readback u >>= (λ y → now (app (nen≤ η x) (nf≤ η y))))))
  ≡⟨⟩
  (nereadback t >>=
         (λ x → (readback u >>= (λ x′ → now (nf≤ η x′) >>=
             (λ n → now (app (nen≤ η x) n))))))
  ∼⟨ bind-cong-r (nereadback t) (λ x → ∼sym (bind-assoc (readback u))) ⟩
  (nereadback t >>=
         (λ x → ((readback u >>= (λ x′ → now (nf≤ η x′))) >>=
             (λ n → now (app (nen≤ η x) n)))))
  ≡⟨⟩
  (nereadback t >>= (λ x → now (nen≤ η x) >>=
    (λ t₁ → ((readback u >>= (λ x′ → now (nf≤ η x′))) >>=
        (λ n → now (app t₁ n))))))
  ∼⟨ ∼sym (bind-assoc (nereadback t)) ⟩
  ((nereadback t >>= (λ x′ → now (nen≤ η x′))) >>=
    (λ t₁ → ((readback u >>= (λ x′ → now (nf≤ η x′))) >>=
        (λ n → now (app t₁ n)))))
  ≡⟨⟩
  (nen≤ η <$> nereadback t >>=
     (λ t₁ → nf≤ η <$> readback u >>= (λ n → now (app t₁ n))))
  ∼⟨ bind-cong-r (nen≤ η <$> nereadback t)
                 (λ x → bind-cong-l (readback≤ η u)
                                    (λ x → _)) ⟩
  (nen≤ η <$> nereadback t >>=
     (λ t₁ → readback (val≤ η u) >>= (λ n → now (app t₁ n))))
  ∼⟨  bind-cong-l (nereadback≤ η t) (λ x → _) ⟩
  (nereadback (nev≤ η t) >>=
     (λ t₁ → readback (val≤ η u) >>= (λ n → now (app t₁ n))))
  ∎
  where open ∼-Reasoning

-- I'll leave this proof for when the structure of the normal forms is
-- completely set.
nereadback≤ η (app■ t u) = {!!}

readback≤ η (ne w) =
  proof
  nf≤ η  <$>  (ne   <$> nereadback w)   ∼⟨ map-compose (nereadback w) ⟩
  (nf≤ η ∘ ne)      <$> nereadback w     ≡⟨⟩
  (Nf.ne ∘ nen≤ η)  <$> nereadback w     ∼⟨ ∼sym (map-compose (nereadback w)) ⟩
  ne <$>  (nen≤ η   <$> nereadback w)    ∼⟨ map-cong ne (nereadback≤ η w) ⟩
  ne <$>   nereadback (nev≤ η w)
  ∎
  where open ∼-Reasoning

readback≤ η (lam t ρ) = ∼later (
  proof
    ((lamreadback t ρ ∞>>= (λ a → now (lam a))) ∞>>= (λ x' → now (nf≤ η x')))
    ∞∼⟨ ∞bind-assoc (lamreadback t ρ) ⟩
    (lamreadback t ρ ∞>>= λ a → now (lam a) >>= (λ x' → now (nf≤ η x')))
    ≡⟨⟩
    (lamreadback t ρ ∞>>= λ a → now (lam (nf≤ (lift η) a)))
    ≡⟨⟩
    (lamreadback t ρ ∞>>= λ x' → now (nf≤ (lift η) x') >>= λ a → now (lam a))
    ∞∼⟨ ∞∼sym (∞bind-assoc (lamreadback t ρ)) ⟩
    ((lamreadback t ρ ∞>>= λ x' → now (nf≤ (lift η) x')) ∞>>= λ a → now (lam a))
    ∞∼⟨ ∞bind-cong-l (lamreadback≤ η t ρ) (λ a → now (lam a)) ⟩
    (lamreadback t (env≤ η ρ) ∞>>= (λ a → now (lam a)))
  ∎)
  where open ∞∼-Reasoning

∼force (lamreadback≤ η t ρ) =
  proof
    ((eval t (env≤ (weak id) ρ , ne (var zero)) >>= readback) >>= (λ a → now (nf≤ (lift η) a)))
    ∼⟨ bind-assoc (eval t (env≤ (weak id) ρ , ne (var zero))) ⟩
    (eval t (env≤ (weak id) ρ , ne (var zero)) >>= λ x → readback x >>= λ a → now (nf≤ (lift η) a))
    ∼⟨ bind-cong-r (eval t (env≤ (weak id) ρ , ne (var zero))) (λ a → readback≤ (lift η) a)⟩
    (eval t (env≤ (weak id) ρ , ne (var zero)) >>= λ x → readback (val≤ (lift η) x))
    ≡⟨⟩
    (eval t (env≤ (weak id) ρ , ne (var zero)) >>= λ x → now (val≤ (lift η) x) >>= readback)
    ∼⟨ ∼sym (bind-assoc (eval t (env≤ (weak id) ρ , ne (var zero)))) ⟩
    ((eval t (env≤ (weak id) ρ , ne (var zero)) >>= λ x → now (val≤ (lift η) x)) >>= readback)
    ∼⟨ bind-cong-l (eval≤ t (env≤ (weak id) ρ , ne (var zero)) (lift η)) readback ⟩
    (eval t (env≤ (lift η) (env≤ (weak id) ρ , ne (var zero))) >>= readback)
    ≡⟨⟩
    (eval t ((env≤ (lift η) (env≤ (weak id) ρ) , val≤ (lift η) (ne (var zero)))) >>= readback)
    ≡⟨ cong (λ x → eval t (x , val≤ (lift η) (ne (var zero))) >>= readback) (env≤-• (lift η) (weak id) ρ) ⟩
    (eval t ((env≤ (lift η • weak id) ρ , val≤ (lift η) (ne (var zero)))) >>= readback)
    ≡⟨⟩
    (eval t ((env≤ (weak (η • id)) ρ , val≤ (lift η) (ne (var zero)))) >>= readback)
    ≡⟨ cong (λ x → eval t (env≤ (weak x) ρ , val≤ (lift η) (ne (var zero))) >>= readback) (η•id η) ⟩
    (eval t ((env≤ (weak η) ρ , val≤ (lift η) (ne (var zero)))) >>= readback)
    ≡⟨⟩
    (eval t ((env≤ (weak id • η) ρ , val≤ (lift η) (ne (var zero)))) >>= readback)
    ≡⟨ cong (λ x → eval t (x , val≤ (lift η) (ne (var zero))) >>= readback) (sym (env≤-• (weak id) η ρ)) ⟩
    (eval t ((env≤ (weak id) (env≤ η ρ) , val≤ (lift η) (ne (var zero)))) >>= readback)
    ≡⟨⟩
    (eval t (env≤ (weak id) (env≤ η ρ) , ne (var zero)) >>= readback)
  ∎
  where open ∼-Reasoning

nereadback≤⇓  :  ∀{Ψ Γ Δ a} (η : Δ ≤ Γ) (t : Ne Val Ψ Γ a) {n : Ne Nf Ψ Γ a} →
                 nereadback t ⇓ n → nereadback (nev≤ η t) ⇓ nen≤ η n

V≤          :  ∀{Ψ Δ Δ′ a}  (η : Δ′ ≤ Δ)  (v : Val Ψ Δ a)  → V v  → V (val≤ η v)
E≤          :  ∀{Ψ Γ Δ Δ′}  (η : Δ′ ≤ Δ)  (ρ : Env Ψ Δ Γ)  → E ρ  → E (env≤ η ρ)

nereadback≤⇓ η t {n} p = subst∼⇓ (map⇓ (nen≤ η) p) (nereadback≤ η t)

V≤ η (ne w) (w' , w⇓w') = nen≤ η w' , nereadback≤⇓ η w w⇓w'
V≤ η (lam t ρ) p   η₁ u u⇓ =
  let v , v⇓ , Vv = p (η₁ • η) u u⇓
  in   v
     , subst (λ x → eval t (x , u) ⇓ fst (p (η₁ • η) u u⇓)) (sym (env≤-• η₁ η ρ)) v⇓
     , Vv

E≤ η ε       θ        = _
E≤ η (ρ , v) (θ , ⟦v⟧) = E≤ η ρ θ , V≤ η v ⟦v⟧

reify : ∀{Ψ Γ a} (v : Val Ψ Γ a) → V v → readback v ⇓
reify (ne w) (w/nf , nereadbackW⇓) = ne w/nf , map⇓ ne nereadbackW⇓
reify (lam t ρ) ⟦f⟧ =
  let
    u   = ne (var zero)
    ⟦u⟧ = var zero , now⇓
    v , v⇓ , ⟦v⟧ = ⟦f⟧ wk u ⟦u⟧
    n , ⇓n = reify v ⟦v⟧
    ⇓λn = later⇓ (bind⇓ (λ x → now (lam x)) (bind⇓ readback v⇓ ⇓n) now⇓)
  in lam n , ⇓λn

⟦var⟧ : ∀{Ψ Δ Γ a} (x : Var Γ a) (ρ : Env Ψ Δ Γ) → E ρ → C (now (lookup x ρ))
⟦var⟧ zero    (_ , v)  (_ , v⇓)  = v , now⇓ , v⇓
⟦var⟧(suc x)  (ρ , _)  (θ , _ )  = ⟦var⟧ x ρ θ

⟦con⟧ : ∀{Ψ Δ Γ a} (x : Var Ψ a) (ρ : Env Ψ Δ Γ) → E ρ → C {Γ = Δ} (now (ne (con x)))
⟦con⟧ x ρ θ  =  ne (con x) , now⇓ , con x , now⇓

⟦abs⟧    :  ∀ {Ψ Δ Γ a b} (t : Tm Ψ (Γ , a) b) (ρ : Env Ψ Δ Γ) (θ : E ρ) →
            (∀{Δ′}(η : Δ′ ≤ Δ)(u : Val Ψ Δ′ a)(u⇓ : V u)
            → C (eval t (env≤ η ρ , u)))
            → C (now (lam t ρ))
⟦abs⟧ t ρ θ ih = lam t ρ , now⇓ , ih

⟦app⟧  :  ∀{Ψ Δ a b} {f? : Delay _ (Val Ψ Δ (a ⇒ b))} {u? : Delay _ (Val Ψ Δ a)} →
          C f? → C u? → C (f? >>= λ f → u? >>= apply f)
⟦app⟧ {f? = w?} {u? = u?} (ne w , w⇓ , rw , rw⇓) (u , u⇓ , ⟦u⟧) =
  let wu⇓ = bind⇓ (λ f → u? >>= (apply f))
                  w⇓
                  (bind⇓ (λ v₂ → now (ne (app w v₂))) u⇓ now⇓)
      ru , ru⇓ = reify u ⟦u⟧
      wuC = app rw ru , bind⇓ (λ m → app m <$> readback u)
                              rw⇓
                              (map⇓ (app rw) ru⇓)
  in ne (app w u) , wu⇓ , wuC

⟦app⟧ {u? = u?} (lam t ρ , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) =
  let v , v⇓ , ⟦v⟧ = ⟦f⟧ id u ⟦u⟧
      v⇓ = bind⇓ (λ f′ → _>>=_ u? (apply f′))
                 f⇓
                 (bind⇓ (λ v₁ → later (beta t ρ v₁))
                        u⇓
                        (later⇓ (subst (λ x → eval t (x , u) ⇓ fst (⟦f⟧ id u ⟦u⟧))
                                       (env≤-id ρ)
                                       v⇓ )))
  in  v , v⇓ , ⟦v⟧

term                 :  ∀ {Ψ Δ Γ a} (t : Tm Ψ Γ a) (ρ : Env Ψ Δ Γ) (θ : E ρ) → C (eval t ρ)
term (var x)    ρ θ  =  ⟦var⟧ x ρ θ
term (con x)    ρ θ  =  ⟦con⟧ x ρ θ
term (abs t)    ρ θ  =  ⟦abs⟧ t ρ θ (λ η u p → term t (env≤ η ρ , u) (E≤ η ρ θ , p))
term (app t u)  ρ θ  =  ⟦app⟧ (term t ρ θ) (term u ρ θ)

⟦ide⟧          :  ∀ Ψ Γ → E (ide Ψ Γ)
⟦ide⟧ Ψ ε        =  _
⟦ide⟧ Ψ (Γ , a)  =  E≤ wk (ide Ψ Γ) (⟦ide⟧ Ψ Γ) , var zero , now⇓

normalize        :  ∀{a}(Ψ Γ : Cxt)(t : Tm Ψ Γ a) → ∃ λ n → nf t ⇓ n
normalize Ψ Γ t = let  v , v⇓ , ⟦v⟧ = term t (ide Ψ Γ) (⟦ide⟧ Ψ Γ)
                       n , ⇓n       = reify v ⟦v⟧
                  in   n , bind⇓ readback v⇓ ⇓n
