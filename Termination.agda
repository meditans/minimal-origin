module Termination where

open import Delay
open import Calculus

open import Data.Unit  public
  using (⊤)

--------------------------------------------------------------------------------
-- Termination proof
--------------------------------------------------------------------------------

V⟦_⟧_  : ∀{Γ} (a : Ty) → Val Γ a            → Set
C⟦_⟧_  : ∀{Γ} (a : Ty) → Delay ∞ (Val Γ a)  → Set

V⟦ t ⟧     ne w    = nereadback w ⇓
V⟦ a ⇒ b ⟧ lam t ρ = ∀{Δ}(η : Δ ≤ _)(u : Val Δ a) → V⟦ a ⟧ u → C⟦ b ⟧ (apply (val≤ η (lam t ρ)) u)

C⟦ a ⟧      v?      = ∃ λ v → v? ⇓ v × V⟦ a ⟧ v

E⟦_⟧_                :  ∀{Δ}(Γ : Cxt) → Env Δ Γ → Set
E⟦ ε ⟧      ε        =  ⊤
E⟦ Γ , a ⟧  (ρ , v)  =  E⟦ Γ ⟧ ρ × V⟦ a ⟧ v

val≤-id  : ∀{Δ a}  (v : Val Δ a)     → val≤ id v ≡ v

env≤-id  : ∀{Γ Δ}  (ρ : Env Δ Γ)     → env≤ id ρ ≡ ρ

nev≤-id  : ∀{Δ a}  (t : Ne Val Δ a)  → nev≤ id t ≡ t

env≤-id ε         = refl
env≤-id (ρ , v)   = cong₂ _,_ (env≤-id ρ) (val≤-id v)

val≤-id (ne t) = cong ne (nev≤-id t)
val≤-id (lam t ρ) = cong (lam t) (env≤-id ρ)

nev≤-id (var x)   = refl
nev≤-id (app t u) = cong₂ app (nev≤-id t) (val≤-id u)

var≤-•  :  ∀{Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (x : Var Δ″ a) →
           var≤ η (var≤ η′ x) ≡ var≤ (η • η′) x

val≤-•  :  ∀{Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (v : Val Δ″ a) →
           val≤ η (val≤ η′ v) ≡ val≤ (η • η′) v

env≤-•  :  ∀{Γ Δ Δ′ Δ″} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (ρ : Env Δ″ Γ) →
           env≤ η (env≤ η′ ρ) ≡ env≤ (η • η′) ρ

nev≤-•  :  ∀{Δ Δ′ Δ″ a} (η : Δ ≤ Δ′) (η′ : Δ′ ≤ Δ″) (t : Ne Val Δ″ a) →
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

nev≤-• η η′ (var x)   = cong var (var≤-• η η′ x)
nev≤-• η η′ (app w v) = cong₂ app (nev≤-• η η′ w) (val≤-• η η′ v)

lookup≤  :  ∀ {Γ Δ Δ′ a} (x : Var Γ a) (ρ : Env Δ Γ) (η : Δ′ ≤ Δ) →
            val≤ η (lookup x ρ) ≡ lookup x (env≤ η ρ)

eval≤    :  ∀ {i Γ Δ Δ′ a} (t : Tm Γ a) (ρ : Env Δ Γ) (η : Δ′ ≤ Δ) →
            (val≤ η <$> (eval t ρ)) ∼⟨ i ⟩∼ (eval t (env≤ η ρ))

apply≤   :  ∀{i Γ Δ a b} (f : Val Γ (a ⇒ b))(v : Val Γ a)(η : Δ ≤ Γ) →
            (val≤ η <$> apply f v) ∼⟨ i ⟩∼ (apply (val≤ η f) (val≤ η v))

beta≤    :  ∀ {i Γ Δ E a b} (t : Tm (Γ , a) b)(ρ : Env Δ Γ) (v : Val Δ a) (η : E ≤ Δ) →
            (val≤ η ∞<$> (beta t ρ v)) ∞∼⟨ i ⟩∼ beta t (env≤ η ρ) (val≤ η v)

lookup≤ zero     (ρ , v) η = refl
lookup≤ (suc x)  (ρ , v) η = lookup≤ x ρ η

eval≤ (var x)   ρ η rewrite lookup≤ x ρ η = ∼now _
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

nereadback≤  :  ∀{i Γ Δ a}(η : Δ ≤ Γ)(t : Ne Val Γ a) →
                (nen≤ η <$> nereadback t) ∼⟨ i ⟩∼ (nereadback (nev≤ η t))

readback≤    :  ∀{i Γ Δ a}(η : Δ ≤ Γ)(v : Val Γ a) →
                (nf≤ η <$> readback v) ∼⟨ i ⟩∼ (readback (val≤ η v))

lamreadback≤  :  ∀{i Γ Γ₁ Δ a b} (η : Δ ≤ Γ) (t : Tm (Γ₁ , a) b) (ρ : Env Γ Γ₁) →
                 (nf≤ (lift η) ∞<$> lamreadback t ρ) ∞∼⟨ i ⟩∼ (lamreadback t (env≤ η ρ))


nereadback≤ η (var x)   = ∼now _
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

nereadback≤⇓  :  ∀{Γ Δ a} (η : Δ ≤ Γ) (t : Ne Val Γ a) {n : Ne Nf Γ a} →
                 nereadback t ⇓ n → nereadback (nev≤ η t) ⇓ nen≤ η n

V⟦⟧≤          :  ∀{Δ Δ′} a  (η : Δ′ ≤ Δ)  (v : Val Δ a)  → V⟦ a ⟧ v  → V⟦ a ⟧ (val≤ η v)
E⟦⟧≤          :  ∀{Γ Δ Δ′}  (η : Δ′ ≤ Δ)  (ρ : Env Δ Γ)  → E⟦ Γ ⟧ ρ  → E⟦ Γ ⟧ (env≤ η ρ)

nereadback≤⇓ η t {n} p = subst∼⇓ (map⇓ (nen≤ η) p) (nereadback≤ η t)

V⟦⟧≤ t η (ne w) (w' , w⇓w') = nen≤ η w' , nereadback≤⇓ η w w⇓w'
V⟦⟧≤ (a ⇒ b) η (lam t ρ) p   η₁ u u⇓ =
  let v′ , p′ , p′′ = p (η₁ • η) u u⇓ in
    v′
  , subst (λ f → apply f u ⇓ fst (p (η₁ • η) u u⇓))
    ((sym (val≤-• η₁ η (lam t ρ)))) p′
  , p′′

E⟦⟧≤ η ε       θ        = _
E⟦⟧≤ η (ρ , v) (θ , ⟦v⟧) = E⟦⟧≤ η ρ θ , V⟦⟧≤ _ η v ⟦v⟧

⟦var⟧ : ∀{Δ Γ a} (x : Var Γ a) (ρ : Env Δ Γ) → E⟦ Γ ⟧ ρ → C⟦ a ⟧ (now (lookup x ρ))
⟦var⟧ zero    (_ , v)  (_ , v⇓)  = v , now⇓ , v⇓
⟦var⟧(suc x)  (ρ , _)  (θ , _ )  = ⟦var⟧ x ρ θ

sound-β  :  ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (u : Val Δ a) →
            C⟦ b ⟧ (eval t  (ρ , u)) → C⟦ b ⟧ (apply (lam t ρ) u)
sound-β t ρ u (v , v⇓ , ⟦v⟧) = v , later⇓ v⇓ , ⟦v⟧

⟦abs⟧    :  ∀ {Δ Γ a b} (t : Tm (Γ , a) b) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) →
            (∀{Δ′}(η : Δ′ ≤ Δ)(u : Val Δ′ a)(u⇓ : V⟦ a ⟧ u)
            → C⟦ b ⟧ (eval t (env≤ η ρ , u)))
            → C⟦ a ⇒ b ⟧ (now (lam t ρ))
⟦abs⟧ t ρ θ ih =  lam t ρ , now⇓ , (λ η u p → sound-β t (env≤ η ρ) u (ih η u p))

⟦app⟧  :  ∀{Δ a b} {f? : Delay _ (Val Δ (a ⇒ b))} {u? : Delay _ (Val Δ a)} →
          C⟦ a ⇒ b ⟧ f? → C⟦ a ⟧ u? → C⟦ b ⟧ (f? >>= λ f → u? >>= apply f)
⟦app⟧ {u? = u?} (ne w , w⇓ , rw , rw⇓) (ne u , u⇓ , ru , ru⇓) =
  let wu⇓ = bind⇓ (λ f → u? >>= apply f)
                  w⇓
                  (bind⇓ (λ v₂ → now (ne (app w v₂))) u⇓ now⇓)
      wuC = app rw (ne ru) , bind⇓ (λ m → app m <$> (ne <$> nereadback u))
                                   rw⇓
                                   (bind⇓ (λ x' → now (app rw x'))
                                          (bind⇓ (λ x' → now (ne x')) ru⇓ now⇓)
                                          now⇓)
  in  ne (app w (ne u)) , wu⇓ , wuC

⟦app⟧ {f? = w?} {u? = f?} (ne w , w⇓ , rw , rw⇓) (lam t ρ , f⇓ , ⟦f⟧) =
  let wf⇓ = bind⇓ (λ f → f? >>= apply f)
                  w⇓
                  (bind⇓ (λ v₂ → now (ne (app w v₂))) f⇓ now⇓)
      wfC = (app rw {!!}) , {!!}
  in ne (app w (lam t ρ)) , wf⇓ , wfC

⟦app⟧ {u? = u?} (lam t ρ , f⇓ , ⟦f⟧) (u , u⇓ , ⟦u⟧) =
  let  v , v⇓ , ⟦v⟧  =  ⟦f⟧ id u ⟦u⟧
       v⇓′           =  bind⇓  (λ f′ → u? >>= apply f′)
                               f⇓
                               (bind⇓  (apply (lam t ρ))
                                       u⇓
                                       (subst  (λ f′ → apply f′ u ⇓ v)
                                               (val≤-id (lam t ρ))
                                               v⇓))
  in   v , v⇓′ , ⟦v⟧

term                 :  ∀ {Δ Γ a} (t : Tm Γ a) (ρ : Env Δ Γ) (θ : E⟦ Γ ⟧ ρ) → C⟦ a ⟧ (eval t ρ)
term (var x)    ρ θ  =  ⟦var⟧ x ρ θ
term (abs t)    ρ θ  =  ⟦abs⟧ t ρ θ (λ η u p → term t (env≤ η ρ , u) (E⟦⟧≤ η ρ θ , p))
term (app t u)  ρ θ  =  ⟦app⟧ (term t ρ θ) (term u ρ θ)

-- mutual

--   reify : ∀{Γ} a (v : Val Γ a) → V⟦ a ⟧ v → readback v ⇓
--   reify = {!!}
--   -- reify ★        (ne _)  (m , ⇓m)  = ne m , map⇓ ne ⇓m
--   -- reify (a ⇒ b)  f       ⟦f⟧       =
--   --   let u             = ne (var zero)
--   --       ⟦u⟧           = reflect a (var zero) (var zero , now⇓)
--   --       v , v⇓ , ⟦v⟧  = ⟦f⟧ wk u ⟦u⟧
--   --       n , ⇓n        = reify b v ⟦v⟧
--   --       ⇓λn           = later⇓ (bind⇓  (λ x → now (lam x))
--   --         (bind⇓ readback v⇓ ⇓n)
--   --         now⇓)
--   --         in  lam n , ⇓λn

--   reflect : ∀{Γ} a (w : Ne Val Γ a) → nereadback w ⇓ → V⟦ a ⟧ (ne w)
--   reflect = {!!}
--   -- reflect ★        w  w⇓                 = w⇓
--   -- reflect (a ⇒ b)  w  (m , w⇓m) η u ⟦u⟧  =
--   --   let  n , ⇓n  = reify a u ⟦u⟧
--   --        m′      = nen≤ η m
--   --        ⇓m      = nereadback≤⇓ η w w⇓m
--   --        wu      = app (nev≤ η w) u
--   --        ⟦wu⟧    = reflect b wu  (app m′ n ,
--   --          bind⇓  (λ m → app m <$> readback u)
--   --          ⇓m
--   --          (bind⇓ (λ n → now (app m′ n)) ⇓n now⇓))
--   --          in   ne wu , now⇓ , ⟦wu⟧

-- var↑           :  ∀{Γ a}(x : Var Γ a) → V⟦ a ⟧ ne (var x)
-- var↑ x         =  reflect _ (var x) (var x , now⇓)

-- ⟦ide⟧          :  ∀ Γ → E⟦ Γ ⟧ (ide Γ)
-- ⟦ide⟧ ε        =  _
-- ⟦ide⟧ (Γ , a)  =  E⟦⟧≤ wk (ide Γ) (⟦ide⟧ Γ) , var↑ zero

-- normalize        :  ∀ Γ a (t : Tm Γ a) → ∃ λ n → nf t ⇓ n
-- normalize Γ a t  =  let  v , v⇓ , ⟦v⟧  = term t (ide Γ) (⟦ide⟧ Γ)
--                          n , ⇓n        = reify a v ⟦v⟧
--                     in   n , bind⇓ readback v⇓ ⇓n
