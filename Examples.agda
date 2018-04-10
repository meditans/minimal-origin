module Examples where

open import Delay
open import Calculus
open import Termination

-- Ovvero (λx.x)z
ex₁ : Tm (ε , ★) ★
ex₁ = app (abs (var zero)) (var zero)

-- Dovrebbe essere ne (var zero)
-- ne (var zero) , later⇓ now⇓
nex₁ : ∃ λ n → nf ex₁ ⇓ n
nex₁ = normalize (ε , ★) ★ ex₁

-- -- Ovvero λx.(λy.x)z
ex₂ : Tm (ε , ★) (★ ⇒ ★)
ex₂ = abs (app (abs (var (suc zero))) (var zero))

-- lam (ne (var zero)) , later⇓ (later⇓ (later⇓ now⇓))
nex₂ : ∃ λ n → nf ex₂ ⇓ n
nex₂ = normalize (ε , ★) (★ ⇒ ★) ex₂

-- Ovvero (λx.(λy.xy))z
ex₃ : Tm (ε , ★ ⇒ ★) (★ ⇒ ★)
ex₃ = app (abs (abs (app (var (suc zero)) (var zero)))) (var zero)

-- lam (ne (app (var (suc zero)) (ne (var zero)))) , later⇓ (later⇓ (later⇓ now⇓))
nex₃ : ∃ λ n → nf ex₃ ⇓ n
nex₃ = normalize (ε , ★ ⇒ ★) (★ ⇒ ★) ex₃

-- Come ex₂, ma l'applicazione e' al livello superiore
-- quindi (λx.(λy.x))z
ex₄ : Tm (ε , ★) (★ ⇒ ★)
ex₄ = app (abs (abs (var (suc zero)))) (var zero)

-- lam (ne (var (suc zero))) , later⇓ (later⇓ (later⇓ now⇓))
nex₄ : ∃ λ n → nf ex₄ ⇓ n
nex₄ = normalize (ε , ★) (★ ⇒ ★) ex₄

-- Test per vedere se il caso con in hsubst funziona
-- quindi (λx.(λy.z))w
ex₅ : Tm ((ε , ★) , ★) (★ ⇒ ★)
ex₅ = app (abs (abs (var zero))) (var (suc zero))

-- lam (ne (var zero)) , later⇓ (later⇓ (later⇓ now⇓))
nex₅ : ∃ λ n → nf ex₅ ⇓ n
nex₅ = normalize ((ε , ★) , ★) (★ ⇒ ★) ex₅

-- Test per vedere se si possono sbloccare gli elementi interni che erano
-- bloccati. quindi λx.(λy.(λw.w)y)z
ex₆ : Tm (ε , ★) (★ ⇒ ★)
ex₆ = abs (app (abs (app (abs (var zero)) (var zero))) (var zero))

-- lam (ne (var zero)) , later⇓ (later⇓ (later⇓ (later⇓ now⇓)))
nex₆ : ∃ λ n → nf ex₆ ⇓ n
nex₆ = normalize (ε , ★) (★ ⇒ ★) ex₆

-- Un ultimo test per la forma normale η-long
ex₇ : Tm (ε , ★ ⇒ ★) (★ ⇒ ★)
ex₇ = var zero

-- lam (ne (app (var (suc zero)) (ne (var zero)))) , later⇓ now⇓
nex₇ : ∃ λ n → nf ex₇ ⇓ n
nex₇ = normalize (ε , ★ ⇒ ★) (★ ⇒ ★) ex₇
