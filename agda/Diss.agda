module Diss where

open import HoTT-UF-Agda public hiding (_+_; transport; id; ap)

add : ℕ → ℕ → ℕ
add m = ℕ-induction (λ _ → ℕ) m (λ _ → λ n → succ n)

_+_ : ℕ → ℕ → ℕ
_+_ = add

proof1plus1 : 1 + 1 ＝ 2
proof1plus1 = refl 2

leq : ℕ → ℕ → 𝓤₀ ̇
leq n m = Σ p ꞉ ℕ , (n + p) ＝ m

proof1leq2 : leq 1 3
proof1leq2 = (2 , refl 3)

id : ( A : 𝓤 ̇ ) → A → A
id A a = a

transport : { A : 𝓤 ̇ } { x y : A } ( D : A → 𝓥 ̇ ) → (x ＝ y) → (D x) → D y
transport {𝓤} {𝓥} {A} {x} {y} D = 𝕁 A (λ x y _ → (D x → D y)) (λ z → id (D z)) x y

ap : { A : 𝓤 ̇ } { B : 𝓥 ̇ } { x y : A } (f : A → B) → (x ＝ y) → (f x ＝ f y)
ap {A = A} {x = x} {y = y} f = 𝕁 A (λ x y _ → f x ＝ f y) (λ z → refl (f z)) x y
-- ap {x = x} f p = transport (λ y → f x ＝ f y) p (refl (f x))

proof_ap_refl : { A : 𝓤 ̇ } { B : 𝓥 ̇ } (f : A → B) (z : A) → ap f (refl z) ＝ refl (f z)
proof_ap_refl f z = refl (refl (f z))
