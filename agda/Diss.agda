module Diss where

open import HoTT-UF-Agda public hiding (_+_; transport)

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

transport : { A : 𝓤 ̇ } { D : A → 𝓥 ̇ } { x y : A } → (x ＝ y) → (D x) → D y
--transport 
