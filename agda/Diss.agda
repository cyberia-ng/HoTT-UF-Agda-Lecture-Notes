module Diss where

open import HoTT-UF-Agda public hiding (_+_; id; _∙'_)

_+_ : ℕ → ℕ → ℕ
m + n = ℕ-induction (λ _ → ℕ) m (λ _ → λ p → succ p) n

proof1plus1 : 1 + 1 ＝ 2
proof1plus1 = refl 2

module Addition where
  open HoTT-UF-Agda.Arithmetic renaming (_+_ to add1)
  open HoTT-UF-Agda.Arithmetic' renaming (_+_ to add2)
  add3 = _+_

  add1_eq_add2_pw : (m n : ℕ) → add1 m n ＝ add2 m n
  add1_eq_add2_pw 0 0 = refl 0
  add1_eq_add2_pw (succ m) 0 = refl (succ m)
  add1_eq_add2_pw 0 (succ n) = ap succ (add1_eq_add2_pw 0 n)
  add1_eq_add2_pw (succ m) (succ n) = ap succ (add1_eq_add2_pw (succ m) n)

  add2_eq_add3_pw : (m n : ℕ) → add2 m n ＝ add3 m n
  add2_eq_add3_pw 0 0 = refl 0
  add2_eq_add3_pw (succ m) 0 = refl (succ m)
  add2_eq_add3_pw 0 (succ n) = ap succ (add2_eq_add3_pw 0 n)
  add2_eq_add3_pw (succ m) (succ n) = ap succ (add2_eq_add3_pw (succ m) n)

  add1_eq_add3_pw : (m n : ℕ) -> add1 m n ＝ add3 m n
  add1_eq_add3_pw m n = (add1_eq_add2_pw m n) ∙ (add2_eq_add3_pw m n)

  add1_eq_add2 : funext 𝓤₀ 𝓤₀ → add1 ＝ add2
  add1_eq_add2 fe = fe (λ m → fe (add1_eq_add2_pw m))

  add2_eq_add3 : funext 𝓤₀ 𝓤₀ → add2 ＝ add3
  add2_eq_add3 fe = fe (λ m → fe (add2_eq_add3_pw m))

leq : ℕ → ℕ → 𝓤₀ ̇
leq n m = Σ p ꞉ ℕ , (n + p) ＝ m

proof1leq2 : leq 1 3
proof1leq2 = (2 , refl 3)

id : ( A : 𝓤 ̇ ) → A → A
id A a = a

ap2 : { A : 𝓤 ̇ } { B : 𝓥 ̇ } { x y : A }
  (f : A → B) → (x ＝ y) → (f x ＝ f y)
ap2 {A = A} {x = x} {y = y} f =
  𝕁 A (λ x y _ → f x ＝ f y) (λ z → refl (f z)) x y

-- ap {x = x} f p = transport (λ y → f x ＝ f y) p (refl (f x))

proof_ap_refl : { A : 𝓤 ̇ } { B : 𝓥 ̇ }
  (f : A → B) (z : A) → ap2 f (refl z) ＝ refl (f z)
proof_ap_refl f z = refl (refl (f z))

_∙'_ : {A : 𝓤 ̇} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
p ∙' q = transport (λ v → v ＝ (rhs q)) (p ⁻¹) q

proof_comp_equal : { A : 𝓤 ̇ } (x y : A) → (p : x ＝ y) → (z : A) → (q : y ＝ z) → (p ∙' q) ＝ (p ∙ q)
proof_comp_equal {A = A} = 𝕁 A C₀ c₀
  where
    C₁ : {A : 𝓤 ̇} (x z : A) → x ＝ z → 𝓤 ̇
    C₁ {A = A} x z q = (refl x) ∙' q ＝ (refl x) ∙ q

    c₁ : {A : 𝓤 ̇} (x : A) → C₁ x x (refl x)
    c₁ x = refl (refl x)

    C₀ : {A : 𝓤 ̇} (x y : A) → x ＝ y → 𝓤 ̇
    C₀ {A = A} x y p = (z : A) → (q : y ＝ z) → (p ∙' q) ＝ (p ∙ q)

    c₀ : {A : 𝓤 ̇} (x : A) → C₀ x x (refl x)
    c₀ {A = A} = 𝕁 A C₁ c₁
