module Diss where

open import HoTT-UF-Agda public hiding (id; _∙'_; _≃_; is-set; is-equiv)

module Addition where
  open HoTT-UF-Agda.Arithmetic renaming (_+_ to add₁)
  open HoTT-UF-Agda.Arithmetic' renaming (_+_ to add₂)
  add₃ : ℕ → ℕ → ℕ
  add₃ m n = ℕ-induction (λ _ → ℕ) m (λ _ → λ p → succ p) n

  proof1plus1 : add₃ 1 1 ＝ 2
  proof1plus1 = refl 2

  add₁_eq_add₂_pw : (m n : ℕ) → add₁ m n ＝ add₂ m n
  add₁_eq_add₂_pw 0 0 = refl 0
  add₁_eq_add₂_pw (succ m) 0 = refl (succ m)
  add₁_eq_add₂_pw 0 (succ n) = ap succ (add₁_eq_add₂_pw 0 n)
  add₁_eq_add₂_pw (succ m) (succ n) = ap succ (add₁_eq_add₂_pw (succ m) n)

  add₂_eq_add₃_pw : (m n : ℕ) → add₂ m n ＝ add₃ m n
  add₂_eq_add₃_pw 0 0 = refl 0
  add₂_eq_add₃_pw (succ m) 0 = refl (succ m)
  add₂_eq_add₃_pw 0 (succ n) = ap succ (add₂_eq_add₃_pw 0 n)
  add₂_eq_add₃_pw (succ m) (succ n) = ap succ (add₂_eq_add₃_pw (succ m) n)

  add₁_eq_add₃_pw : (m n : ℕ) -> add₁ m n ＝ add₃ m n
  add₁_eq_add₃_pw m n = (add₁_eq_add₂_pw m n) ∙ (add₂_eq_add₃_pw m n)

  add₁_eq_add₂ : funext 𝓤₀ 𝓤₀ → add₁ ＝ add₂
  add₁_eq_add₂ fe = fe (λ m → fe (add₁_eq_add₂_pw m))

  add₂_eq_add₃ : funext 𝓤₀ 𝓤₀ → add₂ ＝ add₃
  add₂_eq_add₃ fe = fe (λ m → fe (add₂_eq_add₃_pw m))

module Equivalences where
  id : ( A : 𝓤 ̇ ) → A → A
  id A a = a

  qinv : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → 𝓤 ⊔ 𝓥 ̇
  qinv {A = A} {B = B} f =
    Σ g ꞉ (B → A) , ((f ∘ g) ∼ (id B)) × ((g ∘ f) ∼ (id A))

  is-equiv : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → 𝓤 ⊔ 𝓥 ̇
  is-equiv {A = A} {B = B} f =
    (Σ g ꞉ (B → A) , f ∘ g ∼ (id B))
      × (Σ h ꞉ (B → A) , h ∘ f ∼ (id A))

  _≃_ : (A : 𝓤 ̇) → (B : 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
  A ≃ B = Σ f ꞉ (A → B) , is-equiv f

  qinv-to-equiv : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B}
    → (qinv f) → (is-equiv f)
  qinv-to-equiv (g , (α , β)) = ((g , α) , (g , β))

module Fin where
  open Equivalences public
  open HoTT-UF-Agda.Arithmetic renaming (_+_ to add)

  _≤_ : ℕ → ℕ → 𝓤₀ ̇
  n ≤ m = Σ p ꞉ ℕ , (add p n) ＝ m

  Fin : ℕ → 𝓤₀ ̇
  Fin 0 = 𝟘
  Fin (succ n) = 𝟙 + (Fin n)

  FinNat : ℕ → 𝓤₀ ̇
  FinNat n = Σ k ꞉ ℕ , (succ k) ≤ n

  f : (n : ℕ) → Fin n → FinNat n
  f 0 z = 𝟘-induction (λ _ → FinNat 0) z
  f (succ n) (inl _) = (0 , (n , refl (succ n)))
  f (succ n) (inr y) = (succ k , (p , ap succ q))
    where
      k = pr₁ (f n y)
      p = pr₁ (pr₂ (f n y))
      q = pr₂ (pr₂ (f n y))

  g : (n : ℕ) → FinNat n → Fin n
  g 0 (k , (p , q)) = 𝟘-induction (λ _ → Fin 0) z
    where
      code : ℕ → 𝓤₀ ̇
      code 0 = 𝟘
      code (succ _) = 𝟙
      z : 𝟘
      z = transport code q ⋆
  g (succ n) (0 , (p , q)) = inl ⋆
  g (succ n) (succ m , (p , q)) = inr (g n (m , (p , ap prev q)))
    where
      prev : ℕ → ℕ
      prev 0 = 0
      prev (succ n) = n

  fin-equivalence : (n : ℕ)
    → ((f n ∘ g n) ∼ id (FinNat n))
    → ((g n ∘ f n) ∼ id (Fin n))
    → Fin n ≃ FinNat n
  fin-equivalence n alpha beta =
    (f n , qinv-to-equiv (g n , (alpha , beta)))
