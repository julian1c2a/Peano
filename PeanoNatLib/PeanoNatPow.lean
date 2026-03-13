/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- PeanoNatLib/PeanoNatPow.lean
-- Potenciación de naturales por naturales.

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatWellFounded
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatDiv


namespace Peano
  open Peano

  namespace Pow
      open Peano.Axioms
      open Peano.StrictOrder
      open Peano.Order
      open Peano.MaxMin
      open Peano.WellFounded
      open Peano.Add
      open Peano.Sub
      open Peano.Mul
      open Peano.Div

    /- Definición de la función de potenciación. -/
    def pow (n m : ℕ₀) : ℕ₀ :=
      match m with
      | 𝟘 => 𝟙
      | σ m' => mul (pow n m') n

    /- Notación para la potenciación. -/
    infix:80 " ^ " => pow

    /- Propiedades de la potenciación. -/
    theorem pow_zero (n : ℕ₀) :
      n ^ 𝟘 = 𝟙
      := by rfl

    theorem zero_pow {m : ℕ₀} (h_neq_0 : m ≠ 𝟘) :
      𝟘 ^ m = 𝟘
      :=  by
      cases m with
      | zero      => contradiction
      | succ m'   => rfl

    theorem one_pow (m : ℕ₀) :
      𝟙 ^ m = 𝟙
      := by
      induction m with
      | zero        => rfl
      | succ m' ih  =>
          unfold pow
          calc 𝟙 ^ (σ m') = mul (𝟙 ^ m') 𝟙 := by rfl
               _ = mul 𝟙 𝟙                 := by rw[ih]
               _ = 𝟙                       := by rfl

    theorem pow_succ (n m : ℕ₀) :
      n ^ (σ m) = mul (n ^ m) n
      := by rfl

    theorem pow_one (n : ℕ₀) :
      n ^ 𝟙 = n
      := by
      unfold pow
      calc n ^ 𝟙 = n ^ (σ  𝟘) := by rfl
               _ = mul (n ^ 𝟘) n := by rfl
               _ = mul 𝟙 n       := by rw[pow_zero]
               _ = n             := by rw[one_mul n]

  theorem pow_gt {n m : ℕ₀} (h_n_gt_0 : n > 𝟘) (h_m_gt_0 : m > 𝟘) :
    n ^ m > 𝟘
    := by
    induction m with
    | zero        => contradiction
    | succ m' ih =>
      show Lt 𝟘 (mul (n ^ m') n)
      apply mul_pos _ h_n_gt_0
      cases m' with
      | zero =>
        -- n ^ 𝟘 = 𝟙 > 𝟘
        rw [pow_zero]
        exact lt_succ_self 𝟘          -- Lt 𝟘 (σ 𝟘) = Lt 𝟘 𝟙
      | succ m'' =>
        -- IH: σ m'' > 𝟘 → n ^ (σ m'') > 𝟘
        exact ih (lt_0_n _ (succ_neq_zero m''))

  theorem pow_ge_one {n m : ℕ₀} (h_n_gt_0 : n > 𝟘) :
    n ^ m ≥ 𝟙
    := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact le_refl 𝟙
  | succ m' ih =>
    show Le 𝟙 (mul (n ^ m') n)
    -- Le 𝟙 n  (de n > 0)
    have h1_le_n : Le 𝟙 n := by
      rcases lt_0n_then_le_1n_wp h_n_gt_0 with h | h
      · exact Or.inl h
      · exact Or.inr h
    -- Le n (n^m' · n)  (de ih : Le 𝟙 (n^m') por mul_le_mono_right)
    have h_n_le_mul : Le n (mul (n ^ m') n) := by
      have := mul_le_mono_right n ih    -- Le (mul 𝟙 n) (mul (n^m') n)
      rwa [one_mul] at this
    -- Transitivity: Le 𝟙 n ≤ (n^m')·n
    exact le_trans 𝟙 n (mul (n ^ m') n) h1_le_n h_n_le_mul

  theorem pow_lt_succ_base {n : ℕ₀} (h_n_ne_0 : n ≠ 𝟘) {m : ℕ₀} (h_m_ne_0 : m ≠ 𝟘) :
    Lt (n ^ m) ((σ n) ^ m) := by
  cases m with
  | zero    => contradiction
  | succ m' =>
    induction m' with
    | zero =>
      -- n^1 = n < σn = (σn)^1
      simp only [pow_succ, pow_zero, one_mul]
      exact lt_succ_self n
    | succ m'' ih =>
      simp only [pow_succ]
      have h_n_gt_0 := lt_0_n n h_n_ne_0
      have h_pow_ge_1 : Le 𝟙 (n ^ σ m'') := pow_ge_one h_n_gt_0
      -- Aplicar ih a su argumento antes de pasarlo a lt_imp_le:
      have h_m''_ne_0 : σ m'' ≠ 𝟘 := succ_neq_zero m''
      have h_ih := ih h_m''_ne_0          -- ahora h_ih : Lt (n ^ σ m'') ((σ n) ^ σ m'')
      have h1 : Lt (mul (n ^ σ m'') n) (mul (n ^ σ m'') (σ n)) := by
        have := mul_lt_full_right (n ^ σ m'') n 𝟙 (le_refl 𝟙) h_pow_ge_1
        rwa [add_one] at this
      have h2 := mul_le_mono_right (σ n) (lt_imp_le_wp h_ih)
      exact lt_of_lt_of_le h1 h2

  /- Versión fuerte: solo requiere m ≠ 0, sin condición sobre n. -/
  theorem pow_lt_succ_base_strong {n m : ℕ₀} (h_m_ne_0 : m ≠ 𝟘) :
    Lt (n ^ m) ((σ n) ^ m) := by
  cases n with
  | zero =>
    -- 0^m = 0 < 1 = (σ 0)^m  (σ 0 = 𝟙 por def, pero rw no unifica sintácticamente)
    rw [zero_pow h_m_ne_0]
    have h : (σ 𝟘) ^ m = 𝟙 := one_pow m
    rw [h]
    exact lt_succ_self 𝟘
  | succ n' =>
    exact pow_lt_succ_base (succ_neq_zero n') h_m_ne_0

  theorem pow_lt_succ_exp {n m : ℕ₀} (h_n_gt_1 : Lt 𝟙 n) :
    Lt (n ^ m) (n ^ σ m) := by
  rw [pow_succ]
  -- Goal: Lt (n^m) (mul (n^m) n)
  have h_n_gt_0 : Lt 𝟘 n := lt_trans 𝟘 𝟙 n (lt_succ_self 𝟘) h_n_gt_1
  have h_pow_ge_1 : Le 𝟙 (n ^ m) := pow_ge_one h_n_gt_0
  have h_pow_ne_0 : n ^ m ≠ 𝟘 := by
    intro h; rw [h] at h_pow_ge_1
    exact absurd h_pow_ge_1 (not_succ_le_zero 𝟘)
  exact mul_lt_left (n ^ m) n h_pow_ne_0 h_n_gt_1

  theorem pow_add_eq_mul_pow (n m k : ℕ₀) :
    n ^ (add m k) = mul (n ^ m) (n ^ k)
    := by
  induction k with
  | zero =>
    calc n ^ (add m 𝟘) = n ^ m := by rfl
         _ = mul (n ^ m) 𝟙 := by rw[mul_one]
         _ = mul (n ^ m) (n ^ 𝟘) := by rw[pow_zero]
  | succ k' ih =>
    calc n ^ (add m (σ k')) = n ^ (σ (add m k')) := by rfl
         _ = mul (n ^ (add m k')) n := by rw[pow_succ]
         _ = mul (mul (n ^ m) (n ^ k')) n := by rw[ih]
         _ = mul (n ^ m) (mul (n ^ k') n) := by rw[mul_assoc]
         _ = mul (n ^ m) (n ^ (σ k')) := by rw[pow_succ]

  theorem mul_pow_n_m_pow_k_m_eq_pow_nk_m (n k m : ℕ₀):
    mul (pow n m) (pow k m) = pow (mul n k) m
    := by
    induction m with
    | zero =>
      calc mul (pow n 𝟘) (pow k 𝟘) = mul 𝟙 (pow k 𝟘) := by
              have is_1 : pow n 𝟘 = 𝟙 := pow_zero n
              exact is_1
           _ = mul 𝟙 𝟙 := by
              have is_1 : pow k 𝟘 = 𝟙 := pow_zero k
              exact is_1
           _ = 𝟙 := mul_one 𝟙
           _ = pow (mul n k) 𝟘 := by
              have is_1 : pow (mul n k) 𝟘 = 𝟙 := pow_zero (mul n k)
              exact is_1
    | succ m' ih =>
      calc mul (pow n (σ m')) (pow k (σ m')) = mul (mul (pow n m') n) (pow k (σ m'))
                := by rw[pow_succ]
           _ = mul (mul (pow n m') n) (mul (pow k m') k)
                := by rw[pow_succ]
           _ = mul (mul (mul (pow n m') n) (pow k m')) k
                := by rw[← mul_assoc (pow k m') (mul (pow n m') n) k]
           _ = mul (mul (pow n m') (mul n (pow k m'))) k
                := by rw[mul_assoc n (pow n m') (pow k m')]
           _ = mul (mul (pow n m') (mul (pow k m') n)) k
                := by rw[mul_comm n (pow k m')]
           _ = mul (mul (pow n m') (pow k m')) (mul n k)
                 := by rw[← mul_assoc (pow k m') (pow n m') n,
                          mul_assoc n (mul (pow n m') (pow k m')) k]
           _ = mul (pow (mul n k) m') (mul n k)
                := by rw[ih]
           _ = pow (mul n k) (σ m') := by rw[pow_succ]

  theorem pow_pow_eq_pow_mul(n m k : ℕ₀) :
    pow (pow n m) k = pow n (mul m k)
    := by
    induction k with
    | zero =>
      calc pow (pow n m) 𝟘 = 𝟙 := by rfl
           _ = pow n 𝟘 := by rw[pow_zero]
    | succ k' ih =>
      calc pow (pow n m) (σ k') = mul (pow (pow n m) k') (pow n m) := by rw[pow_succ]
           _ = mul (pow n (mul m k')) (pow n m) := by rw[ih]
           _ = mul (pow n m) (pow n (mul m k')) := by rw[mul_comm]
           _ = pow n (add m (mul m k')) := by rw[pow_add_eq_mul_pow]
           _ = pow n (add (mul m k') m) := by rw[add_comm]

  /- n ≠ 0 → n^m ≠ 0. -/
  theorem pow_ne_zero {n : ℕ₀} (h : n ≠ 𝟘) (m : ℕ₀) : n ^ m ≠ 𝟘 := by
    cases m with
    | zero    => rw [pow_zero]; exact succ_neq_zero 𝟘
    | succ m' =>
      have h_gt := pow_gt (lt_0_n n h) (lt_0_n (σ m') (succ_neq_zero m'))
      intro heq
      rw [heq] at h_gt
      exact lt_zero 𝟘 h_gt

  /- n^2 = n · n. -/
  theorem pow_two (n : ℕ₀) : n ^ 𝟚 = mul n n := by
    show mul (n ^ 𝟙) n = mul n n
    rw [pow_one]

  /- n^m = 0 ↔ n = 0 ∧ m ≠ 0. -/
  theorem pow_eq_zero_iff {n m : ℕ₀} : n ^ m = 𝟘 ↔ n = 𝟘 ∧ m ≠ 𝟘 := by
    constructor
    · intro h
      cases m with
      | zero    =>
        rw [pow_zero] at h
        exact absurd h (succ_neq_zero 𝟘)
      | succ m' =>
        exact ⟨Classical.byContradiction (fun hn => absurd h (pow_ne_zero hn (σ m'))),
               succ_neq_zero m'⟩
    · intro ⟨hn, hm⟩
      rw [hn]; exact zero_pow hm

  /- 1 < n → m ≠ 0 → 1 < n^m. -/
  theorem one_lt_pow {n : ℕ₀} (h_n_gt_1 : Lt 𝟙 n) {m : ℕ₀} (h_m_ne_0 : m ≠ 𝟘) :
      Lt 𝟙 (n ^ m) := by
    cases m with
    | zero    => contradiction
    | succ m' =>
      induction m' with
      | zero      =>
          have h_pow : n ^ σ 𝟘 = n := pow_one n
          rw [h_pow]; exact h_n_gt_1
      | succ m'' ih =>
          exact lt_trans 𝟙 (n ^ σ m'') (n ^ σ (σ m''))
                  (ih (succ_neq_zero m'')) (pow_lt_succ_exp h_n_gt_1)

  /- n^m = 1 ↔ n = 1 ∨ m = 0  (con n ≠ 0). -/
  theorem pow_eq_one_iff {n : ℕ₀} (h_n_ne_0 : n ≠ 𝟘) {m : ℕ₀} :
      n ^ m = 𝟙 ↔ n = 𝟙 ∨ m = 𝟘 := by
    constructor
    · intro h
      cases m with
      | zero    => exact Or.inr rfl
      | succ m' =>
        rcases lt_0n_then_le_1n_wp (lt_0_n n h_n_ne_0) with h_gt1 | h_eq1
        · exfalso
          have hlt := one_lt_pow h_gt1 (succ_neq_zero m')
          rw [h] at hlt
          exact lt_zero 𝟘 ((succ_lt_succ_iff 𝟘 𝟘).mp hlt)
        · exact Or.inl h_eq1.symm
    · intro h
      rcases h with h_n | h_m
      · rw [h_n]; exact one_pow m
      · rw [h_m]; exact pow_zero n

  /- Monotonicidad estricta en el exponente: 1 < n → m < k → n^m < n^k. -/
  theorem pow_lt_mono_exp {n : ℕ₀} (h_n_gt_1 : Lt 𝟙 n) {m k : ℕ₀} (h : Lt m k) :
      Lt (n ^ m) (n ^ k) := by
    induction k with
    | zero    => exact absurd h (lt_zero m)
    | succ k' ih =>
      rcases (lt_succ_iff_lt_or_eq m k').mp h with h_lt | h_eq
      · exact lt_trans (n ^ m) (n ^ k') (n ^ σ k') (ih h_lt) (pow_lt_succ_exp h_n_gt_1)
      · subst h_eq; exact pow_lt_succ_exp h_n_gt_1

  /- Monotonicidad en el exponente: 1 < n → m ≤ k → n^m ≤ n^k. -/
  theorem pow_le_pow_right {n : ℕ₀} (h_n_gt_1 : Lt 𝟙 n) {m k : ℕ₀} (h : Le m k) :
      Le (n ^ m) (n ^ k) := by
    rcases (le_iff_lt_or_eq m k).mp h with h_lt | h_eq
    · exact lt_imp_le_wp (pow_lt_mono_exp h_n_gt_1 h_lt)
    · subst h_eq; exact le_refl (n ^ m)

  /- Monotonicidad estricta en la base: m < n → k ≠ 0 → m^k < n^k. -/
  theorem pow_lt_mono_base {m n : ℕ₀} (h : Lt m n) {k : ℕ₀} (h_k_ne_0 : k ≠ 𝟘) :
      Lt (m ^ k) (n ^ k) := by
    induction n with
    | zero    => exact absurd h (lt_zero m)
    | succ n' ih =>
      rcases (lt_succ_iff_lt_or_eq m n').mp h with h_lt | h_eq
      · exact lt_trans (m ^ k) (n' ^ k) ((σ n') ^ k) (ih h_lt) (pow_lt_succ_base_strong h_k_ne_0)
      · subst h_eq; exact pow_lt_succ_base_strong h_k_ne_0

  /- Monotonicidad en la base: m ≤ n → k ≠ 0 → m^k ≤ n^k. -/
  theorem pow_le_pow_left {m n : ℕ₀} (h : Le m n) {k : ℕ₀} (h_k_ne_0 : k ≠ 𝟘) :
      Le (m ^ k) (n ^ k) := by
    rcases (le_iff_lt_or_eq m n).mp h with h_lt | h_eq
    · exact lt_imp_le_wp (pow_lt_mono_base h_lt h_k_ne_0)
    · subst h_eq; exact le_refl (m ^ k)

  /- n^m · n^k = n^k · n^m. -/
  theorem pow_mul_comm (n m k : ℕ₀) : mul (n ^ m) (n ^ k) = mul (n ^ k) (n ^ m) :=
    mul_comm (n ^ m) (n ^ k)

  end Pow
end Peano

export Peano.Pow (
  pow
  pow_zero
  zero_pow
  one_pow
  pow_one
  pow_succ
  pow_gt
  pow_ge_one
  pow_lt_succ_base
  pow_lt_succ_base_strong
  pow_lt_succ_exp
  pow_add_eq_mul_pow
  mul_pow_n_m_pow_k_m_eq_pow_nk_m
  pow_pow_eq_pow_mul
  pow_ne_zero
  pow_two
  pow_eq_zero_iff
  one_lt_pow
  pow_eq_one_iff
  pow_lt_mono_exp
  pow_le_pow_right
  pow_lt_mono_base
  pow_le_pow_left
  pow_mul_comm
)
