/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Pow.lean
-- Potenciación de naturales por naturales.

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Lattice
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div


namespace Peano
  open Peano

  namespace Pow
      open Peano.Axioms
      open Peano.StrictOrder
      open Peano.Order
      open Peano.Lattice
      open Peano.WellFounded
      open Peano.Add
      open Peano.Sub
      open Peano.Mul
      open Peano.Div

    /- Definición de la función de potenciación. -/
    def pow (n m : ℕ₀) : ℕ₀ :=
      match m with
      | .zero => 𝟙
      | .succ m' => mul (pow n m') n

    /- Notación para la potenciación. -/
    scoped infix:80 " ^ " => pow

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
      show lt₀ 𝟘 (mul (n ^ m') n)
      apply mul_pos _ h_n_gt_0
      cases m' with
      | zero =>
        -- n ^ 𝟘 = 𝟙 > 𝟘
        rw [pow_zero]
        exact lt_succ_self 𝟘          -- lt₀ 𝟘 (σ 𝟘) = lt₀ 𝟘 𝟙
      | succ m'' =>
        -- IH: σ m'' > 𝟘 → n ^ (σ m'') > 𝟘
        exact ih (pos_of_ne_zero _ (succ_neq_zero m''))

  theorem pow_ge_one {n m : ℕ₀} (h_n_gt_0 : n > 𝟘) :
    n ^ m ≥ 𝟙
    := by
    induction m with
    | zero =>
      rw [pow_zero]
      exact le_refl 𝟙
    | succ m' ih =>
      rw [pow_succ]
      exact le_le_mul_le_compat ih (lt_0n_then_le_1n_wp h_n_gt_0)

  /- n ≠ 0 → n^m ≠ 0. -/
  theorem pow_ne_zero {n : ℕ₀} (h : n ≠ 𝟘) (m : ℕ₀) : n ^ m ≠ 𝟘 := by
    cases m with
    | zero    => rw [pow_zero]; exact succ_neq_zero 𝟘
    | succ m' =>
      have h_gt := pow_gt (pos_of_ne_zero n h) (pos_of_ne_zero (σ m') (succ_neq_zero m'))
      intro heq
      rw [heq] at h_gt
      exact lt_zero 𝟘 h_gt

  /- Versión fuerte: solo requiere m ≠ 0, sin condición sobre n. -/
  theorem pow_lt_succ_base_strong {n m : ℕ₀} (h_m_ne_0 : m ≠ 𝟘) :
    lt₀ (n ^ m) ((σ n) ^ m) := by
    have h0 : n = 𝟘 ∨ n ≠ 𝟘 := Decidable.em (n = 𝟘)
    cases h0 with
    | inl h_eq_0 =>
      rw [h_eq_0]
      change lt₀ (𝟘 ^ m) (𝟙 ^ m)
      have h_0_pow : 𝟘 ^ m = 𝟘 := zero_pow h_m_ne_0
      have h_1_pow : 𝟙 ^ m = 𝟙 := one_pow m
      rw [h_0_pow, h_1_pow]
      exact lt_succ_self 𝟘
    | inr h_neq_0 =>
      induction m with
      | zero => contradiction
      | succ m' ih =>
        cases m' with
        | zero =>
          change lt₀ (n ^ 𝟙) ((σ n) ^ 𝟙)
          rw [pow_one, pow_one]
          exact lt_succ_self n
        | succ m'' =>
          have hm'_ne_0 : σ m'' ≠ 𝟘 := succ_neq_zero m''
          have h_ih := ih hm'_ne_0
          rw [pow_succ, pow_succ]
          have h_n_pow_ne_0 : n ^ (σ m'') ≠ 𝟘 := pow_ne_zero h_neq_0 (σ m'')
          exact lt_lt_mul_lt_compat h_ih (lt_succ_self n) h_neq_0 h_n_pow_ne_0

  theorem pow_lt_succ_base {n : ℕ₀} (h_n_ne_0 : n ≠ 𝟘) {m : ℕ₀} (h_m_ne_0 : m ≠ 𝟘) :
    lt₀ (n ^ m) ((σ n) ^ m) := by
    exact pow_lt_succ_base_strong h_m_ne_0

  theorem pow_lt_succ_exp {n m : ℕ₀} (h_n_gt_1 : lt₀ 𝟙 n) :
    lt₀ (n ^ m) (n ^ σ m) := by
    rw [pow_succ]
    have h_n_ne_0 : n ≠ 𝟘 := by
      intro h
      rw [h] at h_n_gt_1
      exact nlt_n_0_false 𝟙 h_n_gt_1
    have h_n_pow_ne_0 : n ^ m ≠ 𝟘 := pow_ne_zero h_n_ne_0 m
    exact mul_lt_left (n ^ m) n h_n_pow_ne_0 h_n_gt_1

  theorem pow_add_eq_mul_pow (n m k : ℕ₀) :
    n ^ (add m k) = mul (n ^ m) (n ^ k)
    := by
    induction k with
    | zero => rw [add_zero, pow_zero, mul_one]
    | succ k' ih => rw [add_succ, pow_succ, ih, pow_succ, mul_assoc]

  theorem mul_pow_n_m_pow_k_m_eq_pow_nk_m (n k m : ℕ₀):
    mul (n ^ m) (k ^ m) = (mul n k) ^ m
    := by
    induction m with
    | zero => rw [pow_zero, pow_zero, pow_zero, mul_one]
    | succ m' ih =>
      rw [pow_succ, pow_succ, pow_succ, ←ih]
      have h1 : mul (mul (n ^ m') n) (mul (k ^ m') k) = mul (mul (n ^ m') (k ^ m')) (mul n k) := by
        rw [mul_assoc n (n^m') (mul (k^m') k)]
        have h2 : mul n (mul (k ^ m') k) = mul (mul n (k ^ m')) k := Eq.symm (mul_assoc (k^m') n k)
        rw [h2]
        have h3 : mul n (k ^ m') = mul (k ^ m') n := mul_comm n (k ^ m')
        rw [h3]
        have h4 : mul (mul (k ^ m') n) k = mul (k ^ m') (mul n k) := mul_assoc n (k^m') k
        rw [h4]
        exact Eq.symm (mul_assoc (k^m') (n^m') (mul n k))
      exact h1

  theorem pow_pow_eq_pow_mul(n m k : ℕ₀) :
    (n ^ m) ^ k = n ^ (mul m k)
    := by
    induction k with
    | zero => rw [pow_zero, mul_zero, pow_zero]
    | succ k' ih => rw [pow_succ, ih, mul_succ, pow_add_eq_mul_pow]



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
        refine ⟨?_, succ_neq_zero m'⟩
        by_cases hn : n = 𝟘
        · exact hn
        · exact absurd h (pow_ne_zero hn (σ m'))
    · intro ⟨hn, hm⟩
      rw [hn]; exact zero_pow hm

  /- 1 < n → m ≠ 0 → 1 < n^m. -/
  theorem one_lt_pow {n : ℕ₀} (h_n_gt_1 : lt₀ 𝟙 n) {m : ℕ₀} (h_m_ne_0 : m ≠ 𝟘) :
      lt₀ 𝟙 (n ^ m) := by
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
        rcases lt_0n_then_le_1n_wp (pos_of_ne_zero n h_n_ne_0) with h_gt1 | h_eq1
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
  theorem pow_lt_mono_exp {n : ℕ₀} (h_n_gt_1 : lt₀ 𝟙 n) {m k : ℕ₀} (h : lt₀ m k) :
      lt₀ (n ^ m) (n ^ k) := by
    induction k with
    | zero    => exact absurd h (lt_zero m)
    | succ k' ih =>
      rcases (lt_succ_iff_lt_or_eq m k').mp h with h_lt | h_eq
      · exact lt_trans (n ^ m) (n ^ k') (n ^ σ k') (ih h_lt) (pow_lt_succ_exp h_n_gt_1)
      · subst h_eq; exact pow_lt_succ_exp h_n_gt_1

  /- Monotonicidad en el exponente: 1 < n → m ≤ k → n^m ≤ n^k. -/
  theorem pow_le_pow_right {n : ℕ₀} (h_n_gt_1 : lt₀ 𝟙 n) {m k : ℕ₀} (h : le₀ m k) :
      le₀ (n ^ m) (n ^ k) := by
    rcases (le_iff_lt_or_eq m k).mp h with h_lt | h_eq
    · exact lt_imp_le_wp (pow_lt_mono_exp h_n_gt_1 h_lt)
    · subst h_eq; exact le_refl (n ^ m)

  /- Monotonicidad estricta en la base: m < n → k ≠ 0 → m^k < n^k. -/
  theorem pow_lt_mono_base {m n : ℕ₀} (h : lt₀ m n) {k : ℕ₀} (h_k_ne_0 : k ≠ 𝟘) :
      lt₀ (m ^ k) (n ^ k) := by
    induction n with
    | zero    => exact absurd h (lt_zero m)
    | succ n' ih =>
      rcases (lt_succ_iff_lt_or_eq m n').mp h with h_lt | h_eq
      · exact lt_trans (m ^ k) (n' ^ k) ((σ n') ^ k) (ih h_lt) (pow_lt_succ_base_strong h_k_ne_0)
      · subst h_eq; exact pow_lt_succ_base_strong h_k_ne_0

  /- Monotonicidad en la base: m ≤ n → k ≠ 0 → m^k ≤ n^k. -/
  theorem pow_le_pow_left {m n : ℕ₀} (h : le₀ m n) {k : ℕ₀} (h_k_ne_0 : k ≠ 𝟘) :
      le₀ (m ^ k) (n ^ k) := by
    rcases (le_iff_lt_or_eq m n).mp h with h_lt | h_eq
    · exact lt_imp_le_wp (pow_lt_mono_base h_lt h_k_ne_0)
    · subst h_eq; exact le_refl (m ^ k)

  /- n^m · n^k = n^k · n^m. -/
  theorem pow_mul_comm (n m k : ℕ₀) : mul (n ^ m) (n ^ k) = mul (n ^ k) (n ^ m) :=
    mul_comm (n ^ m) (n ^ k)

    -- ═══════════════════════════════════════════════════════════
    -- § Isomorfismo Ψ/Λ para pow
    -- ═══════════════════════════════════════════════════════════

    theorem isomorph_Ψ_pow (n m : ℕ₀) :
      Ψ (pow n m) = Nat.pow (Ψ n) (Ψ m)
        := by
      induction m with
      | zero =>
        calc
          Ψ (pow n 𝟘) = Ψ 𝟙 := by rw [pow_zero]
          _ = 1 := by rfl
          _ = Nat.pow (Ψ n) 0 := by rfl
      | succ m' ih =>
        calc
          Ψ (pow n (σ m')) = Ψ (mul (pow n m') n) := by rw [pow_succ]
          _ = Nat.mul (Ψ (pow n m')) (Ψ n) := by rw [isomorph_Ψ_mul]
          _ = Nat.mul (Nat.pow (Ψ n) (Ψ m')) (Ψ n) := by rw [ih]

    theorem isomorph_Λ_pow (n m : Nat) :
      Λ (Nat.pow n m) = pow (Λ n) (Λ m)
        := by
      induction m with
      | zero =>
        calc
          Λ (Nat.pow n 0) = Λ 1 := by rfl
          _ = 𝟙 := by rfl
          _ = pow (Λ n) 𝟘 := by rfl
      | succ m' ih =>
        calc
          Λ (Nat.pow n (Nat.succ m'))
            = Λ (Nat.mul (Nat.pow n m') n) := by rfl
          _ = mul (Λ (Nat.pow n m')) (Λ n) := by rw [isomorph_Λ_mul]
          _ = mul (pow (Λ n) (Λ m')) (Λ n) := by rw [ih]
          _ = pow (Λ n) (σ (Λ m')) := by rw [pow_succ]
          _ = pow (Λ n) (Λ (Nat.succ m')) := by rw [← Λ_σ_eq_σ_Ψ]

    theorem n_le_two_pow_n (n : ℕ₀) :
        le₀ n ((σ (σ 𝟘)) ^ n) := by
      induction n with
      | zero =>
        rw [pow_zero]
        exact zero_le 𝟙
      | succ n' ih =>
        have h_base_gt_0 : lt₀ 𝟘 (σ (σ 𝟘)) := le_0_succ_then_lt_0_succ_wp (zero_le (σ (σ 𝟘)))
        have h1 : le₀ 𝟙 ((σ (σ 𝟘)) ^ n') := pow_ge_one h_base_gt_0
        have h2 : le₀ (Add.add n' 𝟙) (Add.add ((σ (σ 𝟘)) ^ n') 𝟙) := by
          rw [add_comm n' 𝟙, add_comm ((σ (σ 𝟘)) ^ n') 𝟙]
          exact add_le_add_left n' ((σ (σ 𝟘)) ^ n') 𝟙 ih
        have h3 : le₀ (Add.add ((σ (σ 𝟘)) ^ n') 𝟙) (Add.add ((σ (σ 𝟘)) ^ n') ((σ (σ 𝟘)) ^ n')) := add_le_add_left 𝟙 ((σ (σ 𝟘)) ^ n') ((σ (σ 𝟘)) ^ n') h1
        have h4 : le₀ (Add.add n' 𝟙) (Add.add ((σ (σ 𝟘)) ^ n') ((σ (σ 𝟘)) ^ n')) := le_trans (Add.add n' 𝟙) (Add.add ((σ (σ 𝟘)) ^ n') 𝟙) (Add.add ((σ (σ 𝟘)) ^ n') ((σ (σ 𝟘)) ^ n')) h2 h3
        have h5 : Add.add n' 𝟙 = σ n' := add_one n'
        have h6 : Add.add ((σ (σ 𝟘)) ^ n') ((σ (σ 𝟘)) ^ n') = mul ((σ (σ 𝟘)) ^ n') (σ (σ 𝟘)) := by
          exact (mul_two ((σ (σ 𝟘)) ^ n')).symm
        have h7 : mul ((σ (σ 𝟘)) ^ n') (σ (σ 𝟘)) = (σ (σ 𝟘)) ^ (σ n') := by
          exact pow_succ (σ (σ 𝟘)) n'
        rw [h5] at h4
        rw [h6] at h4
        rw [h7] at h4
        exact h4

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
  isomorph_Ψ_pow
  isomorph_Λ_pow
  n_le_two_pow_n
)

instance : Pow ℕ₀ ℕ₀ where
  pow := Peano.Pow.pow

@[simp] theorem pow_def (a b : ℕ₀) : a ^ b = Peano.Pow.pow a b := rfl
