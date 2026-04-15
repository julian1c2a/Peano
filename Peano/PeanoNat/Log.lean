/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Log.lean

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Combinatorics.Pow

set_option autoImplicit false

namespace Peano
  open Peano

  namespace Log
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.WellFounded
    open Peano.Add
    open Peano.Sub
    open Peano.Mul
    open Peano.Div
    open Peano.Pow


    /-!
    ## § 1. Logarithm with remainder

    `logMod b n` returns `(k, r)` where:
    - `k = ⌊log_b(n)⌋` (floor logarithm)
    - `r = n − b^k` (remainder)
    - Spec: `n = b^k + r` when `b > 1` and `n ≠ 0`
    - Exact (n is a perfect power of b) iff `r = 0`
    !-/

    /--
      Returns `(k, r)` where `k = ⌊log_b(n)⌋` and `r = n − b^k`.
      Edge cases: `logMod b 0 = (0, 0)` and `logMod b n = (0, 0)` when `b ≤ 1`.
    -/
    def logMod (b n : ℕ₀) : ℕ₀ × ℕ₀ :=
      if h_b : le₀ b 𝟙 then (𝟘, 𝟘)
      else if h_n : n = 𝟘 then (𝟘, 𝟘)
      else if _ : lt₀ n b then (𝟘, sub n 𝟙)
      else
        have h_b_gt_1 : lt₀ 𝟙 b := (nle_iff_gt b 𝟙).mp h_b
        have _h_div_lt_n : lt₀ (n / b) n := div_lt_self n b h_b_gt_1 h_n
        let p : ℕ₀ × ℕ₀ := logMod b (n / b)
        (σ p.1, add (mul p.2 b) (n % b))
    termination_by n
    decreasing_by exact _h_div_lt_n

    def log (b n : ℕ₀) : ℕ₀ := (logMod b n).1

    def logRem (b n : ℕ₀) : ℕ₀ := (logMod b n).2


    /-!
    ## § 2. Helper lemmas
    !-/

    private theorem one_le_of_ne_zero {n : ℕ₀} (h : n ≠ 𝟘) : le₀ 𝟙 n := by
      cases n with
      | zero => exact absurd rfl h
      | succ n' =>
        cases n' with
        | zero => exact Or.inr rfl
        | succ _ => exact Or.inl (by unfold lt₀; trivial)

    private theorem b_neq_zero_of_gt_one {b : ℕ₀} (h : lt₀ 𝟙 b) : b ≠ 𝟘 :=
      (gt_imp_neq_zero_one b h).1

    private theorem div_ne_zero_of_ge {n b : ℕ₀} (h_b : lt₀ 𝟙 b) (h_nlt : ¬(lt₀ n b)) (_h_n : n ≠ 𝟘) :
        (n / b) ≠ 𝟘 := by
      intro h_div_0
      have h_b_ne_0 : b ≠ 𝟘 := b_neq_zero_of_gt_one h_b
      have h_spec := divMod_spec n b h_b_ne_0
      simp only [div_def] at h_div_0
      unfold div at h_div_0
      rw [h_div_0, zero_mul, zero_add] at h_spec
      have h_mod_lt := mod_lt n b h_b_ne_0
      simp only [mod_def] at h_mod_lt
      unfold mod at h_mod_lt
      rw [← h_spec] at h_mod_lt
      exact h_nlt h_mod_lt


    /-!
    ## § 3. Basic properties
    !-/

    theorem log_zero (b : ℕ₀) : log b 𝟘 = 𝟘 := by
      unfold log logMod
      split
      · rfl
      · rfl

    theorem logRem_zero (b : ℕ₀) : logRem b 𝟘 = 𝟘 := by
      unfold logRem logMod
      split
      · rfl
      · rfl

    theorem log_of_lt {b n : ℕ₀} (h_b : lt₀ 𝟙 b) (h_n : n ≠ 𝟘) (h_lt : lt₀ n b) :
        log b n = 𝟘 := by
      unfold log logMod
      have h_nle : ¬(le₀ b 𝟙) := (nle_iff_gt b 𝟙).mpr h_b
      rw [dif_neg h_nle, dif_neg h_n, dif_pos h_lt]

    theorem logRem_of_lt {b n : ℕ₀} (h_b : lt₀ 𝟙 b) (h_n : n ≠ 𝟘) (h_lt : lt₀ n b) :
        logRem b n = sub n 𝟙 := by
      unfold logRem logMod
      have h_nle : ¬(le₀ b 𝟙) := (nle_iff_gt b 𝟙).mpr h_b
      rw [dif_neg h_nle, dif_neg h_n, dif_pos h_lt]

    theorem log_one {b : ℕ₀} (h_b : lt₀ 𝟙 b) : log b 𝟙 = 𝟘 :=
      log_of_lt h_b (succ_neq_zero 𝟘) h_b

    theorem logRem_one {b : ℕ₀} (h_b : lt₀ 𝟙 b) : logRem b 𝟙 = 𝟘 := by
      unfold logRem logMod
      have h_nle : ¬(le₀ b 𝟙) := (nle_iff_gt b 𝟙).mpr h_b
      rw [dif_neg h_nle]
      -- The condition is `one = 𝟘` (≠ `σ 𝟘 = 𝟘` syntactically)
      have h_one_ne : one ≠ 𝟘 := succ_neq_zero 𝟘
      rw [dif_neg h_one_ne, dif_pos h_b, sub_self]


    /-!
    ## § 4. Specification theorem
    !-/

    /--
      Main specification: `n = b^(log b n) + logRem b n` when `b > 1` and `n ≠ 0`.
    -/
    theorem logMod_spec {b n : ℕ₀} (h_b : lt₀ 𝟙 b) (h_n : n ≠ 𝟘) :
        n = add (pow b (logMod b n).1) (logMod b n).2 := by
      induction n using well_founded_lt.induction
      rename_i n ih
      unfold logMod
      have h_nle : ¬(le₀ b 𝟙) := (nle_iff_gt b 𝟙).mpr h_b
      rw [dif_neg h_nle, dif_neg h_n]
      if h_lt : lt₀ n b then
        rw [dif_pos h_lt, pow_zero, add_comm]
        exact (sub_k_add_k n 𝟙 (one_le_of_ne_zero h_n)).symm
      else
        rw [dif_neg h_lt]
        simp only
        have h_b_ne_0 : b ≠ 𝟘 := b_neq_zero_of_gt_one h_b
        have h_div_lt : lt₀ (n / b) n := div_lt_self n b h_b h_n
        have h_div_ne_0 : (n / b) ≠ 𝟘 := div_ne_zero_of_ge h_b h_lt h_n
        have h_ih := ih (n / b) h_div_lt h_div_ne_0
        -- Work backwards from goal to divMod_spec:
        -- Goal: n = b^(σ k) + (r*b + n%b)
        -- ← pow_succ: b^(σ k) = (b^k)*b
        -- ← add_assoc: (b^k)*b + (r*b + n%b) = ((b^k)*b + r*b) + n%b
        -- ← add_mul: (b^k)*b + r*b = (b^k + r)*b
        -- ← h_ih: b^k + r = n/b
        -- => goal = (n/b)*b + n%b = n (divMod_spec)
        rw [pow_succ, add_assoc, ← add_mul, ← h_ih]
        exact divMod_spec n b h_b_ne_0


    /-!
    ## § 5. Upper bound
    !-/

    /--
      Upper bound: `n < b^(⌊log_b(n)⌋ + 1)` when `b > 1` and `n ≠ 0`.
    -/
    theorem log_upper_bound {b n : ℕ₀} (h_b : lt₀ 𝟙 b) (h_n : n ≠ 𝟘) :
        lt₀ n (pow b (σ (logMod b n).1)) := by
      induction n using well_founded_lt.induction
      rename_i n ih
      unfold logMod
      have h_nle : ¬(le₀ b 𝟙) := (nle_iff_gt b 𝟙).mpr h_b
      rw [dif_neg h_nle, dif_neg h_n]
      if h_lt : lt₀ n b then
        rw [dif_pos h_lt]
        simp only []
        -- Goal: lt₀ n (pow b (σ 𝟘))
        -- Use pow_succ + pow_zero + one_mul to avoid `pow_one` notation mismatch
        rw [pow_succ, pow_zero, one_mul]
        exact h_lt
      else
        rw [dif_neg h_lt]
        dsimp only []
        have h_b_ne_0 : b ≠ 𝟘 := b_neq_zero_of_gt_one h_b
        have h_div_lt : lt₀ (n / b) n := div_lt_self n b h_b h_n
        have h_div_ne_0 : (n / b) ≠ 𝟘 := div_ne_zero_of_ge h_b h_lt h_n
        have h_ih_ub := ih (n / b) h_div_lt h_div_ne_0
        have h_dm := divMod_spec n b h_b_ne_0
        have h_mod_lt := mod_lt n b h_b_ne_0
        unfold mod at h_mod_lt
        unfold div at h_ih_ub
        -- Step 1: n < mul (σ (divMod n b).fst) b
        have h_n_lt_succ_mul : lt₀ n (mul (σ (divMod n b).fst) b) := by
          rw [succ_mul]
          calc n
              = add (mul (divMod n b).fst b) (divMod n b).snd := h_dm
            _ < add (mul (divMod n b).fst b) b :=
                (add_lt_add_left_iff (mul (divMod n b).fst b) (divMod n b).snd b).mpr h_mod_lt
        -- Step 2: le₀ (σ (divMod n b).fst) (pow b (σ k))
        --   From h_ih_ub: lt₀ x y, and le₀ (σ x) y ↔ lt₀ (σ x) (σ y) = lt₀ x y
        have h_succ_le : le₀ (σ (divMod n b).fst)
            (pow b (σ (logMod b (divMod n b).fst).fst)) :=
          (le_iff_lt_succ (σ (divMod n b).fst)
            (pow b (σ (logMod b (divMod n b).fst).fst))).mpr h_ih_ub
        -- Combine: n < (σ q)*b ≤ b^(σ k)*b = b^(σ (σ k))
        rw [pow_succ]
        exact lt_of_lt_of_le h_n_lt_succ_mul (mul_le_mono_right b h_succ_le)



    /-!
    ## § 6. Ceiling logarithm (clog)

    `clog b n` returns `⌈log_b(n)⌉`:
    - If `n` is an exact power of `b`, `clog b n = log b n`.
    - Otherwise, `clog b n = log b n + 1`.
    !-/

    private theorem sub_succ_one (k : ℕ₀) : sub (σ k) 𝟙 = k := by
      rw [← one_add k, add_k_sub_k]

    private theorem succ_sub_one' (n : ℕ₀) (h : n ≠ 𝟘) : σ (sub n 𝟙) = n := by
      cases n with
      | zero => exact absurd rfl h
      | succ n' => rw [sub_succ_one n']

    /-- Ceiling logarithm: `⌈log_b(n)⌉`. -/
    def clog (b n : ℕ₀) : ℕ₀ :=
      if logRem b n = 𝟘 then log b n else σ (log b n)

    theorem clog_zero (b : ℕ₀) : clog b 𝟘 = 𝟘 := by
      unfold clog
      rw [logRem_zero, if_pos rfl, log_zero]

    theorem clog_one {b : ℕ₀} (h_b : lt₀ 𝟙 b) : clog b 𝟙 = 𝟘 := by
      unfold clog
      rw [logRem_one h_b, if_pos rfl, log_one h_b]

    /-- `n ≤ b^⌈log_b(n)⌉` — ceiling log gives an exponent at least as large. -/
    theorem le_clog_pow {b n : ℕ₀} (h_b : lt₀ 𝟙 b) (h_n : n ≠ 𝟘) :
        le₀ n (pow b (clog b n)) := by
      by_cases h_rem : logRem b n = 𝟘
      · -- Exact power: clog = log, n = b^(log b n)
        have h_clog : clog b n = log b n := by unfold clog; rw [if_pos h_rem]
        rw [h_clog]
        unfold log
        unfold logRem at h_rem
        have h_spec := logMod_spec h_b h_n
        rw [h_rem, add_zero] at h_spec
        exact (le_iff_lt_or_eq n (pow b (logMod b n).1)).mpr (Or.inr h_spec)
      · -- Not exact power: clog = σ (log b n), use log_upper_bound
        have h_clog : clog b n = σ (log b n) := by unfold clog; rw [if_neg h_rem]
        rw [h_clog]
        unfold log
        exact (le_iff_lt_or_eq n (pow b (σ (logMod b n).1))).mpr
              (Or.inl (log_upper_bound h_b h_n))

    /-- `⌈log_b(n)⌉ ≠ 0 → b^(⌈log_b(n)⌉ − 1) < n` — ceiling is tight from below. -/
    theorem clog_lower {b n : ℕ₀} (h_b : lt₀ 𝟙 b) (h_n : n ≠ 𝟘)
        (h : clog b n ≠ 𝟘) : lt₀ (pow b (sub (clog b n) 𝟙)) n := by
      by_cases h_rem : logRem b n = 𝟘
      · -- clog = log b n ≠ 𝟘, n = b^(log b n) exactly
        have h_clog : clog b n = log b n := by unfold clog; rw [if_pos h_rem]
        rw [h_clog] at h ⊢
        unfold log at h ⊢
        unfold logRem at h_rem
        have h_spec := logMod_spec h_b h_n
        rw [h_rem, add_zero] at h_spec
        have h_succ_pred := succ_sub_one' (logMod b n).1 h
        have h_b_ne := b_neq_zero_of_gt_one h_b
        have h_lt_mul := mul_lt_left (pow b (sub (logMod b n).1 𝟙)) b
          (pow_ne_zero h_b_ne _) h_b
        rw [← pow_succ, h_succ_pred, ← h_spec] at h_lt_mul
        exact h_lt_mul
      · -- clog = σ (log b n), logRem ≠ 0
        have h_clog : clog b n = σ (log b n) := by unfold clog; rw [if_neg h_rem]
        rw [h_clog, sub_succ_one]
        unfold log
        unfold logRem at h_rem
        have h_spec := logMod_spec h_b h_n
        have h_lt :=
          (add_lt_add_left_iff (pow b (logMod b n).1) 𝟘 (logMod b n).2).mpr
          (neq_0_then_lt_0 h_rem)
        rw [add_zero, ← h_spec] at h_lt
        exact h_lt


  end Log
end Peano


-- § Exports
export Peano.Log (
  logMod
  log
  logRem
  log_zero
  logRem_zero
  log_of_lt
  logRem_of_lt
  log_one
  logRem_one
  logMod_spec
  log_upper_bound
  clog
  clog_zero
  clog_one
  le_clog_pow
  clog_lower
)
