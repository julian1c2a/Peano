/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Sqrt.lean

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Combinatorics.Pow

set_option autoImplicit false

namespace Peano
  open Peano

  namespace Sqrt
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.WellFounded
    open Peano.Add
    open Peano.Sub
    open Peano.Mul
    open Peano.Pow


    /-!
    ## § 1. Auxiliary lemmas
    !-/

    private theorem one_le_of_ne_zero' {n : ℕ₀} (h : n ≠ 𝟘) : Le 𝟙 n := by
      cases n with
      | zero => exact absurd rfl h
      | succ n' =>
        cases n' with
        | zero => exact Or.inr rfl
        | succ _ => exact Or.inl (by unfold Lt; trivial)

    private theorem succ_sub_one (n : ℕ₀) (h : n ≠ 𝟘) : σ (sub n 𝟙) = n := by
      cases n with
      | zero => exact absurd rfl h
      | succ n' =>
        have h_le : Le 𝟙 (σ n') := one_le_of_ne_zero' (succ_neq_zero n')
        have h_eq := sub_k_add_k (σ n') 𝟙 h_le
        rw [← add_one]
        exact h_eq


    /-!
    ## § 2. Integer square root with remainder

    `sqrtMod n` returns `(k, r)` where:
    - `k = ⌊√n⌋` (floor square root)
    - `r = n − k²` (remainder)
    - Spec: `n = k² + r` where `r < 2k + 1` (equivalently `n < (k+1)²`)
    - Exact (n is a perfect square) iff `r = 0`
    !-/

    /--
      Returns `(k, r)` where `k = ⌊√n⌋` and `r = n − k²`.
      Uses the identity: if `√(n−1) = k` with remainder `r`, then `√n = k` with remainder `σ r`
      unless `σ r = 2k + 1`, in which case `√n = k + 1` with remainder `0`.
    -/
    def sqrtMod (n : ℕ₀) : ℕ₀ × ℕ₀ :=
      if h_n : n = 𝟘 then (𝟘, 𝟘)
      else
        have _h_term : Lt (sub n 𝟙) n :=
          sub_lt_self n 𝟙 (one_le_of_ne_zero' h_n) (succ_neq_zero 𝟘)
        let p : ℕ₀ × ℕ₀ := sqrtMod (sub n 𝟙)
        if σ p.2 = add (add p.1 p.1) 𝟙 then
          (σ p.1, 𝟘)
        else
          (p.1, σ p.2)
    termination_by n
    decreasing_by
      simp_wf
      exact (isomorph_Ψ_lt (sub n 𝟙) n).mp _h_term

    def sqrt (n : ℕ₀) : ℕ₀ := (sqrtMod n).1

    def sqrtRem (n : ℕ₀) : ℕ₀ := (sqrtMod n).2


    /-!
    ## § 3. Basic properties
    !-/

    theorem sqrt_zero : sqrt 𝟘 = 𝟘 := by
      unfold sqrt sqrtMod
      rw [dif_pos rfl]

    theorem sqrtRem_zero : sqrtRem 𝟘 = 𝟘 := by
      unfold sqrtRem sqrtMod
      rw [dif_pos rfl]

    theorem sqrt_one :
        sqrt 𝟙 = 𝟙
          := by
      unfold sqrt sqrtMod
      have h_one_ne : one ≠ 𝟘 := succ_neq_zero 𝟘
      rw [dif_neg h_one_ne]
      simp only
      have h_sub : sub one one = 𝟘 := sub_self one
      rw [h_sub]
      unfold sqrtMod
      rw [dif_pos rfl]
      simp only
      rw [add_zero, zero_add]
      split
      next => rfl
      next h => exact absurd rfl h

    theorem sqrtRem_one :
        sqrtRem 𝟙 = 𝟘
          := by
      unfold sqrtRem sqrtMod
      have h_one_ne : one ≠ 𝟘 := succ_neq_zero 𝟘
      rw [dif_neg h_one_ne]
      simp only
      have h_sub : sub one one = 𝟘 := sub_self one
      rw [h_sub]
      unfold sqrtMod
      rw [dif_pos rfl]
      simp only
      rw [add_zero, zero_add]
      split
      next => rfl
      next h => exact absurd rfl h


    /-!
    ## § 4. Key identity: (k+1)² = k² + (2k + 1)
    !-/

    private theorem succ_sq
      (k : ℕ₀) :
        pow (σ k) 𝟚 = add (pow k 𝟚) (add (add k k) 𝟙)
          := by
      rw [pow_two (σ k), pow_two k]
      rw [mul_succ (σ k) k, succ_mul k k]
      rw [← add_assoc (mul k k) k (σ k)]
      congr 1


    /-!
    ## § 5. Specification theorem
    !-/

    /--
      Main specification: `n = (sqrt n)² + sqrtRem n`.
    -/
    theorem sqrtMod_spec
      (n : ℕ₀) :
        n = add (pow (sqrtMod n).1 𝟚) (sqrtMod n).2
          := by
      induction n using well_founded_lt.induction
      rename_i n ih
      unfold sqrtMod
      if h_n : n = 𝟘 then
        rw [dif_pos h_n]
        simp only []
        rw [h_n, pow_two, mul_zero, add_zero]
      else
        rw [dif_neg h_n]
        simp only
        have h_term : Lt (sub n 𝟙) n :=
          sub_lt_self n 𝟙 (one_le_of_ne_zero' h_n) (succ_neq_zero 𝟘)
        have h_ih := ih (sub n 𝟙) h_term
        if h_eq : σ (sqrtMod (sub n 𝟙)).2 = add (add (sqrtMod (sub n 𝟙)).1 (sqrtMod (sub n 𝟙)).1) 𝟙 then
          rw [if_pos h_eq]
          simp only []
          rw [add_zero, succ_sq, ← h_eq, add_succ, ← h_ih]
          exact (succ_sub_one n h_n).symm
        else
          rw [if_neg h_eq]
          simp only []
          rw [add_succ, ← h_ih]
          exact (succ_sub_one n h_n).symm


    /-!
    ## § 6. Bounds
    !-/

    /--
      Remainder bound: the remainder `r` satisfies `r < 2k + 1`.
    -/
    theorem sqrtRem_lt
      (n : ℕ₀) :
        Lt (sqrtMod n).2 (add (add (sqrtMod n).1 (sqrtMod n).1) 𝟙)
          := by
      induction n using well_founded_lt.induction
      rename_i n ih
      unfold sqrtMod
      if h_n : n = 𝟘 then
        rw [dif_pos h_n]
        simp only []
        rw [add_zero, zero_add]
        exact neq_0_then_lt_0 (succ_neq_zero 𝟘)
      else
        rw [dif_neg h_n]
        simp only
        have h_term : Lt (sub n 𝟙) n :=
          sub_lt_self n 𝟙 (one_le_of_ne_zero' h_n) (succ_neq_zero 𝟘)
        have h_ih_rem := ih (sub n 𝟙) h_term
        if h_eq : σ (sqrtMod (sub n 𝟙)).2 = add (add (sqrtMod (sub n 𝟙)).1 (sqrtMod (sub n 𝟙)).1) 𝟙 then
          rw [if_pos h_eq]
          simp only []
          rw [add_one]
          exact neq_0_then_lt_0 (succ_neq_zero _)
        else
          rw [if_neg h_eq]
          simp only []
          rw [add_one] at h_ih_rem h_eq ⊢
          have h_le := (lt_succ_iff_lt_or_eq_alt _ _).mp h_ih_rem
          cases h_le with
          | inl h_lt => exact h_lt
          | inr h_r_eq => exact absurd (h_r_eq ▸ rfl) h_eq

    /--
      Upper bound: `n < (sqrt n + 1)²`.
    -/
    theorem sqrt_upper_bound
      (n : ℕ₀) :
        Lt n (pow (σ (sqrtMod n).1) 𝟚)
          := by
      have h_spec := sqrtMod_spec n
      have h_rem := sqrtRem_lt n
      have h_lt_add : Lt (add (pow (sqrtMod n).1 𝟚) (sqrtMod n).2)
                         (add (pow (sqrtMod n).1 𝟚) (add (add (sqrtMod n).1 (sqrtMod n).1) 𝟙)) :=
        (add_lt_add_left_iff _ _ _).mpr h_rem
      rw [← succ_sq] at h_lt_add
      rw [← h_spec] at h_lt_add
      exact h_lt_add


  end Sqrt
end Peano


-- § Exports
export Peano.Sqrt (
  sqrtMod
  sqrt
  sqrtRem
  sqrt_zero
  sqrtRem_zero
  sqrt_one
  sqrtRem_one
  sqrtMod_spec
  sqrtRem_lt
  sqrt_upper_bound
)
