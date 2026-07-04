/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatDiv.lean

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Lattice
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul


namespace Peano
  open Peano

  namespace Div
      open Peano.Axioms
      open Peano.StrictOrder
      open Peano.Order
      open Peano.Lattice
      open Peano.WellFounded
      open Peano.Add
      open Peano.Sub
      open Peano.Mul


    /-!
    Performs Euclidean division of `a` by `b`.
    Returns a pair `(quotient, remainder)` such that `a = quotient * b + remainder`
    and `remainder < b` (if `b ≠ 𝟘`).
    If `b = 𝟘`, returns `(𝟘, 𝟘)`.
    !--/

    -- Definimos un lema para conectar `lt₀` con `sizeOf` para la prueba de terminación.
    theorem lt_sizeOf (a b : ℕ₀) : lt₀ a b → sizeOf a < sizeOf b := by
      intro h_lt
      -- `sizeOf` se define como `Ψ` en PeanoNatWellFounded.lean
      exact (isomorph_Ψ_lt a b).mp h_lt

    def divMod (a b : ℕ₀) : ℕ₀ × ℕ₀ :=
      if h_b_is_zero : b = 𝟘 then (𝟘, 𝟘)
      else
        if h_a_is_zero : a = 𝟘 then  (𝟘, 𝟘)
        else
          if h_b_is_one : b = 𝟙 then (a, 𝟘)
          else -- h_b_is_one : b ≠ 𝟙 (y también h_b_is_zero : b ≠ 𝟘 del 'else' anterior)
            if h_a_lt_b : lt₀ a b then
                (𝟘, a)
            else -- h_a_lt_b_false : ¬ (lt₀ a b)
              if h_a_eq_b : a = b then
                (𝟙, 𝟘)
              else
                have h_b_lt_a : lt₀ b a := by
                  apply not_lt_and_not_eq_implies_gt a b
                  exact h_a_lt_b -- Esta es la hipótesis ¬(lt₀ a b)
                  exact h_a_eq_b -- Esta es la hipótesis ¬(a = b)
                have h_le_b_a : le₀ b a := by
                  apply lt_imp_le
                  exact h_b_lt_a
                have h_sub_a_b_lt_a : lt₀ (sub a b) a := by
                  apply sub_lt_self a b
                  exact h_le_b_a -- b ≤ a
                  exact h_b_is_zero -- b ≠ 𝟘
                let (a', b') : ℕ₀ × ℕ₀ := divMod (sub a b) b
                (σ a', b')
    termination_by a
    decreasing_by exact h_sub_a_b_lt_a

    def div (a b : ℕ₀) : ℕ₀ :=
      (divMod a b).1

    def mod (a b : ℕ₀) : ℕ₀ :=
      (divMod a b).2

    instance : Div ℕ₀ where
      div := Div.div

    instance : Mod ℕ₀ where
      mod := Div.mod

    @[simp] theorem div_def (a b : ℕ₀) : a / b = div a b := rfl
    @[simp] theorem mod_def (a b : ℕ₀) : a % b = mod a b := rfl

    /--
      Teorema general de la división euclídea.
    -/
    theorem divMod_spec (a b : ℕ₀) : b ≠ 𝟘 → a = add (mul (divMod a b).1 b) (divMod a b).2 := by
      intro h_b_neq_0
      induction a using well_founded_lt.induction
      rename_i a ih
      unfold divMod
      if h_b_zero : b = 𝟘 then
        exact False.elim (h_b_neq_0 h_b_zero)
      else
        rw [dif_neg h_b_zero]
        if h_a_zero : a = 𝟘 then
          rw [dif_pos h_a_zero, h_a_zero, zero_mul, zero_add]
        else
          rw [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            rw [dif_pos h_b_one]
            simp only
            rw [h_b_one, mul_one, add_zero]
          else
            rw [dif_neg h_b_one]
            if h_a_lt_b : lt₀ a b then
              rw [dif_pos h_a_lt_b, zero_mul, zero_add]
            else
              rw [dif_neg h_a_lt_b]
              if h_a_eq_b : a = b then
                rw [dif_pos h_a_eq_b, one_mul, add_zero]
                exact h_a_eq_b
              else
                rw [dif_neg h_a_eq_b]
                have h_b_lt_a : lt₀ b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
                have h_le_b_a : le₀ b a := lt_imp_le b a h_b_lt_a
                have h_sub_lt_a : lt₀ (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0
                have h_ih_call := ih (sub a b) h_sub_lt_a
                simp only [succ_mul]
                have h_divmod_eq : (divMod (sub a b) b) = ((divMod (sub a b) b).1, (divMod (sub a b) b).2) := by simp
                rw [h_divmod_eq]
                simp only
                rw [←add_assoc]
                rw [add_comm b ((divMod (sub a b) b).2)]
                rw [add_assoc]
                rw [←h_ih_call]
                exact (sub_k_add_k a b h_le_b_a).symm

    /--
      El resto de la división siempre es menor que el divisor.
    -/
    theorem mod_lt (a b : ℕ₀) (h_b_neq_0 : b ≠ 𝟘) :
      lt₀ (a % b) b := by
      induction a using well_founded_lt.induction
      rename_i a ih
      show lt₀ (mod a b) b
      unfold mod divMod
      if h_b_zero : b = 𝟘 then
        exact False.elim (h_b_neq_0 h_b_zero)
      else
        rw [dif_neg h_b_zero]
        if h_a_zero : a = 𝟘 then
          rw [dif_pos h_a_zero]
          exact neq_0_then_lt_0 h_b_neq_0
        else
          rw [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            rw [dif_pos h_b_one]
            simp only
            rw [h_b_one]
            exact lt_0_1
          else
            rw [dif_neg h_b_one]
            if h_a_lt_b : lt₀ a b then
              rw [dif_pos h_a_lt_b]
              exact h_a_lt_b
            else
              rw [dif_neg h_a_lt_b]
              if h_a_eq_b : a = b then
                rw [dif_pos h_a_eq_b]
                have h_lt_1_b : lt₀ 𝟙 b := neq_01_then_gt_1 b ⟨h_b_neq_0, h_b_one⟩
                exact lt_trans 𝟘 𝟙 b lt_0_1 h_lt_1_b
              else
                rw [dif_neg h_a_eq_b]
                have h_b_lt_a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
                have h_le_b_a := lt_imp_le b a h_b_lt_a
                have h_sub_lt_a := sub_lt_self a b h_le_b_a h_b_neq_0
                exact ih (sub a b) h_sub_lt_a

    /--
      El cociente de la división de `a` por `b` es menor o igual que `a`.
    -/
    theorem div_le_self (a b : ℕ₀) (h_b_neq_0 : b ≠ 𝟘) :
      le₀ (a / b) a := by
      let q := a / b
      have h_eq := divMod_spec a b h_b_neq_0
      have h_qb_le_a : le₀ (mul q b) a := by
        rw [h_eq]
        exact le_self_add_r (mul q b) (a % b)
      if h_b_one : b = 𝟙 then
        rw [h_b_one, mul_one] at h_qb_le_a
        exact h_qb_le_a
      else
        have h_q_le_qb : le₀ q (mul q b) := by
          have h_lt_0_b : lt₀ 𝟘 b := neq_0_then_lt_0 h_b_neq_0
          have h_le_1_b : le₀ 𝟙 b := lt_0_then_le_1 b h_lt_0_b
          exact mul_le_right q b h_b_neq_0
        exact le_trans q (mul q b) a h_q_le_qb h_qb_le_a

    -- Lema auxiliar que faltaba.
    theorem gt_imp_neq_zero_one (b : ℕ₀) (h : lt₀ 𝟙 b) : b ≠ 𝟘 ∧ b ≠ 𝟙 :=
      ⟨lt_1_b_then_b_neq_0 h, lt_1_b_then_b_neq_1 h⟩

    /--
      El cociente de la división de `a` por `b` es estrictamente menor que `a` si `b > 𝟙` y `a ≠ 𝟘`.
    -/
    theorem div_lt_self (a b : ℕ₀) (h_b_gt_1 : lt₀ 𝟙 b) (h_a_neq_0 : a ≠ 𝟘) :
      lt₀ (a / b) a := by
      have ⟨h_b_neq_0, _⟩ := gt_imp_neq_zero_one b h_b_gt_1
      have h_div_le_a : le₀ (a / b) a := div_le_self a b h_b_neq_0
      apply lt_of_le_of_ne (a / b) a h_div_le_a
      intro h_eq_div_a
      have h_div_eq : a = add (mul (a / b) b) (a % b) := by
        simpa [div, mod] using (divMod_spec a b h_b_neq_0)
      have h_mul_lt : lt₀ a (mul a b) := mul_lt_left a b h_a_neq_0 h_b_gt_1
      have h_mul_le : le₀ (mul a b) a := by
        rw [h_eq_div_a] at h_div_eq
        have h_mul_le_sum : le₀ (mul a b) (add (mul a b) (a % b)) :=
          le_self_add_r (mul a b) (a % b)
        have h_sum_le_a : le₀ (add (mul a b) (a % b)) a :=
          le_of_eq (add (mul a b) (a % b)) a h_div_eq.symm
        exact le_trans (mul a b) (add (mul a b) (a % b)) a h_mul_le_sum h_sum_le_a
      have h_lt_a_a : lt₀ a a := lt_of_lt_of_le h_mul_lt h_mul_le
      exact lt_irrefl a h_lt_a_a

    /--
      Si `a < b`, el cociente es 0.
    -/
    theorem div_of_lt (a b : ℕ₀) (h_lt : lt₀ a b) :
      (a / b) = 𝟘 := by
      show div a b = 𝟘
      unfold div divMod
      if h_b_zero : b = 𝟘 then
        have h_a_lt_zero : lt₀ a 𝟘 := by rw [h_b_zero] at h_lt; exact h_lt
        exact (nlt_n_0 a h_a_lt_zero).elim
      else
        rw [dif_neg h_b_zero]
        if h_a_zero : a = 𝟘 then
          rw [dif_pos h_a_zero]
        else
          rw [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            have h_a_lt_one : lt₀ a 𝟙 := by rw [h_b_one] at h_lt; exact h_lt
            have h_a_eq_zero : a = 𝟘 := lt_b_1_then_b_eq_0 h_a_lt_one
            exact (h_a_zero h_a_eq_zero).elim
          else
            rw [dif_neg h_b_one]
            rw [dif_pos h_lt]

    /--
      Si `a < b`, el resto es `a`.
    -/
    theorem mod_of_lt (a b : ℕ₀) (h_lt : lt₀ a b) :
      (a % b) = a := by
      show mod a b = a
      unfold mod divMod
      if h_b_zero : b = 𝟘 then
        have h_a_lt_zero : lt₀ a 𝟘 := by rw [h_b_zero] at h_lt; exact h_lt
        exact (nlt_n_0 a h_a_lt_zero).elim
      else
        rw [dif_neg h_b_zero]
        if h_a_zero : a = 𝟘 then
          rw [dif_pos h_a_zero]
          simp only
          exact h_a_zero.symm
        else
          rw [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            have h_a_lt_one : lt₀ a 𝟙 := by
              rw [h_b_one] at h_lt
              exact h_lt
            have h_a_eq_zero : a = 𝟘 := lt_b_1_then_b_eq_0 h_a_lt_one
            exact (h_a_zero h_a_eq_zero).elim
          else
            rw [dif_neg h_b_one]
            rw [dif_pos h_lt]


    /--
      Si `b ≤ a < 2 * b`, el cociente es 1.
    -/
    theorem div_of_lt_fst_interval (a b : ℕ₀) (h_le : le₀ b a) (h_a_lt_2b : lt₀ a (add b b)) :
      (a / b) = 𝟙 := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero, add_zero] at h_a_lt_2b
        exact (nlt_n_0 a h_a_lt_2b).elim
      let q := a / b
      have h_a_eq_qbr : a = add (mul q b) (a % b) := by
        simpa [div, mod, q] using (divMod_spec a b h_b_neq_0)
      have h_r_lt_b : lt₀ (a % b) b := mod_lt a b h_b_neq_0
      -- Probamos `q ≥ 1`
      have h_q_ge_1 : le₀ 𝟙 q := by
        cases h_q : q with
        | zero =>
          have h_a_eq_r : a = a % b := by
            rw [h_q] at h_a_eq_qbr
            simp [zero_mul, zero_add] at h_a_eq_qbr
            exact h_a_eq_qbr
          have h_a_lt_b : lt₀ a b := by
            simpa [h_a_eq_r.symm] using h_r_lt_b
          exact (nlt_of_le h_le h_a_lt_b).elim
        | succ q' =>
          exact le_1_succ q'
      -- Probamos `q < 2`
      have h_q_lt_2 : lt₀ q 𝟚 := by
        apply nle_then_gt_wp
        intro h_q_ge_2
        have h_2b_le_qb : le₀ (mul 𝟚 b) (mul q b) := mul_le_mono_right b h_q_ge_2
        rw [two_mul] at h_2b_le_qb
        have h_2b_le_a : le₀ (add b b) a := by
          rw [h_a_eq_qbr]
          exact le_trans (add b b) (mul q b) (add (mul q b) (a % b)) h_2b_le_qb (le_self_add_r _ _)
        exact nlt_of_le h_2b_le_a h_a_lt_2b
      -- Si `1 ≤ q` y `q < 2`, entonces `q = 1`.
      have h_q_le_1 : le₀ q 𝟙 := lt_then_le_succ_wp h_q_lt_2
      have h_q_eq : q = 𝟙 := le_antisymm q 𝟙 h_q_le_1 h_q_ge_1
      simpa [q] using h_q_eq

    /--
      Si `2 * b ≤ a < 3 * b`, el cociente es 2.
    -/
    theorem div_eq_two (a b : ℕ₀) (h_le : le₀ (add b b) a) (h_a_lt_3b : lt₀ a (add (add b b) b)) :
      (a / b) = 𝟚 := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero, add_zero] at h_a_lt_3b
        exact (nlt_n_0 a h_a_lt_3b).elim
      let q := a / b
      let r := a % b
      have h_a_eq_qbr : a = add (mul q b) r := by
        simpa [div, mod, q, r] using (divMod_spec a b h_b_neq_0)
      have h_r_lt_b : lt₀ r b := mod_lt a b h_b_neq_0
      -- Probamos `q ≥ 2`
      have h_q_ge_2 : le₀ 𝟚 q := by
        have h_q_gt_1 : lt₀ 𝟙 q := by
          apply nle_then_gt_wp
          intro h_q_le_1
          have h_q_eq := le_m_1_then_m_eq_0or1_wp h_q_le_1
          cases h_q_eq with
          | inl h_q_zero =>
            have h_a_eq_r : a = r := by
              rw [h_q_zero] at h_a_eq_qbr
              simp [zero_mul, zero_add] at h_a_eq_qbr
              exact h_a_eq_qbr
            have h_a_lt_b : lt₀ a b := by
              simpa [h_a_eq_r.symm] using h_r_lt_b
            have h_a_lt_2b : lt₀ a (add b b) := add_lt a b b h_a_lt_b
            exact (nlt_of_le h_le h_a_lt_2b).elim
          | inr h_q_one =>
            have h_a_eq_br : a = add b r := by
              rw [h_q_one] at h_a_eq_qbr
              simp [one_mul] at h_a_eq_qbr
              exact h_a_eq_qbr
            have h_a_lt_2b : lt₀ a (add b b) := by
              rw [h_a_eq_br]
              exact (add_lt_add_left_iff b r b).mpr h_r_lt_b
            exact (nlt_of_le h_le h_a_lt_2b).elim
        exact lt_then_le_succ_wp h_q_gt_1
      -- Probamos `q < 3`
      have h_q_lt_3 : lt₀ q 𝟛 := by
        apply nle_then_gt_wp
        intro h_q_ge_3
        have h_3b_le_qb : le₀ (mul 𝟛 b) (mul q b) := mul_le_mono_right b h_q_ge_3
        rw [three_mul] at h_3b_le_qb
        have h_3b_le_a : le₀ (add (add b b) b) a := by
          rw [h_a_eq_qbr]
          exact le_trans (add (add b b) b) (mul q b) (add (mul q b) r) h_3b_le_qb (le_self_add_r _ _)
        exact nlt_of_le h_3b_le_a h_a_lt_3b
      -- Si `2 ≤ q` y `q < 3`, entonces `q = 2`.
      have h_q_le_2 : le₀ q 𝟚 := lt_then_le_succ_wp h_q_lt_3
      have h_q_eq : q = 𝟚 := le_antisymm q 𝟚 h_q_le_2 h_q_ge_2
      simpa [q] using h_q_eq



    theorem le___mul__div_a_b__b____a (a b : ℕ₀) (h_b_neq_0 : b ≠ 𝟘) :
      le₀ (mul (div a b) b) a
        := by
      have h_eq : a = add (mul (div a b) b) (a % b) := by
        simpa [div, mod] using (divMod_spec a b h_b_neq_0)
      have h_le_sum : le₀ (mul (div a b) b) (add (mul (div a b) b) (a % b)) :=
        le_self_add_r (mul (div a b) b) (a % b)
      have h_sum_le_a : le₀ (add (mul (div a b) b) (a % b)) a :=
        le_of_eq (add (mul (div a b) b) (a % b)) a h_eq.symm
      exact le_trans (mul (div a b) b) (add (mul (div a b) b) (a % b)) a h_le_sum h_sum_le_a

    /--
      Si `a * n ≤ b < a * (σ n)`, entonces `b / a = n`.
    -/
    theorem div_of_lt_nth_interval (a b n : ℕ₀)
      (h_le : le₀ (mul a n) b)
      (h_lt : lt₀ b (mul a (σ n))) :
      (b / a) = n := by
      have h_a_neq_0 : a ≠ 𝟘 := by
        intro h_a_zero
        rw [h_a_zero, zero_mul] at h_lt
        exact (nlt_n_0 b h_lt).elim
      let q := b / a
      have h_div_eq : b = add (mul q a) (b % a) := by
        simpa [div, mod, q] using (divMod_spec b a h_a_neq_0)
      have h_r_lt_a : lt₀ (b % a) a := mod_lt b a h_a_neq_0

      have h_q_le_n : le₀ q n := by
        by_cases h_q_le_n : le₀ q n
        · exact h_q_le_n
        · have h_n_lt_q : lt₀ n q := nle_then_gt_wp h_q_le_n
          have h_succn_le_q : le₀ (σ n) q := lt_then_le_succ_wp h_n_lt_q
          have h_mul_le : le₀ (mul (σ n) a) (mul q a) := mul_le_mono_right a h_succn_le_q
          have h_mul_le_b : le₀ (mul q a) b := by
            rw [h_div_eq]
            exact le_self_add_r (mul q a) (b % a)
          have h_a_succn_le_b : le₀ (mul (σ n) a) b :=
            le_trans (mul (σ n) a) (mul q a) b h_mul_le h_mul_le_b
          have h_b_lt_a_succn : lt₀ b (mul (σ n) a) := by
            simpa [mul_comm] using h_lt
          exact (False.elim (nlt_of_le h_a_succn_le_b h_b_lt_a_succn))

      have h_n_le_q : le₀ n q := by
        by_cases h_n_le_q : le₀ n q
        · exact h_n_le_q
        · have h_q_lt_n : lt₀ q n := nle_then_gt_wp h_n_le_q
          obtain ⟨d, h_n_eq⟩ := (lt_iff_exists_add_succ q n).mp h_q_lt_n
          have h_b_lt_add : lt₀ b (add (mul q a) a) := by
            rw [h_div_eq]
            exact (add_lt_add_left_iff (mul q a) (b % a) a).mpr h_r_lt_a
          have h_add_le_mul_n : le₀ (add (mul q a) a) (mul n a) := by
            rw [h_n_eq, add_mul]
            have h_a_le_mul : le₀ a (mul (σ d) a) := by
              have h_a_le_mul' : le₀ a (mul a (σ d)) :=
                mul_le_right a (σ d) (succ_neq_zero d)
              simpa [mul_comm] using h_a_le_mul'
            exact add_le_add_left a (mul (σ d) a) (mul q a) h_a_le_mul
          have h_b_lt_mul_n : lt₀ b (mul n a) :=
            lt_of_lt_of_le h_b_lt_add h_add_le_mul_n
          have h_b_lt_mul_a_n : lt₀ b (mul a n) := by
            simpa [mul_comm] using h_b_lt_mul_n
          exact (False.elim (nlt_of_le h_le h_b_lt_mul_a_n))

      have h_q_eq_n : q = n := le_antisymm q n h_q_le_n h_n_le_q
      simpa [q] using h_q_eq_n

    /--
      Si `b ≤ a < 2 * b`, el resto es `a - b`.
    -/
    theorem mod_of_lt_fst_interval (a b : ℕ₀) (h_le : le₀ b a) (h_a_lt_2b : lt₀ a (add b b)) :
      (a % b) = sub a b := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero, add_zero] at h_a_lt_2b
        exact (nlt_n_0 a h_a_lt_2b).elim
      let r := a % b
      have h_div_eq : a = add (mul (a / b) b) (a % b) := by
        simpa [div, mod] using (divMod_spec a b h_b_neq_0)
      have h_div_eq' : a = add b r := by
        rw [div_of_lt_fst_interval a b h_le h_a_lt_2b] at h_div_eq
        simpa [one_mul, r] using h_div_eq
      have h_sub : sub (add b r) b = r := by
        simpa [r] using (add_k_sub_k r b)
      have h_sub' : r = sub (add b r) b := h_sub.symm
      rw [←h_div_eq'] at h_sub'
      simpa [r] using h_sub'

    /--
      Si `2 * b ≤ a < 3 * b`, el resto es `a - 2 * b`.
    -/
    theorem mod_of_lt_snd_interval (a b : ℕ₀) (h_le : le₀ (add b b) a) (h_a_lt_3b : lt₀ a (add (add b b) b)) :
      (a % b) = sub a (add b b) := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero, add_zero] at h_a_lt_3b
        exact (nlt_n_0 a h_a_lt_3b).elim
      let r := a % b
      have h_div_eq : a = add (mul (a / b) b) (a % b) := by
        simpa [div, mod] using (divMod_spec a b h_b_neq_0)
      have h_div_eq' : a = add (add b b) r := by
        rw [div_eq_two a b h_le h_a_lt_3b] at h_div_eq
        simpa [two_mul, r] using h_div_eq
      have h_sub : sub (add (add b b) r) (add b b) = r := by
        simpa [r] using (add_k_sub_k r (add b b))
      have h_sub' : r = sub (add (add b b) r) (add b b) := h_sub.symm
      rw [←h_div_eq'] at h_sub'
      simpa [r] using h_sub'

    /--
      Si `a * n ≤ b < a * (σ n)`, el resto es `b - a * n`.
    -/
    theorem mod_of_lt_nth_interval (a b n : ℕ₀)
      (h_le : le₀ (mul a n) b)
      (h_lt : lt₀ b (mul a (σ n))) :
      (b % a) = sub b (mul a n) := by
      have h_a_neq_0 : a ≠ 𝟘 := by
        intro h_a_zero
        rw [h_a_zero, zero_mul] at h_lt
        exact (nlt_n_0 b h_lt).elim
      let r := b % a
      have h_div_eq : b = add (mul (b / a) a) (b % a) := by
        simpa [div, mod] using (divMod_spec b a h_a_neq_0)
      have h_div_eq' : b = add (mul a n) r := by
        rw [div_of_lt_nth_interval a b n h_le h_lt] at h_div_eq
        simpa [mul_comm, r] using h_div_eq
      have h_sub : sub (add (mul a n) r) (mul a n) = r := by
        simpa [r] using (add_k_sub_k r (mul a n))
      have h_sub' : r = sub (add (mul a n) r) (mul a n) := h_sub.symm
      rw [←h_div_eq'] at h_sub'
      simpa [r] using h_sub'

    /--
      Teorema 1: Unicidad del cociente y resto.
    -/
    theorem div_mod_unique (a b q1 r1 q2 r2 : ℕ₀) (hb : b ≠ 𝟘)
      (h1 : a = add (mul q1 b) r1) (hr1 : lt₀ r1 b)
      (h2 : a = add (mul q2 b) r2) (hr2 : lt₀ r2 b) : q1 = q2 := by
      have h_tri := trichotomy q1 q2
      cases h_tri with
      | inl h_lt12 =>
        have hr1_add : lt₀ (add (mul q1 b) r1) (add (mul q1 b) b) := (add_lt_add_left_iff (mul q1 b) r1 b).mpr hr1
        have h_le_q2 : le₀ (σ q1) q2 := lt_then_le_succ_wp h_lt12
        have h_mul_le : le₀ (mul (σ q1) b) (mul q2 b) := mul_le_mono_right b h_le_q2
        rw [succ_mul] at h_mul_le
        have h_add_le : le₀ (add (mul q1 b) b) (add (mul q2 b) r2) :=
          le_trans (add (mul q1 b) b) (mul q2 b) (add (mul q2 b) r2) h_mul_le (le_self_add_r _ _)
        have h_lt_a : lt₀ (add (mul q1 b) r1) (add (mul q2 b) r2) := lt_of_lt_of_le hr1_add h_add_le
        rw [← h1, ← h2] at h_lt_a
        exact False.elim (lt_irrefl a h_lt_a)
      | inr h_or =>
        cases h_or with
        | inl h_eq => exact h_eq
        | inr h_lt21 =>
          have hr2_add : lt₀ (add (mul q2 b) r2) (add (mul q2 b) b) := (add_lt_add_left_iff (mul q2 b) r2 b).mpr hr2
          have h_le_q1 : le₀ (σ q2) q1 := lt_then_le_succ_wp h_lt21
          have h_mul_le : le₀ (mul (σ q2) b) (mul q1 b) := mul_le_mono_right b h_le_q1
          rw [succ_mul] at h_mul_le
          have h_add_le : le₀ (add (mul q2 b) b) (add (mul q1 b) r1) :=
            le_trans (add (mul q2 b) b) (mul q1 b) (add (mul q1 b) r1) h_mul_le (le_self_add_r _ _)
          have h_lt_a : lt₀ (add (mul q2 b) r2) (add (mul q1 b) r1) := lt_of_lt_of_le hr2_add h_add_le
          rw [← h2, ← h1] at h_lt_a
          exact False.elim (lt_irrefl a h_lt_a)

    /--
      Teorema 2: Igualdad de cocientes por igualdad de productos cruzados.
    -/
    theorem div_eq_of_mul_eq (a b c d : ℕ₀) (hb : b ≠ 𝟘) (hd : d ≠ 𝟘)
      (h : mul a d = mul c b) : a / b = c / d := by
      let qa := a / b
      let ra := a % b
      let qc := c / d
      let rc := c % d
      have ha : a = add (mul qa b) ra := divMod_spec a b hb
      have hc : c = add (mul qc d) rc := divMod_spec c d hd
      have hra : lt₀ ra b := mod_lt a b hb
      have hrc : lt₀ rc d := mod_lt c d hd
      have h_bd_neq_0 : mul b d ≠ 𝟘 := eq_zero_of_mul_eq_zero hb hd

      have h_ad_expanded : mul c b = add (mul qa (mul b d)) (mul ra d) := by
        rw [← h, ha, add_mul, mul_assoc]

      have h_cb_expanded : mul c b = add (mul qc (mul b d)) (mul rc b) := by
        rw [hc, add_mul, mul_assoc, mul_comm d b]

      have h_rad_lt : lt₀ (mul ra d) (mul b d) := by
        have h_or : ra = 𝟘 ∨ ra ≠ 𝟘 := by
          cases ra
          · exact Or.inl rfl
          · exact Or.inr (succ_neq_zero _)
        cases h_or with
        | inl h_zero =>
          rw [h_zero, zero_mul]
          exact neq_0_then_lt_0 h_bd_neq_0
        | inr h_neq =>
          have h_lt : lt₀ (mul d ra) (mul d b) := le_lt_mul_lt_compat (le_refl d) hra h_neq hd
          rw [mul_comm d ra, mul_comm d b] at h_lt
          exact h_lt

      have h_rcb_lt : lt₀ (mul rc b) (mul b d) := by
        rw [mul_comm b d]
        have h_or : rc = 𝟘 ∨ rc ≠ 𝟘 := by
          cases rc
          · exact Or.inl rfl
          · exact Or.inr (succ_neq_zero _)
        cases h_or with
        | inl h_zero =>
          rw [h_zero, zero_mul]
          have h_db_neq_0 : mul d b ≠ 𝟘 := eq_zero_of_mul_eq_zero hd hb
          exact neq_0_then_lt_0 h_db_neq_0
        | inr h_neq =>
          have h_lt : lt₀ (mul b rc) (mul b d) := le_lt_mul_lt_compat (le_refl b) hrc h_neq hb
          rw [mul_comm b rc, mul_comm b d] at h_lt
          exact h_lt

      exact div_mod_unique (mul c b) (mul b d) qa (mul ra d) qc (mul rc b) h_bd_neq_0 h_ad_expanded h_rad_lt h_cb_expanded h_rcb_lt

    -- ═══════════════════════════════════════════════════════════
    -- § Isomorfismo Ψ/Λ para div y mod
    -- ═══════════════════════════════════════════════════════════

    theorem isomorph_Ψ_div (n m : ℕ₀) :
      Ψ (div n m) = Nat.div (Ψ n) (Ψ m)
        := by
      by_cases h_m : m = 𝟘
      · subst h_m
        have h1 : div n 𝟘 = 𝟘 := by simp [div, divMod]
        rw [h1]; exact (Nat.div_zero (Ψ n)).symm
      · have h_eq : n = add (mul (div n m) m) (mod n m) := divMod_spec n m h_m
        have h_transported := congrArg Ψ h_eq
        rw [isomorph_Ψ_add, isomorph_Ψ_mul] at h_transported
        simp only [Nat.add_eq, Nat.mul_eq] at h_transported
        have h_mod_lt := (isomorph_Ψ_lt _ _).mp (mod_lt n m h_m)
        symm
        apply Nat.div_eq_of_lt_le
        · rw [h_transported]; exact Nat.le_add_right _ _
        · rw [h_transported, Nat.add_mul, Nat.one_mul]
          exact Nat.add_lt_add_left h_mod_lt _

    theorem isomorph_Ψ_mod (n m : ℕ₀) (hm : m ≠ 𝟘) :
      Ψ (mod n m) = Nat.mod (Ψ n) (Ψ m)
        := by
      have h_eq : n = add (mul (div n m) m) (mod n m) := divMod_spec n m hm
      have h_transported := congrArg Ψ h_eq
      rw [isomorph_Ψ_add, isomorph_Ψ_mul] at h_transported
      simp only [Nat.add_eq, Nat.mul_eq] at h_transported
      have h_div : Ψ (div n m) = Nat.div (Ψ n) (Ψ m) := isomorph_Ψ_div n m
      rw [h_div] at h_transported
      have h_dam := Nat.div_add_mod (Ψ n) (Ψ m)
      rw [Nat.mul_comm] at h_dam
      exact Nat.add_left_cancel (h_transported.symm.trans h_dam.symm)

    theorem isomorph_Λ_div (n m : Nat) :
      Λ (Nat.div n m) = div (Λ n) (Λ m)
        := by
      have h := isomorph_Ψ_div (Λ n) (Λ m)
      rw [ΨΛ, ΨΛ] at h
      have := congrArg Λ h
      rw [ΛΨ] at this
      exact this.symm

    theorem isomorph_Λ_mod (n m : Nat) (hm : m ≠ 0) :
      Λ (Nat.mod n m) = mod (Λ n) (Λ m)
        := by
      have h := isomorph_Ψ_mod (Λ n) (Λ m) (by rwa [Λ_neq_zero_iff_neq_zero])
      rw [ΨΛ, ΨΛ] at h
      have := congrArg Λ h
      rw [ΛΨ] at this
      exact this.symm

  end Div

end Peano

export Peano.Div (
  divMod
  div
  mod
  div_def
  mod_def
  divMod_spec
  mod_lt
  div_le_self
  div_lt_self
  mod_of_lt
  div_of_lt
  mod_of_lt_fst_interval
  div_eq_two
  mod_of_lt_snd_interval
  div_of_lt_nth_interval
  mod_of_lt_nth_interval
  div_mod_unique
  div_eq_of_mul_eq
  isomorph_Ψ_div
  isomorph_Ψ_mod
  isomorph_Λ_div
  isomorph_Λ_mod
)
