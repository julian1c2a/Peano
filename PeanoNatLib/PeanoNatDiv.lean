-- PeanoNatLib/PeanoNatDiv.lean

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatWellFounded
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatMul


namespace Peano
  open Peano

  namespace Div
      open Peano.Axioms
      open Peano.StrictOrder
      open Peano.Order
      open Peano.MaxMin
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

    -- Definimos un lema para conectar `Lt` con `sizeOf` para la prueba de terminación.
    theorem lt_sizeOf (a b : ℕ₀) : Lt a b → sizeOf a < sizeOf b := by
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
            if h_a_lt_b : Lt a b then
                (𝟘, a)
            else -- h_a_lt_b_false : ¬ (Lt a b)
              if h_a_eq_b : a = b then
                (𝟙, 𝟘)
              else
                have h_b_lt_a : Lt b a := by
                  apply not_lt_and_not_eq_implies_gt a b
                  exact h_a_lt_b -- Esta es la hipótesis ¬(Lt a b)
                  exact h_a_eq_b -- Esta es la hipótesis ¬(a = b)
                have h_le_b_a : Le b a := by
                  apply lt_imp_le
                  exact h_b_lt_a
                have h_sub_a_b_lt_a : Lt (sub a b) a := by
                  apply sub_lt_self a b
                  exact h_le_b_a -- b ≤ a
                  exact h_b_is_zero -- b ≠ 𝟘
                let (a', b') : ℕ₀ × ℕ₀ := divMod (sub a b) b
                (σ a', b')
    termination_by a
    decreasing_by
      simp_wf
      apply lt_sizeOf
      exact h_sub_a_b_lt_a

    def div (a b : ℕ₀) : ℕ₀ :=
      (divMod a b).1

    notation a " / " b => div a b

    def mod (a b : ℕ₀) : ℕ₀ :=
      (divMod a b).2

    notation a " % " b => mod a b

    /--
      Teorema general de la división euclídea.
    -/
    theorem divMod_eq (a b : ℕ₀) : b ≠ 𝟘 → a = add (mul (divMod a b).1 b) (divMod a b).2 := by
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
            rw [dif_pos h_b_one, mul_one, add_zero]
          else
            rw [dif_neg h_b_one]
            if h_a_lt_b : Lt a b then
              rw [dif_pos h_a_lt_b, zero_mul, zero_add]
            else
              rw [dif_neg h_a_lt_b]
              if h_a_eq_b : a = b then
                rw [dif_pos h_a_eq_b, one_mul, add_zero]
              else
                rw [dif_neg h_a_eq_b]
                have h_b_lt_a : Lt b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
                have h_le_b_a : Le b a := lt_imp_le b a h_b_lt_a
                have h_sub_lt_a : Lt (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0
                have h_ih_call := ih (sub a b) h_sub_lt_a
                rw [succ_mul, add_assoc]
                rw [add_comm ((divMod (sub a b) b).2) b, ←add_assoc]
                rw [←h_ih_call]
                exact (sub_k_add_k a b h_le_b_a).symm

    /--
      El resto de la división siempre es menor que el divisor.
    -/
    theorem mod_lt_divisor (a b : ℕ₀) (h_b_neq_0 : b ≠ 𝟘) :
      Lt (a % b) b := by
      induction a using well_founded_lt.induction
      rename_i a ih
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
            if h_a_lt_b : Lt a b then
              rw [dif_pos h_a_lt_b]
              exact h_a_lt_b
            else
              rw [dif_neg h_a_lt_b]
              if h_a_eq_b : a = b then
                rw [dif_pos h_a_eq_b]
                have h_lt_1_b : Lt 𝟙 b := neq_01_then_gt_1 b ⟨h_b_neq_0, h_b_one⟩
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
      Le (a / b) a
        := by
      let q := a / b
      have h_eq := divMod_eq a b h_b_neq_0
      have h_qb_le_a : Le (mul q b) a := by
        rw [h_eq]
        exact le_self_add_r (mul q b) (a % b)
      if h_b_one : b = 𝟙 then
        rw [h_b_one, mul_one] at h_qb_le_a
        exact h_qb_le_a
      else
        have h_q_le_qb : Le q (mul q b) := by
          have h_lt_0_b : Lt 𝟘 b := neq_0_then_lt_0 h_b_neq_0
          have h_le_1_b : Le 𝟙 b := lt_0_then_le_1 b h_lt_0_b
          exact mul_le_right q b h_le_1_b
        exact le_trans q (mul q b) a h_q_le_qb h_qb_le_a

    -- Lema auxiliar que faltaba.
    theorem gt_imp_neq_zero_one (b : ℕ₀) (h : Lt 𝟙 b) :
      b ≠ 𝟘 ∧ b ≠ 𝟙
        :=  ⟨lt_1_b_then_b_neq_0 h, lt_1_b_then_b_neq_1 h⟩

    /--
      El cociente de la división de `a` por `b` es estrictamente menor que `a` si `b > 𝟙` y `a ≠ 𝟘`.
    -/
    theorem div_lt_self (a b : ℕ₀) (h_b_gt_1 : Lt 𝟙 b) (h_a_neq_0 : a ≠ 𝟘) :
      Lt (a / b) a
        := by
      have ⟨h_b_neq_0, _⟩ := gt_imp_neq_zero_one b h_b_gt_1
      have h_div_le_a : Le (a / b) a := div_le_self a b h_b_neq_0
      apply lt_of_le_of_ne h_div_le_a
      intro h_eq_div_a
      have h_div_eq := divMod_eq a b h_b_neq_0
      rw [h_eq_div_a] at h_div_eq
      have h_mul_lt : Lt a (mul a b) := by
        rw [mul_comm]
        exact mul_lt_right a b h_a_neq_0 h_b_gt_1
      have h_mul_le_sum : Le (mul a b) (add (mul a b) (a % b)) :=
        le_self_add_r (mul a b) (a % b)
      rw [←h_div_eq] at h_mul_le_sum
      have h_lt_a_a := lt_of_lt_of_le h_mul_lt h_mul_le_sum
      exact lt_irrefl a h_lt_a_a

    /--
      Si `a < b`, el cociente es 0.
    -/
    theorem div_of_lt (a b : ℕ₀) (h_lt : Lt a b) :
      (a / b) = 𝟘 := by
      unfold div divMod
      if h_b_zero : b = 𝟘 then
        have h_a_lt_zero : Lt a 𝟘 := by rw [h_b_zero] at h_lt; exact h_lt
        exact (nlt_n_0 a h_a_lt_zero).elim
      else
        rw [dif_neg h_b_zero]
        if h_a_zero : a = 𝟘 then
          rw [dif_pos h_a_zero]
        else
          rw [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            have h_a_lt_one : Lt a 𝟙 := by rw [h_b_one] at h_lt; exact h_lt
            have h_a_eq_zero : a = 𝟘 := lt_b_1_then_b_eq_0 h_a_lt_one
            exact (h_a_zero h_a_eq_zero).elim
          else
            rw [dif_neg h_b_one]
            rw [dif_pos h_lt]

    /--
      Si `a < b`, el resto es `a`.
    -/
    theorem mod_of_lt (a b : ℕ₀) (h_lt : Lt a b) :
      (a % b) = a := by
      unfold mod divMod
      if h_b_zero : b = 𝟘 then
        have h_a_lt_zero : Lt a 𝟘 := by rw [h_b_zero] at h_lt; exact h_lt
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
            have h_a_lt_one : Lt a 𝟙 := by
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
    theorem div_of_lt_fst_interval (a b : ℕ₀) (h_le : Le b a) (h_a_lt_2b : Lt a (add b b)) :
      (a / b) = 𝟙 := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero] at h_le
        exact not_succ_le_zero 𝟘 h_le
      let q := a / b
      have h_a_eq_qbr : a = q * b + (a % b) := divMod_eq a b h_b_neq_0
      have h_r_lt_b : Lt (a % b) b := mod_lt_divisor a b h_b_neq_0
      -- Probamos `q ≥ 1`
      have h_q_ge_1 : Le 𝟙 q := by
        by_contra h_not_q_ge_1
        have h_q_eq_0 : q = 𝟘 := by
          cases q with
          | zero => rfl
          | succ q' => exact False.elim (h_not_q_ge_1 (le_1_succ q'))
        rw [h_q_eq_0] at h_a_eq_qbr
        simp [zero_mul, zero_add] at h_a_eq_qbr
        rw [h_a_eq_qbr] at h_le
        exact nlt_of_le h_le h_r_lt_b
      -- Probamos `q < 2`
      have h_q_lt_2 : Lt q 𝟚 := by
        by_contra h_not_q_lt_2
        have h_q_ge_2 : Le 𝟚 q := nle_then_gt_wp h_not_q_lt_2
        have h_2b_le_qb : Le (mul 𝟚 b) (mul q b) := mul_le_mono_right b h_q_ge_2
        rw [two_mul] at h_2b_le_qb
        have h_2b_le_a : Le (add b b) a := by
          rw [←h_a_eq_qbr]
          exact le_trans (add b b) (mul q b) (add (mul q b) (a % b)) h_2b_le_qb (le_self_add_r _ _)
        exact nlt_of_le h_2b_le_a h_a_lt_2b
      -- Si `1 ≤ q` y `q < 2`, entonces `q = 1`.
      have h_q_le_1 : Le q 𝟙 := lt_then_le_succ_wp h_q_lt_2
      exact le_antisymm q � h_q_le_1 h_q_ge_1

    /--
      Si `2 * b ≤ a < 3 * b`, el cociente es 2.
    -/
    theorem div_of_lt_snd_interval (a b : ℕ₀) (h_le : Le (add b b) a) (h_a_lt_3b : Lt a (add (add b b) b)) :
      (a / b) = 𝟚 := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero, add_zero] at h_le
        exact not_succ_le_zero 𝟘 h_le
      let q := a / b
      let r := a % b
      have h_a_eq_qbr : a = q * b + r := divMod_eq a b h_b_neq_0
      have h_r_lt_b : Lt r b := mod_lt_divisor a b h_b_neq_0
      -- Probamos `q ≥ 2`
      have h_q_ge_2 : Le 𝟚 q := by
        by_contra h_not_q_ge_2
        have h_q_lt_2 : Lt q 𝟚 := nle_then_gt_wp h_not_q_ge_2
        have h_q_le_1 : Le q 𝟙 := lt_then_le_succ_wp h_q_lt_2
        have h_qb_le_b : Le (mul q b) b := by
          have h_mul_le_1 : Le (mul q b) (mul 𝟙 b) := mul_le_mono_right b h_q_le_1
          rw [one_mul] at h_mul_le_1
          exact h_mul_le_1
        have h_a_lt_2b : Lt a (add b b) := by
          rw [h_a_eq_qbr]
          apply lt_of_le_of_lt h_qb_le_b
          rw [two_mul]
          exact lt_add_of_pos_right b r (lt_of_lt_of_le h_r_lt_b (le_refl b))
        exact nlt_of_le h_le h_a_lt_2b
      -- Probamos `q < 3`
      have h_q_lt_3 : Lt q 𝟛 := by
        by_contra h_not_q_lt_3
        have h_q_ge_3 : Le 𝟛 q := nle_then_gt_wp h_not_q_lt_3
        have h_3b_le_qb : Le (mul 𝟛 b) (mul q b) := mul_le_mono_right b h_q_ge_3
        rw [three_mul] at h_3b_le_qb
        have h_3b_le_a : Le (add (add b b) b) a := by
          rw [←h_a_eq_qbr]
          exact le_trans (add (add b b) b) (mul q b) (add (mul q b) r) h_3b_le_qb (le_self_add_r _ _)
        exact nlt_of_le h_3b_le_a h_a_lt_3b
      -- Si `2 ≤ q` y `q < 3`, entonces `q = 2`.
      have h_q_le_2 : Le q 𝟚 := lt_then_le_succ_wp h_q_lt_3
      exact le_antisymm q 𝟚 h_q_le_2 h_q_ge_2

  end Div

end Peano

export Peano.Div (
  divMod
  div
  mod
  divMod_eq
  mod_lt_divisor
  div_le_self
  div_lt_self
  div_of_lt
  mod_of_lt
  div_of_lt_fst_interval
  div_of_lt_snd_interval
)


�