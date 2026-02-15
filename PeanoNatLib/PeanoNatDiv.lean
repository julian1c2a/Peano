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
            rw [dif_pos h_b_one]
            simp only
            rw [h_b_one, mul_one, add_zero]
          else
            rw [dif_neg h_b_one]
            if h_a_lt_b : Lt a b then
              rw [dif_pos h_a_lt_b, zero_mul, zero_add]
            else
              rw [dif_neg h_a_lt_b]
              if h_a_eq_b : a = b then
                rw [dif_pos h_a_eq_b, one_mul, add_zero]
                exact h_a_eq_b
              else
                rw [dif_neg h_a_eq_b]
                have h_b_lt_a : Lt b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
                have h_le_b_a : Le b a := lt_imp_le b a h_b_lt_a
                have h_sub_lt_a : Lt (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0
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
      Le (a / b) a := by
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
          exact mul_le_right q b h_b_neq_0
        exact le_trans q (mul q b) a h_q_le_qb h_qb_le_a

    -- Lema auxiliar que faltaba.
    theorem gt_imp_neq_zero_one (b : ℕ₀) (h : Lt 𝟙 b) : b ≠ 𝟘 ∧ b ≠ 𝟙 :=
      ⟨lt_1_b_then_b_neq_0 h, lt_1_b_then_b_neq_1 h⟩

    /--
      El cociente de la división de `a` por `b` es estrictamente menor que `a` si `b > 𝟙` y `a ≠ 𝟘`.
    -/
    theorem div_lt_self (a b : ℕ₀) (h_b_gt_1 : Lt 𝟙 b) (h_a_neq_0 : a ≠ 𝟘) :
      Lt (a / b) a := by
      have ⟨h_b_neq_0, _⟩ := gt_imp_neq_zero_one b h_b_gt_1
      have h_div_le_a : Le (a / b) a := div_le_self a b h_b_neq_0
      apply lt_of_le_of_ne (a / b) a h_div_le_a
      intro h_eq_div_a
      have h_div_eq : a = add (mul (a / b) b) (a % b) := by
        simpa [div, mod] using (divMod_eq a b h_b_neq_0)
      have h_mul_lt : Lt a (mul a b) := mul_lt_left a b h_a_neq_0 h_b_gt_1
      have h_mul_le : Le (mul a b) a := by
        rw [h_eq_div_a] at h_div_eq
        have h_mul_le_sum : Le (mul a b) (add (mul a b) (a % b)) :=
          le_self_add_r (mul a b) (a % b)
        have h_sum_le_a : Le (add (mul a b) (a % b)) a :=
          le_of_eq (add (mul a b) (a % b)) a h_div_eq.symm
        exact le_trans (mul a b) (add (mul a b) (a % b)) a h_mul_le_sum h_sum_le_a
      have h_lt_a_a : Lt a a := lt_of_lt_of_le h_mul_lt h_mul_le
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
        rw [h_b_zero, add_zero] at h_a_lt_2b
        exact (nlt_n_0 a h_a_lt_2b).elim
      let q := a / b
      have h_a_eq_qbr : a = add (mul q b) (a % b) := by
        simpa [div, mod, q] using (divMod_eq a b h_b_neq_0)
      have h_r_lt_b : Lt (a % b) b := mod_lt_divisor a b h_b_neq_0
      -- Probamos `q ≥ 1`
      have h_q_ge_1 : Le 𝟙 q := by
        cases h_q : q with
        | zero =>
          have h_a_eq_r : a = a % b := by
            rw [h_q] at h_a_eq_qbr
            simp [zero_mul, zero_add] at h_a_eq_qbr
            exact h_a_eq_qbr
          have h_a_lt_b : Lt a b := by
            simpa [h_a_eq_r.symm] using h_r_lt_b
          exact (nlt_of_le h_le h_a_lt_b).elim
        | succ q' =>
          exact le_1_succ q'
      -- Probamos `q < 2`
      have h_q_lt_2 : Lt q 𝟚 := by
        apply nle_then_gt_wp
        intro h_q_ge_2
        have h_2b_le_qb : Le (mul 𝟚 b) (mul q b) := mul_le_mono_right b h_q_ge_2
        rw [two_mul] at h_2b_le_qb
        have h_2b_le_a : Le (add b b) a := by
          rw [h_a_eq_qbr]
          exact le_trans (add b b) (mul q b) (add (mul q b) (a % b)) h_2b_le_qb (le_self_add_r _ _)
        exact nlt_of_le h_2b_le_a h_a_lt_2b
      -- Si `1 ≤ q` y `q < 2`, entonces `q = 1`.
      have h_q_le_1 : Le q 𝟙 := lt_then_le_succ_wp h_q_lt_2
      have h_q_eq : q = 𝟙 := le_antisymm q 𝟙 h_q_le_1 h_q_ge_1
      simpa [q] using h_q_eq

    /--
      Si `2 * b ≤ a < 3 * b`, el cociente es 2.
    -/
    theorem div_of_lt_snd_interval (a b : ℕ₀) (h_le : Le (add b b) a) (h_a_lt_3b : Lt a (add (add b b) b)) :
      (a / b) = 𝟚 := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero, add_zero] at h_a_lt_3b
        exact (nlt_n_0 a h_a_lt_3b).elim
      let q := a / b
      let r := a % b
      have h_a_eq_qbr : a = add (mul q b) r := by
        simpa [div, mod, q, r] using (divMod_eq a b h_b_neq_0)
      have h_r_lt_b : Lt r b := mod_lt_divisor a b h_b_neq_0
      -- Probamos `q ≥ 2`
      have h_q_ge_2 : Le 𝟚 q := by
        have h_q_gt_1 : Lt 𝟙 q := by
          apply nle_then_gt_wp
          intro h_q_le_1
          have h_q_eq := le_m_1_then_m_eq_0or1_wp h_q_le_1
          cases h_q_eq with
          | inl h_q_zero =>
            have h_a_eq_r : a = r := by
              rw [h_q_zero] at h_a_eq_qbr
              simp [zero_mul, zero_add] at h_a_eq_qbr
              exact h_a_eq_qbr
            have h_a_lt_b : Lt a b := by
              simpa [h_a_eq_r.symm] using h_r_lt_b
            have h_a_lt_2b : Lt a (add b b) := add_lt a b b h_a_lt_b
            exact (nlt_of_le h_le h_a_lt_2b).elim
          | inr h_q_one =>
            have h_a_eq_br : a = add b r := by
              rw [h_q_one] at h_a_eq_qbr
              simp [one_mul] at h_a_eq_qbr
              exact h_a_eq_qbr
            have h_a_lt_2b : Lt a (add b b) := by
              rw [h_a_eq_br]
              exact (add_lt_add_left_iff b r b).mpr h_r_lt_b
            exact (nlt_of_le h_le h_a_lt_2b).elim
        exact lt_then_le_succ_wp h_q_gt_1
      -- Probamos `q < 3`
      have h_q_lt_3 : Lt q 𝟛 := by
        apply nle_then_gt_wp
        intro h_q_ge_3
        have h_3b_le_qb : Le (mul 𝟛 b) (mul q b) := mul_le_mono_right b h_q_ge_3
        rw [three_mul] at h_3b_le_qb
        have h_3b_le_a : Le (add (add b b) b) a := by
          rw [h_a_eq_qbr]
          exact le_trans (add (add b b) b) (mul q b) (add (mul q b) r) h_3b_le_qb (le_self_add_r _ _)
        exact nlt_of_le h_3b_le_a h_a_lt_3b
      -- Si `2 ≤ q` y `q < 3`, entonces `q = 2`.
      have h_q_le_2 : Le q 𝟚 := lt_then_le_succ_wp h_q_lt_3
      have h_q_eq : q = 𝟚 := le_antisymm q 𝟚 h_q_le_2 h_q_ge_2
      simpa [q] using h_q_eq



    theorem le___mul__div_a_b__b____a (a b : ℕ₀) (h_b_neq_0 : b ≠ 𝟘) :
      Le (mul (div a b) b) a
        := by
      have h_eq : a = add (mul (div a b) b) (a % b) := by
        simpa [div, mod] using (divMod_eq a b h_b_neq_0)
      have h_le_sum : Le (mul (div a b) b) (add (mul (div a b) b) (a % b)) :=
        le_self_add_r (mul (div a b) b) (a % b)
      have h_sum_le_a : Le (add (mul (div a b) b) (a % b)) a :=
        le_of_eq (add (mul (div a b) b) (a % b)) a h_eq.symm
      exact le_trans (mul (div a b) b) (add (mul (div a b) b) (a % b)) a h_le_sum h_sum_le_a

    /--
      Si `a * n ≤ b < a * (σ n)`, entonces `b / a = n`.
    -/
    theorem div_of_lt_nth_interval (a b n : ℕ₀)
      (h_le : Le (mul a n) b)
      (h_lt : Lt b (mul a (σ n))) :
      (b / a) = n := by
      have h_a_neq_0 : a ≠ 𝟘 := by
        intro h_a_zero
        rw [h_a_zero, zero_mul] at h_lt
        exact (nlt_n_0 b h_lt).elim
      let q := b / a
      have h_div_eq : b = add (mul q a) (b % a) := by
        simpa [div, mod, q] using (divMod_eq b a h_a_neq_0)
      have h_r_lt_a : Lt (b % a) a := mod_lt_divisor b a h_a_neq_0

      have h_q_le_n : Le q n := by
        by_cases h_q_le_n : Le q n
        · exact h_q_le_n
        · have h_n_lt_q : Lt n q := nle_then_gt_wp h_q_le_n
          have h_succn_le_q : Le (σ n) q := lt_then_le_succ_wp h_n_lt_q
          have h_mul_le : Le (mul (σ n) a) (mul q a) := mul_le_mono_right a h_succn_le_q
          have h_mul_le_b : Le (mul q a) b := by
            rw [h_div_eq]
            exact le_self_add_r (mul q a) (b % a)
          have h_a_succn_le_b : Le (mul (σ n) a) b :=
            le_trans (mul (σ n) a) (mul q a) b h_mul_le h_mul_le_b
          have h_b_lt_a_succn : Lt b (mul (σ n) a) := by
            simpa [mul_comm] using h_lt
          exact (False.elim (nlt_of_le h_a_succn_le_b h_b_lt_a_succn))

      have h_n_le_q : Le n q := by
        by_cases h_n_le_q : Le n q
        · exact h_n_le_q
        · have h_q_lt_n : Lt q n := nle_then_gt_wp h_n_le_q
          obtain ⟨d, h_n_eq⟩ := (lt_iff_exists_add_succ q n).mp h_q_lt_n
          have h_b_lt_add : Lt b (add (mul q a) a) := by
            rw [h_div_eq]
            exact (add_lt_add_left_iff (mul q a) (b % a) a).mpr h_r_lt_a
          have h_add_le_mul_n : Le (add (mul q a) a) (mul n a) := by
            rw [h_n_eq, mul_rdistr]
            have h_a_le_mul : Le a (mul (σ d) a) := by
              have h_a_le_mul' : Le a (mul a (σ d)) :=
                mul_le_right a (σ d) (succ_neq_zero d)
              simpa [mul_comm] using h_a_le_mul'
            exact add_le_add_left a (mul (σ d) a) (mul q a) h_a_le_mul
          have h_b_lt_mul_n : Lt b (mul n a) :=
            lt_of_lt_of_le h_b_lt_add h_add_le_mul_n
          have h_b_lt_mul_a_n : Lt b (mul a n) := by
            simpa [mul_comm] using h_b_lt_mul_n
          exact (False.elim (nlt_of_le h_le h_b_lt_mul_a_n))

      have h_q_eq_n : q = n := le_antisymm q n h_q_le_n h_n_le_q
      simpa [q] using h_q_eq_n

    /--
      Si `b ≤ a < 2 * b`, el resto es `a - b`.
    -/
    theorem mod_of_lt_fst_interval (a b : ℕ₀) (h_le : Le b a) (h_a_lt_2b : Lt a (add b b)) :
      (a % b) = sub a b := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero, add_zero] at h_a_lt_2b
        exact (nlt_n_0 a h_a_lt_2b).elim
      let r := a % b
      have h_div_eq : a = add (mul (a / b) b) (a % b) := by
        simpa [div, mod] using (divMod_eq a b h_b_neq_0)
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
    theorem mod_of_lt_snd_interval (a b : ℕ₀) (h_le : Le (add b b) a) (h_a_lt_3b : Lt a (add (add b b) b)) :
      (a % b) = sub a (add b b) := by
      have h_b_neq_0 : b ≠ 𝟘 := by
        intro h_b_zero
        rw [h_b_zero, add_zero] at h_a_lt_3b
        exact (nlt_n_0 a h_a_lt_3b).elim
      let r := a % b
      have h_div_eq : a = add (mul (a / b) b) (a % b) := by
        simpa [div, mod] using (divMod_eq a b h_b_neq_0)
      have h_div_eq' : a = add (add b b) r := by
        rw [div_of_lt_snd_interval a b h_le h_a_lt_3b] at h_div_eq
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
      (h_le : Le (mul a n) b)
      (h_lt : Lt b (mul a (σ n))) :
      (b % a) = sub b (mul a n) := by
      have h_a_neq_0 : a ≠ 𝟘 := by
        intro h_a_zero
        rw [h_a_zero, zero_mul] at h_lt
        exact (nlt_n_0 b h_lt).elim
      let r := b % a
      have h_div_eq : b = add (mul (b / a) a) (b % a) := by
        simpa [div, mod] using (divMod_eq b a h_a_neq_0)
      have h_div_eq' : b = add (mul a n) r := by
        rw [div_of_lt_nth_interval a b n h_le h_lt] at h_div_eq
        simpa [mul_comm, r] using h_div_eq
      have h_sub : sub (add (mul a n) r) (mul a n) = r := by
        simpa [r] using (add_k_sub_k r (mul a n))
      have h_sub' : r = sub (add (mul a n) r) (mul a n) := h_sub.symm
      rw [←h_div_eq'] at h_sub'
      simpa [r] using h_sub'

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
  mod_of_lt
  div_of_lt
  mod_of_lt_fst_interval
  div_of_lt_snd_interval
  mod_of_lt_snd_interval
  div_of_lt_nth_interval
  mod_of_lt_nth_interval
)
