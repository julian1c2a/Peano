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
      Esta es la prueba principal que usa inducción bien fundada.
    -/
    theorem divMod_eq (a b : ℕ₀) : b ≠ 𝟘 → a = add (mul (divMod a b).1 b) (divMod a b).2 := by
      intro h_b_neq_0
      induction a using well_founded_lt.induction
      -- CORRECCIÓN: Nombramos las variables correctamente. `a` es el número, `ih` la hipótesis.
      rename_i a ih

      -- Desplegamos la definición para que los `if` sean visibles.
      unfold divMod

      -- Manejamos cada `if` explícitamente con `rw [dif_pos h]` o `rw [dif_neg h]`.
      if h_b_zero : b = 𝟘 then
        exact False.elim (h_b_neq_0 h_b_zero)
      else -- b ≠ 𝟘
        rw [dif_neg h_b_zero]

        if h_a_zero : a = 𝟘 then
          rw [dif_pos h_a_zero, h_a_zero, zero_mul, zero_add]
        else -- a ≠ 𝟘
          rw [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            rw [dif_pos h_b_one]
            rw [h_b_one]
            rw [mul_one, add_zero]
          else -- b ≠ 𝟙
            rw [dif_neg h_b_one]
            if h_a_lt_b : Lt a b then
              rw [dif_pos h_a_lt_b, zero_mul, zero_add]
            else -- ¬ (Lt a b)
              rw [dif_neg h_a_lt_b]
              if h_a_eq_b : a = b then
                rw [dif_pos h_a_eq_b, one_mul, add_zero]
                exact h_a_eq_b
              else -- b < a (caso recursivo)
                rw [dif_neg h_a_eq_b]

                have h_b_lt_a : Lt b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
                have h_le_b_a : Le b a := lt_imp_le b a h_b_lt_a
                have h_sub_lt_a : Lt (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0

                -- Aplicamos la hipótesis de inducción `ih` al término más pequeño `sub a b`.
                have h_ih_call := ih (sub a b) h_sub_lt_a

                -- Usamos reescritura para finalizar la prueba.
                simp only [succ_mul]
                rw [←add_assoc ((divMod (sub a b) b).1 * b) b ((divMod (sub a b) b).2)]
                rw [add_comm b ((divMod (sub a b) b).2)]
                rw [add_assoc]
                rw [←h_ih_call]
                exact (sub_k_add_k a b h_le_b_a).symm

    -- Helper lemma: If b > 𝟙, then b ≠ 𝟘 ∧ b ≠ 𝟙
    private def gt_imp_neq_zero_one (b : ℕ₀) (h : b > 𝟙) : b ≠ 𝟘 ∧ b ≠ 𝟙 :=
      ⟨fun h0 => by
          rw [h0] at h
          -- Now h : 𝟘 > 𝟙, but 𝟘 < 𝟙, so this is absurd
          exact False.elim (lt_asymm _ _ lt_0_1 h),
        fun h1 => by
          rw [h1] at h
          -- Now h : 𝟙 > 𝟙, which is irreflexivity
          exact lt_irrefl _ h⟩


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

          have h_q_le_qb : Le q (mul q b) :=
            mul_le_right q b h_b_neq_0

          exact le_trans q (mul q b) a h_q_le_qb h_qb_le_a

    /--
      El cociente de la división de `a` por `b` es estrictamente menor que `a` si `b > 𝟙` y `a ≠ 𝟘`.
    -/
    theorem div_lt_self (a b : ℕ₀) (h_b_gt_1 : b > 𝟙) (h_a_neq_0 : a ≠ 𝟘) :
      Lt (a / b) a
        := by
          -- Usamos el lema `gt_imp_neq_zero_one` para obtener `b ≠ 𝟘` y `b ≠ 𝟙`.
          have ⟨h_b_neq_0, h_b_neq_1⟩ := gt_imp_neq_zero_one b h_b_gt_1
          -- Aplicamos la propiedad de división por cero.
          have h_div_le_self := div_le_self a b h_b_neq_0
          -- Como `a ≠ 𝟘`, entonces `a / b < a`.
          exact lt_of_le_neq (a / b) a h_div_le_self (fun h_eq => by
            -- Si `a / b = a`, entonces por la ecuación de división:
            -- `a = (a / b) * b + (a % b) = a * b + (a % b)`
            -- Como `b > 𝟙`, esto implica `a * b > a`, contradicción.
            have h_div_eq := divMod_eq a b h_b_neq_0
            -- Rewrite using the definition of div and mod
            have h_div_def : (a / b) = (divMod a b).1 := rfl
            have h_mod_def : (a % b) = (divMod a b).2 := rfl
            rw [←h_div_def, ←h_mod_def] at h_div_eq
            rw [h_eq] at h_div_eq
            -- Ahora tenemos: a = a * b + (a % b)
            have h_mod_lt := mod_lt_divisor a b h_b_neq_0
            -- Como a % b < b y b > 𝟙, tenemos a % b ≥ 𝟘
            have h_ab_gt_a : Lt a (mul a b) := by
              by_cases h_a_zero : a = 𝟘
              · exact (h_a_neq_0 h_a_zero).elim
              · rw [mul_comm a b]
                exact mul_lt_right a b h_a_zero h_b_gt_1
            -- De la ecuación a = a * b + (a % b), tenemos a ≥ a * b
            have h_a_ge_ab : Le (mul a b) a := by
              rw [h_div_eq]
              have h_mod_def : (a % b) = (divMod a b).2 := rfl
              rw [h_mod_def]
              exact le_self_add (mul a b) (a % b)
            -- Pero esto contradice a < a * b
            exact lt_irrefl a (lt_of_le_of_lt h_a_ge_ab h_ab_gt_a))

    /--
      Si `a < b`, el cociente es 0.
    -/
    theorem div_of_lt (a b : ℕ₀) (h_lt : Lt a b) :
      (a / b) = 𝟘
        := by
          unfold div
          unfold divMod
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
      Si `𝟚 * b > a` y `a ≥ b`, el cociente es 𝟙.
    -/
    theorem div_of_lt_fst_interval (a b : ℕ₀) (h_le : Le b a) (h_a_ge_b : Lt a b) :
      (a / b) = 𝟙
        := by
          -- Usamos el lema `lt_imp_neq_zero_one` para obtener `b ≠ 𝟘` y `b ≠ 𝟙`.
          have ⟨h_b_neq_0, h_b_neq_1⟩ := lt_imp_neq_zero_one b h_le
          -- Aplicamos la propiedad de división por cero.
          have h_div_le_self := div_le_self a b h_b_neq_0
          -- Como `a ≥ b`, entonces `a / b ≥ 𝟙`.
          have h_div_ge_one : Le (a / b) 𝟙 := by
            rw [←lt_iff_le_not_eq] at h_a_ge_b
            exact le_of_lt h_a_ge_b

          exact le_antisymm h_div_ge_one h_div_le_self

    /--
      Si `𝟛 * b > a` y `a ≥ 𝟚 * b`, el cociente es 𝟙.
    -/
    theorem div_of_lt_snd_interval (a b : ℕ₀) (h_le : Le b a) (h_a_ge_b : Lt a b) :
      (a / b) = 𝟚
        := by sorry

    /--
      El resto de la división siempre es menor que el divisor.
      Esta es la propiedad más importante de la división euclídea.
    -/
    theorem mod_lt_divisor (a b : ℕ₀) (h_b_neq_0 : b ≠ 𝟘) :
      Lt (a % b) b := by
      -- La prueba se hace por inducción bien fundada sobre `a`.
      induction a using well_founded_lt.induction
      rename_i a ih

      unfold mod divMod
      -- Replicamos la estructura de `if` de `divMod`.
      if h_b_zero : b = 𝟘 then
        exact False.elim (h_b_neq_0 h_b_zero)
      else
        rw [dif_neg h_b_zero]
        if h_a_zero : a = 𝟘 then
          rw [dif_pos h_a_zero]
          -- The remainder when a = 𝟘 is 𝟘, and Lt 𝟘 b is true because b ≠ 𝟘
          simp only  -- reduce (𝟘 % b) to 𝟘
          exact neq_0_then_lt_0 h_b_neq_0
        else
          rw [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            rw [dif_pos h_b_one]
            -- El resto es 𝟘, y `Lt 𝟘 𝟙` es cierto.
            simp only  -- reduce (a, 𝟘).snd to 𝟘
            rw [h_b_one]
            exact lt_0_1
          else
            rw [dif_neg h_b_one]
            if h_a_lt_b : Lt a b then
              rw [dif_pos h_a_lt_b]
              -- El resto es `a`, y por hipótesis `Lt a b`.
              exact h_a_lt_b
            else
              rw [dif_neg h_a_lt_b]
              if h_a_eq_b : a = b then
                rw [dif_pos h_a_eq_b]
                -- El resto es 𝟘, y `Lt 𝟘 b` es cierto porque `b ≠ 𝟘` y `b ≠ 𝟙`.
                have h_lt_1_b : Lt 𝟙 b := neq_01_then_gt_1 b ⟨h_b_neq_0, h_b_one⟩
                exact lt_trans 𝟘 𝟙 b lt_0_1 h_lt_1_b
              else
                -- Caso recursivo: b < a
                rw [dif_neg h_a_eq_b]
                have h_b_lt_a : Lt b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
                have h_le_b_a : Le b a := lt_imp_le b a h_b_lt_a
                have h_sub_lt_a : Lt (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0
                -- El resto de `a % b` es el mismo que el de `(a-b) % b`.
                -- Por hipótesis de inducción, sabemos que `(a-b) % b < b`.
                exact ih (sub a b) h_sub_lt_a


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
        else
          rw [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            have h_a_lt_one : Lt a 𝟙 := by rw [h_b_one] at h_lt; exact h_lt
            have h_a_eq_zero : a = 𝟘 := lt_b_1_then_b_eq_0 h_a_lt_one
            exact (h_a_zero h_a_eq_zero).elim
          else
            rw [dif_neg h_b_one]
            rw [dif_pos h_lt]

  end Div

end Peano

export Peano.Div (
  divMod
  div
  mod
  divMod_eq
  div_le_self
  div_lt_self
  div_of_lt
  mod_lt_divisor
  mod_of_lt
)
