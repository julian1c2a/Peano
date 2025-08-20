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

    theorem not_lt_and_not_eq_implies_gt (a b : ℕ₀) (h_not_lt : ¬ Lt a b) (h_not_eq : ¬ a = b) : Lt b a := by
      rcases trichotomy a b with hlt | heq | hgt
      · contradiction -- hlt contradicts h_not_lt
      · contradiction -- heq contradicts h_not_eq
      · exact hgt

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
      -- Usamos inducción bien fundada sobre `a` con la relación `Lt`.
      induction a using well_founded_lt.induction with a ih

      -- Desplegamos la definición para analizar los casos.
      unfold divMod

      -- Usamos `if/else` con `simp` para manejar los casos.
      if h_b_zero : b = 𝟘 then
        exact False.elim (h_b_neq_0 h_b_zero)
      else -- b ≠ 𝟘
        simp [dif_neg h_b_zero]
        if h_a_zero : a = 𝟘 then
          simp [dif_pos h_a_zero, zero_mul, zero_add]
        else -- a ≠ 𝟘
          simp [dif_neg h_a_zero]
          if h_b_one : b = 𝟙 then
            simp [dif_pos h_b_one, mul_one, add_zero]
          else -- b ≠ 𝟙
            simp [dif_neg h_b_one]
            if h_a_lt_b : Lt a b then
              simp [dif_pos h_a_lt_b, zero_mul, add_comm, zero_add]
            else -- ¬ (Lt a b)
              simp [dif_neg h_a_lt_b]
              if h_a_eq_b : a = b then
                simp [dif_pos h_a_eq_b, one_mul, add_zero]
              else -- b < a (caso recursivo)
                simp [dif_neg h_a_eq_b]
                have h_b_lt_a : Lt b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
                have h_le_b_a : Le b a := lt_imp_le b a h_b_lt_a
                have h_sub_lt_a : Lt (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0

                -- Aplicamos la hipótesis de inducción `ih` al término más pequeño `sub a b`.
                have h_ih_call := ih (sub a b) h_sub_lt_a

                -- Ahora podemos reescribir y finalizar la prueba.
                rw [succ_mul, add_assoc]
                rw [add_comm ((divMod (sub a b) b).2) b, ←add_assoc]
                rw [←h_ih_call]
                exact (sub_k_add_k a b h_le_b_a).symm

  end Div

end Peano
/-!
  This file contains theorems related to the division of natural numbers in Peano's axioms.
  It includes the definition of Euclidean division, properties of division, and related lemmas.
-/
