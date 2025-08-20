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
import Init.WF


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

    instance : SizeOf ℕ₀ where
      sizeOf := Ψ

    theorem lt_sizeOf (a b : ℕ₀) : Lt a b → sizeOf a < sizeOf b := by
      intro h_lt
      rw [isomorph_Ψ_lt] at h_lt
      exact h_lt


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
    termination_by sizeOf a
    decreasing_by
      simp only [sizeOf]
      apply lt_sizeOf
      exact h_sub_a_b_lt_a

    -- #eval divMod 𝟘 𝟘
    -- #eval divMod 𝟙 𝟘
    -- #eval divMod 𝟙 𝟙
    -- #eval divMod 𝟙 𝟚
    -- #eval divMod 𝟚 𝟘
    -- #eval divMod 𝟚 𝟙
    -- #eval divMod 𝟚 𝟚
    -- #eval divMod 𝟚 𝟛
    -- #eval divMod 𝟛 𝟘
    -- #eval divMod 𝟛 𝟙
    -- #eval divMod 𝟛 𝟚
    -- #eval divMod 𝟛 𝟛
    -- #eval divMod 𝟛 𝟜


    def div (a b : ℕ₀) : ℕ₀ :=
      (divMod a b).1

    notation a " / " b => div a b

    def mod (a b : ℕ₀) : ℕ₀ :=
      (divMod a b).2

    notation a " % " b => mod a b

    theorem sub_lt_of_lt_and_neq_zero {a b : ℕ₀} (h_lt : Lt b a) (h_b_neq_zero : b ≠ 𝟘) :
        Lt (sub a b) a
            := by
        have h_le : Le b a := lt_imp_le b a h_lt
        exact sub_lt_self a b h_le h_b_neq_zero


    theorem lt_add_of_pos_right (a b : ℕ₀) (h_b_pos : Lt 𝟘 b) :
        Lt a (add a b)
            := by
        induction b with
        | zero =>
          exfalso
          exact nlt_self 𝟘 h_b_pos
        | succ b' =>
          rw [add_succ]
          have h_le : Le a (add a b') := le_self_add_forall a b'
          exact le_then_lt_succ_wp h_le


    theorem divMod_eq__eq_a_0
      (a b : ℕ₀) (h_a_eq_zero : a = 𝟘) :
        b ≠ 𝟘 → a = add (mul (divMod a b).fst b) (divMod a b).snd
          := by
      intro h_b_neq_0
      -- Sustituimos `a` por `𝟘` usando la hipótesis `h_a_eq_zero`.
      rw [h_a_eq_zero]
      -- Desplegamos la definición de `divMod` para ver los `if`.
      unfold divMod
      -- El primer `if` comprueba `b = 𝟘`. Usamos la hipótesis `h_b_neq_0`.
      -- `dif_neg` elige la rama `else`.
      rw [dif_neg h_b_neq_0]
      -- El segundo `if` comprueba `a = 𝟘`. `a` ya es `𝟘`.
      -- `dif_pos rfl` elige la rama `then`.
      simp
      -- El objetivo se simplifica a `𝟘 = 𝟘 * b + 𝟘`, lo cual es cierto.
      rw [zero_mul, zero_add]


    theorem divMod_eq__neq_a_0__eq_b_1
      (a b : ℕ₀)
      (h_a_eq_zero : a ≠ 𝟘)
      (h_b_eq_1 : b = 𝟙) :
        b ≠ 𝟘 → a = add (mul ((divMod a b).1) b) ((divMod a b).2)
          := by
      intro h_b_neq_0
      unfold divMod
      split
      case isTrue h_b_is_zero =>
        have h_b_not_zero : b ≠ 𝟘
          := by
            rw [h_b_eq_1]
            exact Ne.symm neq_1_0
        contradiction
      case isFalse h_b_not_zero_again =>
        simp only
        rw [h_b_eq_1]
        simp only [mul_one, add_zero]

    theorem divMod_eq__neq_a_0__lt_1_b__lt_a_b
      (a b : ℕ₀)
      (h_neq_a_0 : a ≠ 𝟘)
      (h_lt_1_b : Lt 𝟙 b)
      (h_lt_a_b : Lt a b)  :
        b ≠ 𝟘 → a = add (mul ((divMod a b).1) b) ((divMod a b).2)
      := by
         unfold divMod
         split
         case isTrue h_b_is_zero =>
           have h_b_not_zero : b ≠ 𝟘 := by
             exact lt_1_b_then_b_neq_0 h_lt_1_b
           contradiction
         case isFalse h_b_not_zero_again =>
           by_cases h_b_is_one : b = 𝟙
           case pos =>
              have h_b_not_one : b ≠ 𝟙 := by
                exact lt_1_b_then_b_neq_1 h_lt_1_b
              contradiction
           case neg =>
              intro
              simp [h_b_is_one]
              by_cases h_a_is_zero : a = 𝟘
              case pos =>
                -- Case a = 𝟘
                rw [h_a_is_zero]
                simp only [add_zero]
                exact Eq.symm (zero_mul b)
              case neg =>
                -- Case b ≠ 𝟙
                -- In this branch, divMod a b = (0, a)
                have h_divMod : divMod a b = (𝟘, a) := by
                  unfold divMod
                  simp [h_lt_a_b]
                  simp [h_b_not_zero_again, h_a_is_zero, h_b_is_one]
                simp only [zero_mul, zero_add]

    theorem divMod_eq__neq_a_0__lt_1_b__eq_a_b
      (a b : ℕ₀)
      (h_neq_a_0 : a ≠ 𝟘)
      (h_lt_1_b : Lt 𝟙 b)
      (h_eq_a_b : a = b) :
        b ≠ 𝟘 → a = add (mul ((divMod a b).1) b) ((divMod a b).2)
      := by
      intro h_b_neq_0
      have h_b_not_one : b ≠ 𝟙 := lt_1_b_then_b_neq_1 h_lt_1_b
      have h_not_lt_a_b : ¬ Lt a b := by rw [h_eq_a_b]; exact lt_irrefl b
      unfold divMod
      simp [dif_neg h_b_neq_0, dif_neg h_neq_a_0, dif_neg h_b_not_one, dif_neg h_not_lt_a_b, dif_pos h_eq_a_b]
      rw [one_mul, add_zero]
      exact h_eq_a_b

    theorem divMod_eq__lt_a_b
      (a b : ℕ₀) (h_lt_a_b : Lt a b) (h_a_neq_0 : a ≠ 𝟘) :
        b ≠ 𝟘 → a = add (mul ((divMod a b).1) b) ((divMod a b).2)
          := by
      intro h_b_neq_0
      -- Desplegamos la definición de `divMod` para ver los `if`.
      unfold divMod
      -- Primer `if` comprueba `b = 𝟘`. Usamos la hipótesis `h_b_neq_0`.
      rw [dif_neg h_b_neq_0]
      -- Segundo `if` comprueba `a = 𝟘`. Usamos la hipótesis `h_a_neq_0`.
      rw [dif_neg h_a_neq_0]
      -- Ahora necesitamos comprobar `b = 𝟙`.
      by_cases h_b_one : b = 𝟙
      · -- Si `b = 𝟙`, entonces `h_lt_a_b` se convierte en `Lt a 𝟙`.
        -- Esto implica `a = 𝟘` por `lt_b_1_then_b_eq_0`.
        -- Esto contradice nuestra hipótesis `h_a_neq_0`.
        have h_a_is_zero : a = 𝟘 := lt_b_1_then_b_eq_0 (h_b_one ▸ h_lt_a_b)
        exact False.elim (h_a_neq_0 h_a_is_zero)
      · -- Si `b ≠ 𝟙`, vamos al siguiente `if`.
        rw [dif_neg h_b_one]
        -- La siguiente condición es `Lt a b`, que es nuestra hipótesis `h_lt_a_b`.
        rw [dif_pos h_lt_a_b]
        -- En este caso, `divMod a b` evalúa a `(𝟘, a)`.
        -- El objetivo se convierte en `a = add (mul 𝟘 b) a`.
        rw [zero_mul, zero_add]

    theorem divMod_eq__lt_b_a__eq_b_1
      (a b : ℕ₀) (h_lt_b_a : Lt b a) (h_b_eq_1 : b = 𝟙) :
        b ≠ 𝟘 → a = add (mul ((divMod a b).1) b) ((divMod a b).2)
          := by
      intro h_b_neq_0
      -- Con `b = 𝟙`, `h_lt_b_a` se convierte en `Lt 𝟙 a`.
      -- Esto implica `a ≠ 𝟘` y `a ≠ 𝟙`.
      have h_a_neq_0 : a ≠ 𝟘 := by
        intro h_a_zero
        rw [h_a_zero] at h_lt_b_a
        rw [h_b_eq_1] at h_lt_b_a -- `Lt 𝟙 𝟘`, que es falso.
        exact nlt_n_0 𝟙 h_lt_b_a
      unfold divMod
      -- Evaluamos los `if` usando las hipótesis.
      rw [dif_neg h_b_neq_0]
      rw [dif_neg h_a_neq_0]
      rw [dif_pos h_b_eq_1]
      -- `divMod a b` se simplifica a `(a, 𝟘)`.
      -- El objetivo se convierte en `a = add (mul a b) 𝟘`.
      rw [h_b_eq_1, mul_one, add_zero]

    theorem divMod_eq__eq_a_b
      (a b : ℕ₀) (h_eq_a_b : a = b) (h_lt_0_a : Lt 𝟘 a) (h_lt_1_b : Lt 𝟙 b) :
        b ≠ 𝟘 → a = add (mul ((divMod a b).1) b) ((divMod a b).2)
          := by
      intro h_b_neq_0
      have h_b_not_one : b ≠ 𝟙 := lt_1_b_then_b_neq_1 h_lt_1_b
      have h_not_lt_a_b : ¬ Lt a b := by rw [h_eq_a_b]; exact lt_irrefl b
      have h_a_neq_0 : a ≠ 𝟘 := by
        intro h
        rw [h] at h_lt_0_a
        exact nlt_self 𝟘 h_lt_0_a
      unfold divMod
      simp [dif_neg h_b_neq_0, dif_neg h_a_neq_0, dif_neg h_b_not_one, dif_neg h_not_lt_a_b, dif_pos h_eq_a_b]
      rw [one_mul, add_zero]
      exact h_eq_a_b

    theorem divMod_eq__lt_b_a__lt_1_b
      (a b : ℕ₀) (h_lt_b_a : Lt b a) (h_lt_1_b : Lt 𝟙 b) :
        b ≠ 𝟘 → a = add (mul ((divMod a b).1) b) ((divMod a b).2)
          := by
      intro h_b_neq_0
      have h_b_neq_1 : b ≠ 𝟙 := lt_1_b_then_b_neq_1 h_lt_1_b
      unfold divMod
      simp [dif_neg h_b_neq_0]
      induction a using well_founded_lt.induction with a ih
      have h_b_lt_a : Lt b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
      have h_le_b_a : Le b a := lt_imp_le b a h_b_lt_a
      have h_sub_lt_a : Lt (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0

      -- Aplicamos la hipótesis de inducción
      have h_ih_call := ih (sub a b) h_sub_lt_a

      -- Probamos la ecuación para este caso
      unfold divMod
      simp [dif_neg h_b_neq_0, dif_neg h_a_zero, dif_neg h_b_one, dif_neg h_a_lt_b, dif_neg h_a_eq_b]
      rw [succ_mul, add_assoc, add_comm ((divMod (sub a b) b).2) b, ←add_assoc]
      rw [←h_ih_call]
      exact (sub_k_add_k a b h_le_b_a).symm

    /--
      Teorema general de la división euclídea.
      Esta es la prueba principal que usa inducción bien fundada.
    -/
    theorem divMod_eq (a b : ℕ₀) : b ≠ 𝟘 → a = add (mul (divMod a b).1 b) (divMod a b).2 := by
      intro h_b_neq_0
      induction a using well_founded_lt.induction with a ih
      unfold divMod
      if h_b_zero : b = 𝟘 then
        exact False.elim (h_b_neq_0 h_b_zero)
      else
        if h_a_zero : a = 𝟘 then
          simp [dif_pos h_a_zero, zero_mul, zero_add]
        else
          if h_b_one : b = 𝟙 then
            simp [dif_pos h_b_one, mul_one, add_zero]
          else
            if h_a_lt_b : Lt a b then
              simp [dif_pos h_a_lt_b, zero_mul, add_comm, zero_add]
            else
              if h_a_eq_b : a = b then
                simp [dif_pos h_a_eq_b, one_mul, add_zero]
              else
                have h_b_lt_a : Lt b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
                have h_le_b_a : Le b a := lt_imp_le b a h_b_lt_a
                have h_sub_lt_a : Lt (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0
                have h_ih_call := ih (sub a b) h_sub_lt_a
                have h_divMod_ab_def : divMod a b = (σ (divMod (sub a b) b).1, (divMod (sub a b) b).2) := by
                  simp [divMod, h_b_zero, h_a_zero, h_b_one, h_a_lt_b, h_a_eq_b]
                rw [h_divMod_ab_def, succ_mul, add_assoc]
                rw [add_comm ((divMod (sub a b) b).2) b, ←add_assoc]
                rw [←h_ih_call]
                exact (sub_k_add_k a b h_le_b_a).symm

  end Div

end Peano
