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

    theorem divMod_eq__eq_a_0
      (a b : ℕ₀)
      (h_a_eq_zero : a = 𝟘)
      (h_b_neq_0 : b ≠ 𝟘) :
        a = (divMod a b).1 * b + (divMod a b).2
      := by
      unfold divMod
      split
      case isTrue h_b_is_zero =>
        subst h_b_is_zero
        contradiction
      case isFalse h_b_not_zero_again =>
        simp only [Prod.fst, Prod.snd, zero_mul, zero_add]
        exact h_a_eq_zero

    theorem divMod_eq__neq_a_0__eq_b_1
      (a b : ℕ₀)
      (h_a_eq_zero : a ≠ 𝟘)
      (h_b_eq_1 : b = 𝟙) :
        a = add (mul ((divMod a b).1) b) ((divMod a b).2)
      := by
      unfold divMod
      split
      case isTrue h_b_is_zero =>
        have h_b_not_zero : b ≠ 𝟘
          := by
            rw [h_b_eq_1]
            exact Ne.symm neq_1_0
        contradiction
      case isFalse h_b_not_zero_again =>
        simp only [Prod.fst, Prod.snd]
        rw [h_b_eq_1]
        simp only [mul_one, add_zero]

    theorem divMod_eq__neq_a_0__lt_1_b__lt_a_b
      (a b : ℕ₀)
      (h_neq_a_0 : a ≠ 𝟘)
      (h_lt_1_b : Lt 𝟙 b)
      (h_lt_a_b : Lt a b)  :
        a = add (mul ((divMod a b).1) b) ((divMod a b).2)
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
              symm
              simp [Prod.fst]
              simp [divMod, h_b_not_zero_again, h_b_is_one, h_lt_a_b]
              simp only [zero_mul]
              simp only [zero_add]

    theorem divMod_eq__neq_a_0__lt_1_b__eq_a_b
      (a b : ℕ₀)
      (h_neq_a_0 : a ≠ 𝟘)
      (h_lt_1_b : Lt 𝟙 b)
      (h_eq_a_b : a = b) :
        a = add (mul ((divMod a b).1) b) ((divMod a b).2)
      := by
      unfold divMod
      split
      case isTrue h_b_is_zero =>
        have h_b_not_zero : b ≠ 𝟘
          := by exact lt_1_b_then_b_neq_0 h_lt_1_b
        contradiction
      case isFalse h_b_not_zero_again =>
        split
        case isTrue h_b_is_one =>
          exfalso
          have h_lt_1_b : Lt 𝟙 b := by exact h_lt_1_b
          have h_b_not_one : b ≠ 𝟙 := by exact lt_1_b_then_b_neq_1 h_lt_1_b
          contradiction
        case isFalse h_b_not_one =>
            split
            case isTrue h_lt_a_b =>
              exfalso
              have h_a_nlt_b : ¬ Lt a b := by
                rw [h_eq_a_b]
                exact lt_irrefl b
              contradiction
            case isFalse h_nlt_a_b =>
              simp only [Prod.fst]
              rw [h_eq_a_b]
              simp only [one_mul, add_zero]


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

    -- theorem divMod_eq (a b : ℕ₀) : b ≠ 𝟘 → a = (divMod a b).1 * b + (divMod a b).2 := by
    --   intro h_b_neq_0
    --   induction a using well_founded_lt with a ih
    --   unfold divMod
    --   simp [h_b_neq_0]
    --   by_cases h_a_zero : a = 𝟘
    --   · simp [h_a_zero, zero_mul, zero_add]
    --   · simp [h_a_zero]
    --     by_cases h_b_one : b = 𝟙
    --     · simp [h_b_one, mul_one, add_zero]
    --     · simp [h_b_one]
    --       by_cases h_a_lt_b : Lt a b
    --       · simp [h_a_lt_b, zero_mul, zero_add]
    --       · simp [h_a_lt_b]
    --         by_cases h_a_eq_b : a = b
    --         · simp [h_a_eq_b, one_mul, add_zero]
    --         · simp [h_a_eq_b]
    --           have h_b_lt_a : Lt b a := not_lt_and_not_eq_implies_gt a b h_a_lt_b h_a_eq_b
    --           have h_le_b_a : Le b a := lt_imp_le b a h_b_lt_a
    --           have h_sub_lt_a : Lt (sub a b) a := sub_lt_self a b h_le_b_a h_b_neq_0
    --           have h_ih := ih (sub a b) h_sub_lt_a
    --           have h_divMod_ab : divMod a b = (σ (divMod (sub a b) b).1, (divMod (sub a b) b).2) := by
    --             simp [divMod, h_b_neq_0, h_a_zero, h_b_one, h_a_lt_b, h_a_eq_b]
    --           rw [h_divMod_ab, succ_mul]
    --           let q := (divMod (sub a b) b).1
    --           let r := (divMod (sub a b) b).2
    --           have h_ih_qr : sub a b = q * b + r := h_ih
    --           have h_sub_add_b_eq_a : sub a b + b = a := sub_add_cancel_of_le h_le_b_a
    --           rw [h_ih_qr] at h_sub_add_b_eq_a
    --           rw [h_sub_add_b_eq_a, add_assoc, add_comm r b, ←add_assoc]
    --           rw [←one_mul b, ←mul_add, succ_eq_add_one]
    --           rfl

    -- theorem divMod_eq__neq_a_0__lt_1_b
    --   (a b : ℕ₀)
    --   (h_lt_1_b : Lt 𝟙 b) :
    --     a = (divMod a b).1 * b + (divMod a b).2
    --   := by
    --     have h_b_neq_0 : b ≠ 𝟘 := lt_0_then_neq_0 (lt_trans 𝟘 𝟙 b lt_0_1 h_lt_1_b)
    --     exact divMod_eq a b h_b_neq_0

  end Div

end Peano
