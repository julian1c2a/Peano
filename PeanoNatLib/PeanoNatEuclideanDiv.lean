import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatMul


namespace Peano
    open Peano

  namespace Div
      open Axioms
      open StrictOrder
      open Order
      open MaxMin
      open Add
      open Sub
      open Mul


  /--!
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
                  apply sub_lt_self
                  exact h_le_b_a -- b ≤ a
                  exact h_b_is_zero -- b ≠ 𝟘
                let (a', b') : ℕ₀ × ℕ₀ := divMod (sub a b) b
                (σ a', b')
    termination_by sizeOf a
    decreasing_by
      simp only [sizeOf]
      apply lt_sizeOf
      exact h_sub_a_b_lt_a

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
      contradiction
    case isFalse h_b_not_zero_again =>
      simp only [Prod.fst, Prod.snd, zero_mul, zero_add]
      exact h_a_eq_zero

  theorem divMod_eq__neq_a_0__eq_b_1
    (a b : ℕ₀)
    (h_a_eq_zero : a ≠ 𝟘)
    (h_b_eq_1 : b = 𝟙) :
      a = (divMod a b).1 * b + (divMod a b).2
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
      -- In this case, b ≠ 𝟘.
      -- The theorem hypotheses are h_a_eq_zero (meaning a ≠ 𝟘) and h_b_eq_1 (b = 𝟙).
      -- These hypotheses are sufficient to simplify `divMod a b` to `(a, 𝟘)`.
      -- The goal becomes `a = (a, 𝟘).1 * b + (a, 𝟘).2`.
      -- Thus, the second `split` is unnecessary and fails. We prove the simplified goal directly.
      simp only [Prod.fst, Prod.snd] -- Goal: a = a * b + 𝟘
      rw [h_b_eq_1] -- Goal: a = a * 𝟙 + 𝟘
      simp only [mul_one, add_zero] -- Goal: a = a, which is true by rfl

  theorem divMod_eq__neq_a_0__lt_1_b__lt_a_b
    (a b : ℕ₀)
    (h_neq_a_0 : a ≠ 𝟘)
    (h_lt_1_b : Lt 𝟙 b)
    (h_lt_a_b : Lt a b):
      -- The goal is to prove that `a = (divMod a b).1 * b + (divMod a b).2`.
      -- We know that `b ≠ 𝟘` and `b ≠ 𝟙` from the hypotheses.
      a = (divMod a b).1 * b + (divMod a b).2
    := by sorry
    -- unfold divMod
    -- split
    -- case isTrue h_b_is_zero =>
    --   have h_b_not_zero : b ≠ 𝟘
    --     := by exact lt_1_b_then_b_neq_0 h_lt_1_b
    --   contradiction -- b ≠ 𝟘 contradicts h_b_is_zero
    -- case isFalse h_b_not_zero_again =>
    --   split
    --   case isTrue h_b_is_one =>
    --     have h_b_not_one : b ≠ 𝟙
    --     := by exact lt_1_b_then_b_neq_1 h_lt_1_b
    --     contradiction -- b ≠ 𝟙 contradicts h_b_is_one
    --   case isFalse h_b_not_one =>
    --     -- In this case, we have `b ≠ 𝟘` and `b ≠ 𝟙`.
    --     -- The theorem hypotheses are h_a_neq_zero (meaning a ≠ 𝟘), h_lt_1_b (b > 𝟙),
    --     -- and h_lt_a_b (a < b).
    --     -- These hypotheses are sufficient to simplify `divMod a b` to `(𝟘, a)`.
    --     -- The goal becomes `a = (𝟘, a).1 * b + (𝟘, a).2`.
    --     simp only [Prod.fst]
    --     --simp only [Prod.snd]
    --     simp only [zero_mul]
    --     --simp only [zero_add]
    --     exact h_lt_a_b -- Goal: a = a, which is true by rfl




  theorem divMod_eq__neq_a_0__lt_1_b__eq_a_b
    (a b : ℕ₀)
    (h_neq_a_0 : a ≠ 𝟘)
    (h_lt_1_b : Lt 𝟙 b)
    (h_eq_a_b : a = b):
      a = (divMod a b).1 * b + (divMod a b).2
    := by sorry

  theorem divMod_eq__neq_a_0__lt_1_b__lt_b_a
    (a b : ℕ₀)
    (h_neq_a_0 : a ≠ 𝟘)
    (h_lt_1_b : Lt 𝟙 b)
    (h_lt_b_a : Lt b a):
      a = (divMod a b).1 * b + (divMod a b).2
    := by sorry



  -- theorem divMod_eq (a b : ℕ₀) (h_lt_a_b : Lt a b):
  --   b ≠ 𝟘 → a = (divMod a b).1 * b + (divMod a b).2
  --     := by
  --   intro h_b_not_zero
  --   unfold divMod
  --   split
  --   case isTrue h_b_is_zero =>
  --     contradiction -- b ≠ 𝟘 contradicts h_b_is_zero
  --   case isFalse h_b_not_zero_again =>
  --     split
  --     case isTrue h_b_is_one =>
  --       rw [h_b_is_one]
  --       simp only [mul_one, add_zero]
  --     case isFalse h_b_not_one =>
  --       have h_qr_eq_0a : (divMod a b) = (𝟘, a) := by
  --         simp [divMod, h_b_not_zero_again, h_b_not_one, h_lt_a_b]
  --       simp only [h_qr_eq_0a, zero_mul, zero_add]


  end Div

end Peano
