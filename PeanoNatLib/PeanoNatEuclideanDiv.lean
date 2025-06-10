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

  theorem divMod_eq (a b : ℕ₀) :
    a = (divMod a b).1 * b + (divMod a b).2
      := by sorry

  end Div

end Peano
