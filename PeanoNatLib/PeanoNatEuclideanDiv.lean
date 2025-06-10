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

  -- Definition of Euclidean division for Peano natural numbers
  /--!
  Performs Euclidean division of `a` by `b`.
  Returns a pair `(quotient, remainder)` such that `a = quotient * b + remainder`
  and `remainder < b` (if `b ≠ 𝟘`).
  If `b = 𝟘`, returns `(𝟘, 𝟘)`.
  !--/
  def div (a b : ℕ₀) : ℕ₀ × ℕ₀ :=
    if b = 𝟘 then
      (𝟘, 𝟘)
    else if b = 𝟙 then
      (a, 𝟘)
    else if a = b then
      (𝟙, 𝟘)
    else if Lt a b then
      (𝟘, a)
    else
      have h_lt : Lt (sub a b) a := by
        -- Since ¬Lt a b and a ≠ b, we have b ≤ a and a ≠ b, so b < a
        -- Therefore sub a b < a
        sorry -- This needs to be proven using your ordering lemmas
      let (q, r) := div (sub a b) b
      (σ q, r)
    termination_by div a b => a
    decreasing_by
      simp_wf
      -- Prove that sub a b < a when b > 0 and a ≥ b
      sorry -- This needs to be proven using your subtraction and ordering lemmas




  end Div

end Peano
