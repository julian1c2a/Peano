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
  def div (a b : ℕ₀) : ℕ₀ × ℕ₀ :=
    if b = 0 then
      (0, 0)
    else if b = 𝟙 then
      (a, 0)
    else if a = b then
      (𝟙, 0)
    else if a < b then
      (0, a)
    else
      let (q, r) := div (sub a b) b
      (q + 𝟙, r)
  end div

  


  end Div

end Peano
