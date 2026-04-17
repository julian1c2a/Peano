import Peano.PeanoNat.Combinatorics.Pow
open Peano
#check Peano.Pow.pow_zero
example (p : ℕ₀) : p ^ 𝟘 = 𝟙 := by
  exact Peano.Pow.pow_zero p
