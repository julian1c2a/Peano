import Peano.PeanoNat.Combinatorics.Group
set_option autoImplicit false
namespace Peano
  open Peano.Group
  private theorem subgroup_ext' {G : FinGroup ℕ₀} {H K : Subgroup G}
      (h : H.carrier = K.carrier) : H = K := by
    cases H; cases K
    simp only [] at h
    subst h
    rename_i ne1 sub1 op1 id1 inv1 ne2 sub2 op2 id2 inv2
    simp only [show ne1 = ne2 from proof_irrel _ _,
               show sub1 = sub2 from proof_irrel _ _,
               show op1 = op2 from proof_irrel _ _,
               show id1 = id2 from proof_irrel _ _,
               show inv1 = inv2 from proof_irrel _ _]
end Peano
