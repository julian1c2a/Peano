import Peano.PeanoNat.Combinatorics.Summation
import Peano.PeanoNat.Combinatorics.GroupTheory.NormalSubgroup
import Peano.PeanoNat.Combinatorics.GroupTheory.Action
open Peano Peano.Group Peano.Mul Peano.FSet Peano.GroupTheory

-- Test conjugAction definition
def testConjAct (G : FinGroup ℕ₀) : GroupAction G G.carrier where
  act := fun g x => G.op (G.op g x) (G.inv g)
  act_closed := fun g x hg hx => op_mem G (op_mem G hg hx) (inv_mem G hg)
  act_id := fun x hx => by
    show G.op (G.op G.id x) (G.inv G.id) = x
    rw [inv_id_eq G, (G.op_id x hx).2, (G.op_id x hx).1]
  act_compat := fun g h x hg hh hx => by
    show G.op (G.op g (G.op (G.op h x) (G.inv h))) (G.inv g) =
         G.op (G.op (G.op g h) x) (G.inv (G.op g h))
    rw [inv_op_eq G hg hh]
    have hghx : G.op (G.op g h) x ∈ G.carrier.elems := op_mem G (op_mem G hg hh) hx
    have hhx  : G.op h x ∈ G.carrier.elems := op_mem G hh hx
    have hhinv : G.inv h ∈ G.carrier.elems := inv_mem G hh
    have hginv : G.inv g ∈ G.carrier.elems := inv_mem G hg
    calc G.op (G.op g (G.op (G.op h x) (G.inv h))) (G.inv g)
        = G.op (G.op (G.op g (G.op h x)) (G.inv h)) (G.inv g) := by
              rw [← G.op_assoc g (G.op h x) (G.inv h) hg hhx hhinv]
      _ = G.op (G.op (G.op (G.op g h) x) (G.inv h)) (G.inv g) := by
              rw [← G.op_assoc g h x hg hh hx]
      _ = G.op (G.op (G.op g h) x) (G.op (G.inv h) (G.inv g)) :=
              G.op_assoc _ _ _ hghx hhinv hginv
