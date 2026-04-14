/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Group.lean

import Peano.PeanoNat
import Peano.PeanoNat.FSet
import Peano.PeanoNat.FSetFunction

set_option autoImplicit false

namespace Peano
  namespace Group
    open Peano.FSet
    open Peano.FSetFunction

    /-!
    # § 4. Estructura de Grupo Finito
    -/

    structure FinGroup where
      carrier : ℕ₀FSet
      op : BinOpOn carrier
      id : ℕ₀
      inv : MapOn carrier carrier
      id_in :
        id ∈ carrier.elems
      op_assoc :
        ∀ a b c,
          a ∈ carrier.elems → b ∈ carrier.elems → c ∈ carrier.elems →
            op (op a b) c = op a (op b c)
      op_id :
        ∀ a,
          a ∈ carrier.elems → op a id = a ∧ op id a = a
      op_inv :
        ∀ a,
          a ∈ carrier.elems → op a (inv a) = id ∧ op (inv a) a = id

    /--
    En cualquier `FinGroup`, el elemento neutro es único.
    -/
    theorem id_unique (G : FinGroup) (e' : ℕ₀)
        (h_e'_in : e' ∈ G.carrier.elems)
        (h_is_id : ∀ a, a ∈ G.carrier.elems → G.op a e' = a ∧ G.op e' a = a) :
        e' = G.id := by
      -- La prueba se basa en que G.id = G.op G.id e' (por la propiedad de e') y e' = G.op G.id e' (por la propiedad de G.id).
      -- Por tanto, e' = G.id.
      let h_id_op_e' := (h_is_id G.id G.id_in).left
      let h_e'_op_id := (G.op_id e' h_e'_in).right
      exact h_e'_op_id.symm.trans h_id_op_e'

    /-!
    # § 5. Subgrupos
    !-/

    /--
    Un subgrupo de un grupo finito G es un subconjunto no vacío cerrado por la operación y la inversa, con la misma operación.
    -/
    structure Subgroup (G : FinGroup) where
      carrier : ℕ₀FSet
      nonempty : ∃ a, a ∈ carrier.elems
      subset : ∀ a, a ∈ carrier.elems → a ∈ G.carrier.elems
      op_closed : ∀ a b, a ∈ carrier.elems → b ∈ carrier.elems → G.op a b ∈ carrier.elems
      id_in : G.id ∈ carrier.elems
      inv_closed : ∀ a, a ∈ carrier.elems → G.inv a ∈ carrier.elems

    /-!
    # § 6. Homomorfismos
    !-/

    /--
    Un morfismo de grupos finitos es una función que respeta la operación, el neutro y la inversa.
    -/
    structure GroupHom (G H : FinGroup) where
      map : MapOn G.carrier H.carrier
      map_op : ∀ a b, a ∈ G.carrier.elems → b ∈ G.carrier.elems →
        map (G.op a b) = H.op (map a) (map b)
      map_id : map G.id = H.id
      map_inv : ∀ a, a ∈ G.carrier.elems → map (G.inv a) = H.inv (map a)

    /-!
    # § 7. Grupo Simétrico (Permutaciones)
    -/

    -- Definición de Permutación: función biyectiva de A en A
    structure Perm (A : ℕ₀FSet) where
      map : MapOn A A
      bijective : map.Bijective



    /--
    El grupo simétrico sobre A: conjunto de todas las permutaciones de A, con composición.
    -/
    def Sym (A : ℕ₀FSet) : FinGroup where
      carrier := sorry  -- El conjunto de todas las permutaciones de A, codificadas como ℕ₀
      op := {
        toFun := fun p₁ p₂ => sorry,
        map_carrier := sorry
      }
      id := sorry      -- La permutación identidad
      inv := {
        toFun := fun p => sorry,
        map_carrier := sorry
      }
      id_in := sorry
      op_assoc := sorry
      op_id := sorry
      op_inv := sorry

  end Group
end Peano
