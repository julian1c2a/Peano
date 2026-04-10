/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Group.lean

import Peano.PeanoNat
import Peano.PeanoNat.FSet

set_option autoImplicit false

namespace Peano
  namespace Group
      open Peano.FSet

      /-!
      ## Definición de grupo finito polimórfico
      -/
      structure FinGroup where
        carrier : ℕ₀FSet
        op : ℕ₀ → ℕ₀ → ℕ₀
        id : ℕ₀
        inv : ℕ₀ → ℕ₀
        op_closed : ∀ a b, a ∈ carrier.elems → b ∈ carrier.elems → op a b ∈ carrier.elems
        id_in : id ∈ carrier.elems
        inv_in : ∀ a, a ∈ carrier.elems → inv a ∈ carrier.elems
        op_assoc : ∀ a b c, a ∈ carrier.elems → b ∈ carrier.elems → c ∈ carrier.elems →
          op (op a b) c = op a (op b c)
        op_id : ∀ a, a ∈ carrier.elems → op a id = a ∧ op id a = a
        op_inv : ∀ a, a ∈ carrier.elems → op a (inv a) = id ∧ op (inv a) a = id
    /-!
    ## Definición de grupo finito
    -/

    /-!
    # § 1. Definición de grupo
    !-/
    -- ...

    /-!
    # § 2. Ejemplos
    !-/
    -- ...

    /-!
    # § 3. Subgrupos y orden
    !-/

    /--
    Un subgrupo de un grupo finito G es un subconjunto no vacío cerrado por la operación y la inversa, con la misma operación.
    -/
    structure Subgroup (G : FinGroup) where
      carrier : ℕ₀FSet
      nonempty : ∃ a, a ∈ carrier
      subset : ∀ a, a ∈ carrier → a ∈ G.carrier
      op_closed : ∀ a b, a ∈ carrier → b ∈ carrier → G.op a b ∈ carrier
      id_in : G.id ∈ carrier
      inv_closed : ∀ a, a ∈ carrier → G.inv a ∈ carrier

    /-!
    # § 4. Homomorfismos y morfismos
    !-/

    /--
    Un morfismo de grupos finitos es una función que respeta la operación, el neutro y la inversa.
    -/
    structure GroupHom (G H : FinGroup) where
      toFun : ℕ₀ → ℕ₀
      map_carrier : ∀ a, a ∈ G.carrier.elems → toFun a ∈ H.carrier.elems
      map_op : ∀ a b, a ∈ G.carrier.elems → b ∈ G.carrier.elems →
        toFun (G.op a b) = H.op (toFun a) (toFun b)
      map_id : toFun G.id = H.id
      map_inv : ∀ a, a ∈ G.carrier.elems → toFun (G.inv a) = H.inv (toFun a)

    /-!
    ## § 2. Ejemplo: grupo simétrico (grupo de permutaciones)
    !-/

    -- Definición de Permutación: función biyectiva de A en A
    structure Perm (A : ℕ₀FSet) where
      toFun : ℕ₀ → ℕ₀
      -- bijective : Function.Bijective toFun -- (comentado para compilar)
      map_carrier : ∀ a, a ∈ A.elems → toFun a ∈ A.elems



    /--
    El grupo simétrico sobre A: conjunto de todas las permutaciones de A, con composición.
    -/
    /-
    def Sym (A : ℕ₀FSet) : FinGroup := ...
    -/

  end Group
end Peano
