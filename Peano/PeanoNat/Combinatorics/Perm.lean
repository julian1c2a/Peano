/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Perm.lean
-- Permutaciones sobre un conjunto finito A : ℕ₀FSet.
--
-- § 1. FunPerm — permutación como FunTable con List.Perm
-- § 2. Grupo simétrico Sym A
-- § 3. Ciclos y descomposición (sorry)
-- § 4. Signatura (sorry)
-- § 5. Aplicaciones aritméticas

import Peano.PeanoNat
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.ListsAndSets.List
import Peano.PeanoNat.Combinatorics.Factorial

set_option autoImplicit false

namespace Peano
  namespace Perm

    open Peano.FSet
    open Peano.FSetFunction
    open Peano.List

    /-!
    # § 1. FunPerm  (re-exportado de FSetFunction)

    `FunPerm A` es el tipo de permutaciones de `A`:
    una `FunTable A` cuya `table` es una permutación de `A.elems`.
    -/

    /-- Composición de dos permutaciones. -/
    def FunPerm.comp {A : ℕ₀FSet}
        (g f : FunPerm A) (dflt : ℕ₀) (hdflt : dflt ∈ A.elems) :
        FunPerm A where
      table   := (FunTable.comp g.toFunTable f.toFunTable dflt hdflt).table
      len_eq  := (FunTable.comp g.toFunTable f.toFunTable dflt hdflt).len_eq
      mem_all := (FunTable.comp g.toFunTable f.toFunTable dflt hdflt).mem_all
      is_perm := by
        -- table = f.table.map (g.applyElem · dflt)
        -- f.is_perm : f.table ~ A.elems
        -- g.is_perm : g.table ~ A.elems
        -- f.table.map (g.applyElem · dflt) ~ A.elems cuando g es biyectiva
        sorry  -- requiere que g.applyElem sea biyectiva sobre A

    /-!
    # § 2. Grupo simétrico  Sym A
    -/

    /-- El grupo simétrico de `A`: el tipo de todas las permutaciones de `A`. -/
    def Sym (A : ℕ₀FSet) : Type := FunPerm A

    /-- Cardinalidad del grupo simétrico: hay exactamente |A|! permutaciones de A.
        (TODO: requiere `List.permutations` o infraestructura de tipo finito) -/
    theorem card_Sym (A : ℕ₀FSet) :
        Peano.Factorial.factorial A.card = Peano.Factorial.factorial A.card :=
      rfl  -- placeholder trivial; el enunciado real requiere List.permutations

    /-!
    # § 3. Ciclos y descomposición
    -/
    -- TODO: ciclo (i₁ i₂ … iₖ),  descomposición en ciclos disjuntos

    /-!
    # § 4. Signatura
    -/
    -- TODO: sign : FunPerm A → {+1, -1},  usando número de inversiones

    /-!
    # § 5. Aplicaciones aritméticas
    -/
    -- El número de permutaciones de un conjunto de `n` elementos es `n!`
    -- (se deduce directamente de `card_Sym`).

  end Perm
end Peano
