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
--
-- Ciclos/descomposición y signatura de permutaciones son responsabilidad de
-- Sign.lean (namespace Peano.Sign, reservado, pendiente de implementación) —
-- no se duplican aquí.

import Peano.PeanoNat
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.ListsAndSets.List

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
        (g f : FunPerm A) (dflt : ℕ₀) :
        FunPerm A where
      table   := (FunTable.comp g.toFunTable f.toFunTable dflt).table
      len_eq  := (FunTable.comp g.toFunTable f.toFunTable dflt).len_eq
      mem_all := (FunTable.comp g.toFunTable f.toFunTable dflt).mem_all
      is_perm := by
        -- table = f.table.map (fun a => g.applyElem a dflt)
        show List.Perm (f.table.map (fun a => g.applyElem a dflt)) A.elems
        have hA_nodup : A.elems.Nodup := sorted_nodup A.sorted
        have h_mem : ∀ a, a ∈ A.elems → g.applyElem a dflt ∈ A.elems :=
          fun a ha => FunTable.applyElem_mem g.toFunTable a dflt ha
        have h_inj : ∀ a b, a ∈ A.elems → b ∈ A.elems →
            g.applyElem a dflt = g.applyElem b dflt → a = b :=
          fun a b ha hb heq => FunPerm.applyElem_injective g dflt ha hb heq
        exact (f.is_perm.map (fun a => g.applyElem a dflt)).trans
          (perm_map_of_injective_on_nodup
            (fun a => g.applyElem a dflt) A.elems hA_nodup h_mem h_inj)

    /-!
    # § 2. Grupo simétrico  Sym A
    -/

    /-- El grupo simétrico de `A`: el tipo de todas las permutaciones de `A`. -/
    def Sym (A : ℕ₀FSet) : Type := FunPerm A

  end Perm
end Peano

export Peano.Perm (
  FunPerm.comp
  Sym
)
