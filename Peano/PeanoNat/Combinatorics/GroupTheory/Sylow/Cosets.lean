/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean
-- Cosetos (laterales) de un subgrupo en un grupo finito.
--
-- § 1. Coseto izquierdo gH
-- § 2. Conjunto de cosetos G/H
-- § 3. Lema de Lagrange: |H| · [G:H] = |G|

import Peano.PeanoNat
import Peano.PeanoNat.Mul
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.Combinatorics.Group

set_option autoImplicit false

namespace Peano
  namespace GroupTheory

    open Peano.FSet
    open Peano.FSetFunction
    open Peano.Group
    open Peano.Mul

    /-!
    # § 1. Coseto izquierdo
    -/

    /-- El coseto izquierdo `gH = { g·h | h ∈ H }` como subconjunto de `G.carrier`.
        Se construye filtrando `G.carrier` por los `x = g·h` para algún `h ∈ H`. -/
    def leftCoset (G : FinGroup) (H : Subgroup G) (g : ℕ₀) : ℕ₀FSet :=
      ℕ₀FSet.filter
        (fun x => H.carrier.elems.any (fun h => decide (G.op g h = x)))
        G.carrier

    /-- `x ∈ gH ↔ ∃ h ∈ H, g·h = x`. -/
    theorem mem_leftCoset_iff (G : FinGroup) (H : Subgroup G) (g x : ℕ₀) :
        x ∈ (leftCoset G H g).elems ↔ ∃ h, h ∈ H.carrier.elems ∧ G.op g h = x :=
      sorry  -- requiere unfold de FSet.filter + List.mem_filter + List.any_eq_true

    /-- Todo coseto tiene la misma cardinalidad que `H`.
        La función `h ↦ g·h` es una biyección `H → gH`. -/
    theorem coset_card_eq_subgroup_card (G : FinGroup) (H : Subgroup G) (g : ℕ₀)
        (hg : g ∈ G.carrier.elems) :
        (leftCoset G H g).card = H.carrier.card :=
      sorry  -- biyección h ↦ g·h entre H.carrier y leftCoset G H g

    /-!
    # § 2. Relación de equivalencia por cosetos
    -/

    /-- `a ~ b ↔ a⁻¹·b ∈ H` (relación de equivalencia por cosetos izquierdos). -/
    def cosetRel (G : FinGroup) (H : Subgroup G) (a b : ℕ₀) : Prop :=
      G.op (G.inv a) b ∈ H.carrier.elems

    theorem cosetRel_refl (G : FinGroup) (H : Subgroup G) (a : ℕ₀)
        (ha : a ∈ G.carrier.elems) :
        cosetRel G H a a := by
      unfold cosetRel
      have : G.op (G.inv a) a = G.id := (G.op_inv a ha).2
      rw [this]; exact H.id_in

    theorem cosetRel_symm (G : FinGroup) (H : Subgroup G) (a b : ℕ₀)
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems)
        (hab : cosetRel G H a b) :
        cosetRel G H b a :=
      sorry  -- (a⁻¹·b)⁻¹ = b⁻¹·a ∈ H porque H es cerrado bajo inversas

    theorem cosetRel_trans (G : FinGroup) (H : Subgroup G) (a b c : ℕ₀)
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems) (hc : c ∈ G.carrier.elems)
        (hab : cosetRel G H a b) (hbc : cosetRel G H b c) :
        cosetRel G H a c :=
      sorry  -- a⁻¹·c = (a⁻¹·b)·(b⁻¹·c) ∈ H porque H es cerrado bajo op

    /-!
    # § 3. Lema de Lagrange
    -/

    /-- **Lema de Lagrange**: el orden de `H` divide al orden de `G`.
        Más precisamente, `|G| = |H| · [G:H]` donde `[G:H]` es el índice. -/
    theorem lagrange (G : FinGroup) (H : Subgroup G) :
        ∃ k : ℕ₀, mul H.carrier.card k = G.carrier.card :=
      sorry
      -- Estrategia:
      -- 1. Los cosetos distintos son disjuntos (cosetRel es de equiv.)
      -- 2. Cada coseto tiene cardinalidad |H| (coset_card_eq_subgroup_card)
      -- 3. Los cosetos particionan G
      -- 4. |G| = nº de cosetos · |H|

  end GroupTheory
end Peano
