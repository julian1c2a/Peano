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
    theorem mem_leftCoset_iff (G : FinGroup) (H : Subgroup G) (g x : ℕ₀)
        (hg : g ∈ G.carrier.elems) :
        x ∈ (leftCoset G H g).elems ↔ ∃ h, h ∈ H.carrier.elems ∧ G.op g h = x := by
      -- (leftCoset G H g).elems = G.carrier.elems.filter pred, por definición
      constructor
      · intro hx
        have hf := List.mem_filter.mp hx
        rw [List.any_eq_true] at hf
        obtain ⟨_, h, hh, hd⟩ := hf
        exact ⟨h, hh, by rwa [decide_eq_true_eq] at hd⟩
      · rintro ⟨h, hh, heq⟩
        exact List.mem_filter.mpr
          ⟨heq ▸ op_mem G hg (H.subset h hh),
           List.any_eq_true.mpr ⟨h, hh, decide_eq_true_eq.mpr heq⟩⟩

    /-- Todo coseto tiene la misma cardinalidad que `H`.
        La función `h ↦ g·h` es una biyección `H → gH`. -/
    theorem coset_card_eq_subgroup_card (G : FinGroup) (H : Subgroup G) (g : ℕ₀)
        (hg : g ∈ G.carrier.elems) :
        (leftCoset G H g).card = H.carrier.card := by
      -- Construimos la biyección h ↦ g·h de H.carrier a gH
      let f : MapOn H.carrier (leftCoset G H g) := {
        toFun := fun h => G.op g h,
        map_carrier := fun h hh =>
          (mem_leftCoset_iff G H g (G.op g h) hg).mpr ⟨h, hh, rfl⟩
      }
      have h_inj : f.Injective := by
        intro h₁ h₂ hh₁ hh₂ heq
        exact op_cancel_left G hg (H.subset h₁ hh₁) (H.subset h₂ hh₂) heq
      have h_surj : f.Surjective := by
        intro y hy
        exact (mem_leftCoset_iff G H g y hg).mp hy
      exact (MapOn.Bijective.card_eq ⟨h_inj, h_surj⟩).symm

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
        cosetRel G H b a := by
      unfold cosetRel at hab ⊢
      -- hab : G.op (G.inv a) b ∈ H
      -- Goal : G.op (G.inv b) a ∈ H
      -- Key: inv(inv(a)·b) = inv(b)·inv(inv(a)) = inv(b)·a
      have h : G.inv (G.op (G.inv a) b) ∈ H.carrier.elems := H.inv_closed _ hab
      rw [inv_op_eq G (inv_mem G ha) hb, inv_inv_eq G ha] at h
      exact h

    theorem cosetRel_trans (G : FinGroup) (H : Subgroup G) (a b c : ℕ₀)
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems) (hc : c ∈ G.carrier.elems)
        (hab : cosetRel G H a b) (hbc : cosetRel G H b c) :
        cosetRel G H a c := by
      unfold cosetRel at hab hbc ⊢
      -- hab : G.op (G.inv a) b ∈ H,  hbc : G.op (G.inv b) c ∈ H
      -- Key: inv(a)·c = (inv(a)·b)·(inv(b)·c) ∈ H (por op_closed)
      have ha' := inv_mem G ha
      have hb' := inv_mem G hb
      have key : G.op (G.inv a) c =
          G.op (G.op (G.inv a) b) (G.op (G.inv b) c) := by
        rw [G.op_assoc (G.inv a) b _ ha' hb (op_mem G hb' hc)]
        rw [← G.op_assoc b (G.inv b) c hb hb' hc]
        rw [(G.op_inv b hb).1, (G.op_id c hc).2]
      rw [key]
      exact H.op_closed _ _ hab hbc

    /-!
    # § 3. Lema de Lagrange
    -/

    /-- **Lema de Lagrange**: el orden de `H` divide al orden de `G`.
        Más precisamente, `|G| = |H| · [G:H]` donde `[G:H]` es el índice. -/
    theorem lagrange (G : FinGroup) (H : Subgroup G) :
        ∃ k : ℕ₀, mul H.carrier.card k = G.carrier.card :=
      sorry
      -- Ingredientes disponibles:
      --   cosetRel es equivalencia (refl, symm, trans ya demostrados)
      --   coset_card_eq_subgroup_card : |gH| = |H|
      -- Falta: partición de G en cosetos + conteo por fibras

  end GroupTheory
end Peano
