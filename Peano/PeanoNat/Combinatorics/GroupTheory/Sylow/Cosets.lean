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
import Peano.PeanoNat.ListsAndSets.EquivRel
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.Combinatorics.Group

set_option autoImplicit false

namespace Peano
  namespace GroupTheory

    open Peano.FSet
    open Peano.EquivRel
    open Peano.FSetFunction
    open Peano.Group
    open Peano.Mul

    /-!
    # § 1. Coseto izquierdo
    -/

    /-- El coseto izquierdo `gH = { g·h | h ∈ H }` como subconjunto de `G.carrier`.
        Se construye filtrando `G.carrier` por los `x = g·h` para algún `h ∈ H`. -/
    def leftCoset {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (g : α) : FSet α :=
      FSet.filter
        (fun x => H.carrier.elems.any (fun h => decide (G.op g h = x)))
        G.carrier

    /-- `x ∈ gH ↔ ∃ h ∈ H, g·h = x`. -/
    theorem mem_leftCoset_iff {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (g x : α)
        (hg : g ∈ G.carrier.elems) :
        x ∈ (leftCoset G H g).elems ↔ ∃ h, h ∈ H.carrier.elems ∧ G.op g h = x := by
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
    theorem coset_card_eq_subgroup_card {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (g : α)
        (hg : g ∈ G.carrier.elems) :
        (leftCoset G H g).card = H.carrier.card := by
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
    def cosetRel {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (a b : α) : Prop :=
      G.op (G.inv a) b ∈ H.carrier.elems

    theorem cosetRel_refl {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (a : α)
        (ha : a ∈ G.carrier.elems) :
        cosetRel G H a a := by
      unfold cosetRel
      have : G.op (G.inv a) a = G.id := (G.op_inv a ha).2
      rw [this]; exact H.id_in

    theorem cosetRel_symm {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (a b : α)
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems)
        (hab : cosetRel G H a b) :
        cosetRel G H b a := by
      unfold cosetRel at hab ⊢
      have h : G.inv (G.op (G.inv a) b) ∈ H.carrier.elems := H.inv_closed _ hab
      rw [inv_op_eq G (inv_mem G ha) hb, inv_inv_eq G ha] at h
      exact h

    theorem cosetRel_trans {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (a b c : α)
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems) (hc : c ∈ G.carrier.elems)
        (hab : cosetRel G H a b) (hbc : cosetRel G H b c) :
        cosetRel G H a c := by
      unfold cosetRel at hab hbc ⊢
      have ha' := inv_mem G ha
      have hb' := inv_mem G hb
      have key : G.op (G.inv a) c =
          G.op (G.op (G.inv a) b) (G.op (G.inv b) c) := by
        rw [G.op_assoc (G.inv a) b _ ha' hb (op_mem G hb' hc)]
        rw [← G.op_assoc b (G.inv b) c hb hb' hc]
        rw [(G.op_inv b hb).1, (G.op_id c hc).2]
      rw [key]
      exact H.op_closed _ _ hab hbc

    /-- `cosetRel` como relación de equivalencia sobre `G.carrier`. -/
    def cosetEquivRel {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) : EquivRelOn G.carrier where
      rel      := cosetRel G H
      decRel   := by
        intro a b
        unfold cosetRel
        infer_instance
      refl_on  := fun a ha => cosetRel_refl G H a ha
      symm_on  := fun a b ha hb hab => cosetRel_symm G H a b ha hb hab
      trans_on := fun a b c ha hb hc hab hbc =>
        cosetRel_trans G H a b c ha hb hc hab hbc

    /-- Para `g ∈ G`, la clase de equivalencia de `g` por `cosetRel`
        coincide punto a punto con el coseto izquierdo `gH`. -/
    theorem mem_classOf_cosetEquivRel_iff_leftCoset
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (g x : α)
        (hg : g ∈ G.carrier.elems) :
        x ∈ ((cosetEquivRel G H).classOf g).elems ↔
        x ∈ (leftCoset G H g).elems := by
      constructor
      · intro hx
        have hxA : x ∈ G.carrier.elems :=
          ((cosetEquivRel G H).mem_classOf_iff g x).mp hx |>.1
        have hrel : cosetRel G H g x :=
          ((cosetEquivRel G H).mem_classOf_iff g x).mp hx |>.2
        have hInH : G.op (G.inv g) x ∈ H.carrier.elems := hrel
        have hginv : G.inv g ∈ G.carrier.elems := inv_mem G hg
        have hEq : G.op g (G.op (G.inv g) x) = x := by
          rw [← G.op_assoc g (G.inv g) x hg hginv hxA,
              (G.op_inv g hg).1,
              (G.op_id x hxA).2]
        exact (mem_leftCoset_iff G H g x hg).mpr ⟨G.op (G.inv g) x, hInH, hEq⟩
      · intro hx
        obtain ⟨h, hh, hEq⟩ := (mem_leftCoset_iff G H g x hg).mp hx
        have hxA : x ∈ G.carrier.elems := by
          rw [← hEq]
          exact op_mem G hg (H.subset h hh)
        have hrel : cosetRel G H g x := by
          unfold cosetRel
          rw [← hEq]
          have hginv : G.inv g ∈ G.carrier.elems := inv_mem G hg
          rw [← G.op_assoc (G.inv g) g h hginv hg (H.subset h hh),
              (G.op_inv g hg).2,
              (G.op_id h (H.subset h hh)).2]
          exact hh
        exact ((cosetEquivRel G H).mem_classOf_iff g x).mpr ⟨hxA, hrel⟩

    /-- Igualdad extensional: clase de `g` por `cosetRel` = coseto `gH`. -/
    theorem classOf_cosetEquivRel_eq_leftCoset
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (g : α)
        (hg : g ∈ G.carrier.elems) :
        (cosetEquivRel G H).classOf g = leftCoset G H g := by
      apply FSet.eq_of_mem_iff'
      intro x
      exact mem_classOf_cosetEquivRel_iff_leftCoset G H g x hg

    /-- Corolario de cardinal: toda clase por `cosetRel` tiene cardinal `|H|`. -/
    theorem classOf_cosetEquivRel_card_eq_subgroup_card
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (g : α)
        (hg : g ∈ G.carrier.elems) :
        ((cosetEquivRel G H).classOf g).card = H.carrier.card := by
      rw [classOf_cosetEquivRel_eq_leftCoset G H g hg]
      exact coset_card_eq_subgroup_card G H g hg

    /-- Familia canónica de representantes de clases para `cosetRel` en `G`.
        Se usa como soporte finito para el conteo por clases en Lagrange. -/
    def cosetClassFamily {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) :
        (cosetEquivRel G H).ClassFamily :=
      (cosetEquivRel G H).canonicalClassFamily

    /-- Cobertura canónica: todo `x ∈ G` pertenece a la clase de algún representante
        de la familia canónica por cosetos. -/
    theorem mem_some_cosetClassFamily_class
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G)
        (x : α) (hx : x ∈ G.carrier.elems) :
        ∃ r, r ∈ (cosetClassFamily G H).reps ∧
          x ∈ ((cosetEquivRel G H).classOf r).elems :=
      (cosetClassFamily G H).cover x hx

    /-- Lista canónica de clases de equivalencia por cosetos en `G`. -/
    def cosetClasses {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) : List (FSet α) :=
      (cosetEquivRel G H).classes

    /-- Uniformidad de cardinal en `cosetClasses`: cada clase tiene cardinal `|H|`. -/
    theorem card_eq_subgroup_card_of_mem_cosetClasses
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) (C : FSet α)
        (hC : C ∈ cosetClasses G H) :
        C.card = H.carrier.card := by
      rcases ((cosetEquivRel G H).mem_classes_iff C).mp hC with ⟨g, hg, hCg⟩
      rw [← hCg]
      exact classOf_cosetEquivRel_card_eq_subgroup_card G H g hg

    /-- Cobertura por clases canónicas de cosetos: todo `x ∈ G` pertenece a
        alguna clase de `cosetClasses`. -/
    theorem mem_some_cosetClasses
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G)
        (x : α) (hx : x ∈ G.carrier.elems) :
        ∃ C, C ∈ cosetClasses G H ∧ x ∈ C.elems :=
      (cosetEquivRel G H).classes_cover x hx

    /-- Si `x ∈ C` y `C` es una clase canónica por cosetos, entonces
        `C` coincide con la clase de `x`. -/
    theorem cosetClass_eq_classOf_of_mem
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G)
        (C : FSet α) (x : α)
        (hC : C ∈ cosetClasses G H) (hxC : x ∈ C.elems) :
        C = (cosetEquivRel G H).classOf x := by
      rcases (cosetEquivRel G H).mem_classes_elim hC with ⟨a, ha, hCa⟩
      rw [hCa] at hxC
      have hEq : (cosetEquivRel G H).classOf x = (cosetEquivRel G H).classOf a :=
        (cosetEquivRel G H).classOf_eq_of_mem_classOf a x ha hxC
      rw [hCa]
      exact hEq.symm

    /-- Si `a ~ b` por `cosetRel`, entonces `aH ⊆ bH`. -/
    theorem leftCoset_subset_of_rel {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G)
        (a b : α)
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems)
        (hab : cosetRel G H a b) :
        ∀ x, x ∈ (leftCoset G H a).elems → x ∈ (leftCoset G H b).elems := by
      intro x hx
      have habH : G.op (G.inv a) b ∈ H.carrier.elems := hab
      obtain ⟨h, hh, hax⟩ := (mem_leftCoset_iff G H a x ha).mp hx
      have h_invab_memG : G.op (G.inv a) b ∈ G.carrier.elems := H.subset _ habH
      have h_inv_invab_memH : G.inv (G.op (G.inv a) b) ∈ H.carrier.elems :=
        H.inv_closed _ habH
      have hh_memG : h ∈ G.carrier.elems := H.subset _ hh
      let hAux : α := G.op (G.inv (G.op (G.inv a) b)) h
      have hhAux : hAux ∈ H.carrier.elems :=
        H.op_closed _ _ h_inv_invab_memH hh
      have hbx : G.op b hAux = x := by
        have hbab : b = G.op a (G.op (G.inv a) b) := by
          rw [← G.op_assoc a (G.inv a) b ha (inv_mem G ha) hb,
              (G.op_inv a ha).1, (G.op_id b hb).2]
        have hstep1 : G.op b hAux = G.op (G.op a (G.op (G.inv a) b)) hAux :=
          congrArg (fun t => G.op t hAux) hbab
        calc
          G.op b hAux
              = G.op (G.op a (G.op (G.inv a) b))
                  hAux := hstep1
          _ = G.op a
                (G.op (G.op (G.inv a) b)
                  hAux) := by
                    rw [G.op_assoc a (G.op (G.inv a) b)
                      hAux
                      ha h_invab_memG (H.subset _ hhAux)]
          _ = G.op a
                (G.op (G.op (G.inv a) b)
                  (G.op (G.inv (G.op (G.inv a) b)) h)) := by
                    simp [hAux]
          _ = G.op a (G.op (G.op (G.op (G.inv a) b) (G.inv (G.op (G.inv a) b))) h) := by
                    rw [← G.op_assoc (G.op (G.inv a) b) (G.inv (G.op (G.inv a) b)) h
                      h_invab_memG (inv_mem G h_invab_memG) hh_memG]
          _ = G.op a h := by
                    rw [(G.op_inv (G.op (G.inv a) b) h_invab_memG).1,
                        (G.op_id h hh_memG).2]
          _ = x := hax
      exact (mem_leftCoset_iff G H b x hb).mpr ⟨hAux, hhAux, hbx⟩

    /-- Si `a ~ b`, entonces los cosetos izquierdos coinciden: `aH = bH`. -/
    theorem leftCoset_eq_of_rel {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G)
        (a b : α)
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems)
        (hab : cosetRel G H a b) :
        leftCoset G H a = leftCoset G H b := by
      apply FSet.eq_of_mem_iff'
      intro x
      constructor
      · exact leftCoset_subset_of_rel G H a b ha hb hab x
      · have hba : cosetRel G H b a := cosetRel_symm G H a b ha hb hab
        exact leftCoset_subset_of_rel G H b a hb ha hba x

    /-!
    # § 3. Lema de Lagrange
    -/

    /-- **Lema de Lagrange**: el orden de `H` divide al orden de `G`.
        Más precisamente, `|G| = |H| · [G:H]` donde `[G:H]` es el índice. -/
    theorem lagrange {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G) :
        ∃ k : ℕ₀, mul H.carrier.card k = G.carrier.card := by
      let classes := cosetClasses G H
      let classesSorted := sortList' classes
      have h_sorted : Sorted (· < ·) classesSorted :=
        sorted_sortList' classes
      let classesFSet : FSet (FSet α) :=
        ⟨classesSorted, h_sorted⟩

      have h_uniform : ∀ C, C ∈ classes → C.card = H.carrier.card :=
        card_eq_subgroup_card_of_mem_cosetClasses G H

      let f : MapOn G.carrier classesFSet := {
        toFun := fun x => (cosetEquivRel G H).classOf x
        map_carrier := fun x hx => by
          have hx_class : (cosetEquivRel G H).classOf x ∈ classes :=
            (cosetEquivRel G H).classOf_mem_classes_of_mem x hx
          exact (mem_sortList'_iff (x := (cosetEquivRel G H).classOf x)
            (l := classes)).mpr hx_class
      }

      have h_fiber : ∀ C, C ∈ classesFSet.elems → (f.fiber C).card = H.carrier.card :=
        fun C hCfs => by
          have hC : C ∈ classes :=
            (mem_sortList'_iff (x := C) (l := classes)).mp hCfs

          have h_fiber_eq : f.fiber C = C := by
            apply FSet.eq_of_mem_iff'
            intro x
            constructor
            · intro hx
              have hxData := (MapOn.mem_fiber_iff f C x).mp hx
              have hxClass : x ∈ ((cosetEquivRel G H).classOf x).elems :=
                (cosetEquivRel G H).classOf_nonempty_of_mem x hxData.1
              have hfx : (cosetEquivRel G H).classOf x = C := by
                simpa [f] using hxData.2
              exact hfx ▸ hxClass
            · intro hxC
              have hCeq : C = (cosetEquivRel G H).classOf x :=
                cosetClass_eq_classOf_of_mem G H C x hC hxC
              have hxClass : x ∈ ((cosetEquivRel G H).classOf x).elems := by
                simpa [← hCeq] using hxC
              have hxG : x ∈ G.carrier.elems :=
                (cosetEquivRel G H).classOf_subset_domain x x hxClass
              exact (MapOn.mem_fiber_iff f C x).mpr ⟨hxG, by simp [f, hCeq.symm]⟩

          calc
            (f.fiber C).card = C.card := by simp [h_fiber_eq]
            _ = H.carrier.card := h_uniform C hC

      have h_card :=
        FSetFunction.card_eq_mul_of_uniform_fibers f H.carrier.card h_fiber

      exact ⟨classesFSet.card, Eq.symm h_card⟩

  end GroupTheory
end Peano
