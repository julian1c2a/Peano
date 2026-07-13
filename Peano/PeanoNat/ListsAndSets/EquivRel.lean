/-
Copyright (c) 2026. All rights reserved.
Author: Julian Calderon Almendros
License: MIT
-/

-- Peano/PeanoNat/ListsAndSets/EquivRel.lean
-- Relaciones de equivalencia sobre dominios finitos (FSet).
--
-- § 1. EquivRelOn  -- relación de equivalencia restringida a A : FSet α
-- § 2. classOf     -- clase de equivalencia de un elemento
-- § 3. Lemas base  -- pertenencia, cobertura, igualdad/disjunción de clases

import Peano.PeanoNat.ListsAndSets.FSet

set_option autoImplicit false

namespace Peano
  namespace EquivRel

    open Peano.FSet

    /-- Relación de equivalencia sobre un dominio finito `A : FSet α`.
        Las leyes (refl/symm/trans) se exigen solo para elementos de `A`. -/
    structure EquivRelOn {α : Type} [DecidableEq α] [LT α]
        (A : FSet α) where
      rel      : α -> α -> Prop
      decRel   : DecidableRel rel
      refl_on  : ∀ a, a ∈ A.elems -> rel a a
      symm_on  : ∀ a b, a ∈ A.elems -> b ∈ A.elems -> rel a b -> rel b a
      trans_on : ∀ a b c,
        a ∈ A.elems -> b ∈ A.elems -> c ∈ A.elems ->
        rel a b -> rel b c -> rel a c

    /-- Clase de equivalencia de `a` en `A`: `{ x ∈ A | a ~ x }`. -/
    def EquivRelOn.classOf {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (a : α) : FSet α := by
      let _ : DecidableRel R.rel := R.decRel
      exact A.filter (fun x => decide (R.rel a x))

    theorem EquivRelOn.mem_classOf_iff {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (a x : α) :
        x ∈ (R.classOf a).elems ↔ x ∈ A.elems ∧ R.rel a x := by
      let _ : DecidableRel R.rel := R.decRel
      simp [EquivRelOn.classOf, FSet.filter, decide_eq_true_eq]

    theorem EquivRelOn.classOf_nonempty_of_mem {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (a : α) (ha : a ∈ A.elems) :
        a ∈ (R.classOf a).elems :=
      (R.mem_classOf_iff a a).mpr ⟨ha, R.refl_on a ha⟩

    theorem EquivRelOn.classOf_subset_domain {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (a x : α)
        (hx : x ∈ (R.classOf a).elems) :
        x ∈ A.elems :=
      (R.mem_classOf_iff a x).mp hx |>.1

    theorem EquivRelOn.rel_of_mem_classOf {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (a x : α)
        (hx : x ∈ (R.classOf a).elems) :
        R.rel a x :=
      (R.mem_classOf_iff a x).mp hx |>.2

    theorem EquivRelOn.mem_classOf_of_rel {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (a x : α)
        (hxA : x ∈ A.elems) (hax : R.rel a x) :
        x ∈ (R.classOf a).elems :=
      (R.mem_classOf_iff a x).mpr ⟨hxA, hax⟩

    theorem EquivRelOn.classOf_eq_of_mem_classOf
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {A : FSet α} (R : EquivRelOn A) (a x : α)
        (ha : a ∈ A.elems) (hx : x ∈ (R.classOf a).elems) :
        R.classOf x = R.classOf a := by
      have hxA : x ∈ A.elems := (R.mem_classOf_iff a x).mp hx |>.1
      have hax : R.rel a x := (R.mem_classOf_iff a x).mp hx |>.2
      have hxa : R.rel x a := R.symm_on a x ha hxA hax
      apply FSet.eq_of_mem_iff'
      intro y
      constructor
      · intro hxy
        have hyA : y ∈ A.elems := (R.mem_classOf_iff x y).mp hxy |>.1
        have hxy' : R.rel x y := (R.mem_classOf_iff x y).mp hxy |>.2
        have hay : R.rel a y := R.trans_on a x y ha hxA hyA hax hxy'
        exact (R.mem_classOf_iff a y).mpr ⟨hyA, hay⟩
      · intro hay
        have hyA : y ∈ A.elems := (R.mem_classOf_iff a y).mp hay |>.1
        have hay' : R.rel a y := (R.mem_classOf_iff a y).mp hay |>.2
        have hxy : R.rel x y := R.trans_on x a y hxA ha hyA hxa hay'
        exact (R.mem_classOf_iff x y).mpr ⟨hyA, hxy⟩

    theorem EquivRelOn.mem_classOf_iff_of_rel {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A)
        (a b x : α)
        (ha : a ∈ A.elems) (hb : b ∈ A.elems)
        (hab : R.rel a b) :
        x ∈ (R.classOf a).elems ↔ x ∈ (R.classOf b).elems := by
      constructor
      · intro hxa
        have hxA : x ∈ A.elems := (R.mem_classOf_iff a x).mp hxa |>.1
        have hax : R.rel a x := (R.mem_classOf_iff a x).mp hxa |>.2
        have hba : R.rel b a := R.symm_on a b ha hb hab
        have hbx : R.rel b x := R.trans_on b a x hb ha hxA hba hax
        exact (R.mem_classOf_iff b x).mpr ⟨hxA, hbx⟩
      · intro hxb
        have hxA : x ∈ A.elems := (R.mem_classOf_iff b x).mp hxb |>.1
        have hbx : R.rel b x := (R.mem_classOf_iff b x).mp hxb |>.2
        have habx : R.rel a x := R.trans_on a b x ha hb hxA hab hbx
        exact (R.mem_classOf_iff a x).mpr ⟨hxA, habx⟩

    theorem EquivRelOn.classOf_eq_or_disjoint {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A)
        (a b : α)
        (ha : a ∈ A.elems) (hb : b ∈ A.elems) :
        (∀ x, x ∈ (R.classOf a).elems ↔ x ∈ (R.classOf b).elems) ∨
        (∀ z, z ∉ (R.classOf a).elems ∨ z ∉ (R.classOf b).elems) := by
      cases hInt : (R.classOf a).elems.any (fun z => decide (z ∈ (R.classOf b).elems)) with
      | true =>
        left
        obtain ⟨z, hza, hzb_dec⟩ := List.any_eq_true.mp hInt
        have hzb : z ∈ (R.classOf b).elems := decide_eq_true_eq.mp hzb_dec
        have hzA : z ∈ A.elems := (R.mem_classOf_iff a z).mp hza |>.1
        have haz : R.rel a z := (R.mem_classOf_iff a z).mp hza |>.2
        have hbz : R.rel b z := (R.mem_classOf_iff b z).mp hzb |>.2
        have hzb' : R.rel z b := R.symm_on b z hb hzA hbz
        have hab : R.rel a b := R.trans_on a z b ha hzA hb haz hzb'
        intro x
        exact R.mem_classOf_iff_of_rel a b x ha hb hab
      | false =>
        have hNotInt : ¬∃ z, z ∈ (R.classOf a).elems ∧ z ∈ (R.classOf b).elems := by
          rintro ⟨z, hza, hzb⟩
          have htrue : (R.classOf a).elems.any (fun w => decide (w ∈ (R.classOf b).elems)) = true :=
            List.any_eq_true.mpr ⟨z, hza, decide_eq_true_eq.mpr hzb⟩
          simp [hInt] at htrue
        right
        intro z
        by_cases hza : z ∈ (R.classOf a).elems
        · exact Or.inr (fun hzb => hNotInt ⟨z, hza, hzb⟩)
        · exact Or.inl hza

    /-- Familia finita de representantes de clases de equivalencia sobre `A`.
        Modela la capa de partición por clases sin requerir todavía cocientes. -/
    structure EquivRelOn.ClassFamily {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) where
      reps : List α
      reps_subset : ∀ r, r ∈ reps -> r ∈ A.elems
      cover : ∀ x, x ∈ A.elems -> ∃ r, r ∈ reps ∧ x ∈ (R.classOf r).elems
      pairwise_classes : ∀ r s, r ∈ reps -> s ∈ reps ->
        (∀ x, x ∈ (R.classOf r).elems ↔ x ∈ (R.classOf s).elems) ∨
        (∀ z, z ∉ (R.classOf r).elems ∨ z ∉ (R.classOf s).elems)

    /-- Familia canónica de clases: usar `A.elems` como lista de representantes.
        Siempre cubre `A`; dos clases de representantes son iguales o disjuntas. -/
    def EquivRelOn.canonicalClassFamily {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) : R.ClassFamily where
      reps := A.elems
      reps_subset := fun r hr => hr
      cover := fun x hx => ⟨x, hx, R.classOf_nonempty_of_mem x hx⟩
      pairwise_classes := fun r s hr hs =>
        R.classOf_eq_or_disjoint r s (by exact hr) (by exact hs)

    /-- Lista canónica de clases de equivalencia: imagen `a ↦ classOf a`
        sobre `A.elems`, con duplicados eliminados por igualdad de `FSet`. -/
    def EquivRelOn.classes {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) : List (FSet α) :=
      (A.elems.map (fun a => R.classOf a)).eraseDups

    theorem EquivRelOn.mem_classes_iff {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (C : FSet α) :
        C ∈ R.classes ↔ ∃ a, a ∈ A.elems ∧ R.classOf a = C := by
      constructor
      · intro hC
        have hMap : C ∈ A.elems.map (fun a => R.classOf a) :=
          (List.mem_eraseDups.mp hC)
        rw [List.mem_map] at hMap
        rcases hMap with ⟨a, ha, hEq⟩
        exact ⟨a, ha, hEq⟩
      · rintro ⟨a, ha, hEq⟩
        apply List.mem_eraseDups.mpr
        rw [List.mem_map]
        exact ⟨a, ha, hEq⟩

    theorem EquivRelOn.classOf_mem_classes_of_mem {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (a : α) (ha : a ∈ A.elems) :
        R.classOf a ∈ R.classes :=
      (R.mem_classes_iff (R.classOf a)).mpr ⟨a, ha, rfl⟩

    theorem EquivRelOn.mem_classes_elim {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A)
        {C : FSet α} (hC : C ∈ R.classes) :
        ∃ a, a ∈ A.elems ∧ C = R.classOf a := by
      rcases (R.mem_classes_iff C).mp hC with ⟨a, ha, hEq⟩
      exact ⟨a, ha, hEq.symm⟩

    theorem EquivRelOn.classes_cover {α : Type} [DecidableEq α] [LT α]
        {A : FSet α} (R : EquivRelOn A) (x : α) (hx : x ∈ A.elems) :
        ∃ C, C ∈ R.classes ∧ x ∈ C.elems := by
      refine ⟨R.classOf x, R.classOf_mem_classes_of_mem x hx, ?_⟩
      exact R.classOf_nonempty_of_mem x hx

  end EquivRel
end Peano

export Peano.EquivRel (
  EquivRelOn
  EquivRelOn.classOf
  EquivRelOn.mem_classOf_iff
  EquivRelOn.classOf_nonempty_of_mem
  EquivRelOn.classOf_subset_domain
  EquivRelOn.rel_of_mem_classOf
  EquivRelOn.mem_classOf_of_rel
  EquivRelOn.classOf_eq_of_mem_classOf
  EquivRelOn.mem_classOf_iff_of_rel
  EquivRelOn.classOf_eq_or_disjoint
  EquivRelOn.ClassFamily
  EquivRelOn.canonicalClassFamily
  EquivRelOn.classes
  EquivRelOn.mem_classes_iff
  EquivRelOn.classOf_mem_classes_of_mem
  EquivRelOn.mem_classes_elim
  EquivRelOn.classes_cover
)
