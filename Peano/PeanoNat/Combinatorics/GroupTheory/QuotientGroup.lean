import Peano.PeanoNat
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Arith
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets
import Peano.PeanoNat.Combinatorics.GroupTheory.NormalSubgroup

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Grupo Cociente G/H

Construye la estructura de grupo finito en el conjunto de cosetos izquierdos
`G/H = { gH | g ∈ G }` cuando `H` es normal en `G`.

## Contenido

- `quotientCarrier G H` — portador del cociente como `Nat0FSetFSet`
- `cosetRepOf G H C` — representante canónico de un coseto
- `quotientOp_welldefined` — bien-definición de la operación bajo normalidad
- `quotientOp G H hn` — operación binaria del cociente
- `quotientGroup G H hn` — estructura `FinGroup ℕ₀FSet`
- `quotient_card` — |G/H| = |G| / |H|
- `quotientHomomorphism` — homomorfismo canónico G → G/H
-/

set_option autoImplicit false

namespace Peano
  namespace QuotientGroup
    open Peano.FSet Peano.FSetFunction Peano.Group Peano.Cosets

    /-!
    ## § 1. Portador del cociente
    -/

    /-- El portador del cociente `G/H`: colección de cosetos izquierdos ordenada. -/
    def quotientCarrier (G : FinGroup ℕ₀) (H : Subgroup G) : Nat0FSetFSet :=
      Nat0FSetFSet.ofSortedList (sortFSetList (cosetClasses G H))
        (sorted_sortFSetList (cosetClasses G H))

    /-- Un coseto pertenece a `quotientCarrier G H` ssi es una clase de `cosetClasses G H`. -/
    theorem mem_quotientCarrier_iff (G : FinGroup ℕ₀) (H : Subgroup G) (C : ℕ₀FSet) :
        C ∈ (quotientCarrier G H).elems ↔ C ∈ cosetClasses G H :=
      mem_sortFSetList_iff

    /-- Todo `C ∈ quotientCarrier G H` es de la forma `leftCoset G H g` para algún `g ∈ G`. -/
    theorem mem_quotientCarrier_is_leftCoset (G : FinGroup ℕ₀) (H : Subgroup G)
        (C : ℕ₀FSet) (hC : C ∈ (quotientCarrier G H).elems) :
        ∃ g, g ∈ G.carrier.elems ∧ C = leftCoset G H g := by
      rw [mem_quotientCarrier_iff] at hC
      rcases (cosetEquivRel G H).mem_classes_elim hC with ⟨g, hg, rfl⟩
      exact ⟨g, hg, classOf_cosetEquivRel_eq_leftCoset G H g hg⟩

    /-- Cada coseto en el portador es no vacío. -/
    theorem coset_nonempty_of_mem_quotientCarrier (G : FinGroup ℕ₀) (H : Subgroup G)
        (C : ℕ₀FSet) (hC : C ∈ (quotientCarrier G H).elems) : C.elems ≠ [] := by
      obtain ⟨g, hg, rfl⟩ := mem_quotientCarrier_is_leftCoset G H C hC
      intro h
      have : g ∈ (leftCoset G H g).elems :=
        (mem_leftCoset_iff G H g g hg).mpr ⟨G.id, H.id_in, (G.op_id g hg).1⟩
      simp [h] at this

    /-- Todo coseto izquierdo `leftCoset G H g` (con `g ∈ G`) pertenece a `cosetClasses G H`. -/
    theorem leftCoset_mem_cosetClasses (G : FinGroup ℕ₀) (H : Subgroup G)
        (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
        leftCoset G H g ∈ cosetClasses G H := by
      rw [← classOf_cosetEquivRel_eq_leftCoset G H g hg]
      exact (cosetEquivRel G H).classOf_mem_classes_of_mem g hg

    /-- Todo coseto izquierdo (con rep en G) pertenece al portador del cociente. -/
    theorem leftCoset_mem_quotientCarrier (G : FinGroup ℕ₀) (H : Subgroup G)
        (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
        leftCoset G H g ∈ (quotientCarrier G H).elems :=
      (mem_quotientCarrier_iff G H _).mpr (leftCoset_mem_cosetClasses G H g hg)

    /-- La identidad H = leftCoset G H G.id pertenece al portador del cociente. -/
    theorem leftCoset_id_mem_quotientCarrier (G : FinGroup ℕ₀) (H : Subgroup G) :
        leftCoset G H G.id ∈ (quotientCarrier G H).elems :=
      leftCoset_mem_quotientCarrier G H G.id G.id_in

    /-!
    ## § 2. Igualdad de cosetos y cosetRel
    -/

    /-- Convertir igualdad de cosetos a `cosetRel G H a a'`. -/
    theorem cosetRel_of_leftCoset_eq (G : FinGroup ℕ₀) (H : Subgroup G) (a a' : ℕ₀)
        (ha : a ∈ G.carrier.elems) (ha' : a' ∈ G.carrier.elems)
        (h : leftCoset G H a = leftCoset G H a') : cosetRel G H a a' := by
      have ha_self : a ∈ (leftCoset G H a).elems :=
        (mem_leftCoset_iff G H a a ha).mpr ⟨G.id, H.id_in, (G.op_id a ha).1⟩
      rw [h, ← classOf_cosetEquivRel_eq_leftCoset G H a' ha'] at ha_self
      exact cosetRel_symm G H a' a ha' ha
        ((cosetEquivRel G H).rel_of_mem_classOf a' a ha_self)

    /-- Bicondicional: `leftCoset G H a = leftCoset G H a' ↔ cosetRel G H a a'`. -/
    theorem leftCoset_eq_iff_cosetRel (G : FinGroup ℕ₀) (H : Subgroup G) (a a' : ℕ₀)
        (ha : a ∈ G.carrier.elems) (ha' : a' ∈ G.carrier.elems) :
        leftCoset G H a = leftCoset G H a' ↔ cosetRel G H a a' :=
      ⟨cosetRel_of_leftCoset_eq G H a a' ha ha',
       leftCoset_eq_of_rel G H a a' ha ha'⟩

    /-!
    ## § 3. Representante canónico de un coseto
    -/

    /-- Representante canónico: primer elemento de la lista del coseto.
        Para `C.elems = []` (imposible en el portador) devuelve `G.id` por defecto. -/
    noncomputable def cosetRepOf (G : FinGroup ℕ₀) (_H : Subgroup G) (C : ℕ₀FSet) : ℕ₀ :=
      if h : C.elems = [] then G.id else C.elems.head h

    theorem cosetRepOf_eq_head (G : FinGroup ℕ₀) (H : Subgroup G) (C : ℕ₀FSet)
        (hne : C.elems ≠ []) : cosetRepOf G H C = C.elems.head hne := by
      simp [cosetRepOf, hne]

    /-- El representante canónico pertenece al coseto. -/
    theorem cosetRepOf_mem_C (G : FinGroup ℕ₀) (H : Subgroup G) (C : ℕ₀FSet)
        (hC : C ∈ (quotientCarrier G H).elems) :
        cosetRepOf G H C ∈ C.elems := by
      have hne := coset_nonempty_of_mem_quotientCarrier G H C hC
      rw [cosetRepOf_eq_head G H C hne]
      exact List.head_mem hne

    /-- El representante canónico pertenece a `G`. -/
    theorem cosetRepOf_mem_G (G : FinGroup ℕ₀) (H : Subgroup G) (C : ℕ₀FSet)
        (hC : C ∈ (quotientCarrier G H).elems) :
        cosetRepOf G H C ∈ G.carrier.elems := by
      have hC' : C ∈ cosetClasses G H := (mem_quotientCarrier_iff G H C).mp hC
      rcases (cosetEquivRel G H).mem_classes_elim hC' with ⟨g, hg, hCg⟩
      -- hCg : C = classOf g → classOf g = leftCoset G H g → C = leftCoset G H g
      have hCg' : C = leftCoset G H g :=
        hCg.trans (classOf_cosetEquivRel_eq_leftCoset G H g hg)
      rw [hCg']  -- goal: cosetRepOf G H (leftCoset G H g) ∈ G.carrier.elems
      have hC_rw : leftCoset G H g ∈ (quotientCarrier G H).elems := hCg' ▸ hC
      have hrep := cosetRepOf_mem_C G H (leftCoset G H g) hC_rw
      obtain ⟨h, hh, heq⟩ := (mem_leftCoset_iff G H g
          (cosetRepOf G H (leftCoset G H g)) hg).mp hrep
      rw [← heq]
      exact op_mem G hg (H.subset h hh)

    /-- El coseto izquierdo del representante es el coseto original. -/
    theorem cosetRepOf_leftCoset_eq (G : FinGroup ℕ₀) (H : Subgroup G) (C : ℕ₀FSet)
        (hC : C ∈ (quotientCarrier G H).elems) :
        leftCoset G H (cosetRepOf G H C) = C := by
      have hC' : C ∈ cosetClasses G H := (mem_quotientCarrier_iff G H C).mp hC
      have hrep : cosetRepOf G H C ∈ C.elems := cosetRepOf_mem_C G H C hC
      have hCeq : C = (cosetEquivRel G H).classOf (cosetRepOf G H C) :=
        cosetClass_eq_classOf_of_mem G H C (cosetRepOf G H C) hC' hrep
      calc leftCoset G H (cosetRepOf G H C)
          = (cosetEquivRel G H).classOf (cosetRepOf G H C) :=
              (classOf_cosetEquivRel_eq_leftCoset G H (cosetRepOf G H C)
                (cosetRepOf_mem_G G H C hC)).symm
        _ = C := hCeq.symm

    /-!
    ## § 4. Bien-definición de la operación de cosetos
    -/

    /-- **Bien-definición**: si `C₁ = aH` y `C₂ = bH`, entonces `(ab)H` solo depende
        de `C₁` y `C₂` (no de la elección de representante), bajo normalidad de `H`. -/
    theorem quotientOp_welldefined (G : FinGroup ℕ₀) (H : Subgroup G) (hn : H.IsNormal)
        (a a' b b' : ℕ₀)
        (ha : a ∈ G.carrier.elems) (ha' : a' ∈ G.carrier.elems)
        (hb : b ∈ G.carrier.elems) (hb' : b' ∈ G.carrier.elems)
        (haa' : leftCoset G H a = leftCoset G H a')
        (hbb' : leftCoset G H b = leftCoset G H b') :
        leftCoset G H (G.op a b) = leftCoset G H (G.op a' b') := by
      apply leftCoset_eq_of_rel G H _ _ (op_mem G ha hb) (op_mem G ha' hb')
      -- Sea k₁ = a⁻¹·a' ∈ H,  k₂ = b⁻¹·b' ∈ H
      have hk₁ : G.op (G.inv a) a' ∈ H.carrier.elems :=
        cosetRel_of_leftCoset_eq G H a a' ha ha' haa'
      have hk₂ : G.op (G.inv b) b' ∈ H.carrier.elems :=
        cosetRel_of_leftCoset_eq G H b b' hb hb' hbb'
      have ha_inv : G.inv a ∈ G.carrier.elems := inv_mem G ha
      have hb_inv : G.inv b ∈ G.carrier.elems := inv_mem G hb
      have hk₁_G : G.op (G.inv a) a' ∈ G.carrier.elems := H.subset _ hk₁
      have hk₂_G : G.op (G.inv b) b' ∈ G.carrier.elems := H.subset _ hk₂
      -- a' = a·k₁  (pues k₁ = a⁻¹·a', luego a·k₁ = a·a⁻¹·a' = a')
      have ha'_eq : a' = G.op a (G.op (G.inv a) a') := by
        rw [← G.op_assoc a (G.inv a) a' ha ha_inv ha',
            (G.op_inv a ha).1, (G.op_id a' ha').2]
      -- b' = b·k₂
      have hb'_eq : b' = G.op b (G.op (G.inv b) b') := by
        rw [← G.op_assoc b (G.inv b) b' hb hb_inv hb',
            (G.op_inv b hb).1, (G.op_id b' hb').2]
      -- b⁻¹·k₁·b ∈ H por normalidad
      have hconj : G.op (G.op (G.inv b) (G.op (G.inv a) a')) b ∈ H.carrier.elems := by
        have := hn (G.inv b) (G.op (G.inv a) a') hb_inv hk₁
        rwa [inv_inv_eq G hb] at this
      -- Ahora: G.inv(ab)·(a'b') = b⁻¹·a⁻¹·(a·k₁)·(b·k₂)
      --      = b⁻¹·k₁·b·k₂  (cancelando a⁻¹·a = e)
      unfold cosetRel
      rw [ha'_eq, hb'_eq, inv_op_eq G ha hb,
          G.op_assoc (G.inv b) (G.inv a) _ hb_inv ha_inv
            (op_mem G (op_mem G ha hk₁_G) (op_mem G hb hk₂_G)),
          ← G.op_assoc (G.inv a) (G.op a (G.op (G.inv a) a'))
              (G.op b (G.op (G.inv b) b'))
              ha_inv (op_mem G ha hk₁_G) (op_mem G hb hk₂_G),
          ← G.op_assoc (G.inv a) a (G.op (G.inv a) a') ha_inv ha hk₁_G,
          (G.op_inv a ha).2, (G.op_id _ hk₁_G).2,
          ← G.op_assoc (G.inv b) (G.op (G.inv a) a') (G.op b (G.op (G.inv b) b'))
              hb_inv hk₁_G (op_mem G hb hk₂_G),
          ← G.op_assoc (G.op (G.inv b) (G.op (G.inv a) a')) b (G.op (G.inv b) b')
              (op_mem G hb_inv hk₁_G) hb hk₂_G]
      exact H.op_closed _ _ hconj hk₂

    /-!
    ## § 5. Operación del grupo cociente
    -/

    /-- Operación del cociente: `C₁ · C₂ = (rep C₁ · rep C₂)H`. -/
    noncomputable def quotientOp (G : FinGroup ℕ₀) (H : Subgroup G)
        (_hn : H.IsNormal) : BinOpOn (quotientCarrier G H) where
      toFun C₁ C₂ := leftCoset G H (G.op (cosetRepOf G H C₁) (cosetRepOf G H C₂))
      map_carrier := fun C₁ C₂ h₁ h₂ => by
        rw [mem_quotientCarrier_iff]
        exact leftCoset_mem_cosetClasses G H _
          (op_mem G (cosetRepOf_mem_G G H C₁ h₁) (cosetRepOf_mem_G G H C₂ h₂))

    /-!
    ## § 6. Inverso en el cociente
    -/

    /-- El coseto inverso de `C = gH` es `g⁻¹H`. -/
    noncomputable def quotientInv (G : FinGroup ℕ₀) (H : Subgroup G)
        (_hn : H.IsNormal) : MapOn (quotientCarrier G H) (quotientCarrier G H) where
      toFun C := leftCoset G H (G.inv (cosetRepOf G H C))
      map_carrier := fun C hC => by
        rw [mem_quotientCarrier_iff]
        exact leftCoset_mem_cosetClasses G H _
          (inv_mem G (cosetRepOf_mem_G G H C hC))

    /-!
    ## § 7. Identidad del cociente
    -/

    /-- La identidad del cociente es el coseto `G.id · H = H`. -/
    noncomputable def quotientId (G : FinGroup ℕ₀) (H : Subgroup G) : ℕ₀FSet :=
      leftCoset G H G.id

    /-- La identidad pertenece al portador del cociente. -/
    theorem quotientId_mem (G : FinGroup ℕ₀) (H : Subgroup G) :
        quotientId G H ∈ (quotientCarrier G H).elems :=
      leftCoset_id_mem_quotientCarrier G H

    /-!
    ## § 8. Axiomas del grupo cociente

    Los tres axiomas (asociatividad, identidad, inverso) se reducen a los axiomas
    del grupo `G` vía la bien-definición de la operación.
    -/

    section GroupAxioms

    variable (G : FinGroup ℕ₀) (H : Subgroup G) (hn : H.IsNormal)

    /-- **Axioma de asociatividad** del cociente: `(C₁C₂)C₃ = C₁(C₂C₃)`. -/
    theorem quotientOp_assoc (C₁ C₂ C₃ : ℕ₀FSet)
        (hC₁ : C₁ ∈ (quotientCarrier G H).elems)
        (hC₂ : C₂ ∈ (quotientCarrier G H).elems)
        (hC₃ : C₃ ∈ (quotientCarrier G H).elems) :
        (quotientOp G H hn) ((quotientOp G H hn) C₁ C₂) C₃ =
          (quotientOp G H hn) C₁ ((quotientOp G H hn) C₂ C₃) := by
      simp only [quotientOp]
      have ha := cosetRepOf_mem_G G H C₁ hC₁
      have hb := cosetRepOf_mem_G G H C₂ hC₂
      have hc := cosetRepOf_mem_G G H C₃ hC₃
      have hab_in : leftCoset G H (G.op (cosetRepOf G H C₁) (cosetRepOf G H C₂)) ∈
          (quotientCarrier G H).elems :=
        leftCoset_mem_quotientCarrier G H _ (op_mem G ha hb)
      have hbc_in : leftCoset G H (G.op (cosetRepOf G H C₂) (cosetRepOf G H C₃)) ∈
          (quotientCarrier G H).elems :=
        leftCoset_mem_quotientCarrier G H _ (op_mem G hb hc)
      have lhs_eq : leftCoset G H (G.op
              (cosetRepOf G H (leftCoset G H (G.op (cosetRepOf G H C₁) (cosetRepOf G H C₂))))
              (cosetRepOf G H C₃)) =
          leftCoset G H (G.op (cosetRepOf G H C₁) (G.op (cosetRepOf G H C₂) (cosetRepOf G H C₃))) :=
        (quotientOp_welldefined G H hn
            (cosetRepOf G H (leftCoset G H (G.op (cosetRepOf G H C₁) (cosetRepOf G H C₂))))
            (G.op (cosetRepOf G H C₁) (cosetRepOf G H C₂))
            (cosetRepOf G H C₃) (cosetRepOf G H C₃)
            (cosetRepOf_mem_G G H _ hab_in) (op_mem G ha hb) hc hc
            (cosetRepOf_leftCoset_eq G H _ hab_in) rfl).trans
          (congrArg (leftCoset G H)
            (G.op_assoc (cosetRepOf G H C₁) (cosetRepOf G H C₂) (cosetRepOf G H C₃) ha hb hc))
      have rhs_eq : leftCoset G H (G.op
              (cosetRepOf G H C₁)
              (cosetRepOf G H (leftCoset G H (G.op (cosetRepOf G H C₂) (cosetRepOf G H C₃))))) =
          leftCoset G H (G.op (cosetRepOf G H C₁) (G.op (cosetRepOf G H C₂) (cosetRepOf G H C₃))) :=
        quotientOp_welldefined G H hn
            (cosetRepOf G H C₁) (cosetRepOf G H C₁)
            (cosetRepOf G H (leftCoset G H (G.op (cosetRepOf G H C₂) (cosetRepOf G H C₃))))
            (G.op (cosetRepOf G H C₂) (cosetRepOf G H C₃))
            ha ha (cosetRepOf_mem_G G H _ hbc_in) (op_mem G hb hc)
            rfl (cosetRepOf_leftCoset_eq G H _ hbc_in)
      exact lhs_eq.trans rhs_eq.symm

    /-- **Axioma de identidad** del cociente: `C · eH = C` y `eH · C = C`. -/
    theorem quotientOp_id (C : ℕ₀FSet)
        (hC : C ∈ (quotientCarrier G H).elems) :
        (quotientOp G H hn) C (quotientId G H) = C ∧
          (quotientOp G H hn) (quotientId G H) C = C := by
      simp only [quotientOp, quotientId]
      have ha := cosetRepOf_mem_G G H C hC
      have hid_in := leftCoset_id_mem_quotientCarrier G H
      have he' := cosetRepOf_mem_G G H (leftCoset G H G.id) hid_in
      have he'_eq := cosetRepOf_leftCoset_eq G H (leftCoset G H G.id) hid_in
      have hC_eq := cosetRepOf_leftCoset_eq G H C hC
      constructor
      · exact ((quotientOp_welldefined G H hn
              (cosetRepOf G H C) (cosetRepOf G H C)
              (cosetRepOf G H (leftCoset G H G.id)) G.id
              ha ha he' G.id_in rfl he'_eq).trans
            (congrArg (leftCoset G H) (G.op_id (cosetRepOf G H C) ha).1)).trans hC_eq
      · exact ((quotientOp_welldefined G H hn
              (cosetRepOf G H (leftCoset G H G.id)) G.id
              (cosetRepOf G H C) (cosetRepOf G H C)
              he' G.id_in ha ha he'_eq rfl).trans
            (congrArg (leftCoset G H) (G.op_id (cosetRepOf G H C) ha).2)).trans hC_eq

    /-- **Axioma de inverso** del cociente: `C · C⁻¹ = eH` y `C⁻¹ · C = eH`. -/
    theorem quotientOp_inv (C : ℕ₀FSet)
        (hC : C ∈ (quotientCarrier G H).elems) :
        (quotientOp G H hn) C ((quotientInv G H hn) C) = quotientId G H ∧
          (quotientOp G H hn) ((quotientInv G H hn) C) C = quotientId G H := by
      simp only [quotientOp, quotientInv, quotientId]
      have ha := cosetRepOf_mem_G G H C hC
      have ha_inv := inv_mem G ha
      have hinv_in : leftCoset G H (G.inv (cosetRepOf G H C)) ∈ (quotientCarrier G H).elems :=
        leftCoset_mem_quotientCarrier G H _ ha_inv
      have ha'_eq := cosetRepOf_leftCoset_eq G H
        (leftCoset G H (G.inv (cosetRepOf G H C))) hinv_in
      have ha' := cosetRepOf_mem_G G H (leftCoset G H (G.inv (cosetRepOf G H C))) hinv_in
      constructor
      · exact (quotientOp_welldefined G H hn
              (cosetRepOf G H C) (cosetRepOf G H C)
              (cosetRepOf G H (leftCoset G H (G.inv (cosetRepOf G H C))))
              (G.inv (cosetRepOf G H C))
              ha ha ha' ha_inv rfl ha'_eq).trans
            (congrArg (leftCoset G H) (G.op_inv (cosetRepOf G H C) ha).1)
      · exact (quotientOp_welldefined G H hn
              (cosetRepOf G H (leftCoset G H (G.inv (cosetRepOf G H C))))
              (G.inv (cosetRepOf G H C))
              (cosetRepOf G H C) (cosetRepOf G H C)
              ha' ha_inv ha ha ha'_eq rfl).trans
            (congrArg (leftCoset G H) (G.op_inv (cosetRepOf G H C) ha).2)

    end GroupAxioms

    /-!
    ## § 9. Estructura `FinGroup ℕ₀FSet`
    -/

    /-- **Grupo cociente** `G/H` cuando `H` es normal en `G`.
        Es un `FinGroup ℕ₀FSet` cuyos elementos son los cosetos izquierdos `gH`. -/
    noncomputable def quotientGroup (G : FinGroup ℕ₀) (H : Subgroup G)
        (hn : H.IsNormal) : FinGroup ℕ₀FSet where
      carrier  := quotientCarrier G H
      op       := quotientOp G H hn
      id       := quotientId G H
      inv      := quotientInv G H hn
      id_in    := quotientId_mem G H
      op_assoc := fun C₁ C₂ C₃ hC₁ hC₂ hC₃ =>
        quotientOp_assoc G H hn C₁ C₂ C₃ hC₁ hC₂ hC₃
      op_id    := fun C hC => quotientOp_id G H hn C hC
      op_inv   := fun C hC => quotientOp_inv G H hn C hC

    /-!
    ## § 10. Cardinal del cociente: |G/H| = |G| / |H|
    -/

    /-- El número de cosetos es `|G| / |H|`. -/
    theorem quotient_card (G : FinGroup ℕ₀) (H : Subgroup G) :
        (quotientCarrier G H).card = Peano.Div.div G.carrier.card H.carrier.card := by
      -- Definimos f : G → quotientCarrier G H por g ↦ classOf g
      let f : MapOn G.carrier (quotientCarrier G H) := {
        toFun := fun x => (cosetEquivRel G H).classOf x
        map_carrier := fun x hx =>
          (mem_quotientCarrier_iff G H _).mpr
            ((cosetEquivRel G H).classOf_mem_classes_of_mem x hx)
      }
      -- Cada fibra f.fiber C = C, luego tiene cardinal |H|
      have h_fiber : ∀ C, C ∈ (quotientCarrier G H).elems →
          (f.fiber C).card = H.carrier.card := fun C hCqs => by
        have hC : C ∈ cosetClasses G H := (mem_quotientCarrier_iff G H C).mp hCqs
        have h_fiber_eq : f.fiber C = C := by
          apply FSet.eq_of_mem_iff; intro x; constructor
          · intro hx
            have hxData := (MapOn.mem_fiber_iff f C x).mp hx
            have hxClass : x ∈ ((cosetEquivRel G H).classOf x).elems :=
              (cosetEquivRel G H).classOf_nonempty_of_mem x hxData.1
            have hfx : (cosetEquivRel G H).classOf x = C := by simpa [f] using hxData.2
            exact hfx ▸ hxClass
          · intro hxC
            have hCeq : C = (cosetEquivRel G H).classOf x :=
              cosetClass_eq_classOf_of_mem G H C x hC hxC
            have hxClass : x ∈ ((cosetEquivRel G H).classOf x).elems := by
              simpa [← hCeq] using hxC
            have hxG := (cosetEquivRel G H).classOf_subset_domain x x hxClass
            exact (MapOn.mem_fiber_iff f C x).mpr ⟨hxG, by simp [f, hCeq.symm]⟩
        calc (f.fiber C).card = C.card := by simp [h_fiber_eq]
          _ = H.carrier.card := card_eq_subgroup_card_of_mem_cosetClasses G H C hC
      -- Aplicamos card_eq_mul_of_uniform_fibers: |G| = |H| · |G/H|
      have h_mul : G.carrier.card = mul H.carrier.card (quotientCarrier G H).card :=
        card_eq_mul_of_uniform_fibers f H.carrier.card h_fiber
      -- H es no vacío → |H| ≠ 0
      have hH_ne : H.carrier.card ≠ 𝟘 := by
        obtain ⟨a, ha⟩ := H.nonempty
        intro h
        cases h_elems : H.carrier.elems with
        | nil => exact absurd (h_elems ▸ ha) List.not_mem_nil
        | cons hd tl =>
          have hcard : H.carrier.card = σ (lengthₚ tl) := by
            unfold FSet.card; rw [h_elems, lengthₚ_cons]
          exact Axioms.succ_neq_zero _ (hcard ▸ h)
      -- |H| ∣ |G| (por Lagrange vía card_eq_mul_of_uniform_fibers)
      have h_dvd : Arith.Divides H.carrier.card G.carrier.card :=
        ⟨(quotientCarrier G H).card, h_mul⟩
      -- div_mul_cancel da: mul (|G|/|H|) |H| = |G|
      have h_div_mul : mul (G.carrier.card / H.carrier.card) H.carrier.card = G.carrier.card :=
        Arith.div_mul_cancel hH_ne h_dvd
      -- Cancelamos |H| de  |H| · |G/H| = |H| · (|G|/|H|)
      have h_eq : mul H.carrier.card (quotientCarrier G H).card =
          mul H.carrier.card (G.carrier.card / H.carrier.card) :=
        h_mul.symm.trans (h_div_mul.symm.trans (Mul.mul_comm _ _))
      exact Mul.mul_cancelation_left H.carrier.card _ _ hH_ne h_eq

    /-!
    ## § 11. Homomorfismo canónico G → G/H
    -/

    /-- Homomorfismo natural `π : G → G/H`, `g ↦ gH`. -/
    noncomputable def quotientHomomorphism (G : FinGroup ℕ₀) (H : Subgroup G) :
        MapOn G.carrier (quotientCarrier G H) where
      toFun g := leftCoset G H g
      map_carrier := fun g hg =>
        leftCoset_mem_quotientCarrier G H g hg

    /-- `π` es compatible con la operación: `π(ab) = π(a) · π(b)`. -/
    theorem quotientHomomorphism_op (G : FinGroup ℕ₀) (H : Subgroup G) (hn : H.IsNormal)
        (a b : ℕ₀) (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems) :
        (quotientHomomorphism G H) (G.op a b) =
          (quotientOp G H hn) ((quotientHomomorphism G H) a) ((quotientHomomorphism G H) b) := by
      simp only [quotientHomomorphism, quotientOp]
      have ha_in := leftCoset_mem_quotientCarrier G H a ha
      have hb_in := leftCoset_mem_quotientCarrier G H b hb
      exact quotientOp_welldefined G H hn a
        (cosetRepOf G H (leftCoset G H a)) b (cosetRepOf G H (leftCoset G H b))
        ha (cosetRepOf_mem_G G H _ ha_in)
        hb (cosetRepOf_mem_G G H _ hb_in)
        (cosetRepOf_leftCoset_eq G H _ ha_in).symm
        (cosetRepOf_leftCoset_eq G H _ hb_in).symm

    /-- El núcleo de `π` es precisamente `H`. -/
    theorem quotientHomomorphism_kernel (G : FinGroup ℕ₀) (H : Subgroup G) (_hn : H.IsNormal)
        (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
        (quotientHomomorphism G H) g = quotientId G H ↔ g ∈ H.carrier.elems := by
      simp only [quotientHomomorphism, quotientId]
      constructor
      · intro heq
        -- cosetRel G H g G.id, i.e., G.inv g · G.id ∈ H, i.e., G.inv g ∈ H
        -- y G.inv (G.inv g) = g ∈ H (por inv_closed)
        have hrel := cosetRel_of_leftCoset_eq G H g G.id hg G.id_in heq
        unfold cosetRel at hrel
        rw [(G.op_id (G.inv g) (inv_mem G hg)).1] at hrel
        -- hrel : G.inv g ∈ H.carrier.elems
        have hinv := H.inv_closed _ hrel
        rwa [inv_inv_eq G hg] at hinv
      · intro hgH
        -- g ∈ H, así cosetRel G H g G.id: G.inv g · G.id = G.inv g ∈ H (por inv_closed)
        apply (leftCoset_eq_iff_cosetRel G H g G.id hg G.id_in).mpr
        unfold cosetRel
        rw [(G.op_id (G.inv g) (inv_mem G hg)).1]
        exact H.inv_closed _ hgH

    /-!
    ## § 12. Teorema de correspondencia (versión básica)

    Si `K` es un subgrupo de `G` con `H ≤ K`, entonces `K/H` es un
    subgrupo de `G/H`, y este mapa da una biyección entre subgrupos
    de `G` que contienen `H` y subgrupos de `G/H`.
    -/

    /-- La imagen de un subgrupo `K` de `G` (con `H ≤ K`) bajo `π` es un subgrupo
        del cociente `G/H`. Se prueba como subgrupo de `FinGroup ℕ₀FSet`. -/
    noncomputable def imageSubgroup (G : FinGroup ℕ₀) (H : Subgroup G) (hn : H.IsNormal)
        (K : Subgroup G) (_hHK : ∀ h, h ∈ H.carrier.elems → h ∈ K.carrier.elems) :
        Subgroup (quotientGroup G H hn) where
      carrier := {
        elems := sortFSetList (K.carrier.elems.map (leftCoset G H))
        sorted := sorted_sortFSetList _
      }
      nonempty := ⟨leftCoset G H G.id,
        mem_sortFSetList_iff.mpr (List.mem_map.mpr ⟨G.id, K.id_in, rfl⟩)⟩
      subset := fun C hC => by
        rw [mem_sortFSetList_iff] at hC
        simp only [List.mem_map] at hC
        obtain ⟨g, hg, rfl⟩ := hC
        exact (mem_quotientCarrier_iff G H _).mpr
          (leftCoset_mem_cosetClasses G H g (K.subset g hg))
      op_closed := fun C₁ C₂ hC₁ hC₂ => by
        simp only [quotientGroup, quotientOp]
        rw [mem_sortFSetList_iff] at hC₁ hC₂ ⊢
        simp only [List.mem_map] at hC₁ hC₂ ⊢
        obtain ⟨g₁, hg₁, rfl⟩ := hC₁
        obtain ⟨g₂, hg₂, rfl⟩ := hC₂
        have hr₁_in := leftCoset_mem_quotientCarrier G H g₁ (K.subset g₁ hg₁)
        have hr₂_in := leftCoset_mem_quotientCarrier G H g₂ (K.subset g₂ hg₂)
        refine ⟨G.op g₁ g₂, K.op_closed g₁ g₂ hg₁ hg₂, ?_⟩
        exact quotientOp_welldefined G H hn g₁
          (cosetRepOf G H (leftCoset G H g₁)) g₂ (cosetRepOf G H (leftCoset G H g₂))
          (K.subset g₁ hg₁) (cosetRepOf_mem_G G H _ hr₁_in)
          (K.subset g₂ hg₂) (cosetRepOf_mem_G G H _ hr₂_in)
          (cosetRepOf_leftCoset_eq G H _ hr₁_in).symm
          (cosetRepOf_leftCoset_eq G H _ hr₂_in).symm
      id_in := by
        simp only [quotientGroup, quotientId]
        rw [mem_sortFSetList_iff]
        simp only [List.mem_map]
        exact ⟨G.id, K.id_in, rfl⟩
      inv_closed := fun C hC => by
        simp only [quotientGroup, quotientInv]
        rw [mem_sortFSetList_iff] at hC ⊢
        simp only [List.mem_map] at hC ⊢
        obtain ⟨g, hg, rfl⟩ := hC
        have hr_in := leftCoset_mem_quotientCarrier G H g (K.subset g hg)
        -- Queremos: G.inv (cosetRepOf G H (leftCoset G H g)) ~ G.inv g en H
        -- pues cosetRepOf (leftCoset G H g) ~ g, y al tomar inversos se preserva el coseto.
        refine ⟨G.inv g, K.inv_closed g hg, ?_⟩
        -- leftCoset G H (G.inv g) = leftCoset G H (G.inv (cosetRepOf G H (leftCoset G H g)))
        apply leftCoset_eq_of_rel G H _ _ (inv_mem G (K.subset g hg))
          (inv_mem G (cosetRepOf_mem_G G H _ hr_in))
        -- cosetRel G H (G.inv g) (G.inv (cosetRepOf G H (leftCoset G H g)))
        -- Prueba: de cosetRepOf_leftCoset_eq obtenemos G.inv r * g ∈ H.
        -- Aplicar normalidad de H con x=g, n = G.inv r * g da:
        --   G.op (G.op g (G.op (G.inv r) g)) (G.inv g) ∈ H
        -- que simplifica a G.op g (G.inv r) ∈ H = cosetRel G H (G.inv g) (G.inv r).
        let r := cosetRepOf G H (leftCoset G H g)
        have hr_G : r ∈ G.carrier.elems := cosetRepOf_mem_G G H _ hr_in
        have hg_G : g ∈ G.carrier.elems := K.subset g hg
        have hrel : G.op (G.inv r) g ∈ H.carrier.elems :=
          cosetRel_of_leftCoset_eq G H r g hr_G hg_G (cosetRepOf_leftCoset_eq G H _ hr_in)
        have h_conj := hn g (G.op (G.inv r) g) hg_G hrel
        have h_simp : G.op (G.op g (G.op (G.inv r) g)) (G.inv g) = G.op g (G.inv r) := by
          have hr' := inv_mem G hr_G
          rw [G.op_assoc g (G.op (G.inv r) g) (G.inv g) hg_G (op_mem G hr' hg_G) (inv_mem G hg_G),
              G.op_assoc (G.inv r) g (G.inv g) hr' hg_G (inv_mem G hg_G),
              (G.op_inv g hg_G).1, (G.op_id (G.inv r) hr').1]
        unfold cosetRel
        rw [inv_inv_eq G hg_G]
        exact h_simp ▸ h_conj

  end QuotientGroup
end Peano

export Peano.QuotientGroup (
  quotientCarrier
  mem_quotientCarrier_iff
  mem_quotientCarrier_is_leftCoset
  coset_nonempty_of_mem_quotientCarrier
  leftCoset_mem_cosetClasses
  leftCoset_mem_quotientCarrier
  leftCoset_id_mem_quotientCarrier
  cosetRel_of_leftCoset_eq
  leftCoset_eq_iff_cosetRel
  cosetRepOf
  cosetRepOf_eq_head
  cosetRepOf_mem_C
  cosetRepOf_mem_G
  cosetRepOf_leftCoset_eq
  quotientOp_welldefined
  quotientOp
  quotientInv
  quotientId
  quotientId_mem
  quotientOp_assoc
  quotientOp_id
  quotientOp_inv
  quotientGroup
  quotient_card
  quotientHomomorphism
  quotientHomomorphism_op
  quotientHomomorphism_kernel
  imageSubgroup
)
