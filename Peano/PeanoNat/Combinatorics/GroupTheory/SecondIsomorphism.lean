import Peano.PeanoNat.Combinatorics.GroupTheory.FirstIsomorphism

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Segundo Teorema de Isomorfía

Dados un grupo finito `G`, un subgrupo `H ≤ G` y un subgrupo normal `N ⊴ G`, este módulo prueba:

1. El producto `HN = { h·n | h ∈ H, n ∈ N }` es un subgrupo de `G`.
2. `H ≤ HN` y `N ≤ HN`.
3. `N ⊴ HN` (N es normal en HN).
4. `H ∩ N ⊴ H` (H∩N es normal en H).
5. Existe un isomorfismo `H/(H∩N) ≅ HN/N`.

## Contenido

§ 0. Lema auxiliar de membresía en H.inter N
§ 1. Subgrupo HN (`subgroupHN`, `mem_subgroupHN_iff`)
§ 2. H ≤ HN y N ≤ HN
§ 3. N como subgrupo de HN (`N_in_subgroupHN`, `N_normal_in_subgroupHN`)
§ 4. H∩N como subgrupo normal de H (`interHN_as_subgroup_H`, `interHN_as_subgroup_H_isNormal`)
§ 5. El isomorfismo φ (`secondIsoMap`, `secondIsoMap_welldefined`,
     `secondIsoMap_injective`, `secondIsoMap_surjective`, `secondIsoMap_bijective`)
-/

set_option autoImplicit false

namespace Peano
  namespace GroupTheory
    open Peano.FSet Peano.FSetFunction Peano.Group Peano.GroupTheory

    /-!
    ## § 0. Lema auxiliar: membresía en H.inter N
    -/

    private theorem mem_inter_iff_aux {G : FinGroup ℕ₀} (H N : Subgroup G) (a : ℕ₀) :
        a ∈ (H.inter N).carrier.elems ↔
        a ∈ G.carrier.elems ∧ a ∈ H.carrier.elems ∧ a ∈ N.carrier.elems := by
      simp only [Subgroup.inter, FSet.filter]
      rw [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨ha_G, ha_H, ha_N⟩
        exact ⟨ha_G, ha_H, ha_N⟩
      · rintro ⟨ha_G, ha_H, ha_N⟩
        exact ⟨ha_G, ha_H, ha_N⟩

    /-!
    ## § 1. El producto HN como subgrupo de G
    -/

    /-- El producto `HN = { h·n | h ∈ H, n ∈ N }` es un subgrupo de `G`. -/
    def subgroupHN (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) : Subgroup G where
      carrier :=
        FSet.filter
          (fun x => H.carrier.elems.any (fun h =>
            N.carrier.elems.any (fun n => decide (G.op h n = x))))
          G.carrier
      nonempty := ⟨G.id, by
        simp only [FSet.filter]
        apply List.mem_filter.mpr
        refine ⟨G.id_in, ?_⟩
        apply List.any_eq_true.mpr
        exact ⟨G.id, H.id_in, List.any_eq_true.mpr
          ⟨G.id, N.id_in, decide_eq_true_eq.mpr ((G.op_id G.id G.id_in).1)⟩⟩⟩
      subset := fun a ha => (List.mem_filter.mp ha).1
      id_in := by
        simp only [FSet.filter]
        apply List.mem_filter.mpr
        refine ⟨G.id_in, ?_⟩
        apply List.any_eq_true.mpr
        exact ⟨G.id, H.id_in, List.any_eq_true.mpr
          ⟨G.id, N.id_in, decide_eq_true_eq.mpr ((G.op_id G.id G.id_in).1)⟩⟩
      op_closed := fun a b ha hb => by
        simp only [FSet.filter] at ha hb ⊢
        obtain ⟨ha_G, ha_any⟩ := List.mem_filter.mp ha
        obtain ⟨hb_G, hb_any⟩ := List.mem_filter.mp hb
        rw [List.any_eq_true] at ha_any hb_any
        obtain ⟨h₁, hh₁, ha_any'⟩ := ha_any
        obtain ⟨h₂, hh₂, hb_any'⟩ := hb_any
        rw [List.any_eq_true] at ha_any' hb_any'
        obtain ⟨n₁, hn₁, ha_dec⟩ := ha_any'
        obtain ⟨n₂, hn₂, hb_dec⟩ := hb_any'
        rw [decide_eq_true_eq] at ha_dec hb_dec
        -- a = h₁·n₁,  b = h₂·n₂
        -- a·b = h₁·n₁·h₂·n₂ = h₁·h₂·(h₂⁻¹·n₁·h₂)·n₂
        -- n₁' = G.op (G.op (G.inv h₂) n₁) h₂ ∈ N por normalidad (con g = G.inv h₂)
        have hh₁_G := H.subset h₁ hh₁
        have hh₂_G := H.subset h₂ hh₂
        have hn₁_G := N.subset n₁ hn₁
        have hn₂_G := N.subset n₂ hn₂
        have hh₂_inv_G := inv_mem G hh₂_G
        -- n₁' = h₂⁻¹·n₁·h₂ ∈ N
        have hn₁' : G.op (G.op (G.inv h₂) n₁) h₂ ∈ N.carrier.elems := by
          have := hn (G.inv h₂) n₁ hh₂_inv_G hn₁
          rwa [inv_inv_eq G hh₂_G] at this
        have hn₁'_G := N.subset _ hn₁'
        -- h₁·h₂ ∈ H
        have hh₁h₂ : G.op h₁ h₂ ∈ H.carrier.elems := H.op_closed h₁ h₂ hh₁ hh₂
        -- n₁'·n₂ ∈ N
        have hn₁'n₂ : G.op (G.op (G.op (G.inv h₂) n₁) h₂) n₂ ∈ N.carrier.elems :=
          N.op_closed _ n₂ hn₁' hn₂
        -- a·b = h₁·n₁·h₂·n₂ = (h₁·h₂)·(h₂⁻¹·n₁·h₂)·n₂
        -- Proof: (h₁·h₂)·(h₂⁻¹·n₁·h₂·n₂) = h₁·(h₂·h₂⁻¹)·n₁·h₂·n₂ = h₁·n₁·h₂·n₂
        let n₁' := G.op (G.op (G.inv h₂) n₁) h₂
        have hn₁'_G' : n₁' ∈ G.carrier.elems := N.subset _ hn₁'
        have hab_eq : G.op (G.op h₁ h₂) (G.op n₁' n₂) = G.op a b := by
          simp only [n₁']
          rw [← ha_dec, ← hb_dec]
          -- (h₁·h₂)·((h₂⁻¹·n₁·h₂)·n₂) = h₁·n₁·h₂·n₂
          rw [G.op_assoc (G.op h₁ h₂) (G.op (G.op (G.inv h₂) n₁) h₂) n₂
                (op_mem G hh₁_G hh₂_G) (op_mem G (op_mem G hh₂_inv_G hn₁_G) hh₂_G) hn₂_G,
              ← G.op_assoc h₁ h₂ (G.op (G.op (G.inv h₂) n₁) h₂)
                hh₁_G hh₂_G (op_mem G (op_mem G hh₂_inv_G hn₁_G) hh₂_G),
              G.op_assoc h₂ (G.op (G.inv h₂) n₁) h₂
                hh₂_G (op_mem G hh₂_inv_G hn₁_G) hh₂_G,
              ← G.op_assoc h₂ (G.inv h₂) n₁ hh₂_G hh₂_inv_G hn₁_G,
              (G.op_inv h₂ hh₂_G).1,
              (G.op_id n₁ hn₁_G).2,
              G.op_assoc h₁ n₁ (G.op h₂ n₂) hh₁_G hn₁_G (op_mem G hh₂_G hn₂_G),
              G.op_assoc n₁ h₂ n₂ hn₁_G hh₂_G hn₂_G]
        apply List.mem_filter.mpr
        refine ⟨hab_eq ▸ op_mem G (H.subset _ hh₁h₂) (N.subset _ hn₁'n₂), ?_⟩
        apply List.any_eq_true.mpr
        exact ⟨G.op h₁ h₂, hh₁h₂, List.any_eq_true.mpr
          ⟨G.op n₁' n₂, hn₁'n₂,
           decide_eq_true_eq.mpr hab_eq⟩⟩
      inv_closed := fun a ha => by
        simp only [FSet.filter] at ha ⊢
        obtain ⟨ha_G, ha_any⟩ := List.mem_filter.mp ha
        rw [List.any_eq_true] at ha_any
        obtain ⟨h, hh, ha_any'⟩ := ha_any
        rw [List.any_eq_true] at ha_any'
        obtain ⟨n, hn_mem, ha_dec⟩ := ha_any'
        rw [decide_eq_true_eq] at ha_dec
        -- a = h·n, so a⁻¹ = n⁻¹·h⁻¹ = h⁻¹·(h·n⁻¹·h⁻¹)
        -- h·n⁻¹·h⁻¹ ∈ N by normality (with g = h, n' = G.inv n)
        have hh_G := H.subset h hh
        have hn_G := N.subset n hn_mem
        have hh_inv := inv_mem G hh_G
        have hn_inv := inv_mem G hn_G
        have hn_inv_mem : G.inv n ∈ N.carrier.elems := N.inv_closed n hn_mem
        -- h·(G.inv n)·h⁻¹ ∈ N
        have hconj : G.op (G.op h (G.inv n)) (G.inv h) ∈ N.carrier.elems :=
          hn h (G.inv n) hh_G hn_inv_mem
        -- a⁻¹ = G.inv (h·n) = G.inv n · G.inv h = G.inv h · (h · G.inv n · G.inv h)
        have ha_inv_eq' : G.op (G.inv h) (G.op (G.op h (G.inv n)) (G.inv h)) = G.inv a := by
          rw [← ha_dec, inv_op_eq G hh_G hn_G]
          rw [← G.op_assoc (G.inv h) (G.op h (G.inv n)) (G.inv h)
                hh_inv (op_mem G hh_G hn_inv) hh_inv,
              ← G.op_assoc (G.inv h) h (G.inv n) hh_inv hh_G hn_inv,
              (G.op_inv h hh_G).2,
              (G.op_id (G.inv n) hn_inv).2]
        apply List.mem_filter.mpr
        refine ⟨ha_inv_eq' ▸ op_mem G hh_inv (N.subset _ hconj), ?_⟩
        apply List.any_eq_true.mpr
        exact ⟨G.inv h, H.inv_closed h hh, List.any_eq_true.mpr
          ⟨G.op (G.op h (G.inv n)) (G.inv h), hconj,
           decide_eq_true_eq.mpr ha_inv_eq'⟩⟩

    /-- Caracterización de la membresía en HN:
        `x ∈ HN ↔ x ∈ G ∧ ∃ h ∈ H, ∃ n ∈ N, h·n = x`. -/
    theorem mem_subgroupHN_iff (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal)
        (x : ℕ₀) :
        x ∈ (subgroupHN G H N hn).carrier.elems ↔
        x ∈ G.carrier.elems ∧ ∃ h ∈ H.carrier.elems, ∃ n ∈ N.carrier.elems, G.op h n = x := by
      simp only [subgroupHN, FSet.filter]
      rw [List.mem_filter, List.any_eq_true]
      constructor
      · rintro ⟨hx_G, h, hh, ha_any⟩
        rw [List.any_eq_true] at ha_any
        obtain ⟨n, hn_mem, hd⟩ := ha_any
        exact ⟨hx_G, h, hh, n, hn_mem, decide_eq_true_eq.mp hd⟩
      · rintro ⟨hx_G, h, hh, n, hn_mem, heq⟩
        exact ⟨hx_G, h, hh, List.any_eq_true.mpr ⟨n, hn_mem, decide_eq_true_eq.mpr heq⟩⟩

    /-!
    ## § 2. H ≤ HN y N ≤ HN
    -/

    theorem H_le_subgroupHN (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal)
        (h : ℕ₀) (hh : h ∈ H.carrier.elems) :
        h ∈ (subgroupHN G H N hn).carrier.elems := by
      rw [mem_subgroupHN_iff]
      exact ⟨H.subset h hh, h, hh, G.id, N.id_in, (G.op_id h (H.subset h hh)).1⟩

    theorem N_le_subgroupHN (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal)
        (n : ℕ₀) (hn' : n ∈ N.carrier.elems) :
        n ∈ (subgroupHN G H N hn).carrier.elems := by
      rw [mem_subgroupHN_iff]
      exact ⟨N.subset n hn', G.id, H.id_in, n, hn', (G.op_id n (N.subset n hn')).2⟩

    /-!
    ## § 3. N como subgrupo normal de HN
    -/

    /-- N como subgrupo de `(subgroupHN G H N hn).toFinGroup`. -/
    def N_in_subgroupHN (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        Subgroup (subgroupHN G H N hn).toFinGroup where
      carrier   := N.carrier
      nonempty  := N.nonempty
      subset    := fun n hn' => N_le_subgroupHN G H N hn n hn'
      op_closed := fun a b ha hb => N.op_closed a b ha hb
      id_in     := N.id_in
      inv_closed := fun a ha => N.inv_closed a ha

    /-- N es normal en HN. -/
    theorem N_normal_in_subgroupHN (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        (N_in_subgroupHN G H N hn).IsNormal := by
      intro g n hg hn_mem
      -- HN.toFinGroup.op = G.op, HN.toFinGroup.inv = G.inv
      -- g ∈ HN ≤ G, n ∈ N ≤ G; normalidad de N en G
      simp only [Subgroup.toFinGroup, N_in_subgroupHN]
      have hg_G : g ∈ G.carrier.elems := (subgroupHN G H N hn).subset g hg
      exact hn g n hg_G hn_mem

    /-!
    ## § 4. H∩N como subgrupo normal de H
    -/

    /-- H∩N como subgrupo de `H.toFinGroup`. -/
    def interHN_as_subgroup_H (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        Subgroup H.toFinGroup where
      carrier   := (H.inter N).carrier
      nonempty  := (H.inter N).nonempty
      subset    := fun a ha => Subgroup.inter_subset_left H N ha
      op_closed := fun a b ha hb => (H.inter N).op_closed a b ha hb
      id_in     := (H.inter N).id_in
      inv_closed := fun a ha => (H.inter N).inv_closed a ha

    /-- H∩N es normal en H. -/
    theorem interHN_as_subgroup_H_isNormal (G : FinGroup ℕ₀) (H N : Subgroup G)
        (hn : N.IsNormal) :
        (interHN_as_subgroup_H G H N hn).IsNormal := by
      -- H.toFinGroup.op = G.op, H.toFinGroup.inv = G.inv
      intro g k hg hk
      -- g ∈ H.toFinGroup → g ∈ H.carrier.elems; k ∈ H∩N
      simp only [Subgroup.toFinGroup, interHN_as_subgroup_H]
      have hg_H := H.subset g hg
      have hg_G := H.subset g hg_H  -- same, g ∈ G
      have hk_H := Subgroup.inter_subset_left H N hk
      have hk_N := Subgroup.inter_subset_right H N hk
      -- gkg⁻¹ ∈ H: because g, k ∈ H and H is a subgroup
      have hgkg_H : G.op (G.op g k) (G.inv g) ∈ H.carrier.elems :=
        H.op_closed _ _ (H.op_closed g k hg_H hk_H) (H.inv_closed g hg_H)
      -- gkg⁻¹ ∈ N: by normality of N in G, since g ∈ G, k ∈ N
      have hgkg_N : G.op (G.op g k) (G.inv g) ∈ N.carrier.elems :=
        hn g k hg_G hk_N
      -- gkg⁻¹ ∈ H∩N
      rw [mem_inter_iff_aux H N]
      exact ⟨H.subset _ hgkg_H, hgkg_H, hgkg_N⟩

    /-!
    ## § 5. El isomorfismo φ : H/(H∩N) → HN/N
    -/

    private noncomputable def inter_H (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        Subgroup H.toFinGroup := interHN_as_subgroup_H G H N hn

    private noncomputable def HN_group (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        FinGroup ℕ₀ := (subgroupHN G H N hn).toFinGroup

    private noncomputable def N_in_HN (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        Subgroup (HN_group G H N hn) := N_in_subgroupHN G H N hn

    /-- El isomorfismo φ : H/(H∩N) → HN/N, dado por `φ(C) = cosetRepOf(C) · N`. -/
    noncomputable def secondIsoMap (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        MapOn
          (quotientCarrier H.toFinGroup (inter_H G H N hn))
          (quotientCarrier (HN_group G H N hn) (N_in_HN G H N hn)) where
      toFun := fun C =>
        leftCoset (HN_group G H N hn) (N_in_HN G H N hn)
          (cosetRepOf H.toFinGroup (inter_H G H N hn) C)
      map_carrier := fun C hC => by
        apply leftCoset_mem_quotientCarrier
        -- cosetRepOf H inter_H C ∈ H.carrier.elems
        have hrep_H := cosetRepOf_mem_G H.toFinGroup (inter_H G H N hn) C hC
        -- H.toFinGroup.carrier = H.carrier, so hrep_H : rep ∈ H.carrier.elems
        -- HN_group.carrier = (subgroupHN ...).carrier
        -- rep ∈ H ≤ HN
        exact H_le_subgroupHN G H N hn _ hrep_H

    /-- Bien-definición de φ: para todo `h ∈ H`,
        `φ(leftCoset H (H∩N) h) = leftCoset HN N h`. -/
    theorem secondIsoMap_welldefined (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal)
        (h : ℕ₀) (hh : h ∈ H.carrier.elems) :
        (secondIsoMap G H N hn).toFun
          (leftCoset H.toFinGroup (inter_H G H N hn) h) =
          leftCoset (HN_group G H N hn) (N_in_HN G H N hn) h := by
      simp only [secondIsoMap]
      -- r = cosetRepOf H (H∩N) (leftCoset H (H∩N) h)
      let K  := inter_H G H N hn
      let r  := cosetRepOf H.toFinGroup K (leftCoset H.toFinGroup K h)
      have hr_in : leftCoset H.toFinGroup K h ∈ (quotientCarrier H.toFinGroup K).elems :=
        leftCoset_mem_quotientCarrier H.toFinGroup K h hh
      have hr_H : r ∈ H.carrier.elems :=
        cosetRepOf_mem_G H.toFinGroup K (leftCoset H.toFinGroup K h) hr_in
      -- cosetRel H (H∩N) r h, i.e., H.op (H.inv r) h ∈ (H∩N).carrier
      have hrel : cosetRel H.toFinGroup K r h :=
        cosetRel_of_leftCoset_eq H.toFinGroup K r h hr_H hh
          (cosetRepOf_leftCoset_eq H.toFinGroup K (leftCoset H.toFinGroup K h) hr_in)
      -- cosetRel H (H∩N) r h means G.op (G.inv r) h ∈ (H.inter N).carrier.elems
      -- (since H.toFinGroup.op = G.op, H.toFinGroup.inv = G.inv)
      unfold cosetRel at hrel
      -- hrel : G.op (G.inv r) h ∈ (H.inter N).carrier.elems
      -- → G.op (G.inv r) h ∈ N.carrier.elems
      have hrel_N : G.op (G.inv r) h ∈ N.carrier.elems :=
        Subgroup.inter_subset_right H N hrel
      -- This means cosetRel (HN_group) (N_in_HN) r h in HN
      have hrel_HN : cosetRel (HN_group G H N hn) (N_in_HN G H N hn) r h := by
        unfold cosetRel
        -- HN_group.op = G.op, HN_group.inv = G.inv (from toFinGroup)
        simp only [HN_group, N_in_HN, Subgroup.toFinGroup, N_in_subgroupHN]
        exact hrel_N
      -- Therefore leftCoset HN N r = leftCoset HN N h
      exact leftCoset_eq_of_rel (HN_group G H N hn) (N_in_HN G H N hn) r h
        (H_le_subgroupHN G H N hn r hr_H)
        (H_le_subgroupHN G H N hn h hh)
        hrel_HN

    /-- φ es inyectiva. -/
    theorem secondIsoMap_injective (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        (secondIsoMap G H N hn).Injective := by
      intro C₁ C₂ hC₁ hC₂ hφ
      -- hφ : leftCoset HN N r₁ = leftCoset HN N r₂
      simp only [secondIsoMap] at hφ
      rw [← cosetRepOf_leftCoset_eq H.toFinGroup (inter_H G H N hn) C₁ hC₁,
          ← cosetRepOf_leftCoset_eq H.toFinGroup (inter_H G H N hn) C₂ hC₂]
      let K  := inter_H G H N hn
      let r₁ := cosetRepOf H.toFinGroup K C₁
      let r₂ := cosetRepOf H.toFinGroup K C₂
      have hr₁_H := cosetRepOf_mem_G H.toFinGroup K C₁ hC₁
      have hr₂_H := cosetRepOf_mem_G H.toFinGroup K C₂ hC₂
      apply (leftCoset_eq_iff_cosetRel H.toFinGroup K r₁ r₂ hr₁_H hr₂_H).mpr
      unfold cosetRel
      -- From hφ: leftCoset HN N r₁ = leftCoset HN N r₂
      -- → cosetRel HN N r₁ r₂ → G.op (G.inv r₁) r₂ ∈ N
      have hrel_HN : cosetRel (HN_group G H N hn) (N_in_HN G H N hn) r₁ r₂ :=
        cosetRel_of_leftCoset_eq (HN_group G H N hn) (N_in_HN G H N hn) r₁ r₂
          (H_le_subgroupHN G H N hn r₁ hr₁_H)
          (H_le_subgroupHN G H N hn r₂ hr₂_H)
          hφ
      unfold cosetRel at hrel_HN
      simp only [HN_group, N_in_HN, Subgroup.toFinGroup, N_in_subgroupHN] at hrel_HN
      -- hrel_HN : G.op (G.inv r₁) r₂ ∈ N.carrier.elems
      -- r₁, r₂ ∈ H → G.inv r₁ ∈ H, G.op (G.inv r₁) r₂ ∈ H
      have hir₁_H : G.inv r₁ ∈ H.carrier.elems := H.inv_closed r₁ hr₁_H
      have hrel_H : G.op (G.inv r₁) r₂ ∈ H.carrier.elems :=
        H.op_closed _ r₂ hir₁_H hr₂_H
      -- So G.op (G.inv r₁) r₂ ∈ H ∩ N
      rw [mem_inter_iff_aux H N]
      exact ⟨H.subset _ hrel_H, hrel_H, hrel_HN⟩

    /-- φ es sobreyectiva. -/
    theorem secondIsoMap_surjective (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        (secondIsoMap G H N hn).Surjective := by
      intro D hD
      -- D ∈ HN/N: D = leftCoset HN N (h·n) for some h ∈ H, n ∈ N
      obtain ⟨x, hx_HN, rfl⟩ := mem_quotientCarrier_is_leftCoset
          (HN_group G H N hn) (N_in_HN G H N hn) _ hD
      -- x ∈ HN → ∃ h ∈ H, ∃ n ∈ N, h·n = x
      rw [mem_subgroupHN_iff] at hx_HN
      obtain ⟨_, h, hh, n, hn_mem, heq⟩ := hx_HN
      -- leftCoset HN N x = leftCoset HN N h
      -- because G.op (G.inv h) x = G.op (G.inv h) (h·n) = n ∈ N
      have hh_HN : h ∈ (HN_group G H N hn).carrier.elems :=
        H_le_subgroupHN G H N hn h hh
      have hx_HN2 : x ∈ (HN_group G H N hn).carrier.elems := by
        rw [mem_subgroupHN_iff]; exact ⟨(subgroupHN G H N hn).subset x hx_HN, h, hh, n, hn_mem, heq⟩
      have hrel : cosetRel (HN_group G H N hn) (N_in_HN G H N hn) h x := by
        unfold cosetRel
        simp only [HN_group, N_in_HN, Subgroup.toFinGroup, N_in_subgroupHN]
        -- G.op (G.inv h) x = G.op (G.inv h) (G.op h n) = n ∈ N
        rw [← heq, ← G.op_assoc (G.inv h) h n (inv_mem G (H.subset h hh)) (H.subset h hh)
              (N.subset n hn_mem),
            (G.op_inv h (H.subset h hh)).2,
            (G.op_id n (N.subset n hn_mem)).2]
        exact hn_mem
      have heq_coset : leftCoset (HN_group G H N hn) (N_in_HN G H N hn) x =
          leftCoset (HN_group G H N hn) (N_in_HN G H N hn) h :=
        (leftCoset_eq_iff_cosetRel (HN_group G H N hn) (N_in_HN G H N hn) h x
          hh_HN hx_HN2).mpr hrel |>.symm
      -- Take C = leftCoset H (H∩N) h ∈ H/(H∩N)
      refine ⟨leftCoset H.toFinGroup (inter_H G H N hn) h,
              leftCoset_mem_quotientCarrier H.toFinGroup (inter_H G H N hn) h hh, ?_⟩
      rw [heq_coset]
      exact secondIsoMap_welldefined G H N hn h hh

    /-- **Segundo Teorema de Isomorfía**: φ : H/(H∩N) → HN/N es biyectivo. -/
    theorem secondIsoMap_bijective (G : FinGroup ℕ₀) (H N : Subgroup G) (hn : N.IsNormal) :
        (secondIsoMap G H N hn).Bijective :=
      ⟨secondIsoMap_injective G H N hn, secondIsoMap_surjective G H N hn⟩

  end GroupTheory
end Peano

export Peano.GroupTheory (
  subgroupHN
  mem_subgroupHN_iff
  H_le_subgroupHN
  N_le_subgroupHN
  N_in_subgroupHN
  N_normal_in_subgroupHN
  interHN_as_subgroup_H
  interHN_as_subgroup_H_isNormal
  secondIsoMap
  secondIsoMap_welldefined
  secondIsoMap_injective
  secondIsoMap_surjective
  secondIsoMap_bijective
)
