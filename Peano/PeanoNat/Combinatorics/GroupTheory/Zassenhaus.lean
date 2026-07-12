import Peano.PeanoNat.Combinatorics.GroupTheory.SecondIsomorphism

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Lema de la Mariposa de Zassenhaus

Sean `G` un grupo finito y `H, K, N, M ≤ G` subgrupos con:
- `N ≤ H` y `N ⊴ H` (N normal en H)
- `M ≤ K` y `M ⊴ K` (M normal en K)

Este módulo prueba:
1. `N ∩ K ⊴ H ∩ K`
2. `H ∩ M ⊴ H ∩ K`
3. `(N ∩ K)(H ∩ M) ⊴ H ∩ K`
4. `N(H ∩ M) ⊴ N(H ∩ K)` y `M(N ∩ K) ⊴ M(H ∩ K)`
5. Existe una biyección `(H ∩ K) / (N ∩ K)(H ∩ M) ≅ N(H ∩ K) / N(H ∩ M)`
6. (Por simetría) también `(H ∩ K) / (N ∩ K)(H ∩ M) ≅ M(H ∩ K) / M(N ∩ K)`
7. (Entre los extremos) también `N(H ∩ K) / N(H ∩ M) ≅ M(H ∩ K) / M(N ∩ K)`

## Hipótesis

Expresamos N ⊴ H y M ⊴ K como predicados explícitos sobre la conjugación en G,
manteniendo todos los subgrupos del mismo tipo `Subgroup G`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Peano
  namespace Zassenhaus
    open Peano.FSet Peano.FSetFunction Peano.Group Peano.Mul
    open Peano.Cosets Peano.NormalSubgroup Peano.QuotientGroup
    open Peano.FirstIsomorphism Peano.SecondIsomorphism

    /-! ## § 0. Lemas auxiliares de membresía en intersecciones -/

    /-- Membresía en la intersección `H ∩ K`. -/
    private theorem mem_inter_iff {G : FinGroup ℕ₀} (H K : Subgroup G) (a : ℕ₀) :
        a ∈ (H.inter K).carrier.elems ↔
        a ∈ G.carrier.elems ∧ a ∈ H.carrier.elems ∧ a ∈ K.carrier.elems := by
      simp only [Subgroup.inter, FSet.filter]
      rw [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨id, id⟩

    private theorem inter_subset_left_aux {G : FinGroup ℕ₀} (H K : Subgroup G) (a : ℕ₀)
        (ha : a ∈ (H.inter K).carrier.elems) : a ∈ H.carrier.elems :=
      ((mem_inter_iff H K a).mp ha).2.1

    private theorem inter_subset_right_aux {G : FinGroup ℕ₀} (H K : Subgroup G) (a : ℕ₀)
        (ha : a ∈ (H.inter K).carrier.elems) : a ∈ K.carrier.elems :=
      ((mem_inter_iff H K a).mp ha).2.2

    /-! ## § 1. Subgrupo producto N · S cuando N ⊴ H y S ≤ H -/

    /-- El producto `N · S = { n · s | n ∈ N, s ∈ S }` como subgrupo de `G`,
        válido cuando `N` y `S` son subgrupos de `G` contenidos en `H`, y `N ⊴ H`. -/
    def prodSubgroup
        (G : FinGroup ℕ₀)
        (N S H : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
        (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
               G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
        Subgroup G where
      carrier :=
        FSet.filter
          (fun x => N.carrier.elems.any (fun n =>
            S.carrier.elems.any (fun s => decide (G.op n s = x))))
          G.carrier
      nonempty := ⟨G.id, by
        simp only [FSet.filter]
        apply List.mem_filter.mpr
        refine ⟨G.id_in, List.any_eq_true.mpr ⟨G.id, N.id_in,
          List.any_eq_true.mpr ⟨G.id, S.id_in,
            decide_eq_true_eq.mpr ((G.op_id G.id G.id_in).1)⟩⟩⟩⟩
      subset := fun a ha => (List.mem_filter.mp ha).1
      id_in := by
        simp only [FSet.filter]
        apply List.mem_filter.mpr
        refine ⟨G.id_in, List.any_eq_true.mpr ⟨G.id, N.id_in,
          List.any_eq_true.mpr ⟨G.id, S.id_in,
            decide_eq_true_eq.mpr ((G.op_id G.id G.id_in).1)⟩⟩⟩
      op_closed := fun a b ha hb => by
        simp only [FSet.filter] at ha hb ⊢
        obtain ⟨ha_G, ha_any⟩ := List.mem_filter.mp ha
        obtain ⟨hb_G, hb_any⟩ := List.mem_filter.mp hb
        rw [List.any_eq_true] at ha_any hb_any
        obtain ⟨n₁, hn₁, ha_any'⟩ := ha_any
        obtain ⟨n₂, hn₂, hb_any'⟩ := hb_any
        rw [List.any_eq_true] at ha_any' hb_any'
        obtain ⟨s₁, hs₁, ha_dec⟩ := ha_any'
        obtain ⟨s₂, hs₂, hb_dec⟩ := hb_any'
        rw [decide_eq_true_eq] at ha_dec hb_dec
        -- a = n₁·s₁, b = n₂·s₂
        -- a·b = n₁·s₁·n₂·s₂ = n₁·(s₁·n₂·s₁⁻¹)·s₁·s₂
        -- s₁·n₂·s₁⁻¹ ∈ N por N ⊴ H y s₁ ∈ S ≤ H
        have hn₁_G := N.subset n₁ hn₁
        have hn₂_G := N.subset n₂ hn₂
        have hs₁_G := S.subset s₁ hs₁
        have hs₂_G := S.subset s₂ hs₂
        have hn₁_H := hNH n₁ hn₁
        have hn₂_H := hNH n₂ hn₂
        have hs₁_H := hSH s₁ hs₁
        have hs₂_H := hSH s₂ hs₂
        have hs₁_inv_G := inv_mem G hs₁_G
        -- n₂' = s₁·n₂·s₁⁻¹ ∈ N
        have hn₂' : G.op (G.op s₁ n₂) (G.inv s₁) ∈ N.carrier.elems :=
          hNN s₁ n₂ hs₁_H hn₂
        have hn₂'_G := N.subset _ hn₂'
        -- n₁·n₂' ∈ N
        have hn₁n₂' := N.op_closed n₁ _ hn₁ hn₂'
        -- s₁·s₂ ∈ S
        have hs₁s₂ := S.op_closed s₁ s₂ hs₁ hs₂
        -- algebraic identity: (n₁·s₁)·(n₂·s₂) = (n₁·(s₁·n₂·s₁⁻¹))·(s₁·s₂)
        have key : G.op (G.op n₁ s₁) (G.op n₂ s₂) =
                   G.op (G.op n₁ (G.op (G.op s₁ n₂) (G.inv s₁))) (G.op s₁ s₂) :=
          calc G.op (G.op n₁ s₁) (G.op n₂ s₂)
              = G.op n₁ (G.op s₁ (G.op n₂ s₂)) :=
                    G.op_assoc n₁ s₁ _ hn₁_G hs₁_G (op_mem G hn₂_G hs₂_G)
            _ = G.op n₁ (G.op (G.op s₁ n₂) s₂) := by
                    rw [← G.op_assoc s₁ n₂ s₂ hs₁_G hn₂_G hs₂_G]
            _ = G.op n₁ (G.op (G.op (G.op s₁ n₂) (G.inv s₁)) (G.op s₁ s₂)) := by
                    congr 1; symm
                    rw [G.op_assoc (G.op s₁ n₂) (G.inv s₁) (G.op s₁ s₂)
                          (op_mem G hs₁_G hn₂_G) hs₁_inv_G (op_mem G hs₁_G hs₂_G),
                        ← G.op_assoc (G.inv s₁) s₁ s₂ hs₁_inv_G hs₁_G hs₂_G,
                        (G.op_inv s₁ hs₁_G).2, (G.op_id s₂ hs₂_G).2]
            _ = G.op (G.op n₁ (G.op (G.op s₁ n₂) (G.inv s₁))) (G.op s₁ s₂) :=
                    (G.op_assoc n₁ _ _ hn₁_G (op_mem G (op_mem G hs₁_G hn₂_G) hs₁_inv_G)
                      (op_mem G hs₁_G hs₂_G)).symm
        rw [ha_dec, hb_dec] at key
        rw [key]
        apply List.mem_filter.mpr
        refine ⟨op_mem G (op_mem G hn₁_G hn₂'_G) (S.subset _ hs₁s₂), ?_⟩
        exact List.any_eq_true.mpr ⟨G.op n₁ (G.op (G.op s₁ n₂) (G.inv s₁)), hn₁n₂',
          List.any_eq_true.mpr ⟨G.op s₁ s₂, hs₁s₂,
            decide_eq_true_eq.mpr rfl⟩⟩
      inv_closed := fun a ha => by
        simp only [FSet.filter] at ha ⊢
        obtain ⟨ha_G, ha_any⟩ := List.mem_filter.mp ha
        rw [List.any_eq_true] at ha_any
        obtain ⟨n, hn_mem, ha_any'⟩ := ha_any
        rw [List.any_eq_true] at ha_any'
        obtain ⟨s, hs_mem, ha_dec⟩ := ha_any'
        rw [decide_eq_true_eq] at ha_dec
        have hn_G := N.subset n hn_mem
        have hs_G := S.subset s hs_mem
        have hn_H := hNH n hn_mem
        have hs_H := hSH s hs_mem
        have hn_inv_mem := N.inv_closed n hn_mem
        have hs_inv_mem := S.inv_closed s hs_mem
        -- Escribir G.inv a = (s⁻¹·n⁻¹·s)·s⁻¹, con s⁻¹·n⁻¹·s ∈ N
        have hs_inv_H := H.inv_closed s hs_H
        -- s⁻¹·n⁻¹·s ∈ N: conjugado de n⁻¹ por s⁻¹ ∈ H
        have hconj : G.op (G.op (G.inv s) (G.inv n)) s ∈ N.carrier.elems := by
          have h := hNN (G.inv s) (G.inv n) hs_inv_H hn_inv_mem
          rwa [inv_inv_eq G hs_G] at h
        -- G.inv a = G.inv (n·s) = s⁻¹·n⁻¹
        have ha_inv : G.inv a = G.op (G.inv s) (G.inv n) := by
          rw [← ha_dec]; exact inv_op_eq G hn_G hs_G
        -- G.inv a = s⁻¹·n⁻¹ = (s⁻¹·n⁻¹·s)·s⁻¹
        have ha_inv_form :
            G.op (G.op (G.op (G.inv s) (G.inv n)) s) (G.inv s) = G.inv a := by
          rw [ha_inv,
              G.op_assoc (G.op (G.inv s) (G.inv n)) s (G.inv s)
                (op_mem G (inv_mem G hs_G) (inv_mem G hn_G)) hs_G (inv_mem G hs_G),
              (G.op_inv s hs_G).1,
              (G.op_id (G.op (G.inv s) (G.inv n))
                (op_mem G (inv_mem G hs_G) (inv_mem G hn_G))).1]
        exact List.mem_filter.mpr
          ⟨ha_inv_form ▸ op_mem G (N.subset _ hconj) (inv_mem G hs_G),
           List.any_eq_true.mpr ⟨G.op (G.op (G.inv s) (G.inv n)) s, hconj,
             List.any_eq_true.mpr ⟨G.inv s, hs_inv_mem,
               decide_eq_true_eq.mpr ha_inv_form⟩⟩⟩

    /-- Caracterización de la membresía en `N · S`. -/
    theorem mem_prodSubgroup_iff
        (G : FinGroup ℕ₀) (N S H : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
        (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
               G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
        (x : ℕ₀) :
        x ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems ↔
        x ∈ G.carrier.elems ∧
        ∃ n ∈ N.carrier.elems, ∃ s ∈ S.carrier.elems, G.op n s = x := by
      simp only [prodSubgroup, FSet.filter]
      rw [List.mem_filter, List.any_eq_true]
      constructor
      · rintro ⟨hx_G, n, hn, ha_any⟩
        rw [List.any_eq_true] at ha_any
        obtain ⟨s, hs, hd⟩ := ha_any
        exact ⟨hx_G, n, hn, s, hs, decide_eq_true_eq.mp hd⟩
      · rintro ⟨hx_G, n, hn, s, hs, heq⟩
        exact ⟨hx_G, n, hn, List.any_eq_true.mpr ⟨s, hs, decide_eq_true_eq.mpr heq⟩⟩

    /-- `N ≤ N · S` (inclusión del primer factor). -/
    theorem N_le_prodSubgroup
        (G : FinGroup ℕ₀) (N S H : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
        (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
               G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
        (n : ℕ₀) (hn : n ∈ N.carrier.elems) :
        n ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems := by
      rw [mem_prodSubgroup_iff]
      exact ⟨N.subset n hn, n, hn, G.id, S.id_in, (G.op_id n (N.subset n hn)).1⟩

    /-- `S ≤ N · S` (inclusión del segundo factor). -/
    theorem S_le_prodSubgroup
        (G : FinGroup ℕ₀) (N S H : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
        (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
               G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
        (s : ℕ₀) (hs : s ∈ S.carrier.elems) :
        s ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems := by
      rw [mem_prodSubgroup_iff]
      exact ⟨S.subset s hs, G.id, N.id_in, s, hs, (G.op_id s (S.subset s hs)).2⟩

    /-! ## § 2. N ∩ K ⊴ H ∩ K -/

    /-- `N ∩ K` es subgrupo normal de `H ∩ K`, dado N ⊴ H y K ≤ G. -/
    theorem inter_N_K_normal_in_inter_H_K
        (G : FinGroup ℕ₀) (H K N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
               G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
        ∀ g x,
          g ∈ (H.inter K).carrier.elems →
          x ∈ (N.inter K).carrier.elems →
          G.op (G.op g x) (G.inv g) ∈ (N.inter K).carrier.elems := by
      intro g x hg hx
      have hg_H := inter_subset_left_aux H K g hg
      have hg_K := inter_subset_right_aux H K g hg
      have hg_G := H.subset g hg_H
      have hx_N := inter_subset_left_aux N K x hx
      have hx_K := inter_subset_right_aux N K x hx
      have hx_G := N.subset x hx_N
      -- g·x·g⁻¹ ∈ N: by N ⊴ H, g ∈ H, x ∈ N
      have h_in_N : G.op (G.op g x) (G.inv g) ∈ N.carrier.elems :=
        hNN g x hg_H hx_N
      -- g·x·g⁻¹ ∈ K: g, x, g⁻¹ ∈ K (K is subgroup)
      have h_in_K : G.op (G.op g x) (G.inv g) ∈ K.carrier.elems :=
        K.op_closed _ _ (K.op_closed g x hg_K hx_K) (K.inv_closed g hg_K)
      rw [mem_inter_iff N K]
      exact ⟨op_mem G (op_mem G hg_G hx_G) (inv_mem G hg_G), h_in_N, h_in_K⟩

    /-! ## § 3. H ∩ M ⊴ H ∩ K -/

    /-- `H ∩ M` es subgrupo normal de `H ∩ K`, dado M ⊴ K. -/
    theorem inter_H_M_normal_in_inter_H_K
        (G : FinGroup ℕ₀) (H K M : Subgroup G)
        (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
               G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
        ∀ g x,
          g ∈ (H.inter K).carrier.elems →
          x ∈ (H.inter M).carrier.elems →
          G.op (G.op g x) (G.inv g) ∈ (H.inter M).carrier.elems := by
      intro g x hg hx
      have hg_H := inter_subset_left_aux H K g hg
      have hg_K := inter_subset_right_aux H K g hg
      have hg_G := H.subset g hg_H
      have hx_H := inter_subset_left_aux H M x hx
      have hx_M := inter_subset_right_aux H M x hx
      -- g·x·g⁻¹ ∈ H: g, x, g⁻¹ ∈ H
      have h_in_H : G.op (G.op g x) (G.inv g) ∈ H.carrier.elems :=
        H.op_closed _ _ (H.op_closed g x hg_H hx_H) (H.inv_closed g hg_H)
      -- g·x·g⁻¹ ∈ M: by M ⊴ K, g ∈ K, x ∈ M
      have h_in_M : G.op (G.op g x) (G.inv g) ∈ M.carrier.elems :=
        hMM g x hg_K hx_M
      rw [mem_inter_iff H M]
      exact ⟨op_mem G (op_mem G hg_G (H.subset x hx_H)) (inv_mem G hg_G),
             h_in_H, h_in_M⟩

    /-! ## § 4. (N ∩ K)(H ∩ M) ⊴ H ∩ K -/

    /-- Las abreviaciones para la prueba del lema de Zassenhaus. -/
    private abbrev HK (G : FinGroup ℕ₀) (H K : Subgroup G) : Subgroup G := H.inter K
    private abbrev NK (G : FinGroup ℕ₀) (N K : Subgroup G) : Subgroup G := N.inter K
    private abbrev HM (G : FinGroup ℕ₀) (H M : Subgroup G) : Subgroup G := H.inter M

    /-- El subgrupo `(N ∩ K)(H ∩ M)` dentro de `H ∩ K`, con N ⊴ H y M ⊴ K. -/
    def prodNKHM
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
               G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
        (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
               G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
        Subgroup G :=
      prodSubgroup G (N.inter K) (H.inter M) (H.inter K)
        (fun a ha => by
          rw [mem_inter_iff H K]
          have ha_N := inter_subset_left_aux N K a ha
          have ha_K := inter_subset_right_aux N K a ha
          exact ⟨H.subset a (hNH a ha_N), hNH a ha_N, ha_K⟩)
        (fun a ha => by
          rw [mem_inter_iff H K]
          have ha_H := inter_subset_left_aux H M a ha
          have ha_M := inter_subset_right_aux H M a ha
          exact ⟨H.subset a ha_H, ha_H, hMK a ha_M⟩)
        (inter_N_K_normal_in_inter_H_K G H K N hNH hNN)

    /-- `(N ∩ K)(H ∩ M)` es normal en `H ∩ K`. -/
    theorem prodNKHM_normal
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
               G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
        (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
               G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
        ∀ g x,
          g ∈ (HK G H K).carrier.elems →
          x ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems →
          G.op (G.op g x) (G.inv g) ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems := by
      intro g x hg hx
      -- Descomponer x = a · b con a ∈ N∩K, b ∈ H∩M
      simp only [prodNKHM] at hx ⊢
      rw [mem_prodSubgroup_iff] at hx ⊢
      obtain ⟨_, a, ha_NK, b, hb_HM, hab⟩ := hx
      have hg_H := inter_subset_left_aux H K g hg
      have hg_K := inter_subset_right_aux H K g hg
      have hg_G := H.subset g hg_H
      have ha_N := inter_subset_left_aux N K a ha_NK
      have ha_K := inter_subset_right_aux N K a ha_NK
      have ha_G := N.subset a ha_N
      have hb_H := inter_subset_left_aux H M b hb_HM
      have hb_M := inter_subset_right_aux H M b hb_HM
      have hb_G := H.subset b hb_H
      -- g·x·g⁻¹ = g·(a·b)·g⁻¹ = (g·a·g⁻¹)·(g·b·g⁻¹)
      -- g·a·g⁻¹ ∈ N∩K: a ∈ N∩K ⊴ H∩K (Prop § 2)
      have hconj_a : G.op (G.op g a) (G.inv g) ∈ (N.inter K).carrier.elems :=
        inter_N_K_normal_in_inter_H_K G H K N hNH hNN g a hg ha_NK
      -- g·b·g⁻¹ ∈ H∩M: b ∈ H∩M ⊴ H∩K (Prop § 3)
      have hconj_b : G.op (G.op g b) (G.inv g) ∈ (H.inter M).carrier.elems :=
        inter_H_M_normal_in_inter_H_K G H K M hMM g b hg hb_HM
      -- g·x·g⁻¹ = (g·a·g⁻¹)·(g·b·g⁻¹)
      have hconj_split :
          G.op (G.op g x) (G.inv g) =
          G.op (G.op (G.op g a) (G.inv g)) (G.op (G.op g b) (G.inv g)) := by
        rw [← hab]
        have hgag := op_mem G hg_G ha_G
        have hbg  := op_mem G hb_G (inv_mem G hg_G)
        have hgbg := op_mem G (op_mem G hg_G hb_G) (inv_mem G hg_G)
        symm
        calc G.op (G.op (G.op g a) (G.inv g)) (G.op (G.op g b) (G.inv g))
            = G.op (G.op g a) (G.op (G.inv g) (G.op (G.op g b) (G.inv g))) :=
                  G.op_assoc _ _ _ hgag (inv_mem G hg_G) hgbg
          _ = G.op (G.op g a) (G.op (G.op (G.inv g) (G.op g b)) (G.inv g)) := by
                  rw [← G.op_assoc (G.inv g) (G.op g b) (G.inv g)
                        (inv_mem G hg_G) (op_mem G hg_G hb_G) (inv_mem G hg_G)]
          _ = G.op (G.op g a) (G.op (G.op (G.op (G.inv g) g) b) (G.inv g)) := by
                  rw [← G.op_assoc (G.inv g) g b (inv_mem G hg_G) hg_G hb_G]
          _ = G.op (G.op g a) (G.op (G.op G.id b) (G.inv g)) := by
                  rw [(G.op_inv g hg_G).2]
          _ = G.op (G.op g a) (G.op b (G.inv g)) := by
                  rw [(G.op_id b hb_G).2]
          _ = G.op (G.op (G.op g a) b) (G.inv g) :=
                  (G.op_assoc _ _ _ hgag hb_G (inv_mem G hg_G)).symm
          _ = G.op (G.op g (G.op a b)) (G.inv g) := by
                  rw [G.op_assoc g a b hg_G ha_G hb_G]
      refine ⟨hconj_split ▸ op_mem G
          (N.subset _ (inter_subset_left_aux N K _ hconj_a))
          (H.subset _ (inter_subset_left_aux H M _ hconj_b)), ?_⟩
      rw [hconj_split]
      exact ⟨G.op (G.op g a) (G.inv g), hconj_a,
             G.op (G.op g b) (G.inv g), hconj_b, rfl⟩

    /-! ## § 5. Los subgrupos producto N(H∩K) y N(H∩M) -/

    /-- Normalidad de N en H expresada como tipo IsNormal-like para N como subgrupo de G. -/
    private def NormalIn (G : FinGroup ℕ₀) (N H : Subgroup G) : Prop :=
      ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
        G.op (G.op g n) (G.inv g) ∈ N.carrier.elems

    /-- `N(H∩K)` = producto de N con H∩K, con N ⊴ H. -/
    def prodN_HK
        (G : FinGroup ℕ₀) (H K N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hNN : NormalIn G N H) :
        Subgroup G :=
      prodSubgroup G N (H.inter K) H
        hNH
        (fun a ha => inter_subset_left_aux H K a ha)
        hNN

    /-- `N(H∩M)` = producto de N con H∩M, con N ⊴ H. -/
    def prodN_HM
        (G : FinGroup ℕ₀) (H M N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hNN : NormalIn G N H) :
        Subgroup G :=
      prodSubgroup G N (H.inter M) H
        hNH
        (fun a ha => inter_subset_left_aux H M a ha)
        hNN

    /-- `N(H∩M) ≤ N(H∩K)` cuando H∩M ≤ H∩K. -/
    theorem prodN_HM_le_prodN_HK
        (G : FinGroup ℕ₀) (H K M N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (x : ℕ₀) :
        x ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems →
        x ∈ (prodN_HK G H K N hNH hNN).carrier.elems := by
      simp only [prodN_HM, prodN_HK]
      rw [mem_prodSubgroup_iff, mem_prodSubgroup_iff]
      rintro ⟨hx_G, n, hn, m, hm_HM, heq⟩
      refine ⟨hx_G, n, hn, m, ?_, heq⟩
      -- m ∈ H∩M implies m ∈ H∩K (using hMK)
      rw [mem_inter_iff H K]
      have hm_H := inter_subset_left_aux H M m hm_HM
      have hm_M := inter_subset_right_aux H M m hm_HM
      exact ⟨H.subset m hm_H, hm_H, hMK m hm_M⟩

    /-! ## § 6. N(H∩M) ⊴ N(H∩K)

    Prueba: Para g ∈ N(H∩K), y ∈ N(H∩M):
    - Escribir g = n_g · k_g con n_g ∈ N, k_g ∈ H∩K
    - Escribir y = n_y · m_y con n_y ∈ N, m_y ∈ H∩M
    - Entonces g·y·g⁻¹ = n''·m_y'·n₀ donde
        n'' = n_g·(k_g·n_y·k_g⁻¹)·n_g⁻¹ ∈ N
        m_y' = k_g·m_y·k_g⁻¹ ∈ H∩M
        n₀ = (G.inv m_y')·(n_g·m_y'·n_g⁻¹) ∈ N  (por N ⊴ N(H∩K))
    - n''·m_y'·n₀ ∈ N(H∩M) pues n'', m_y', n₀ ∈ N(H∩M) y N(H∩M) es subgrupo.
    -/

    /-- N es normal en N(H∩K). -/
    private theorem N_normal_in_prodN_HK
        (G : FinGroup ℕ₀) (H K N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hNN : NormalIn G N H) :
        NormalIn G N (prodN_HK G H K N hNH hNN) := by
      intro g n hg hn
      simp only [prodN_HK] at hg
      rw [mem_prodSubgroup_iff] at hg
      obtain ⟨_, a, ha, b, hb, hg_eq⟩ := hg
      have hg_H : g ∈ H.carrier.elems := by
        rw [← hg_eq]
        exact H.op_closed _ _ (hNH a ha) (inter_subset_left_aux H K b hb)
      exact hNN g n hg_H hn

    /-- `N(H∩M) ⊴ N(H∩K)`. -/
    theorem prodN_HM_normal_in_prodN_HK
        (G : FinGroup ℕ₀) (H K M N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        ∀ g y,
          g ∈ (prodN_HK G H K N hNH hNN).carrier.elems →
          y ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems →
          G.op (G.op g y) (G.inv g) ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems := by
      intro g y hg hy
      -- Descomponer g = n_g · k_g y y = n_y · m_y
      simp only [prodN_HK, prodN_HM] at hg hy ⊢
      rw [mem_prodSubgroup_iff] at hg hy
      obtain ⟨_, n_g, hn_g, k_g, hk_g, hg_eq⟩ := hg
      obtain ⟨_, n_y, hn_y, m_y, hm_y, hy_eq⟩ := hy
      have hng_G := N.subset n_g hn_g
      have hng_H := hNH n_g hn_g
      have hkg_G := (H.inter K).subset k_g hk_g
      have hkg_H := inter_subset_left_aux H K k_g hk_g
      have hkg_K := inter_subset_right_aux H K k_g hk_g
      have hny_G := N.subset n_y hn_y
      have hmy_H := inter_subset_left_aux H M m_y hm_y
      have hmy_M := inter_subset_right_aux H M m_y hm_y
      have hmy_G := H.subset m_y hmy_H
      -- Definir los elementos intermedios
      -- n_y' = k_g · n_y · k_g⁻¹ ∈ N
      have hny' : G.op (G.op k_g n_y) (G.inv k_g) ∈ N.carrier.elems :=
        hNN k_g n_y hkg_H hn_y
      -- m_y' = k_g · m_y · k_g⁻¹ ∈ H∩M
      have hmy'_M : G.op (G.op k_g m_y) (G.inv k_g) ∈ M.carrier.elems :=
        hMM k_g m_y hkg_K hmy_M
      have hmy'_H : G.op (G.op k_g m_y) (G.inv k_g) ∈ H.carrier.elems :=
        H.op_closed _ _ (H.op_closed k_g m_y hkg_H hmy_H) (H.inv_closed k_g hkg_H)
      have hmy'_HM : G.op (G.op k_g m_y) (G.inv k_g) ∈ (H.inter M).carrier.elems := by
        rw [mem_inter_iff H M]
        exact ⟨op_mem G (op_mem G hkg_G hmy_G) (inv_mem G hkg_G), hmy'_H, hmy'_M⟩
      let m_y' := G.op (G.op k_g m_y) (G.inv k_g)
      have hmy'_G := H.subset m_y' hmy'_H
      -- n'' = n_g · n_y' · n_g⁻¹ ∈ N
      have hny'' : G.op (G.op n_g (G.op (G.op k_g n_y) (G.inv k_g))) (G.inv n_g)
                   ∈ N.carrier.elems :=
        hNN n_g _ hng_H hny'
      -- n₀ = (m_y')⁻¹ · n_g · m_y' · n_g⁻¹ ∈ N  (usando N ⊴ N(H∩K))
      -- Equivalentemente: (m_y')⁻¹ · (n_g · m_y' · n_g⁻¹) ∈ N pues
      -- n_g · m_y' · n_g⁻¹ ∈ N(H∩M) ... hmm, necesitamos más.
      -- Mejor: n₀ = (m_y')⁻¹ · m''  donde m'' = n_g · m_y' · n_g⁻¹
      --         = G.op (G.inv m_y') (G.op (G.op n_g m_y') (G.inv n_g))
      -- Probar n₀ ∈ N:
      --   (G.inv m_y') ∈ N(H∩K) pues m_y'∈H∩M≤H∩K≤N(H∩K)
      --   Por N⊴N(H∩K): (G.inv m_y')·n_g·m_y' ∈ N
      -- Key: use that N ⊴ H (and G.inv m_y' ∈ H since H∩K ≤ H):
      --   G.op (G.op (G.inv m_y') n_g) m_y' ∈ N pues hNN (G.inv m_y') n_g (H.inv_closed m_y' hmy'_H) hn_g
      --   and then G.inv of (G.inv m_y') = m_y', so this is: conj of n_g by G.inv m_y'
      -- α = m_y' · n_g⁻¹ · m_y'⁻¹ ∈ N  (conjugate of n_g⁻¹ ∈ N by m_y' ∈ H)
      have hα : G.op (G.op m_y' (G.inv n_g)) (G.inv m_y') ∈ N.carrier.elems :=
        hNN m_y' (G.inv n_g) hmy'_H (N.inv_closed n_g hn_g)
      -- n_pair = n_g · n_y' · α  where n_y' = k_g·n_y·k_g⁻¹
      -- n_pair ∈ N since n_g ∈ N, n_y' ∈ N, α ∈ N
      have hn_pair : G.op n_g (G.op (G.op (G.op k_g n_y) (G.inv k_g))
                                    (G.op (G.op m_y' (G.inv n_g)) (G.inv m_y')))
          ∈ N.carrier.elems := by
        exact N.op_closed _ _ hn_g (N.op_closed _ _ hny' hα)
      -- Identity: n_pair · m_y' = g · y · g⁻¹
      -- Proof outline:
      --   n_pair · m_y'
      --   = n_g · n_y' · (m_y'·n_g⁻¹·m_y'⁻¹) · m_y'           [definition]
      --   = n_g · n_y' · m_y' · (n_g⁻¹·(m_y'⁻¹·m_y'))          [reassociate]
      --   = n_g · n_y' · m_y' · n_g⁻¹                           [m_y'⁻¹·m_y' = e]
      --   = n_g · (k_g·n_y·k_g⁻¹) · (k_g·m_y·k_g⁻¹) · n_g⁻¹   [def of n_y', m_y']
      --   = n_g · k_g · n_y · (k_g⁻¹·k_g) · m_y · k_g⁻¹ · n_g⁻¹ [insert e]
      --   = n_g · k_g · n_y · m_y · k_g⁻¹ · n_g⁻¹               [k_g⁻¹·k_g = e]
      --   = g · y · g⁻¹                                           [hg_eq, hy_eq]
      have hident : G.op
          (G.op n_g (G.op (G.op (G.op k_g n_y) (G.inv k_g))
                          (G.op (G.op m_y' (G.inv n_g)) (G.inv m_y'))))
          m_y' =
          G.op (G.op g y) (G.inv g) := by
        have hinvkg_G := inv_mem G hkg_G
        have hinvng_G := inv_mem G hng_G
        have hinvmy'_G := inv_mem G hmy'_G
        have hny'_G := N.subset _ hny'
        -- First: (m_y'·n_g⁻¹·m_y'⁻¹)·m_y' = m_y'·n_g⁻¹  (right cancel m_y'⁻¹·m_y')
        have hcancel : G.op (G.op (G.op m_y' (G.inv n_g)) (G.inv m_y')) m_y' =
                       G.op m_y' (G.inv n_g) := by
          rw [G.op_assoc (G.op m_y' (G.inv n_g)) (G.inv m_y') m_y'
                (op_mem G hmy'_G hinvng_G) hinvmy'_G hmy'_G,
              (G.op_inv m_y' hmy'_G).2,
              (G.op_id (G.op m_y' (G.inv n_g)) (op_mem G hmy'_G hinvng_G)).1]
        -- Apply hcancel in LHS: pull m_y' inside
        -- LHS = n_g · n_y' · (α · m_y')
        --     = n_g · n_y' · (m_y'·n_g⁻¹)            [hcancel]
        --     = n_g · (n_y' · m_y') · n_g⁻¹           [reassociate]
        -- Goal transformation: pull m_y' to the innermost position
        rw [G.op_assoc n_g
              (G.op (G.op (G.op k_g n_y) (G.inv k_g))
                    (G.op (G.op m_y' (G.inv n_g)) (G.inv m_y')))
              m_y'
              hng_G
              (op_mem G (op_mem G (op_mem G hkg_G hny_G) hinvkg_G)
                        (op_mem G (op_mem G hmy'_G hinvng_G) hinvmy'_G))
              hmy'_G,
            G.op_assoc (G.op (G.op k_g n_y) (G.inv k_g))
              (G.op (G.op m_y' (G.inv n_g)) (G.inv m_y')) m_y'
              (op_mem G (op_mem G hkg_G hny_G) hinvkg_G)
              (op_mem G (op_mem G hmy'_G hinvng_G) hinvmy'_G)
              hmy'_G,
            hcancel]
        -- LHS is now: n_g · (n_y' · (m_y'·n_g⁻¹))
        -- = n_g · (n_y' · m_y') · n_g⁻¹
        rw [← G.op_assoc (G.op (G.op k_g n_y) (G.inv k_g)) m_y' (G.inv n_g)
              (op_mem G (op_mem G hkg_G hny_G) hinvkg_G) hmy'_G hinvng_G,
            ← G.op_assoc n_g
                (G.op (G.op (G.op k_g n_y) (G.inv k_g)) m_y') (G.inv n_g)
                hng_G
                (op_mem G (op_mem G (op_mem G hkg_G hny_G) hinvkg_G) hmy'_G)
                hinvng_G]
        -- LHS: n_g · (n_y' · m_y') · n_g⁻¹  where m_y' = k_g·m_y·k_g⁻¹
        -- = n_g · (k_g·n_y·k_g⁻¹ · k_g·m_y·k_g⁻¹) · n_g⁻¹
        -- fold k_g⁻¹·k_g:
        -- k_g·n_y·k_g⁻¹ · k_g·m_y·k_g⁻¹
        -- = k_g·n_y · (k_g⁻¹·k_g) · m_y · k_g⁻¹
        -- = k_g·n_y · m_y · k_g⁻¹
        -- = k_g · (n_y·m_y) · k_g⁻¹
        -- Prove: (k_g·n_y·k_g⁻¹) · m_y' = k_g·(n_y·m_y)·k_g⁻¹
        have hfold : G.op (G.op (G.op k_g n_y) (G.inv k_g)) m_y' =
                     G.op (G.op k_g (G.op n_y m_y)) (G.inv k_g) := by
          show G.op (G.op (G.op k_g n_y) (G.inv k_g)) (G.op (G.op k_g m_y) (G.inv k_g)) =
               G.op (G.op k_g (G.op n_y m_y)) (G.inv k_g)
          -- (k_g·n_y·k_g⁻¹)·(k_g·m_y·k_g⁻¹) = k_g·(n_y·m_y)·k_g⁻¹
          -- Step: fold k_g⁻¹·k_g = e in the middle
          -- Goal: (k_g·n_y·k_g⁻¹)·(k_g·m_y·k_g⁻¹) = k_g·(n_y·m_y)·k_g⁻¹
          -- Reassociate LHS: k_g·n_y · (k_g⁻¹·k_g·m_y·k_g⁻¹)
          rw [G.op_assoc (G.op k_g n_y) (G.inv k_g) (G.op (G.op k_g m_y) (G.inv k_g))
                (op_mem G hkg_G hny_G) hinvkg_G (op_mem G (op_mem G hkg_G hmy_G) hinvkg_G)]
          -- now: (k_g·n_y) · (k_g⁻¹·((k_g·m_y)·k_g⁻¹))
          -- expand (k_g·m_y)·k_g⁻¹ → k_g·(m_y·k_g⁻¹), then fold k_g⁻¹·k_g
          rw [G.op_assoc k_g m_y (G.inv k_g) hkg_G hmy_G hinvkg_G,
              ← G.op_assoc (G.inv k_g) k_g (G.op m_y (G.inv k_g))
                  hinvkg_G hkg_G (op_mem G hmy_G hinvkg_G),
              (G.op_inv k_g hkg_G).2,
              (G.op_id (G.op m_y (G.inv k_g)) (op_mem G hmy_G hinvkg_G)).2,
              ← G.op_assoc (G.op k_g n_y) m_y (G.inv k_g)
                  (op_mem G hkg_G hny_G) hmy_G hinvkg_G,
              G.op_assoc k_g n_y m_y hkg_G hny_G hmy_G]
        -- LHS: n_g · (k_g·(n_y·m_y)·k_g⁻¹) · n_g⁻¹
        -- RHS: g·y·g⁻¹ = (n_g·k_g)·(n_y·m_y)·(k_g⁻¹·n_g⁻¹)
        rw [hfold, ← hg_eq, ← hy_eq, inv_op_eq G hng_G hkg_G,
            G.op_assoc n_g (G.op (G.op k_g (G.op n_y m_y)) (G.inv k_g)) (G.inv n_g)
              hng_G (op_mem G (op_mem G hkg_G (op_mem G hny_G hmy_G)) hinvkg_G) hinvng_G,
            G.op_assoc (G.op k_g (G.op n_y m_y)) (G.inv k_g) (G.inv n_g)
              (op_mem G hkg_G (op_mem G hny_G hmy_G)) hinvkg_G hinvng_G,
            G.op_assoc k_g (G.op n_y m_y) (G.op (G.inv k_g) (G.inv n_g))
                hkg_G (op_mem G hny_G hmy_G) (op_mem G hinvkg_G hinvng_G),
            ← G.op_assoc n_g k_g (G.op (G.op n_y m_y) (G.op (G.inv k_g) (G.inv n_g)))
                hng_G hkg_G (op_mem G (op_mem G hny_G hmy_G) (op_mem G hinvkg_G hinvng_G)),
            ← G.op_assoc (G.op n_g k_g) (G.op n_y m_y) (G.op (G.inv k_g) (G.inv n_g))
                (op_mem G hng_G hkg_G) (op_mem G hny_G hmy_G) (op_mem G hinvkg_G hinvng_G)]
      rw [mem_prodSubgroup_iff]
      refine ⟨?_, ?_⟩
      · have hg_G' : g ∈ G.carrier.elems := hg_eq ▸ op_mem G hng_G hkg_G
        have hy_G' : y ∈ G.carrier.elems := hy_eq ▸ op_mem G hny_G hmy_G
        exact op_mem G (op_mem G hg_G' hy_G') (inv_mem G hg_G')
      · exact ⟨G.op n_g (G.op (G.op (G.op k_g n_y) (G.inv k_g))
                                (G.op (G.op m_y' (G.inv n_g)) (G.inv m_y'))),
               hn_pair, m_y', hmy'_HM, hident⟩
      -- Identity: n_pair · m_y' = g · y · g⁻¹
      -- n_g · (k_g·n_y·k_g⁻¹) · (m_y'·n_g⁻¹·m_y'⁻¹) · m_y'
    /-! ## § 7. Normalidad de `(N∩K)(H∩M)` en `H∩K`, y la biyección principal. -/

    /-! ### § 7.1. Subgrupos empaquetados para los cocientes -/

    /-- Todos los elementos de `(N∩K)(H∩M)` pertenecen a `H∩K`. -/
    private theorem prodNKHM_le_HK
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K)
        (x : ℕ₀) :
        x ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems →
        x ∈ (H.inter K).carrier.elems := by
      intro hx
      simp only [prodNKHM] at hx
      rw [mem_prodSubgroup_iff] at hx
      obtain ⟨_, a, ha_NK, b, hb_HM, heq⟩ := hx
      have ha_N := inter_subset_left_aux N K a ha_NK
      have ha_K := inter_subset_right_aux N K a ha_NK
      have ha_H := hNH a ha_N
      have hb_H := inter_subset_left_aux H M b hb_HM
      have hb_M := inter_subset_right_aux H M b hb_HM
      have hb_K := hMK b hb_M
      rw [mem_inter_iff H K, ← heq]
      exact ⟨op_mem G (H.subset a ha_H) (H.subset b hb_H),
             H.op_closed a b ha_H hb_H,
             K.op_closed a b ha_K hb_K⟩

    /-- `(N∩K)(H∩M)` como subgrupo del grupo finito `H∩K`. -/
    private def prodNKHM_in_HK
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        Subgroup (Subgroup.toFinGroup (H.inter K)) where
      carrier    := (prodNKHM G H K N M hNH hMK hNN hMM).carrier
      nonempty   := (prodNKHM G H K N M hNH hMK hNN hMM).nonempty
      subset     := fun a ha =>
        prodNKHM_le_HK G H K N M hNH hMK hNN hMM a ha
      op_closed  := fun a b ha hb =>
        (prodNKHM G H K N M hNH hMK hNN hMM).op_closed a b ha hb
      id_in      := (prodNKHM G H K N M hNH hMK hNN hMM).id_in
      inv_closed := fun a ha =>
        (prodNKHM G H K N M hNH hMK hNN hMM).inv_closed a ha

    /-- `N(H∩M)` como subgrupo del grupo finito `N(H∩K)`. -/
    private def prodN_HM_in_prodN_HK
        (G : FinGroup ℕ₀) (H K M N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H) :
        Subgroup (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN)) where
      carrier    := (prodN_HM G H M N hNH hMH hNN).carrier
      nonempty   := (prodN_HM G H M N hNH hMH hNN).nonempty
      subset     := fun a ha =>
        prodN_HM_le_prodN_HK G H K M N hNH hMH hMK hNN a ha
      op_closed  := fun a b ha hb =>
        (prodN_HM G H M N hNH hMH hNN).op_closed a b ha hb
      id_in      := (prodN_HM G H M N hNH hMH hNN).id_in
      inv_closed := fun a ha =>
        (prodN_HM G H M N hNH hMH hNN).inv_closed a ha

    /-! ### § 7.2. Lemas algebraicos para la biyección -/

    /-- `(N∩K)(H∩M) ≤ N(H∩M)` como subconjuntos de `G`. -/
    private theorem prodNKHM_sub_prodN_HM
        (G : FinGroup ℕ₀) (H K M N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K)
        (x : ℕ₀) :
        x ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems →
        x ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems := by
      intro hx
      simp only [prodNKHM, prodN_HM] at hx ⊢
      rw [mem_prodSubgroup_iff] at hx ⊢
      obtain ⟨hx_G, a, ha_NK, b, hb_HM, heq⟩ := hx
      exact ⟨hx_G, a, inter_subset_left_aux N K a ha_NK, b, hb_HM, heq⟩

    /-- **Lema clave**: `(H∩K) ∩ N(H∩M) ≤ (N∩K)(H∩M)`. -/
    private theorem HK_inter_prodN_HM_le_prodNKHM
        (G : FinGroup ℕ₀) (H K M N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K)
        (x : ℕ₀) :
        x ∈ (H.inter K).carrier.elems →
        x ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems →
        x ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems := by
      intro hx_HK hx_NHM
      simp only [prodN_HM] at hx_NHM
      rw [mem_prodSubgroup_iff] at hx_NHM
      obtain ⟨_, n, hn_N, m, hm_HM, heq⟩ := hx_NHM
      -- n = x · m⁻¹, y n ∈ N∩K
      have hx_K  := inter_subset_right_aux H K x hx_HK
      have hm_M  := inter_subset_right_aux H M m hm_HM
      have hm_K  := hMK m hm_M
      have hn_G  := N.subset n hn_N
      have hm_G  := M.subset m hm_M
      have hx_G  := (H.inter K).subset x hx_HK
      -- n = x · m⁻¹
      have hn_eq : n = G.op x (G.inv m) := by
        rw [← heq,
            G.op_assoc n m (G.inv m) hn_G hm_G (inv_mem G hm_G),
            (G.op_inv m hm_G).1, (G.op_id n hn_G).1]
      -- n ∈ K
      have hn_K : n ∈ K.carrier.elems :=
        hn_eq ▸ K.op_closed x (G.inv m) hx_K (K.inv_closed m hm_K)
      -- n ∈ N∩K
      have hn_NK : n ∈ (N.inter K).carrier.elems := by
        rw [mem_inter_iff N K]
        exact ⟨hn_G, hn_N, hn_K⟩
      simp only [prodNKHM]
      rw [mem_prodSubgroup_iff]
      exact ⟨hx_G, n, hn_NK, m, hm_HM, heq⟩

    /-- `H∩K ≤ N(H∩K)`. -/
    private theorem HK_le_prodN_HK
        (G : FinGroup ℕ₀) (H K N : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hNN : NormalIn G N H)
        (x : ℕ₀) :
        x ∈ (H.inter K).carrier.elems →
        x ∈ (prodN_HK G H K N hNH hNN).carrier.elems :=
      fun hx =>
        S_le_prodSubgroup G N (H.inter K) H hNH
          (fun a ha => inter_subset_left_aux H K a ha) hNN x hx

    /-! ### § 7.3. La biyección de Zassenhaus -/

    /-- La aplicación `(H∩K)/(N∩K)(H∩M) → N(H∩K)/N(H∩M)`:
        `C ↦ (cosetRepOf C) · N(H∩M)`. -/
    private noncomputable def zassenhaus_map
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        MapOn
          (quotientCarrier
            (Subgroup.toFinGroup (H.inter K))
            (prodNKHM_in_HK G H K N M hNH hMK hNN hMM))
          (quotientCarrier
            (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN))
            (prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN)) where
      toFun := fun C =>
        leftCoset
          (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN))
          (prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN)
          (cosetRepOf
            (Subgroup.toFinGroup (H.inter K))
            (prodNKHM_in_HK G H K N M hNH hMK hNN hMM)
            C)
      map_carrier := fun C hC =>
        leftCoset_mem_quotientCarrier
          (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN))
          (prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN)
          _
          (HK_le_prodN_HK G H K N hNH hNN _
            (cosetRepOf_mem_G
              (Subgroup.toFinGroup (H.inter K))
              (prodNKHM_in_HK G H K N M hNH hMK hNN hMM)
              C hC))

    /-- Bien-definición: `zassenhaus_map(k · B) = k · N(H∩M)` para `k ∈ H∩K`. -/
    private theorem zassenhaus_map_welldefined
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K)
        (k : ℕ₀) (hk : k ∈ (H.inter K).carrier.elems) :
        (zassenhaus_map G H K N M hNH hMH hMK hNN hMM).toFun
          (leftCoset
            (Subgroup.toFinGroup (H.inter K))
            (prodNKHM_in_HK G H K N M hNH hMK hNN hMM)
            k) =
          leftCoset
            (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN))
            (prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN)
            k := by
      simp only [zassenhaus_map]
      let HKg     := Subgroup.toFinGroup (H.inter K)
      let NKHM    := prodNKHM_in_HK G H K N M hNH hMK hNN hMM
      let NHKg    := Subgroup.toFinGroup (prodN_HK G H K N hNH hNN)
      let NHM_sub := prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN
      have hk_in : leftCoset HKg NKHM k ∈ (quotientCarrier HKg NKHM).elems :=
        leftCoset_mem_quotientCarrier HKg NKHM k hk
      let r := cosetRepOf HKg NKHM (leftCoset HKg NKHM k)
      have hr_HK : r ∈ (H.inter K).carrier.elems :=
        cosetRepOf_mem_G HKg NKHM _ hk_in
      have hrel : cosetRel HKg NKHM r k :=
        cosetRel_of_leftCoset_eq HKg NKHM r k hr_HK hk
          (cosetRepOf_leftCoset_eq HKg NKHM _ hk_in)
      -- r⁻¹*k ∈ prodNKHM → ∈ prodN_HM
      unfold cosetRel at hrel
      have hrel_NHM : G.op (G.inv r) k ∈
          (prodN_HM G H M N hNH hMH hNN).carrier.elems :=
        prodNKHM_sub_prodN_HM G H K M N hNH hMH hMK hNN hMM _ hrel
      -- cosetRel NHKg NHM_sub r k
      have hrel2 : cosetRel NHKg NHM_sub r k := by
        unfold cosetRel
        exact hrel_NHM
      exact leftCoset_eq_of_rel NHKg NHM_sub r k
        (HK_le_prodN_HK G H K N hNH hNN r hr_HK)
        (HK_le_prodN_HK G H K N hNH hNN k hk)
        hrel2

    /-- `zassenhaus_map` es inyectiva. -/
    private theorem zassenhaus_map_injective
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        (zassenhaus_map G H K N M hNH hMH hMK hNN hMM).Injective := by
      intro C₁ C₂ hC₁ hC₂ hφ
      simp only [zassenhaus_map] at hφ
      let HKg     := Subgroup.toFinGroup (H.inter K)
      let NKHM    := prodNKHM_in_HK G H K N M hNH hMK hNN hMM
      let NHKg    := Subgroup.toFinGroup (prodN_HK G H K N hNH hNN)
      let NHM_sub := prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN
      rw [← cosetRepOf_leftCoset_eq HKg NKHM C₁ hC₁,
          ← cosetRepOf_leftCoset_eq HKg NKHM C₂ hC₂]
      let r₁ := cosetRepOf HKg NKHM C₁
      let r₂ := cosetRepOf HKg NKHM C₂
      have hr₁_HK := cosetRepOf_mem_G HKg NKHM C₁ hC₁
      have hr₂_HK := cosetRepOf_mem_G HKg NKHM C₂ hC₂
      -- φ(C₁) = φ(C₂) ⟹ cosetRel NHKg NHM_sub r₁ r₂
      have hrel_NHM : cosetRel NHKg NHM_sub r₁ r₂ :=
        cosetRel_of_leftCoset_eq NHKg NHM_sub r₁ r₂
          (HK_le_prodN_HK G H K N hNH hNN r₁ hr₁_HK)
          (HK_le_prodN_HK G H K N hNH hNN r₂ hr₂_HK)
          hφ
      unfold cosetRel at hrel_NHM
      -- r₁⁻¹*r₂ ∈ H∩K (ya que r₁, r₂ ∈ H∩K)
      have hr₁_H := inter_subset_left_aux H K r₁ hr₁_HK
      have hr₂_H := inter_subset_left_aux H K r₂ hr₂_HK
      have hr₁_K := inter_subset_right_aux H K r₁ hr₁_HK
      have hr₂_K := inter_subset_right_aux H K r₂ hr₂_HK
      have hr₁_G := H.subset r₁ hr₁_H
      have hr₂_G := H.subset r₂ hr₂_H
      have hinvr₁_r₂_HK : G.op (G.inv r₁) r₂ ∈ (H.inter K).carrier.elems := by
        rw [mem_inter_iff H K]
        exact ⟨op_mem G (inv_mem G hr₁_G) hr₂_G,
               H.op_closed (G.inv r₁) r₂ (H.inv_closed r₁ hr₁_H) hr₂_H,
               K.op_closed (G.inv r₁) r₂ (K.inv_closed r₁ hr₁_K) hr₂_K⟩
      -- Lema clave: r₁⁻¹*r₂ ∈ H∩K ∩ prodN_HM ⟹ ∈ prodNKHM
      have hrel_NKHM : G.op (G.inv r₁) r₂ ∈
          (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems :=
        HK_inter_prodN_HM_le_prodNKHM G H K M N hNH hMH hMK hNN hMM _
          hinvr₁_r₂_HK hrel_NHM
      -- cosetRel HKg NKHM r₁ r₂
      apply (leftCoset_eq_iff_cosetRel HKg NKHM r₁ r₂ hr₁_HK hr₂_HK).mpr
      unfold cosetRel
      exact hrel_NKHM

    /-- `zassenhaus_map` es sobreyectiva. -/
    private theorem zassenhaus_map_surjective
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        (zassenhaus_map G H K N M hNH hMH hMK hNN hMM).Surjective := by
      intro D hD
      let HKg     := Subgroup.toFinGroup (H.inter K)
      let NKHM    := prodNKHM_in_HK G H K N M hNH hMK hNN hMM
      let NHKg    := Subgroup.toFinGroup (prodN_HK G H K N hNH hNN)
      let NHM_sub := prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN
      -- D = leftCoset NHKg NHM_sub x para x ∈ prodN_HK
      obtain ⟨x, hx_NHK, rfl⟩ :=
        mem_quotientCarrier_is_leftCoset NHKg NHM_sub _ hD
      -- x = n * k con n ∈ N, k ∈ H∩K
      have hx_in : x ∈ (prodN_HK G H K N hNH hNN).carrier.elems := hx_NHK
      simp only [prodN_HK] at hx_in
      rw [mem_prodSubgroup_iff] at hx_in
      obtain ⟨_, n, hn_N, k, hk_HK, heq_x⟩ := hx_in
      -- El preimagen es leftCoset HKg NKHM k
      refine ⟨leftCoset HKg NKHM k,
              leftCoset_mem_quotientCarrier HKg NKHM k hk_HK, ?_⟩
      rw [zassenhaus_map_welldefined G H K N M hNH hMH hMK hNN hMM k hk_HK]
      -- Basta: leftCoset NHKg NHM_sub k = leftCoset NHKg NHM_sub x
      -- i.e., cosetRel NHKg NHM_sub k x, i.e., k⁻¹ * x ∈ prodN_HM
      apply leftCoset_eq_of_rel NHKg NHM_sub k x
        (HK_le_prodN_HK G H K N hNH hNN k hk_HK)
        hx_NHK
      -- k⁻¹ * x = k⁻¹ * (n * k) = (k⁻¹ * n) * k ∈ N ≤ prodN_HM
      unfold cosetRel
      have hk_H  := inter_subset_left_aux H K k hk_HK
      have hk_G  := H.subset k hk_H
      have hn_G  := N.subset n hn_N
      -- (k⁻¹*n)*k ∈ N via conjugación
      have hconj : G.op (G.op (G.inv k) n) (G.inv (G.inv k)) ∈ N.carrier.elems :=
        hNN (G.inv k) n (H.inv_closed k hk_H) hn_N
      rw [inv_inv_eq G hk_G] at hconj
      -- Construimos: G.op (G.inv k) (G.op n k) ∈ prodN_HM
      have hmem_NK : G.op (G.inv k) (G.op n k) ∈
          (prodN_HM G H M N hNH hMH hNN).carrier.elems := by
        rw [← G.op_assoc (G.inv k) n k (inv_mem G hk_G) hn_G hk_G]
        exact N_le_prodSubgroup G N (H.inter M) H hNH
          (fun a ha => inter_subset_left_aux H M a ha) hNN _ hconj
      -- heq_x : G.op n k = x; sustituimos en hmem_NK para obtener el goal
      rw [heq_x] at hmem_NK
      exact hmem_NK

    /-- `zassenhaus_map` es biyectiva. -/
    private theorem zassenhaus_map_bijective
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        (zassenhaus_map G H K N M hNH hMH hMK hNN hMM).Bijective :=
      ⟨zassenhaus_map_injective G H K N M hNH hMH hMK hNN hMM,
       zassenhaus_map_surjective G H K N M hNH hMH hMK hNN hMM⟩

    /-- **Lema de la Mariposa de Zassenhaus** (enunciado principal):
        Existe una biyección `(H∩K)/[(N∩K)(H∩M)] ↔ N(H∩K)/N(H∩M)`. -/
    theorem zassenhaus_bijection
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        ∃ (f : MapOn
            (quotientCarrier
              (Subgroup.toFinGroup (H.inter K))
              (prodNKHM_in_HK G H K N M hNH hMK hNN hMM))
            (quotientCarrier
              (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN))
              (prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN))),
          f.Bijective :=
      ⟨zassenhaus_map G H K N M hNH hMH hMK hNN hMM,
       zassenhaus_map_bijective G H K N M hNH hMH hMK hNN hMM⟩

    /-- **Lema de la Mariposa de Zassenhaus** (enunciado simétrico):
        Intercambiando el papel de `(H, N)` y `(K, M)`, se obtiene una biyección
        `(K∩H)/[(M∩H)(K∩N)] ↔ M(K∩H)/M(K∩N)`.
        Requiere la hipótesis extra `hNK : N ≤ K`. -/
    theorem zassenhaus_bijection_symm
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hNK : ∀ a, a ∈ N.carrier.elems → a ∈ K.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        ∃ (f : MapOn
            (quotientCarrier
              (Subgroup.toFinGroup (K.inter H))
              (prodNKHM_in_HK G K H M N hMK hNH hMM hNN))
            (quotientCarrier
              (Subgroup.toFinGroup (prodN_HK G K H M hMK hMM))
              (prodN_HM_in_prodN_HK G K H N M hMK hNK hNH hMM))),
            f.Bijective :=
        zassenhaus_bijection G K H M N hMK hNK hNH hMM hNN

    -- Lema auxiliar: H∩K = K∩H como subgrupos
    private theorem inter_comm_lem {G : FinGroup ℕ₀} (H K : Subgroup G) :
        H.inter K = K.inter H := by
      apply Subgroup.ext_carrier
      apply FSet.eq_of_mem_iff
      intro z
      constructor
      · intro hz
        obtain ⟨hzG, hzH, hzK⟩ := (mem_inter_iff H K z).mp hz
        exact (mem_inter_iff K H z).mpr ⟨hzG, hzK, hzH⟩
      · intro hz
        obtain ⟨hzG, hzK, hzH⟩ := (mem_inter_iff K H z).mp hz
        exact (mem_inter_iff H K z).mpr ⟨hzG, hzH, hzK⟩

    -- Lema auxiliar: los carriers de prodNKHM son iguales (N∩K)(H∩M) = (M∩H)(K∩N)
    private theorem prodNKHM_carrier_eq
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        (prodNKHM G H K N M hNH hMK hNN hMM).carrier =
        (prodNKHM G K H M N hMK hNH hMM hNN).carrier := by
      apply FSet.eq_of_mem_iff
      intro x
      -- Abreviatura: A = N∩K, B = H∩M, AB = A·B en H∩K
      --              A'= M∩H, B'= K∩N, A'B'= A'·B' en K∩H
      -- LHS: x ∈ (N∩K)(H∩M)  iff  x ∈ G ∧ ∃ a ∈ N∩K, ∃ b ∈ H∩M, a*b = x
      -- RHS: x ∈ (M∩H)(K∩N)  iff  x ∈ G ∧ ∃ a ∈ M∩H, ∃ b ∈ K∩N, a*b = x
      rw [show (prodNKHM G H K N M hNH hMK hNN hMM).carrier =
              (prodSubgroup G (N.inter K) (H.inter M) (H.inter K)
                (fun a ha => by
                  rw [mem_inter_iff H K]
                  exact ⟨H.subset a (hNH a (inter_subset_left_aux N K a ha)),
                         hNH a (inter_subset_left_aux N K a ha),
                         inter_subset_right_aux N K a ha⟩)
                (fun a ha => by
                  rw [mem_inter_iff H K]
                  exact ⟨H.subset a (inter_subset_left_aux H M a ha),
                         inter_subset_left_aux H M a ha,
                         hMK a (inter_subset_right_aux H M a ha)⟩)
                (inter_N_K_normal_in_inter_H_K G H K N hNH hNN)).carrier from rfl]
      rw [show (prodNKHM G K H M N hMK hNH hMM hNN).carrier =
              (prodSubgroup G (M.inter H) (K.inter N) (K.inter H)
                (fun a ha => by
                  rw [mem_inter_iff K H]
                  exact ⟨K.subset a (hMK a (inter_subset_left_aux M H a ha)),
                         hMK a (inter_subset_left_aux M H a ha),
                         inter_subset_right_aux M H a ha⟩)
                (fun a ha => by
                  rw [mem_inter_iff K H]
                  exact ⟨K.subset a (inter_subset_left_aux K N a ha),
                         inter_subset_left_aux K N a ha,
                         hNH a (inter_subset_right_aux K N a ha)⟩)
                (inter_N_K_normal_in_inter_H_K G K H M hMK hMM)).carrier from rfl]
      rw [mem_prodSubgroup_iff G (N.inter K) (H.inter M) (H.inter K)
            (fun a ha => by
              rw [mem_inter_iff H K]
              exact ⟨H.subset a (hNH a (inter_subset_left_aux N K a ha)),
                     hNH a (inter_subset_left_aux N K a ha),
                     inter_subset_right_aux N K a ha⟩)
            (fun a ha => by
              rw [mem_inter_iff H K]
              exact ⟨H.subset a (inter_subset_left_aux H M a ha),
                     inter_subset_left_aux H M a ha,
                     hMK a (inter_subset_right_aux H M a ha)⟩)
            (inter_N_K_normal_in_inter_H_K G H K N hNH hNN)]
      rw [mem_prodSubgroup_iff G (M.inter H) (K.inter N) (K.inter H)
            (fun a ha => by
              rw [mem_inter_iff K H]
              exact ⟨K.subset a (hMK a (inter_subset_left_aux M H a ha)),
                     hMK a (inter_subset_left_aux M H a ha),
                     inter_subset_right_aux M H a ha⟩)
            (fun a ha => by
              rw [mem_inter_iff K H]
              exact ⟨K.subset a (inter_subset_left_aux K N a ha),
                     inter_subset_left_aux K N a ha,
                     hNH a (inter_subset_right_aux K N a ha)⟩)
            (inter_N_K_normal_in_inter_H_K G K H M hMK hMM)]
      constructor
      · intro ⟨hxG, n, hn_NK, s, hs_HM, heq⟩
        have hn_N  := inter_subset_left_aux N K n hn_NK
        have hn_K  := inter_subset_right_aux N K n hn_NK
        have hs_H  := inter_subset_left_aux H M s hs_HM
        have hs_M  := inter_subset_right_aux H M s hs_HM
        have hn_G  := N.subset n hn_N
        have hs_G  := H.subset s hs_H
        have hs_K  := hMK s hs_M
        -- n' = (inv s)*n*s ∈ N∩K por normalidad
        have hinvs_HK : G.inv s ∈ (H.inter K).carrier.elems := by
          rw [mem_inter_iff]
          exact ⟨inv_mem G hs_G, H.inv_closed s hs_H, K.inv_closed s hs_K⟩
        have hn'_NK := inter_N_K_normal_in_inter_H_K G H K N hNH hNN (G.inv s) n hinvs_HK hn_NK
        rw [inv_inv_eq G hs_G] at hn'_NK
        -- n' = (inv s) * n * s
        have hn'_def : G.op (G.op (G.inv s) n) s ∈ (N.inter K).carrier.elems := hn'_NK
        -- x = s * n'
        have hxeq : x = G.op s (G.op (G.op (G.inv s) n) s) := by
          rw [← heq]
          rw [← G.op_assoc s (G.op (G.inv s) n) s hs_G (op_mem G (inv_mem G hs_G) hn_G) hs_G,
              ← G.op_assoc s (G.inv s) n hs_G (inv_mem G hs_G) hn_G,
              (G.op_inv s hs_G).1,
              (G.op_id n hn_G).2]
        have hs_MH : s ∈ (M.inter H).carrier.elems := by
          rw [mem_inter_iff]; exact ⟨M.subset s hs_M, hs_M, hs_H⟩
        have hn'_KN : (G.op (G.op (G.inv s) n) s) ∈ (K.inter N).carrier.elems := by
          rw [mem_inter_iff]
          exact ⟨K.subset _ (inter_subset_right_aux N K _ hn'_NK),
                 inter_subset_right_aux N K _ hn'_NK,
                 inter_subset_left_aux N K _ hn'_NK⟩
        exact ⟨hxeq ▸ op_mem G hs_G (K.subset _ (inter_subset_right_aux N K _ hn'_NK)),
               s, hs_MH, G.op (G.op (G.inv s) n) s, hn'_KN, hxeq.symm⟩
      · intro ⟨hxG, m, hm_MH, k, hk_KN, heq⟩
        have hm_M  := inter_subset_left_aux M H m hm_MH
        have hm_H  := inter_subset_right_aux M H m hm_MH
        have hk_K  := inter_subset_left_aux K N k hk_KN
        have hk_N  := inter_subset_right_aux K N k hk_KN
        have hm_G  := M.subset m hm_M
        have hk_G  := K.subset k hk_K
        have hm_K  := hMK m hm_M
        -- k' = m*k*(inv m) ∈ K∩N por normalidad
        have hm_KH : m ∈ (K.inter H).carrier.elems := by
          rw [mem_inter_iff]; exact ⟨K.subset m hm_K, hm_K, hm_H⟩
        have hk'_KN := inter_H_M_normal_in_inter_H_K G K H N hNN m k hm_KH hk_KN
        -- k' = m * k * (inv m)
        have hk'_def : G.op (G.op m k) (G.inv m) ∈ (K.inter N).carrier.elems := hk'_KN
        -- x = k' * m
        have hxeq : x = G.op (G.op (G.op m k) (G.inv m)) m := by
          rw [← heq]
          rw [G.op_assoc (G.op m k) (G.inv m) m (op_mem G hm_G hk_G) (inv_mem G hm_G) hm_G,
              (G.op_inv m hm_G).2,
              (G.op_id (G.op m k) (op_mem G hm_G hk_G)).1]
        have hk'_NK : G.op (G.op m k) (G.inv m) ∈ (N.inter K).carrier.elems := by
          rw [mem_inter_iff]
          exact ⟨N.subset _ (inter_subset_right_aux K N _ hk'_KN),
                 inter_subset_right_aux K N _ hk'_KN,
                 inter_subset_left_aux K N _ hk'_KN⟩
        have hm_HM : m ∈ (H.inter M).carrier.elems := by
          rw [mem_inter_iff]; exact ⟨H.subset m hm_H, hm_H, hm_M⟩
        exact ⟨hxeq ▸ op_mem G (N.subset _ (inter_subset_right_aux K N _ hk'_KN)) hm_G,
               G.op (G.op m k) (G.inv m), hk'_NK, m, hm_HM, hxeq.symm⟩

    -- Lema auxiliar: los quotientCarriers intermedios (H∩K y K∩H) son iguales
    private theorem quotientCarrier_inter_eq
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        quotientCarrier
          (Subgroup.toFinGroup (H.inter K))
          (prodNKHM_in_HK G H K N M hNH hMK hNN hMM) =
        quotientCarrier
          (Subgroup.toFinGroup (K.inter H))
          (prodNKHM_in_HK G K H M N hMK hNH hMM hNN) := by
      -- Los carriers de (H∩K) y (K∩H) son iguales (como FSet ℕ₀)
      have hHK_car : (H.inter K).carrier.elems = (K.inter H).carrier.elems :=
        congrArg FSet.elems (congrArg Subgroup.carrier (inter_comm_lem H K))
      -- Los carriers del subgrupo son iguales
      have hprod_car : (prodNKHM_in_HK G H K N M hNH hMK hNN hMM).carrier.elems =
                       (prodNKHM_in_HK G K H M N hMK hNH hMM hNN).carrier.elems :=
        congrArg FSet.elems (prodNKHM_carrier_eq G H K N M hNH hMK hNN hMM)
      -- Probamos igualdad de FSet (FSet ℕ₀) por extensionalidad
      apply FSet.eq_of_mem_iff'
      intro C
      constructor
      · intro hC
        obtain ⟨g, hg, rfl⟩ := mem_quotientCarrier_is_leftCoset _ _ C hC
        have hg' : g ∈ (Subgroup.toFinGroup (K.inter H)).carrier.elems :=
          hHK_car ▸ hg
        have hleq : leftCoset (Subgroup.toFinGroup (H.inter K))
                      (prodNKHM_in_HK G H K N M hNH hMK hNN hMM) g =
                    leftCoset (Subgroup.toFinGroup (K.inter H))
                      (prodNKHM_in_HK G K H M N hMK hNH hMM hNN) g := by
          apply FSet.eq_of_mem_iff; intro z
          rw [mem_leftCoset_iff _ _ _ _ hg, mem_leftCoset_iff _ _ _ _ hg']
          constructor
          · rintro ⟨h, hh, heq⟩; exact ⟨h, hprod_car ▸ hh, heq⟩
          · rintro ⟨h, hh, heq⟩; exact ⟨h, hprod_car.symm ▸ hh, heq⟩
        rw [hleq]
        exact leftCoset_mem_quotientCarrier _ _ g hg'
      · intro hC
        obtain ⟨g, hg, rfl⟩ := mem_quotientCarrier_is_leftCoset _ _ C hC
        have hg' : g ∈ (Subgroup.toFinGroup (H.inter K)).carrier.elems :=
          hHK_car.symm ▸ hg
        have hleq : leftCoset (Subgroup.toFinGroup (K.inter H))
                      (prodNKHM_in_HK G K H M N hMK hNH hMM hNN) g =
                    leftCoset (Subgroup.toFinGroup (H.inter K))
                      (prodNKHM_in_HK G H K N M hNH hMK hNN hMM) g := by
          apply FSet.eq_of_mem_iff; intro z
          rw [mem_leftCoset_iff _ _ _ _ hg, mem_leftCoset_iff _ _ _ _ hg']
          constructor
          · rintro ⟨h, hh, heq⟩; exact ⟨h, hprod_car.symm ▸ hh, heq⟩
          · rintro ⟨h, hh, heq⟩; exact ⟨h, hprod_car ▸ hh, heq⟩
        rw [hleq]
        exact leftCoset_mem_quotientCarrier _ _ g hg'

    /-- Transporte de biyectividad a lo largo de igualdad del codominio.
        La variable `B` es libre en el enunciado, por lo que `subst heq` sí funciona
        (a diferencia del sitio de uso, donde `B` y `C` son términos concretos). -/
    private theorem mapOn_bijective_cast
        {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B C : FSet β} (f : MapOn A B) (h : f.Bijective) (heq : B = C) :
        (heq ▸ f).Bijective := by
      subst heq; exact h

    /-- **Lema de la Mariposa de Zassenhaus** (enunciado entre extremos):
        Existe una biyección `N(H∩K)/N(H∩M) ↔ M(K∩H)/M(K∩N)`.
        Se obtiene componiendo la inversa de `zassenhaus_bijection` con
        `zassenhaus_bijection_symm`, previa identificación de los cocientes intermedios
        `M(K∩H)/M(K∩N)↔ N(H∩K)/N(H∩M)` vía la transitividad de la equivalencia. -/
    theorem zassenhaus_bijection_extremes
        (G : FinGroup ℕ₀) (H K N M : Subgroup G)
        (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
        (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
        (hNK : ∀ a, a ∈ N.carrier.elems → a ∈ K.carrier.elems)
        (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
        (hNN : NormalIn G N H)
        (hMM : NormalIn G M K) :
        ∃ (f : MapOn
            (quotientCarrier
              (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN))
              (prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN))
            (quotientCarrier
              (Subgroup.toFinGroup (prodN_HK G K H M hMK hMM))
              (prodN_HM_in_prodN_HK G K H N M hMK hNK hNH hMM))),
            f.Bijective := by
      -- f₁ : (H∩K)/prodNKHM → prodN_HK(H,K)/prodN_HM  (enunciado principal)
      obtain ⟨f₁, hf₁⟩ := zassenhaus_bijection G H K N M hNH hMH hMK hNN hMM
      -- f₂ : (K∩H)/prodNKHM' → prodN_HK(K,H)/prodN_HM'  (enunciado simétrico)
      obtain ⟨f₂, hf₂⟩ := zassenhaus_bijection_symm G H K N M hNH hNK hMK hNN hMM
      -- Elemento por defecto para construir f₁⁻¹: el coseto identidad en el dominio de f₁
      let dflt := leftCoset (Subgroup.toFinGroup (H.inter K))
                    (prodNKHM_in_HK G H K N M hNH hMK hNN hMM)
                    (Subgroup.toFinGroup (H.inter K)).id
      have hdflt_mem : dflt ∈ (quotientCarrier
          (Subgroup.toFinGroup (H.inter K))
          (prodNKHM_in_HK G H K N M hNH hMK hNN hMM)).elems :=
        leftCoset_id_mem_quotientCarrier _ _
      let f₁_inv := f₁.inverse hf₁ dflt hdflt_mem
      -- Los quotientCarriers intermedios coinciden: (H∩K)/prodNKHM = (K∩H)/prodNKHM'
      have hquo_eq := quotientCarrier_inter_eq G H K N M hNH hMK hNN hMM
      -- Reindexamos f₁_inv con hquo_eq para que su codomain coincida con el dominio de f₂
      -- f₁_inv : MapOn (quotientCarrier prodN_HK prodN_HM) (quotientCarrier (H∩K) prodNKHM)
      -- hquo_eq : quotientCarrier (H∩K) prodNKHM = quotientCarrier (K∩H) prodNKHM'
      -- f₂ : MapOn (quotientCarrier (K∩H) prodNKHM') (quotientCarrier prodN_HK' prodN_HM')
      -- Calculamos la inversa de f₁ y su biyectividad
      have hbij_inv : f₁_inv.Bijective := f₁.inverse_bijective hf₁ dflt hdflt_mem
      -- Transportamos la biyectividad de f₁_inv a través de hquo_eq
      -- (usando mapOn_bijective_cast, donde subst funciona porque las variables son libres)
      -- y componemos: h = f₂ ∘ (hquo_eq ▸ f₁_inv) es la biyección deseada
      exact ⟨f₂.comp (hquo_eq ▸ f₁_inv),
             MapOn.comp_bijective (mapOn_bijective_cast f₁_inv hbij_inv hquo_eq) hf₂⟩

  end Zassenhaus
end Peano

export Peano.Zassenhaus (
  prodSubgroup
  mem_prodSubgroup_iff
  N_le_prodSubgroup
  S_le_prodSubgroup
  inter_N_K_normal_in_inter_H_K
  inter_H_M_normal_in_inter_H_K
  prodNKHM
  prodNKHM_normal
  prodN_HK
  prodN_HM
  prodN_HM_le_prodN_HK
  prodN_HM_normal_in_prodN_HK
  zassenhaus_bijection
  zassenhaus_bijection_symm
  zassenhaus_bijection_extremes
)
