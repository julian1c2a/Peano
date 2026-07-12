/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean
-- Subgrupos normales: centralizador, centro, normalizador y criterios de normalidad.
--
-- § 1. Centralizador C_G(S)
-- § 2. Centro Z(G)
-- § 3. Normalizador N_G(H)
-- § 4. Criterios equivalentes de normalidad

import Peano.PeanoNat
import Peano.PeanoNat.Mul
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets

set_option autoImplicit false

namespace Peano
  namespace NormalSubgroup

    open Peano.FSet
    open Peano.Group
    open Peano.Mul
    open Peano.Cosets

    /-!
    # § 1. Centralizador C_G(H)
    -/

    /-- El centralizador de `H` en `G`: los elementos de `G` que conmutan con todo
        elemento de `H`. El predicado es decidible porque `H.carrier` es finito. -/
    def centralizer (G : FinGroup ℕ₀) (H : Subgroup G) : Subgroup G where
      carrier := ℕ₀FSet.filter
        (fun g => H.carrier.elems.all (fun h => decide (G.op g h = G.op h g)))
        G.carrier
      nonempty := ⟨G.id, List.mem_filter.mpr ⟨G.id_in, by
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro h hh
        have hh_G := H.subset h hh
        rw [(G.op_id h hh_G).2, (G.op_id h hh_G).1]⟩⟩
      subset := fun a ha => (List.mem_filter.mp ha).1
      id_in := List.mem_filter.mpr ⟨G.id_in, by
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro h hh
        have hh_G := H.subset h hh
        rw [(G.op_id h hh_G).2, (G.op_id h hh_G).1]⟩
      op_closed := fun a b ha hb => by
        obtain ⟨ha_G, ha_all⟩ := List.mem_filter.mp ha
        obtain ⟨hb_G, hb_all⟩ := List.mem_filter.mp hb
        simp only [List.all_eq_true, decide_eq_true_eq] at ha_all hb_all
        refine List.mem_filter.mpr ⟨op_mem G ha_G hb_G, ?_⟩
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro h hh
        have hh_G := H.subset h hh
        have has := ha_all h hh
        have hbs := hb_all h hh
        calc G.op (G.op a b) h
            = G.op a (G.op b h) := G.op_assoc a b h ha_G hb_G hh_G
          _ = G.op a (G.op h b) := by rw [hbs]
          _ = G.op (G.op a h) b := (G.op_assoc a h b ha_G hh_G hb_G).symm
          _ = G.op (G.op h a) b := by rw [has]
          _ = G.op h (G.op a b) := G.op_assoc h a b hh_G ha_G hb_G
      inv_closed := fun a ha => by
        obtain ⟨ha_G, ha_all⟩ := List.mem_filter.mp ha
        simp only [List.all_eq_true, decide_eq_true_eq] at ha_all
        refine List.mem_filter.mpr ⟨inv_mem G ha_G, ?_⟩
        simp only [List.all_eq_true, decide_eq_true_eq]
        intro h hh
        have hh_G := H.subset h hh
        have ha' := inv_mem G ha_G
        have has := ha_all h hh
        -- a⁻¹·h = h·a⁻¹: cancelar multiplicando a por la izquierda
        apply op_cancel_left G ha_G (op_mem G ha' hh_G) (op_mem G hh_G ha')
        rw [← G.op_assoc a (G.inv a) h ha_G ha' hh_G,
            (G.op_inv a ha_G).1, (G.op_id h hh_G).2,
            ← G.op_assoc a h (G.inv a) ha_G hh_G ha',
            has, G.op_assoc h a (G.inv a) hh_G ha_G ha',
            (G.op_inv a ha_G).1, (G.op_id h hh_G).1]

    /-- `g ∈ C_G(H) ↔ g ∈ G ∧ ∀ h ∈ H, g·h = h·g`. -/
    theorem mem_centralizer_iff (G : FinGroup ℕ₀) (H : Subgroup G) (g : ℕ₀) :
        g ∈ (centralizer G H).carrier.elems ↔
          g ∈ G.carrier.elems ∧ ∀ h, h ∈ H.carrier.elems → G.op g h = G.op h g := by
      constructor
      · intro hg
        obtain ⟨hg_G, hg_all⟩ := List.mem_filter.mp hg
        simp only [List.all_eq_true, decide_eq_true_eq] at hg_all
        exact ⟨hg_G, hg_all⟩
      · rintro ⟨hg_G, hg_all⟩
        exact List.mem_filter.mpr ⟨hg_G, by
          simp only [List.all_eq_true, decide_eq_true_eq]
          exact hg_all⟩

    /-!
    # § 2. Centro Z(G)
    -/

    /-- El centro de `G`: los elementos que conmutan con todos los demás.
        Definido como centralizador del subgrupo impropio (= G). -/
    def center (G : FinGroup ℕ₀) : Subgroup G :=
      centralizer G (improperSubgroup G)

    /-- `g ∈ Z(G) ↔ ∀ x ∈ G, g·x = x·g`. -/
    theorem mem_center_iff (G : FinGroup ℕ₀) (g : ℕ₀) :
        g ∈ (center G).carrier.elems ↔
          g ∈ G.carrier.elems ∧ ∀ x, x ∈ G.carrier.elems → G.op g x = G.op x g :=
      mem_centralizer_iff G (improperSubgroup G) g

    /-- El centro es normal en `G`. -/
    theorem center_isNormal (G : FinGroup ℕ₀) : (center G).IsNormal := by
      intro g z hg hz
      obtain ⟨hz_G, hz_comm⟩ := (mem_center_iff G z).mp hz
      have hg' := inv_mem G hg
      -- g·z·g⁻¹: usar que z conmuta con g para obtener = z
      have heq : G.op (G.op g z) (G.inv g) = z := by
        rw [← hz_comm g hg, G.op_assoc z g (G.inv g) hz_G hg hg',
            (G.op_inv g hg).1, (G.op_id z hz_G).1]
      rw [heq]; exact hz

    /-- Si `H.carrier ⊆ Z(G)`, entonces `H` es normal. -/
    theorem central_subgroup_isNormal (G : FinGroup ℕ₀) (H : Subgroup G)
        (h_central : ∀ h, h ∈ H.carrier.elems → h ∈ (center G).carrier.elems) :
        H.IsNormal := by
      intro g n hg hn
      obtain ⟨hn_G, hn_comm⟩ := (mem_center_iff G n).mp (h_central n hn)
      have hg' := inv_mem G hg
      have heq : G.op (G.op g n) (G.inv g) = n := by
        rw [← hn_comm g hg, G.op_assoc n g (G.inv g) hn_G hg hg',
            (G.op_inv g hg).1, (G.op_id n hn_G).1]
      rw [heq]; exact hn

    /-!
    # § 3. Normalizador N_G(H)
    -/

    /-- El normalizador de `H` en `G`: los `g ∈ G` tales que `gHg⁻¹ = H`.
        Para evitar la prueba de sobreyectividad, usamos la condición simétrica:
        tanto `gHg⁻¹ ⊆ H` como `g⁻¹Hg ⊆ H`. -/
    def normalizer (G : FinGroup ℕ₀) (H : Subgroup G) : Subgroup G where
      carrier := ℕ₀FSet.filter
        (fun g => H.carrier.elems.all (fun h =>
          decide (G.op (G.op g h) (G.inv g) ∈ H.carrier) &&
          decide (G.op (G.op (G.inv g) h) g ∈ H.carrier)))
        G.carrier
      nonempty := ⟨G.id, List.mem_filter.mpr ⟨G.id_in, by
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        intro h hh
        have hh_G := H.subset h hh
        constructor
        · rw [inv_id_eq G, (G.op_id h hh_G).2, (G.op_id h hh_G).1]; exact hh
        · rw [inv_id_eq G, (G.op_id h hh_G).2, (G.op_id h hh_G).1]; exact hh⟩⟩
      subset := fun a ha => (List.mem_filter.mp ha).1
      id_in := List.mem_filter.mpr ⟨G.id_in, by
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        intro h hh
        have hh_G := H.subset h hh
        constructor
        · rw [inv_id_eq G, (G.op_id h hh_G).2, (G.op_id h hh_G).1]; exact hh
        · rw [inv_id_eq G, (G.op_id h hh_G).2, (G.op_id h hh_G).1]; exact hh⟩
      op_closed := fun a b ha hb => by
        obtain ⟨ha_G, ha_all⟩ := List.mem_filter.mp ha
        obtain ⟨hb_G, hb_all⟩ := List.mem_filter.mp hb
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha_all hb_all
        refine List.mem_filter.mpr ⟨op_mem G ha_G hb_G, ?_⟩
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        intro h hh
        have ha' := inv_mem G ha_G
        have hb' := inv_mem G hb_G
        have hh_G := H.subset h hh
        have hb_l := (hb_all h hh).1
        have ha_r := (ha_all h hh).2
        constructor
        · -- (ab)h(ab)⁻¹ = a(bhb⁻¹)a⁻¹ ∈ H
          have goal_mem := (ha_all (G.op (G.op b h) (G.inv b)) hb_l).1
          rw [inv_op_eq G ha_G hb_G,
              G.op_assoc a b h ha_G hb_G hh_G,
              G.op_assoc a (G.op b h) (G.op (G.inv b) (G.inv a))
                ha_G (op_mem G hb_G hh_G) (op_mem G hb' ha'),
              ← G.op_assoc (G.op b h) (G.inv b) (G.inv a)
                (op_mem G hb_G hh_G) hb' ha',
              ← G.op_assoc a (G.op (G.op b h) (G.inv b)) (G.inv a)
                ha_G (op_mem G (op_mem G hb_G hh_G) hb') ha']
          exact goal_mem
        · -- (ab)⁻¹h(ab) = b⁻¹(a⁻¹ha)b ∈ H
          have goal_mem := (hb_all (G.op (G.op (G.inv a) h) a) ha_r).2
          rw [inv_op_eq G ha_G hb_G,
              G.op_assoc (G.inv b) (G.inv a) h hb' ha' hh_G,
              G.op_assoc (G.inv b) (G.op (G.inv a) h) (G.op a b)
                hb' (op_mem G ha' hh_G) (op_mem G ha_G hb_G),
              ← G.op_assoc (G.op (G.inv a) h) a b
                (op_mem G ha' hh_G) ha_G hb_G,
              ← G.op_assoc (G.inv b) (G.op (G.op (G.inv a) h) a) b
                hb' (op_mem G (op_mem G ha' hh_G) ha_G) hb_G]
          exact goal_mem
      inv_closed := fun a ha => by
        obtain ⟨ha_G, ha_all⟩ := List.mem_filter.mp ha
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha_all
        refine List.mem_filter.mpr ⟨inv_mem G ha_G, ?_⟩
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        intro h hh
        rw [inv_inv_eq G ha_G]
        exact ⟨(ha_all h hh).2, (ha_all h hh).1⟩

    /-- `g ∈ N_G(H) ↔ g ∈ G ∧ (∀ h ∈ H, ghg⁻¹ ∈ H) ∧ (∀ h ∈ H, g⁻¹hg ∈ H)`. -/
    theorem mem_normalizer_iff (G : FinGroup ℕ₀) (H : Subgroup G) (g : ℕ₀) :
        g ∈ (normalizer G H).carrier.elems ↔
          g ∈ G.carrier.elems ∧
          (∀ h, h ∈ H.carrier.elems → G.op (G.op g h) (G.inv g) ∈ H.carrier.elems) ∧
          (∀ h, h ∈ H.carrier.elems → G.op (G.op (G.inv g) h) g ∈ H.carrier.elems) := by
      constructor
      · intro hg
        obtain ⟨hg_G, hg_all⟩ := List.mem_filter.mp hg
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hg_all
        exact ⟨hg_G, fun h hh => (hg_all h hh).1, fun h hh => (hg_all h hh).2⟩
      · rintro ⟨hg_G, hl, hr⟩
        refine List.mem_filter.mpr ⟨hg_G, ?_⟩
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact fun h hh => ⟨hl h hh, hr h hh⟩

    /-- `H ⊆ N_G(H)`: el subgrupo está contenido en su propio normalizador. -/
    theorem H_subset_normalizer (G : FinGroup ℕ₀) (H : Subgroup G) :
        ∀ h, h ∈ H.carrier.elems → h ∈ (normalizer G H).carrier.elems := by
      intro h hh
      rw [mem_normalizer_iff]
      refine ⟨H.subset h hh, fun k hk => ?_, fun k hk => ?_⟩
      · -- hkh⁻¹ ∈ H: H.op_closed + H.inv_closed
        exact H.op_closed _ _ (H.op_closed _ _ hh hk) (H.inv_closed _ hh)
      · exact H.op_closed _ _ (H.op_closed _ _ (H.inv_closed _ hh) hk) hh

    /-- `H` es normal en `G` sii `N_G(H) = G`. -/
    theorem isNormal_iff_normalizer_eq_G (G : FinGroup ℕ₀) (H : Subgroup G) :
        H.IsNormal ↔ (normalizer G H).carrier = G.carrier := by
      constructor
      · intro hn
        apply FSet.eq_of_mem_iff
        intro g
        constructor
        · exact (normalizer G H).subset g
        · intro hg
          rw [mem_normalizer_iff]
          exact ⟨hg, fun h hh => hn g h hg hh,
            fun h hh => by
              have hg' := inv_mem G hg
              have := hn (G.inv g) h hg' hh
              rwa [inv_inv_eq G hg] at this⟩
      · intro heq g n hg hn
        have hg_norm : g ∈ (normalizer G H).carrier.elems := by
          rw [heq]; exact hg
        exact ((mem_normalizer_iff G H g).mp hg_norm).2.1 n hn

    /-!
    # § 4. Criterios equivalentes de normalidad
    -/

    /-- Coseto derecho `Hg = { h·g | h ∈ H }`. -/
    def rightCoset (G : FinGroup ℕ₀) (H : Subgroup G) (g : ℕ₀) : ℕ₀FSet :=
      ℕ₀FSet.filter
        (fun x => H.carrier.elems.any (fun h => decide (G.op h g = x)))
        G.carrier

    theorem mem_rightCoset_iff (G : FinGroup ℕ₀) (H : Subgroup G) (g x : ℕ₀)
        (hg : g ∈ G.carrier.elems) :
        x ∈ (rightCoset G H g).elems ↔ ∃ h, h ∈ H.carrier.elems ∧ G.op h g = x := by
      constructor
      · intro hx
        obtain ⟨_, hall⟩ := List.mem_filter.mp hx
        rw [List.any_eq_true] at hall
        obtain ⟨h, hh, hd⟩ := hall
        exact ⟨h, hh, by rwa [decide_eq_true_eq] at hd⟩
      · rintro ⟨h, hh, heq⟩
        exact List.mem_filter.mpr
          ⟨heq ▸ op_mem G (H.subset h hh) hg,
           List.any_eq_true.mpr ⟨h, hh, decide_eq_true_eq.mpr heq⟩⟩

    /-- `H` es normal en `G` sii todo coseto izquierdo es igual al coseto derecho:
        `gH = Hg` para todo `g ∈ G`. -/
    theorem isNormal_iff_leftCoset_eq_rightCoset (G : FinGroup ℕ₀) (H : Subgroup G) :
        H.IsNormal ↔
        ∀ g, g ∈ G.carrier.elems → leftCoset G H g = rightCoset G H g := by
      constructor
      · intro hn g hg
        apply FSet.eq_of_mem_iff
        intro x
        constructor
        · -- x ∈ gH → x ∈ Hg
          intro hx
          obtain ⟨h, hh, heq⟩ := (mem_leftCoset_iff G H g x hg).mp hx
          -- x = gh, want x = h'g for some h' ∈ H
          -- h' = ghg⁻¹·g... wait: x = gh, so x·g⁻¹ = ghg⁻¹ ∈ H
          -- Then x = (ghg⁻¹)·g, and ghg⁻¹ ∈ H by hn
          have hconj := hn g h hg hh
          refine (mem_rightCoset_iff G H g x hg).mpr ⟨G.op (G.op g h) (G.inv g), hconj, ?_⟩
          have hh_G := H.subset h hh
          have hg' := inv_mem G hg
          rw [G.op_assoc (G.op g h) (G.inv g) g (op_mem G hg hh_G) hg' hg,
              (G.op_inv g hg).2, (G.op_id (G.op g h) (op_mem G hg hh_G)).1,
              ← heq]
        · -- x ∈ Hg → x ∈ gH
          intro hx
          obtain ⟨h, hh, heq⟩ := (mem_rightCoset_iff G H g x hg).mp hx
          -- x = hg, want x = gh' for some h' ∈ H
          -- g⁻¹hg ∈ H by hn applied to g⁻¹
          have hg' := inv_mem G hg
          -- g⁻¹hg ∈ H: hn (G.inv g) h gives G.op (G.op (G.inv g) h) (G.inv (G.inv g)) ∈ H
          -- rw inv_inv to get G.op (G.op (G.inv g) h) g ∈ H
          have hconj : G.op (G.op (G.inv g) h) g ∈ H.carrier.elems := by
            have := hn (G.inv g) h hg' hh
            rwa [inv_inv_eq G hg] at this
          have hh_G := H.subset h hh
          -- h' = G.op (G.op (G.inv g) h) g, then g·h' = g·(g⁻¹·h·g) = h·g = x
          refine (mem_leftCoset_iff G H g x hg).mpr
            ⟨G.op (G.op (G.inv g) h) g, hconj, ?_⟩
          rw [← G.op_assoc g (G.op (G.inv g) h) g hg (op_mem G hg' hh_G) hg,
              ← G.op_assoc g (G.inv g) h hg hg' hh_G,
              (G.op_inv g hg).1, (G.op_id h hh_G).2,
              heq]
      · intro h_eq g n hg hn
        -- g·n·g⁻¹ ∈ H: it suffices to show it's in gH ∩ Hg, but gH = Hg
        -- g·n ∈ gH (trivially), and by assumption gH = Hg
        -- so g·n = h·g for some h ∈ H, giving g·n·g⁻¹ = h ∈ H
        have hg' := inv_mem G hg
        have hn_G := H.subset n hn
        have hgn_in_lc : G.op g n ∈ (leftCoset G H g).elems :=
          (mem_leftCoset_iff G H g (G.op g n) hg).mpr ⟨n, hn, rfl⟩
        rw [h_eq g hg] at hgn_in_lc
        obtain ⟨h, hh, heq⟩ := (mem_rightCoset_iff G H g (G.op g n) hg).mp hgn_in_lc
        -- heq : G.op h g = G.op g n
        -- Then g·n·g⁻¹ = h·g·g⁻¹ = h ∈ H
        have : G.op (G.op g n) (G.inv g) = h := by
          rw [← heq, G.op_assoc h g (G.inv g) (H.subset h hh) hg hg',
              (G.op_inv g hg).1, (G.op_id h (H.subset h hh)).1]
        rw [this]; exact hh

  end NormalSubgroup
end Peano

export Peano.NormalSubgroup (
  centralizer
  mem_centralizer_iff
  center
  mem_center_iff
  center_isNormal
  central_subgroup_isNormal
  normalizer
  mem_normalizer_iff
  H_subset_normalizer
  isNormal_iff_normalizer_eq_G
  rightCoset
  mem_rightCoset_iff
  isNormal_iff_leftCoset_eq_rightCoset
)
