/-
  CorrespondenceTheorem.lean
  ==========================
  Teorema de Correspondencia (Cuarto Teorema de Isomorfismo)

  Sea G un grupo finito y N un subgrupo normal de G. Entonces existe una
  biyección entre:
    • El conjunto de subgrupos de G que contienen a N
    • El conjunto de todos los subgrupos del grupo cociente G/N

  La biyección viene dada por:
    φ(K) = imageSubgroup G N hn K hNK   (imagen de K en G/N bajo π : G → G/N)
    ψ(Q) = preimageSubgroup G N hn Q    (preimagen de Q ≤ G/N bajo π)

  Contenido:
    § 0. Extensionalidad genérica de FSet (sorted_list_unique, FSet_eq_of_mem_iff)
    § 1. Extensionalidad de Subgroup (subgroup_ext')
    § 2. Auxiliar de inversas en cociente (leftCoset_inv_eq)
    § 3. Definición de preimageSubgroup
    § 4. Caracterización de membresía (mem_preimageSubgroup_iff)
    § 5. N ≤ ψ(Q) para todo Q ≤ G/N
    § 6. Caracterización de membresía de imageSubgroup
    § 7. φ(ψ(Q)) = Q
    § 8. ψ(φ(K)) = K (cuando N ≤ K)
    § 9. SubgroupAbove y la biyección formal
-/
import Peano.PeanoNat.Combinatorics.GroupTheory.QuotientGroup

set_option autoImplicit false

namespace Peano
  namespace CorrespondenceTheorem

    open Peano.FSet Peano.FSetFunction Peano.Group Peano.Cosets Peano.QuotientGroup

    /-======================================================================
      § 0. Extensionalidad genérica de FSet
      Reproducimos la lógica de `sorted_nodup_unique_list` (privada en FSet.lean)
      de forma genérica sobre cualquier `StrictLinearOrder α`.
    ======================================================================-/

    private theorem sorted_list_unique {α : Type} [DecidableEq α] [LT α]
        [slo : StrictLinearOrder α] :
        ∀ {l₁ l₂ : List α},
        List.Pairwise (· < ·) l₁ → List.Pairwise (· < ·) l₂ →
        (∀ z : α, z ∈ l₁ ↔ z ∈ l₂) → l₁ = l₂
      | [], [], _, _, _ => rfl
      | [], y :: ys, _, _, hmem =>
          absurd ((hmem y).mpr List.mem_cons_self) List.not_mem_nil
      | x :: xs, [], _, _, hmem =>
          absurd ((hmem x).mp List.mem_cons_self) List.not_mem_nil
      | x :: xs, y :: ys, hs₁, hs₂, hmem =>
          have hxs₁ := List.pairwise_cons.mp hs₁
          have hxs₂ := List.pairwise_cons.mp hs₂
          have hxy : x = y := by
            have hx_in : x ∈ y :: ys := (hmem x).mp List.mem_cons_self
            have hy_in : y ∈ x :: xs := (hmem y).mpr List.mem_cons_self
            rcases List.mem_cons.mp hx_in with rfl | hx_ys
            · rfl
            · rcases List.mem_cons.mp hy_in with rfl | hy_xs
              · rfl
              · exact absurd
                    (slo.trans (List.rel_of_pairwise_cons hs₁ hy_xs)
                               (List.rel_of_pairwise_cons hs₂ hx_ys))
                    (slo.irrefl x)
          have htail : xs = ys := by
            apply sorted_list_unique hxs₁.2 hxs₂.2
            intro z
            constructor
            · intro hz
              have hzy := (hmem z).mp (List.mem_cons.mpr (Or.inr hz))
              rcases List.mem_cons.mp hzy with h_eq | h
              · have h_lt : x < z := List.rel_of_pairwise_cons hs₁ hz
                rw [h_eq, ← hxy] at h_lt
                exact absurd h_lt (slo.irrefl x)
              · exact h
            · intro hz
              have hzx := (hmem z).mpr (List.mem_cons.mpr (Or.inr hz))
              rcases List.mem_cons.mp hzx with h_eq | h
              · have h_lt : y < z := List.rel_of_pairwise_cons hs₂ hz
                rw [h_eq, hxy] at h_lt
                exact absurd h_lt (slo.irrefl y)
              · exact h
          Eq.trans (congrArg (List.cons x) htail) (congrArg (· :: ys) hxy)

    /-- Extensionalidad de `FSet α` por membresía (versión genérica). -/
    private theorem FSet_eq_of_mem_iff {α : Type} [DecidableEq α] [LT α]
        [StrictLinearOrder α] {s₁ s₂ : FSet α}
        (h : ∀ z : α, z ∈ s₁.elems ↔ z ∈ s₂.elems) : s₁ = s₂ :=
      FSet.ext (sorted_list_unique s₁.sorted s₂.sorted h)

    /-======================================================================
      § 1. Extensionalidad de Subgroup
    ======================================================================-/

    /-- Dos subgrupos de G son iguales si y solo si tienen el mismo portador. -/
    private theorem subgroup_ext' {G : FinGroup ℕ₀} {H K : Subgroup G}
        (h : H.carrier = K.carrier) : H = K := by
      cases H; cases K; simp only [] at h; subst h; rfl

    /-- Versión por membresía: dos subgrupos de G con la misma membresía son iguales. -/
    private theorem subgroup_ext_mem {G : FinGroup ℕ₀} {H K : Subgroup G}
        (h : ∀ a, a ∈ H.carrier.elems ↔ a ∈ K.carrier.elems) : H = K :=
      subgroup_ext' (FSet.eq_of_mem_iff h)

    /-- Extensionalidad de subgrupos del grupo cociente. -/
    private theorem qsubgroup_ext' {G : FinGroup ℕ₀} {N : Subgroup G} {hn : N.IsNormal}
        {H K : Subgroup (quotientGroup G N hn)}
        (h : H.carrier = K.carrier) : H = K := by
      cases H; cases K; simp only [] at h; subst h; rfl

    /-- Versión por membresía para subgrupos del cociente. -/
    private theorem qsubgroup_ext_mem {G : FinGroup ℕ₀} {N : Subgroup G} {hn : N.IsNormal}
        {H K : Subgroup (quotientGroup G N hn)}
        (h : ∀ C, C ∈ H.carrier.elems ↔ C ∈ K.carrier.elems) : H = K :=
      qsubgroup_ext' (FSet_eq_of_mem_iff h)

    /-======================================================================
      § 2. Auxiliar: leftCoset G N (G.inv b) = (quotientGroup G N hn).inv (leftCoset G N b)
      Este lema no aparece explícitamente en QuotientGroup.lean pero
      se deduce del mismo argumento usado en imageSubgroup.inv_closed.
    ======================================================================-/

    private theorem leftCoset_inv_eq (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (b : ℕ₀) (hb : b ∈ G.carrier.elems) :
        leftCoset G N (G.inv b) = (quotientGroup G N hn).inv (leftCoset G N b) := by
      simp only [quotientGroup, quotientInv]
      apply leftCoset_eq_of_rel G N _ _
        (inv_mem G hb)
        (inv_mem G (cosetRepOf_mem_G G N _ (leftCoset_mem_quotientCarrier G N b hb)))
      -- cosetRel G N (G.inv b) (G.inv (cosetRepOf G N (leftCoset G N b)))
      let r := cosetRepOf G N (leftCoset G N b)
      have hr_G : r ∈ G.carrier.elems :=
        cosetRepOf_mem_G G N _ (leftCoset_mem_quotientCarrier G N b hb)
      have hrel : G.op (G.inv r) b ∈ N.carrier.elems :=
        cosetRel_of_leftCoset_eq G N r b hr_G hb
          (cosetRepOf_leftCoset_eq G N _ (leftCoset_mem_quotientCarrier G N b hb))
      have h_conj := hn b (G.op (G.inv r) b) hb hrel
      have h_simp : G.op (G.op b (G.op (G.inv r) b)) (G.inv b) = G.op b (G.inv r) := by
        have hr' := inv_mem G hr_G
        rw [G.op_assoc b (G.op (G.inv r) b) (G.inv b) hb (op_mem G hr' hb) (inv_mem G hb),
            G.op_assoc (G.inv r) b (G.inv b) hr' hb (inv_mem G hb),
            (G.op_inv b hb).1, (G.op_id (G.inv r) hr').1]
      unfold cosetRel
      rw [inv_inv_eq G hb]
      exact h_simp ▸ h_conj

    /-======================================================================
      § 3. Definición de preimageSubgroup
      ψ(Q) = {g ∈ G | π(g) ∈ Q} donde π(g) = leftCoset G N g
    ======================================================================-/

    /-- Preimagen de un subgrupo `Q ≤ G/N` bajo el homomorfismo canónico
        `π : G → G/N`, `g ↦ gN`. -/
    noncomputable def preimageSubgroup (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (Q : Subgroup (quotientGroup G N hn)) : Subgroup G where
      carrier :=
        ℕ₀FSet.filter (fun g => decide (leftCoset G N g ∈ Q.carrier.elems)) G.carrier
      nonempty := ⟨G.id, List.mem_filter.mpr ⟨G.id_in, by
          rw [decide_eq_true_eq]
          -- leftCoset G N G.id = (quotientGroup G N hn).id ∈ Q
          have hqid : leftCoset G N G.id = (quotientGroup G N hn).id := rfl
          rw [hqid]; exact Q.id_in⟩⟩
      subset := fun a ha => (List.mem_filter.mp ha).1
      op_closed := fun a b ha hb => by
        obtain ⟨ha_G, ha_bool⟩ := List.mem_filter.mp ha
        obtain ⟨hb_G, hb_bool⟩ := List.mem_filter.mp hb
        rw [decide_eq_true_eq] at ha_bool hb_bool
        refine List.mem_filter.mpr ⟨op_mem G ha_G hb_G, ?_⟩
        rw [decide_eq_true_eq]
        -- leftCoset G N (G.op a b) = (quotientGroup G N hn).op (leftCoset G N a) (leftCoset G N b)
        have hop_eq : leftCoset G N (G.op a b) =
            (quotientGroup G N hn).op (leftCoset G N a) (leftCoset G N b) :=
          quotientHomomorphism_op G N hn a b ha_G hb_G
        rw [hop_eq]
        exact Q.op_closed _ _ ha_bool hb_bool
      id_in := List.mem_filter.mpr ⟨G.id_in, by
          rw [decide_eq_true_eq]
          have hqid : leftCoset G N G.id = (quotientGroup G N hn).id := rfl
          rw [hqid]; exact Q.id_in⟩
      inv_closed := fun a ha => by
        obtain ⟨ha_G, ha_bool⟩ := List.mem_filter.mp ha
        rw [decide_eq_true_eq] at ha_bool
        refine List.mem_filter.mpr ⟨inv_mem G ha_G, ?_⟩
        rw [decide_eq_true_eq]
        -- leftCoset G N (G.inv a) = (quotientGroup G N hn).inv (leftCoset G N a)
        rw [leftCoset_inv_eq G N hn a ha_G]
        exact Q.inv_closed _ ha_bool

    /-======================================================================
      § 4. Caracterización de membresía de preimageSubgroup
    ======================================================================-/

    theorem mem_preimageSubgroup_iff (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (Q : Subgroup (quotientGroup G N hn)) (g : ℕ₀) :
        g ∈ (preimageSubgroup G N hn Q).carrier.elems ↔
        g ∈ G.carrier.elems ∧ leftCoset G N g ∈ Q.carrier.elems := by
      simp only [preimageSubgroup]
      constructor
      · intro hg
        obtain ⟨hg_G, hg_bool⟩ := List.mem_filter.mp hg
        exact ⟨hg_G, decide_eq_true_eq.mp hg_bool⟩
      · intro ⟨hg_G, hg_Q⟩
        exact List.mem_filter.mpr ⟨hg_G, decide_eq_true_eq.mpr hg_Q⟩

    /-======================================================================
      § 5. N ≤ ψ(Q) para todo Q ≤ G/N
    ======================================================================-/

    theorem N_le_preimageSubgroup (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (Q : Subgroup (quotientGroup G N hn)) :
        ∀ n, n ∈ N.carrier.elems → n ∈ (preimageSubgroup G N hn Q).carrier.elems := by
      intro n hn_N
      rw [mem_preimageSubgroup_iff]
      refine ⟨N.subset n hn_N, ?_⟩
      -- leftCoset G N n = (quotientGroup G N hn).id ∈ Q
      have hkey : leftCoset G N n = (quotientGroup G N hn).id :=
        (quotientHomomorphism_kernel G N hn n (N.subset n hn_N)).mpr hn_N
      rw [hkey]
      exact Q.id_in

    /-======================================================================
      § 6. Caracterización de membresía de imageSubgroup
    ======================================================================-/

    private theorem mem_imageSubgroup_iff (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (K : Subgroup G) (hNK : ∀ h, h ∈ N.carrier.elems → h ∈ K.carrier.elems)
        (C : ℕ₀FSet) :
        C ∈ (imageSubgroup G N hn K hNK).carrier.elems ↔
        ∃ k, k ∈ K.carrier.elems ∧ leftCoset G N k = C := by
      simp only [imageSubgroup, mem_sortFSetList_iff, List.mem_map]

    /-======================================================================
      § 7. φ(ψ(Q)) = Q
    ======================================================================-/

    /-- La imagen de la preimagen es el subgrupo original: φ(ψ(Q)) = Q. -/
    theorem imageSubgroup_preimage (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (Q : Subgroup (quotientGroup G N hn)) :
        imageSubgroup G N hn (preimageSubgroup G N hn Q)
          (N_le_preimageSubgroup G N hn Q) = Q := by
      apply qsubgroup_ext_mem
      intro C
      rw [mem_imageSubgroup_iff G N hn (preimageSubgroup G N hn Q)
            (N_le_preimageSubgroup G N hn Q)]
      constructor
      · -- ∃ g ∈ ψ(Q), leftCoset G N g = C → C ∈ Q
        rintro ⟨g, hg_psi, rfl⟩
        rw [mem_preimageSubgroup_iff] at hg_psi
        exact hg_psi.2
      · -- C ∈ Q → ∃ g ∈ ψ(Q), leftCoset G N g = C
        intro hC_Q
        have hC_car : C ∈ (quotientGroup G N hn).carrier.elems :=
          Q.subset C hC_Q
        -- Tomar g = cosetRepOf G N C
        let g := cosetRepOf G N C
        have hg_G : g ∈ G.carrier.elems := cosetRepOf_mem_G G N C hC_car
        have hg_lc : leftCoset G N g = C :=
          cosetRepOf_leftCoset_eq G N C hC_car
        refine ⟨g, ?_, hg_lc⟩
        rw [mem_preimageSubgroup_iff]
        exact ⟨hg_G, hg_lc ▸ hC_Q⟩

    /-======================================================================
      § 8. ψ(φ(K)) = K (cuando N ≤ K)
    ======================================================================-/

    /-- La preimagen de la imagen es el subgrupo original: ψ(φ(K)) = K. -/
    theorem preimageSubgroup_image (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (K : Subgroup G) (hNK : ∀ h, h ∈ N.carrier.elems → h ∈ K.carrier.elems) :
        preimageSubgroup G N hn (imageSubgroup G N hn K hNK) = K := by
      apply subgroup_ext_mem
      intro g
      rw [mem_preimageSubgroup_iff]
      constructor
      · -- g ∈ ψ(φ(K)) → g ∈ K
        rintro ⟨hg_G, hg_phi⟩
        rw [mem_imageSubgroup_iff G N hn K hNK] at hg_phi
        obtain ⟨k, hk_K, hk_lc⟩ := hg_phi
        -- hk_lc : leftCoset G N k = leftCoset G N g
        -- Luego cosetRel G N g k: G.op (G.inv g) k ∈ N
        have hk_G : k ∈ G.carrier.elems := K.subset k hk_K
        have hcoset_eq : leftCoset G N g = leftCoset G N k := hk_lc.symm
        have hrel : G.op (G.inv g) k ∈ N.carrier.elems :=
          cosetRel_of_leftCoset_eq G N g k hg_G hk_G hcoset_eq
        -- n = G.op (G.inv g) k ∈ N ≤ K
        let n := G.op (G.inv g) k
        have hn_K : n ∈ K.carrier.elems := hNK n hrel
        -- G.inv n = G.op (G.inv k) g (por inv_op_eq + inv_inv_eq)
        have hginv_n : G.inv n = G.op (G.inv k) g := by
          simp only [n, inv_op_eq G (inv_mem G hg_G) hk_G, inv_inv_eq G hg_G]
        -- g = G.op k (G.inv n) = K.op k (K.inv n) ∈ K
        have hg_eq : g = G.op k (G.inv n) := by
          rw [hginv_n,
              ← G.op_assoc k (G.inv k) g hk_G (inv_mem G hk_G) hg_G,
              (G.op_inv k hk_G).1, (G.op_id g hg_G).2]
        rw [hg_eq]
        exact K.op_closed k (G.inv n) hk_K (K.inv_closed n hn_K)
      · -- g ∈ K → g ∈ ψ(φ(K))
        intro hg_K
        refine ⟨K.subset g hg_K, ?_⟩
        rw [mem_imageSubgroup_iff G N hn K hNK]
        exact ⟨g, hg_K, rfl⟩

    /-======================================================================
      § 9. SubgroupAbove y la biyección formal
    ======================================================================-/

    /-- Subtipo de subgrupos de G que contienen a N. -/
    def SubgroupAbove (G : FinGroup ℕ₀) (N : Subgroup G) (_hn : N.IsNormal) : Type :=
      { K : Subgroup G // ∀ h, h ∈ N.carrier.elems → h ∈ K.carrier.elems }

    /-- φ: subgrupo de G conteniendo N → subgrupo de G/N -/
    noncomputable def correspondencePhi (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal) :
        SubgroupAbove G N hn → Subgroup (quotientGroup G N hn) :=
      fun ⟨K, hNK⟩ => imageSubgroup G N hn K hNK

    /-- ψ: subgrupo de G/N → subgrupo de G conteniendo N -/
    noncomputable def correspondencePsi (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal) :
        Subgroup (quotientGroup G N hn) → SubgroupAbove G N hn :=
      fun Q => ⟨preimageSubgroup G N hn Q, N_le_preimageSubgroup G N hn Q⟩

    /-- φ ∘ ψ = id: la imagen de la preimagen es el subgrupo original. -/
    theorem correspondencePhi_psi (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (Q : Subgroup (quotientGroup G N hn)) :
        correspondencePhi G N hn (correspondencePsi G N hn Q) = Q :=
      imageSubgroup_preimage G N hn Q

    /-- ψ ∘ φ = id: la preimagen de la imagen es el subgrupo original. -/
    theorem correspondencePsi_phi (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (K : SubgroupAbove G N hn) :
        correspondencePsi G N hn (correspondencePhi G N hn K) = K := by
      obtain ⟨Kval, hNK⟩ := K
      simp only [correspondencePsi, correspondencePhi]
      exact Subtype.ext (preimageSubgroup_image G N hn Kval hNK)

    /-- El teorema de correspondencia: φ es inyectiva. -/
    theorem correspondenceInjective (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal) :
        ∀ K₁ K₂ : SubgroupAbove G N hn,
        correspondencePhi G N hn K₁ = correspondencePhi G N hn K₂ → K₁ = K₂ := by
      intro K₁ K₂ h
      have h_eq := congrArg (correspondencePsi G N hn) h
      rw [correspondencePsi_phi, correspondencePsi_phi] at h_eq
      exact h_eq

    /-- El teorema de correspondencia: φ es sobreyectiva. -/
    theorem correspondenceSurjective (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal) :
        ∀ Q : Subgroup (quotientGroup G N hn), ∃ K : SubgroupAbove G N hn,
        correspondencePhi G N hn K = Q := by
      intro Q
      exact ⟨correspondencePsi G N hn Q, correspondencePhi_psi G N hn Q⟩

    /-!
    # § 10. Cardinalidad de preimageSubgroup
    -/

    /-- La preimagen de `Q ≤ G/N` tiene cardinalidad `|Q| · |N|`. -/
    theorem preimage_subgroup_card (G : FinGroup ℕ₀) (N : Subgroup G) (hn : N.IsNormal)
        (Q : Subgroup (quotientGroup G N hn)) :
        (preimageSubgroup G N hn Q).carrier.card =
          Mul.mul Q.carrier.card N.carrier.card := by
      let ψQ := preimageSubgroup G N hn Q
      let QG := quotientGroup G N hn
      let f : MapOn ψQ.carrier Q.carrier := {
        toFun := fun g => leftCoset G N g
        map_carrier := fun g hg => ((mem_preimageSubgroup_iff G N hn Q g).mp hg).2
      }
      have h_uniform : ∀ C, C ∈ Q.carrier.elems →
          (f.fiber C).card = N.carrier.card := by
        intro C hC
        have hC_QG : C ∈ QG.carrier.elems := Q.subset C hC
        let r := cosetRepOf G N C
        have hr_G : r ∈ G.carrier.elems := cosetRepOf_mem_G G N C hC_QG
        have hr_lc : leftCoset G N r = C := cosetRepOf_leftCoset_eq G N C hC_QG
        have h_eq : f.fiber C = leftCoset G N r := by
          apply FSet.eq_of_mem_iff'
          intro x
          constructor
          · intro hx
            obtain ⟨hx_ψ, hx_map⟩ := (MapOn.mem_fiber_iff f C x).mp hx
            have hx_G : x ∈ G.carrier.elems := ψQ.subset x hx_ψ
            have hlc : leftCoset G N x = leftCoset G N r := by
              have h1 : leftCoset G N x = C := hx_map
              exact h1.trans hr_lc.symm
            exact (mem_leftCoset_iff G N r x hr_G).mpr
              ⟨G.op (G.inv r) x,
               cosetRel_symm G N x r hx_G hr_G
                 (cosetRel_of_leftCoset_eq G N x r hx_G hr_G hlc),
               by rw [← G.op_assoc r (G.inv r) x hr_G (inv_mem G hr_G) hx_G,
                      (G.op_inv r hr_G).1, (G.op_id x hx_G).2]⟩
          · intro hx_coset
            obtain ⟨n, hn_N, hn_eq⟩ := (mem_leftCoset_iff G N r x hr_G).mp hx_coset
            have hx_G : x ∈ G.carrier.elems := by
              rw [← hn_eq]; exact op_mem G hr_G (N.subset n hn_N)
            have hrel_rx : cosetRel G N r x := by
              unfold cosetRel
              rw [← hn_eq,
                  ← G.op_assoc (G.inv r) r n (inv_mem G hr_G) hr_G (N.subset n hn_N),
                  (G.op_inv r hr_G).2, (G.op_id n (N.subset n hn_N)).2]
              exact hn_N
            have hlc_eq : leftCoset G N x = C :=
              (leftCoset_eq_of_rel G N r x hr_G hx_G hrel_rx).symm.trans hr_lc
            exact (MapOn.mem_fiber_iff f C x).mpr
              ⟨(mem_preimageSubgroup_iff G N hn Q x).mpr
                 ⟨hx_G, by rw [hlc_eq]; exact hC⟩,
               hlc_eq⟩
        rw [h_eq]
        exact coset_card_eq_subgroup_card G N r hr_G
      have h_card := card_eq_mul_of_uniform_fibers f N.carrier.card h_uniform
      rw [h_card, mul_comm]

  end CorrespondenceTheorem
end Peano

export Peano.CorrespondenceTheorem (
  preimageSubgroup
  mem_preimageSubgroup_iff
  N_le_preimageSubgroup
  imageSubgroup_preimage
  preimageSubgroup_image
  SubgroupAbove
  correspondencePhi
  correspondencePsi
  correspondencePhi_psi
  correspondencePsi_phi
  correspondenceInjective
  correspondenceSurjective
  preimage_subgroup_card
)
