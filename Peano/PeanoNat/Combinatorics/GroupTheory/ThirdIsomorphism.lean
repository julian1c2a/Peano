import Peano.PeanoNat.Combinatorics.GroupTheory.QuotientGroup

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Tercer Teorema de Isomorfía

Sean `G` un grupo finito y `N, K` subgrupos normales de `G` con `N ≤ K`.
Este módulo construye el homomorfismo canónico sobreyectivo `φ : G/N → G/K`,
definido por `φ(gN) = gK`, y demuestra que su núcleo es exactamente `K/N`.

De ello se deduce el **Tercer Teorema de Isomorfía**: `(G/N) / (K/N) ≅ G/K`.

## Contenido

- § 0. Lemas auxiliares (`cosetRel_N_imp_K`, `cosetRel_inv_of_normal`)
- § 1. `K/N` es normal en `G/N` (`KmodN_normal`)
- § 2. Mapa canónico `φ` (`thirdIsoMap`)
- § 3. `φ` es homomorfismo de grupos (`thirdIsoMap_op`, `thirdIsoMap_id`,
       `thirdIsoMap_inv`, `thirdIsoGroupHom`)
- § 4. `φ` es sobreyectivo (`thirdIsoMap_surjective`)
- § 5. `ker φ = K/N` (`thirdIsoMap_kernel`)
-/

set_option autoImplicit false

namespace Peano
  namespace GroupTheory
    open Peano.FSet Peano.FSetFunction Peano.Group

    /-! ## § 0. Lemas auxiliares -/

    /-- Si `N ≤ K` (como subgrupos de `G`), entonces `cosetRel G N a b → cosetRel G K a b`. -/
    theorem cosetRel_N_imp_K (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems)
        (a b : ℕ₀) (_ha : a ∈ G.carrier.elems) (_hb : b ∈ G.carrier.elems)
        (h : cosetRel G N a b) : cosetRel G K a b := by
      unfold cosetRel at *
      exact hNK _ h

    /-- Si `K ⊴ G` y `cosetRel G K a b`, entonces `cosetRel G K (G.inv a) (G.inv b)`. -/
    private theorem cosetRel_inv_of_normal (G : FinGroup ℕ₀) (K : Subgroup G)
        (hn_K : K.IsNormal) (a b : ℕ₀)
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems)
        (h : cosetRel G K a b) : cosetRel G K (G.inv a) (G.inv b) := by
      unfold cosetRel at *
      rw [inv_inv_eq G ha]
      -- h : G.op (G.inv a) b ∈ K.carrier.elems
      -- Goal : G.op a (G.inv b) ∈ K.carrier.elems
      -- Paso 1: G.op (G.inv b) a ∈ K  (por K.inv_closed aplicado a h y usando inv_op_eq)
      have h1 : G.op (G.inv b) a ∈ K.carrier.elems := by
        have hk := K.inv_closed _ h
        rwa [inv_op_eq G (inv_mem G ha) hb, inv_inv_eq G ha] at hk
      -- Paso 2: Aplicar normalidad de K:  g = a,  n = G.op (G.inv b) a
      --   Da: G.op (G.op a (G.op (G.inv b) a)) (G.inv a) ∈ K
      have h2 := hn_K a (G.op (G.inv b) a) ha h1
      -- Paso 3: Simplificar  a·(b⁻¹·a)·a⁻¹  =  a·b⁻¹
      have h_simp : G.op (G.op a (G.op (G.inv b) a)) (G.inv a) = G.op a (G.inv b) := by
        rw [G.op_assoc a (G.op (G.inv b) a) (G.inv a) ha
              (op_mem G (inv_mem G hb) ha) (inv_mem G ha),
            G.op_assoc (G.inv b) a (G.inv a) (inv_mem G hb) ha (inv_mem G ha),
            (G.op_inv a ha).1, (G.op_id (G.inv b) (inv_mem G hb)).1]
      exact h_simp ▸ h2

    /-! ## § 1. `K/N` es normal en `G/N` -/

    /-- `imageSubgroup G N hn_N K hNK` (= K/N) es subgrupo normal de `quotientGroup G N hn_N` (= G/N). -/
    theorem KmodN_normal (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hn_N : N.IsNormal) (hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems) :
        (imageSubgroup G N hn_N K hNK).IsNormal := by
      -- IsNormal en quotientGroup G N hn_N:
      -- ∀ C D, C ∈ G/N → D ∈ K/N → CDC⁻¹ ∈ K/N
      intro C D hC hD
      simp only [imageSubgroup] at hD ⊢
      rw [mem_sortFSetList_iff, List.mem_map] at hD ⊢
      obtain ⟨k, hk, rfl⟩ := hD
      -- k ∈ K ≤ G
      have hk_G := K.subset k hk
      -- Representante de C en G
      have hr_G := cosetRepOf_mem_G G N C hC
      -- Representante de leftCoset G N k
      have hr_D_in : leftCoset G N k ∈ (quotientCarrier G N).elems :=
        leftCoset_mem_quotientCarrier G N k hk_G
      have hr_D_G := cosetRepOf_mem_G G N (leftCoset G N k) hr_D_in
      -- cosetRepOf G N (leftCoset G N k) ↔ k  (en N)
      have h_rD_eq : leftCoset G N (cosetRepOf G N (leftCoset G N k)) = leftCoset G N k :=
        cosetRepOf_leftCoset_eq G N _ hr_D_in
      -- Desplegar la operación del grupo cociente
      simp only [quotientGroup, quotientOp, quotientInv]
      -- La expresión es: leftCoset G N (G.op X Y) donde
      --   X = cosetRepOf G N (leftCoset G N (G.op r r_D))
      --   Y = cosetRepOf G N (leftCoset G N (G.inv r))
      -- La probamos igual a leftCoset G N (G.op (G.op r k) (G.inv r))  que está en K
      let r := cosetRepOf G N C
      let r_D := cosetRepOf G N (leftCoset G N k)
      have h_rep_inner : leftCoset G N (G.op r r_D) ∈ (quotientCarrier G N).elems :=
        leftCoset_mem_quotientCarrier G N _ (op_mem G hr_G hr_D_G)
      have h_rep_inv : leftCoset G N (G.inv r) ∈ (quotientCarrier G N).elems :=
        leftCoset_mem_quotientCarrier G N _ (inv_mem G hr_G)
      -- Paso 1: cosetRep(cosetRep(r*r_D) * cosetRep(r⁻¹)) = (r*r_D)*r⁻¹ mod N
      --   luego leftCoset G N (...) = leftCoset G N ((r*r_D)*r⁻¹)
      have h1 : leftCoset G N
          (G.op (cosetRepOf G N (leftCoset G N (G.op r r_D)))
                (cosetRepOf G N (leftCoset G N (G.inv r))))
          = leftCoset G N (G.op (G.op r r_D) (G.inv r)) :=
        quotientOp_welldefined G N hn_N
          (cosetRepOf G N (leftCoset G N (G.op r r_D))) (G.op r r_D)
          (cosetRepOf G N (leftCoset G N (G.inv r))) (G.inv r)
          (cosetRepOf_mem_G G N _ h_rep_inner) (op_mem G hr_G hr_D_G)
          (cosetRepOf_mem_G G N _ h_rep_inv) (inv_mem G hr_G)
          (cosetRepOf_leftCoset_eq G N _ h_rep_inner)
          (cosetRepOf_leftCoset_eq G N _ h_rep_inv)
      -- Paso 2: (r*r_D)*r⁻¹ = (r*k)*r⁻¹  mod N  (pues r_D ↔ k en N)
      have h2 : leftCoset G N (G.op (G.op r r_D) (G.inv r))
          = leftCoset G N (G.op (G.op r k) (G.inv r)) :=
        quotientOp_welldefined G N hn_N
          (G.op r r_D) (G.op r k) (G.inv r) (G.inv r)
          (op_mem G hr_G hr_D_G) (op_mem G hr_G hk_G)
          (inv_mem G hr_G) (inv_mem G hr_G)
          (quotientOp_welldefined G N hn_N r r r_D k hr_G hr_G hr_D_G hk_G rfl h_rD_eq)
          rfl
      rw [h1, h2]
      -- Paso 3: r * k * r⁻¹ ∈ K  por normalidad de K en G
      exact ⟨G.op (G.op r k) (G.inv r), hn_K r k hr_G hk, rfl⟩

    /-! ## § 2. Mapa canónico `φ : G/N → G/K` -/

    /-- El mapa canónico `φ : G/N → G/K` definido por `φ(C) = leftCoset G K (cosetRepOf G N C)`. -/
    noncomputable def thirdIsoMap (G : FinGroup ℕ₀) (N K : Subgroup G)
        (_hn_N : N.IsNormal) (_hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems) :
        MapOn (quotientCarrier G N) (quotientCarrier G K) where
      toFun := fun C => leftCoset G K (cosetRepOf G N C)
      map_carrier := fun C hC =>
        leftCoset_mem_quotientCarrier G K _ (cosetRepOf_mem_G G N C hC)

    /-- `thirdIsoMap` es bien-definido: si `C = leftCoset G N g`, entonces `φ(C) = leftCoset G K g`. -/
    theorem thirdIsoMap_welldefined (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hn_N : N.IsNormal) (hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems)
        (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
        (thirdIsoMap G N K hn_N hn_K hNK).toFun (leftCoset G N g) = leftCoset G K g := by
      simp only [thirdIsoMap]
      have h_in : leftCoset G N g ∈ (quotientCarrier G N).elems :=
        leftCoset_mem_quotientCarrier G N g hg
      have h_rep_G := cosetRepOf_mem_G G N _ h_in
      -- cosetRepOf G N (leftCoset G N g) ∼_N g
      have h_rel_N := cosetRel_of_leftCoset_eq G N _ g h_rep_G hg
        (cosetRepOf_leftCoset_eq G N _ h_in)
      -- ∼_N implica ∼_K
      have h_rel_K := cosetRel_N_imp_K G N K hNK _ _ h_rep_G hg h_rel_N
      exact leftCoset_eq_of_rel G K _ g h_rep_G hg h_rel_K

    /-! ## § 3. `φ` es homomorfismo de grupos -/

    /-- `φ` preserva la operación del grupo cociente. -/
    theorem thirdIsoMap_op (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hn_N : N.IsNormal) (hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems)
        (C₁ C₂ : ℕ₀FSet)
        (hC₁ : C₁ ∈ (quotientCarrier G N).elems)
        (hC₂ : C₂ ∈ (quotientCarrier G N).elems) :
        (thirdIsoMap G N K hn_N hn_K hNK).toFun ((quotientOp G N hn_N) C₁ C₂) =
          (quotientOp G K hn_K)
            ((thirdIsoMap G N K hn_N hn_K hNK).toFun C₁)
            ((thirdIsoMap G N K hn_N hn_K hNK).toFun C₂) := by
      simp only [thirdIsoMap, quotientOp]
      let r₁ := cosetRepOf G N C₁
      let r₂ := cosetRepOf G N C₂
      have hr₁_G := cosetRepOf_mem_G G N C₁ hC₁
      have hr₂_G := cosetRepOf_mem_G G N C₂ hC₂
      -- Membresía del producto en G/N
      have h_prod_in : leftCoset G N (G.op r₁ r₂) ∈ (quotientCarrier G N).elems :=
        leftCoset_mem_quotientCarrier G N _ (op_mem G hr₁_G hr₂_G)
      -- LHS = leftCoset G K (cosetRepOf G N (leftCoset G N (r₁·r₂)))
      --     = leftCoset G K (r₁·r₂)  [pues rep ∼_N r₁·r₂, y ∼_N ⊆ ∼_K]
      have h_lhs : leftCoset G K (cosetRepOf G N (leftCoset G N (G.op r₁ r₂)))
          = leftCoset G K (G.op r₁ r₂) := by
        have h_rep_G := cosetRepOf_mem_G G N _ h_prod_in
        have h_rel_N := cosetRel_of_leftCoset_eq G N _ (G.op r₁ r₂) h_rep_G
          (op_mem G hr₁_G hr₂_G) (cosetRepOf_leftCoset_eq G N _ h_prod_in)
        exact leftCoset_eq_of_rel G K _ _ h_rep_G (op_mem G hr₁_G hr₂_G)
          (cosetRel_N_imp_K G N K hNK _ _ h_rep_G (op_mem G hr₁_G hr₂_G) h_rel_N)
      -- RHS = leftCoset G K (G.op (cosetRepOf G K (leftCoset G K r₁))
      --                           (cosetRepOf G K (leftCoset G K r₂)))
      --     = leftCoset G K (r₁·r₂)  [por quotientOp_welldefined en K]
      have hr₁_K_in := leftCoset_mem_quotientCarrier G K r₁ hr₁_G
      have hr₂_K_in := leftCoset_mem_quotientCarrier G K r₂ hr₂_G
      have h_rhs : leftCoset G K
          (G.op (cosetRepOf G K (leftCoset G K r₁))
                (cosetRepOf G K (leftCoset G K r₂)))
          = leftCoset G K (G.op r₁ r₂) :=
        quotientOp_welldefined G K hn_K
          (cosetRepOf G K (leftCoset G K r₁)) r₁
          (cosetRepOf G K (leftCoset G K r₂)) r₂
          (cosetRepOf_mem_G G K _ hr₁_K_in) hr₁_G
          (cosetRepOf_mem_G G K _ hr₂_K_in) hr₂_G
          (cosetRepOf_leftCoset_eq G K _ hr₁_K_in)
          (cosetRepOf_leftCoset_eq G K _ hr₂_K_in)
      exact h_lhs.trans h_rhs.symm

    /-- `φ` preserva la identidad del grupo cociente. -/
    theorem thirdIsoMap_id (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hn_N : N.IsNormal) (hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems) :
        (thirdIsoMap G N K hn_N hn_K hNK).toFun (quotientId G N) = quotientId G K := by
      simp only [thirdIsoMap, quotientId]
      have hid_N_in : leftCoset G N G.id ∈ (quotientCarrier G N).elems :=
        leftCoset_id_mem_quotientCarrier G N
      have h_rep_G := cosetRepOf_mem_G G N _ hid_N_in
      -- cosetRepOf G N (leftCoset G N G.id) ∼_N G.id
      have h_rel_N := cosetRel_of_leftCoset_eq G N _ G.id h_rep_G G.id_in
        (cosetRepOf_leftCoset_eq G N _ hid_N_in)
      -- cosetRel G N rep G.id  ↔  G.op (G.inv rep) G.id ∈ N
      unfold cosetRel at h_rel_N
      rw [(G.op_id (G.inv _) (inv_mem G h_rep_G)).1] at h_rel_N
      -- G.inv rep ∈ N ≤ K, luego leftCoset G K rep = leftCoset G K G.id
      apply leftCoset_eq_of_rel G K _ G.id h_rep_G G.id_in
      unfold cosetRel
      rw [(G.op_id (G.inv _) (inv_mem G h_rep_G)).1]
      exact hNK _ h_rel_N

    /-- `φ` preserva inversos en el grupo cociente. -/
    theorem thirdIsoMap_inv (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hn_N : N.IsNormal) (hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems)
        (C : ℕ₀FSet) (hC : C ∈ (quotientCarrier G N).elems) :
        (thirdIsoMap G N K hn_N hn_K hNK).toFun ((quotientInv G N hn_N) C) =
          (quotientInv G K hn_K) ((thirdIsoMap G N K hn_N hn_K hNK).toFun C) := by
      simp only [thirdIsoMap, quotientInv]
      let r := cosetRepOf G N C
      have hr_G := cosetRepOf_mem_G G N C hC
      -- LHS = leftCoset G K (cosetRepOf G N (leftCoset G N (G.inv r)))
      --     = leftCoset G K (G.inv r)  [rep ∼_N G.inv r, y ∼_N ⊆ ∼_K]
      have h_inv_in : leftCoset G N (G.inv r) ∈ (quotientCarrier G N).elems :=
        leftCoset_mem_quotientCarrier G N _ (inv_mem G hr_G)
      have h_lhs : leftCoset G K (cosetRepOf G N (leftCoset G N (G.inv r)))
          = leftCoset G K (G.inv r) := by
        have h_rep_G' := cosetRepOf_mem_G G N _ h_inv_in
        have h_rel_N := cosetRel_of_leftCoset_eq G N _ (G.inv r) h_rep_G'
          (inv_mem G hr_G) (cosetRepOf_leftCoset_eq G N _ h_inv_in)
        exact leftCoset_eq_of_rel G K _ _ h_rep_G' (inv_mem G hr_G)
          (cosetRel_N_imp_K G N K hNK _ _ h_rep_G' (inv_mem G hr_G) h_rel_N)
      -- RHS = leftCoset G K (G.inv (cosetRepOf G K (leftCoset G K r)))
      --     = leftCoset G K (G.inv r)  [cosetRel_inv_of_normal]
      have hr_K_in := leftCoset_mem_quotientCarrier G K r hr_G
      have h_rep_K_G := cosetRepOf_mem_G G K _ hr_K_in
      have h_rep_rel : cosetRel G K (cosetRepOf G K (leftCoset G K r)) r :=
        cosetRel_of_leftCoset_eq G K _ r h_rep_K_G hr_G
          (cosetRepOf_leftCoset_eq G K _ hr_K_in)
      have h_rhs : leftCoset G K (G.inv (cosetRepOf G K (leftCoset G K r)))
          = leftCoset G K (G.inv r) :=
        leftCoset_eq_of_rel G K _ _
          (inv_mem G h_rep_K_G) (inv_mem G hr_G)
          (cosetRel_inv_of_normal G K hn_K _ r h_rep_K_G hr_G h_rep_rel)
      exact h_lhs.trans h_rhs.symm

    /-- El mapa `φ : G/N → G/K` es un homomorfismo de grupos. -/
    noncomputable def thirdIsoGroupHom (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hn_N : N.IsNormal) (hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems) :
        GroupHom (quotientGroup G N hn_N) (quotientGroup G K hn_K) where
      map := thirdIsoMap G N K hn_N hn_K hNK
      map_op := fun C₁ C₂ hC₁ hC₂ => by
        show (thirdIsoMap G N K hn_N hn_K hNK).toFun
              ((quotientGroup G N hn_N).op C₁ C₂) =
            (quotientGroup G K hn_K).op
              ((thirdIsoMap G N K hn_N hn_K hNK).toFun C₁)
              ((thirdIsoMap G N K hn_N hn_K hNK).toFun C₂)
        simp only [quotientGroup, quotientOp]
        exact thirdIsoMap_op G N K hn_N hn_K hNK C₁ C₂ hC₁ hC₂
      map_id := by
        show (thirdIsoMap G N K hn_N hn_K hNK).toFun
              (quotientGroup G N hn_N).id =
            (quotientGroup G K hn_K).id
        simp only [quotientGroup, quotientId]
        exact thirdIsoMap_id G N K hn_N hn_K hNK
      map_inv := fun C hC => by
        show (thirdIsoMap G N K hn_N hn_K hNK).toFun
              ((quotientGroup G N hn_N).inv C) =
            (quotientGroup G K hn_K).inv
              ((thirdIsoMap G N K hn_N hn_K hNK).toFun C)
        simp only [quotientGroup, quotientInv]
        exact thirdIsoMap_inv G N K hn_N hn_K hNK C hC

    /-! ## § 4. `φ` es sobreyectivo -/

    /-- El mapa `φ : G/N → G/K` es sobreyectivo. -/
    theorem thirdIsoMap_surjective (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hn_N : N.IsNormal) (hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems) :
        (thirdIsoMap G N K hn_N hn_K hNK).Surjective := by
      -- SurjectiveOn f A B = ∀ b, b ∈ B.elems → ∃ a, a ∈ A.elems ∧ f a = b
      intro D hD
      obtain ⟨g, hg, hgD⟩ := mem_quotientCarrier_is_leftCoset G K D hD
      -- hgD : leftCoset G K g = D
      exact ⟨leftCoset G N g, leftCoset_mem_quotientCarrier G N g hg,
        (thirdIsoMap_welldefined G N K hn_N hn_K hNK g hg).trans hgD.symm⟩

    /-! ## § 5. `ker φ = K/N` -/

    /-- El núcleo de `φ` es exactamente `K/N`:
        `φ(C) = quotientId G K ↔ C ∈ (imageSubgroup G N hn_N K hNK).carrier`. -/
    theorem thirdIsoMap_kernel (G : FinGroup ℕ₀) (N K : Subgroup G)
        (hn_N : N.IsNormal) (hn_K : K.IsNormal)
        (hNK : ∀ n, n ∈ N.carrier.elems → n ∈ K.carrier.elems)
        (C : ℕ₀FSet) (hC : C ∈ (quotientCarrier G N).elems) :
        (thirdIsoMap G N K hn_N hn_K hNK).toFun C = quotientId G K ↔
          C ∈ (imageSubgroup G N hn_N K hNK).carrier.elems := by
      constructor
      · intro heq
        simp only [thirdIsoMap, quotientId] at heq
        simp only [imageSubgroup, mem_sortFSetList_iff, List.mem_map]
        have hr_G := cosetRepOf_mem_G G N C hC
        -- heq : leftCoset G K (cosetRepOf G N C) = leftCoset G K G.id
        -- → cosetRel G K rep G.id → G.inv rep ∈ K → rep ∈ K
        have h_rel := cosetRel_of_leftCoset_eq G K _ G.id hr_G G.id_in heq
        unfold cosetRel at h_rel
        rw [(G.op_id (G.inv _) (inv_mem G hr_G)).1] at h_rel
        -- h_rel : G.inv (cosetRepOf G N C) ∈ K
        have hr_K : cosetRepOf G N C ∈ K.carrier.elems := by
          have := K.inv_closed _ h_rel
          rwa [inv_inv_eq G hr_G] at this
        -- C = leftCoset G N (cosetRepOf G N C)  [from cosetRepOf_leftCoset_eq]
        exact ⟨cosetRepOf G N C, hr_K, cosetRepOf_leftCoset_eq G N C hC⟩
      · intro hC_mem
        simp only [imageSubgroup, mem_sortFSetList_iff, List.mem_map] at hC_mem
        obtain ⟨k, hk, hCk⟩ := hC_mem
        simp only [thirdIsoMap, quotientId]
        -- hCk : C = leftCoset G N k  (o  leftCoset G N k = C ?)
        -- La dirección depende de la definición de List.mem_map
        -- List.mem_map : x ∈ l.map f ↔ ∃ a ∈ l, f a = x
        -- Así hCk : leftCoset G N k = C
        -- → cosetRepOf G N C = cosetRepOf G N (leftCoset G N k)
        have hk_G := K.subset k hk
        have h_in : leftCoset G N k ∈ (quotientCarrier G N).elems :=
          leftCoset_mem_quotientCarrier G N k hk_G
        rw [← hCk]
        -- Goal: leftCoset G K (cosetRepOf G N (leftCoset G N k)) = leftCoset G K G.id
        have h_rep_G := cosetRepOf_mem_G G N _ h_in
        -- cosetRel G N rep k  (rep ∼_N k)
        have h_rel_N := cosetRel_of_leftCoset_eq G N _ k h_rep_G hk_G
          (cosetRepOf_leftCoset_eq G N _ h_in)
        -- G.op (G.inv rep) k ∈ N ≤ K
        have h_rel_K_raw : G.op (G.inv (cosetRepOf G N (leftCoset G N k))) k ∈ K.carrier.elems :=
          hNK _ (by unfold cosetRel at h_rel_N; exact h_rel_N)
        -- rep ∈ K: de G.inv rep · k ∈ K y k ∈ K, obtenemos G.inv rep ∈ K,
        --          luego rep = (G.inv rep)⁻¹ ∈ K
        have hrep_K : cosetRepOf G N (leftCoset G N k) ∈ K.carrier.elems := by
          have h := K.op_closed _ _ h_rel_K_raw (K.inv_closed k hk)
          rw [G.op_assoc (G.inv _) k (G.inv k) (inv_mem G h_rep_G) hk_G (inv_mem G hk_G),
              (G.op_inv k hk_G).1, (G.op_id (G.inv _) (inv_mem G h_rep_G)).1] at h
          -- h : G.inv rep ∈ K
          have := K.inv_closed _ h
          rwa [inv_inv_eq G h_rep_G] at this
        -- leftCoset G K rep = leftCoset G K G.id  pues G.inv rep ∈ K
        apply leftCoset_eq_of_rel G K _ G.id h_rep_G G.id_in
        unfold cosetRel
        rw [(G.op_id (G.inv _) (inv_mem G h_rep_G)).1]
        exact K.inv_closed _ hrep_K

  end GroupTheory
end Peano

export Peano.GroupTheory (
  cosetRel_N_imp_K
  KmodN_normal
  thirdIsoMap
  thirdIsoMap_welldefined
  thirdIsoMap_op
  thirdIsoMap_id
  thirdIsoMap_inv
  thirdIsoGroupHom
  thirdIsoMap_surjective
  thirdIsoMap_kernel
)
