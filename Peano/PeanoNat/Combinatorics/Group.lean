import Peano.PeanoNat
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Group.lean

set_option autoImplicit false

namespace Peano
  namespace Group
    open Peano.FSet
    open Peano.FSetFunction

    /-!
    # § 4. Estructura de Grupo Finito
    -/

    structure FinGroup where
      carrier : ℕ₀FSet
      op : BinOpOn carrier
      id : ℕ₀
      inv : MapOn carrier carrier
      id_in :
        id ∈ carrier.elems
      op_assoc :
        ∀ a b c,
          a ∈ carrier.elems → b ∈ carrier.elems → c ∈ carrier.elems →
            op (op a b) c = op a (op b c)
      op_id :
        ∀ a,
          a ∈ carrier.elems → op a id = a ∧ op id a = a
      op_inv :
        ∀ a,
          a ∈ carrier.elems → op a (inv a) = id ∧ op (inv a) a = id

    /--
    En cualquier `FinGroup`, el elemento neutro es único.
    -/
    theorem id_unique (G : FinGroup) (e' : ℕ₀)
        (h_e'_in : e' ∈ G.carrier.elems)
        (h_is_id : ∀ a, a ∈ G.carrier.elems → G.op a e' = a ∧ G.op e' a = a) :
        e' = G.id := by
      -- La prueba se basa en que G.id = G.op G.id e' (por la propiedad de e') y e' = G.op G.id e' (por la propiedad de G.id).
      -- Por tanto, e' = G.id.
      let h_id_op_e' := (h_is_id G.id G.id_in).left
      let h_e'_op_id := (G.op_id e' h_e'_in).right
      exact h_e'_op_id.symm.trans h_id_op_e'

    /-!
    # § 4b. Lemas auxiliares de grupo
    -/

    /-- Pertenencia del inverso al carrier. -/
    theorem inv_mem (G : FinGroup) {a : ℕ₀} (ha : a ∈ G.carrier.elems) :
        G.inv a ∈ G.carrier.elems :=
      G.inv.map_carrier a ha

    /-- Pertenencia del producto al carrier. -/
    theorem op_mem (G : FinGroup) {a b : ℕ₀}
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems) :
        G.op a b ∈ G.carrier.elems :=
      G.op.map_carrier a b ha hb

    /-- Cancelación izquierda: `a·x = a·y → x = y`. -/
    theorem op_cancel_left (G : FinGroup) {a x y : ℕ₀}
        (ha : a ∈ G.carrier.elems) (hx : x ∈ G.carrier.elems) (hy : y ∈ G.carrier.elems)
        (h : G.op a x = G.op a y) : x = y := by
      have ha' := inv_mem G ha
      have h1 : G.op (G.inv a) (G.op a x) = G.op (G.inv a) (G.op a y) := by rw [h]
      rw [← G.op_assoc (G.inv a) a x ha' ha hx,
          ← G.op_assoc (G.inv a) a y ha' ha hy,
          (G.op_inv a ha).2, (G.op_id x hx).2, (G.op_id y hy).2] at h1
      exact h1

    /-- Cancelación derecha: `x·a = y·a → x = y`. -/
    theorem op_cancel_right (G : FinGroup) {a x y : ℕ₀}
        (ha : a ∈ G.carrier.elems) (hx : x ∈ G.carrier.elems) (hy : y ∈ G.carrier.elems)
        (h : G.op x a = G.op y a) : x = y := by
      have ha' := inv_mem G ha
      have h1 : G.op (G.op x a) (G.inv a) = G.op (G.op y a) (G.inv a) := by rw [h]
      rw [G.op_assoc x a (G.inv a) hx ha ha',
          G.op_assoc y a (G.inv a) hy ha ha',
          (G.op_inv a ha).1, (G.op_id x hx).1, (G.op_id y hy).1] at h1
      exact h1

    /-- `inv(inv(a)) = a`. -/
    theorem inv_inv_eq (G : FinGroup) {a : ℕ₀} (ha : a ∈ G.carrier.elems) :
        G.inv (G.inv a) = a := by
      apply op_cancel_right G (inv_mem G ha) (inv_mem G (inv_mem G ha)) ha
      rw [(G.op_inv (G.inv a) (inv_mem G ha)).2, (G.op_inv a ha).1]

    /-- `inv(id) = id`. -/
    theorem inv_id_eq (G : FinGroup) : G.inv G.id = G.id := by
      have h1 : G.op G.id (G.inv G.id) = G.id := (G.op_inv G.id G.id_in).1
      have h2 : G.op G.id (G.inv G.id) = G.inv G.id :=
        (G.op_id (G.inv G.id) (inv_mem G G.id_in)).2
      exact h2.symm.trans h1

    /-- `inv(a·b) = inv(b)·inv(a)`. -/
    theorem inv_op_eq (G : FinGroup) {a b : ℕ₀}
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems) :
        G.inv (G.op a b) = G.op (G.inv b) (G.inv a) := by
      have hab := op_mem G ha hb
      have ha' := inv_mem G ha
      have hb' := inv_mem G hb
      have hba' := op_mem G hb' ha'
      have key : G.op (G.op a b) (G.op (G.inv b) (G.inv a)) = G.id := by
        rw [G.op_assoc a b _ ha hb hba',
            ← G.op_assoc b (G.inv b) (G.inv a) hb hb' ha',
            (G.op_inv b hb).1, (G.op_id (G.inv a) ha').2, (G.op_inv a ha).1]
      exact op_cancel_left G hab (inv_mem G hab) hba'
        ((G.op_inv _ hab).1 |>.trans key.symm)

    /-- Unicidad del inverso: si `a·b = id ∧ b·a = id`, entonces `b = inv(a)`. -/
    theorem inv_unique (G : FinGroup) {a b : ℕ₀}
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems)
        (h : G.op a b = G.id ∧ G.op b a = G.id) :
        b = G.inv a := by
      apply op_cancel_left G ha hb (inv_mem G ha)
      rw [h.1, (G.op_inv a ha).1]

    /-!
    # § 4c. Potencia iterada y orden de un elemento
    -/

    /-- Potencia iterada: `gpow G g n = g^n` (por la derecha).
        `gpow G g 0 = id`, `gpow G g (n+1) = (gpow G g n) · g`. -/
    def gpow (G : FinGroup) (g : ℕ₀) : ℕ₀ → ℕ₀
      | .zero   => G.id
      | .succ n => G.op (gpow G g n) g

    @[simp] theorem gpow_zero (G : FinGroup) (g : ℕ₀) :
        gpow G g 𝟘 = G.id := rfl

    @[simp] theorem gpow_succ (G : FinGroup) (g : ℕ₀) (n : ℕ₀) :
        gpow G g (σ n) = G.op (gpow G g n) g := rfl

    theorem gpow_one (G : FinGroup) (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
        gpow G g 𝟙 = g :=
      (G.op_id g hg).2

    /-- `g^n ∈ G` para todo `n`. -/
    theorem gpow_mem (G : FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems) :
        ∀ n : ℕ₀, gpow G g n ∈ G.carrier.elems
      | .zero   => G.id_in
      | .succ n => op_mem G (gpow_mem G hg n) hg

    /-- `g^(m+n) = g^m · g^n`. -/
    theorem gpow_add (G : FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
        (m n : ℕ₀) :
        gpow G g (add m n) = G.op (gpow G g m) (gpow G g n) := by
      induction n with
      | zero =>
        simp [add_zero, gpow_zero, (G.op_id (gpow G g m) (gpow_mem G hg m)).1]
      | succ n ih =>
        rw [add_succ, gpow_succ, ih, gpow_succ,
            G.op_assoc (gpow G g m) (gpow G g n) g
              (gpow_mem G hg m) (gpow_mem G hg n) hg]

    /-- `g · g^n = g^n · g` (la potencia conmuta con la base). -/
    theorem gpow_comm_single (G : FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
        (n : ℕ₀) : G.op g (gpow G g n) = G.op (gpow G g n) g := by
      calc G.op g (gpow G g n)
          = G.op (gpow G g 𝟙) (gpow G g n) := by rw [gpow_one G g hg]
        _ = gpow G g (add 𝟙 n)              := by rw [← gpow_add G hg 𝟙 n]
        _ = gpow G g (σ n)                   := by congr 1; exact add_comm 𝟙 n
        _ = G.op (gpow G g n) g              := gpow_succ G g n

    /-- `(g⁻¹)^n = (g^n)⁻¹`. -/
    theorem gpow_inv (G : FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
        : ∀ n : ℕ₀, gpow G (G.inv g) n = G.inv (gpow G g n)
      | .zero => by rw [gpow_zero, gpow_zero, inv_id_eq]
      | .succ n => by
        have ih := gpow_inv G hg n
        have hgn := gpow_mem G hg n
        have hig := inv_mem G hg
        calc gpow G (G.inv g) (σ n)
            = G.op (gpow G (G.inv g) n) (G.inv g)  := gpow_succ G (G.inv g) n
          _ = G.op (G.inv g) (gpow G (G.inv g) n)  := (gpow_comm_single G hig n).symm
          _ = G.op (G.inv g) (G.inv (gpow G g n))  := by rw [ih]
          _ = G.inv (G.op (gpow G g n) g)           := (inv_op_eq G hgn hg).symm
          _ = G.inv (gpow G g (σ n))                 := by rw [← gpow_succ]

    /-!
    # § 5. Subgrupos
    !-/

    /--
    Un subgrupo de un grupo finito G es un subconjunto no vacío cerrado por la operación y la inversa, con la misma operación.
    -/
    structure Subgroup (G : FinGroup) where
      carrier : ℕ₀FSet
      nonempty : ∃ a, a ∈ carrier.elems
      subset : ∀ a, a ∈ carrier.elems → a ∈ G.carrier.elems
      op_closed : ∀ a b, a ∈ carrier.elems → b ∈ carrier.elems → G.op a b ∈ carrier.elems
      id_in : G.id ∈ carrier.elems
      inv_closed : ∀ a, a ∈ carrier.elems → G.inv a ∈ carrier.elems

    /-- Criterio de un paso: `H ≤ G` si y solo si `H ⊆ G`, `H ≠ ∅` y
        `∀ a b ∈ H, a · b⁻¹ ∈ H`. -/
    theorem Subgroup.op_inv_closed (G : FinGroup) (H : Subgroup G)
        (a b : ℕ₀) (ha : a ∈ H.carrier.elems) (hb : b ∈ H.carrier.elems) :
        G.op a (G.inv b) ∈ H.carrier.elems :=
      H.op_closed a (G.inv b) ha (H.inv_closed b hb)

    /-- Recíproco: si `S ⊆ G` es no vacío y cerrado bajo `a · b⁻¹`,
        entonces `S` es subgrupo de `G`. -/
    def subgroup_of_op_inv_closed (G : FinGroup)
        (S : ℕ₀FSet)
        (h_sub : ∀ a, a ∈ S.elems → a ∈ G.carrier.elems)
        (h_ne : ∃ a, a ∈ S.elems)
        (h_cl : ∀ a b, a ∈ S.elems → b ∈ S.elems →
                  G.op a (G.inv b) ∈ S.elems) :
        Subgroup G where
      carrier := S
      nonempty := h_ne
      subset := h_sub
      id_in := by
        obtain ⟨a, ha⟩ := h_ne
        have : G.op a (G.inv a) ∈ S.elems := h_cl a a ha ha
        rwa [(G.op_inv a (h_sub a ha)).1] at this
      inv_closed := fun b hb => by
        obtain ⟨a, ha⟩ := h_ne
        have hid : G.id ∈ S.elems := by
          have := h_cl a a ha ha
          rwa [(G.op_inv a (h_sub a ha)).1] at this
        have : G.op G.id (G.inv b) ∈ S.elems := h_cl G.id b hid hb
        rwa [(G.op_id (G.inv b) (inv_mem G (h_sub b hb))).2] at this
      op_closed := fun a b ha hb => by
        have hb' : G.inv b ∈ S.elems := by
          have hid : G.id ∈ S.elems := by
            obtain ⟨c, hc⟩ := h_ne
            have := h_cl c c hc hc
            rwa [(G.op_inv c (h_sub c hc)).1] at this
          have := h_cl G.id b hid hb
          rwa [(G.op_id (G.inv b) (inv_mem G (h_sub b hb))).2] at this
        -- a · b = a · inv(inv(b))
        have key : G.op a b = G.op a (G.inv (G.inv b)) := by
          rw [inv_inv_eq G (h_sub b hb)]
        rw [key]
        exact h_cl a (G.inv b) ha hb'

    /-!
    # § 5b. Tipos especiales de subgrupos
    !-/

    /-- El subgrupo trivial `{e}`. -/
    def trivialSubgroup (G : FinGroup) : Subgroup G where
      carrier  := ℕ₀FSet.singleton G.id
      nonempty := ⟨G.id, List.mem_cons.mpr (Or.inl rfl)⟩
      subset   := fun a ha => by
        simp only [ℕ₀FSet.singleton, FSet.singleton, List.mem_singleton] at ha
        exact ha ▸ G.id_in
      op_closed := fun a b ha hb => by
        simp only [ℕ₀FSet.singleton, FSet.singleton, List.mem_singleton] at ha hb ⊢
        rw [ha, hb, (G.op_id G.id G.id_in).1]
      id_in    := List.mem_cons.mpr (Or.inl rfl)
      inv_closed := fun a ha => by
        simp only [ℕ₀FSet.singleton, FSet.singleton, List.mem_singleton] at ha ⊢
        rw [ha, inv_id_eq]

    /-- El subgrupo impropio `G` como subgrupo de sí mismo. -/
    def improperSubgroup (G : FinGroup) : Subgroup G where
      carrier    := G.carrier
      nonempty   := ⟨G.id, G.id_in⟩
      subset     := fun _ ha => ha
      op_closed  := fun a b ha hb => op_mem G ha hb
      id_in      := G.id_in
      inv_closed := fun a ha => inv_mem G ha

    /-- Un subgrupo es trivial si tiene exactamente un elemento. -/
    def Subgroup.IsTrivial {G : FinGroup} (H : Subgroup G) : Prop :=
      H.carrier.card = 𝟙

    /-- Un subgrupo es propio si no es el grupo entero. -/
    def Subgroup.IsProper {G : FinGroup} (H : Subgroup G) : Prop :=
      H.carrier.card ≠ G.carrier.card

    /-!
    # § 5c. Subgrupo cíclico
    !-/

    private def cyclicCarrier (G : FinGroup) (g : ℕ₀) : ℕ₀FSet :=
      ℕ₀FSet.filter
        (fun x => (ℕ₀FSet.Fin₀Set (σ G.carrier.card)).elems.any
                    (fun i => decide (gpow G g i = x)))
        G.carrier

    private theorem cyclicCarrier_id_in (G : FinGroup) (g : ℕ₀) :
        G.id ∈ (cyclicCarrier G g).elems :=
      List.mem_filter.mpr ⟨G.id_in,
        List.any_eq_true.mpr ⟨𝟘,
          (ℕ₀FSet.mem_Fin₀Set_iff (σ G.carrier.card) 𝟘).mpr
            (by unfold Peano.StrictOrder.lt₀; trivial),
          decide_eq_true_eq.mpr (gpow_zero G g)⟩⟩

    private theorem cyclicCarrier_mem_iff (G : FinGroup) (g x : ℕ₀) :
        x ∈ (cyclicCarrier G g).elems ↔
          x ∈ G.carrier.elems ∧
          ∃ i ∈ (ℕ₀FSet.Fin₀Set (σ G.carrier.card)).elems, gpow G g i = x := by
      simp only [cyclicCarrier, ℕ₀FSet.filter, FSet.filter, List.mem_filter,
                 List.any_eq_true, decide_eq_true_eq]

    /-- El subgrupo cíclico generado por `g`, definido mediante el criterio de un paso. -/
    def cyclicSubgroup (G : FinGroup) (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
        Subgroup G :=
      subgroup_of_op_inv_closed G
        (cyclicCarrier G g)
        (fun a ha => (List.mem_filter.mp ha).1)
        ⟨G.id, cyclicCarrier_id_in G g⟩
        (fun a b ha hb => by
          -- Obtener testigos de potencias
          obtain ⟨ha_G, m, _hm_idx, hm⟩ := (cyclicCarrier_mem_iff G g a).mp ha
          obtain ⟨_,   n, _hn_idx, hn⟩ := (cyclicCarrier_mem_iff G g b).mp hb
          -- a · inv(b) = g^m · (g^n)⁻¹ = g^m · (g⁻¹)^n ... no, usamos a·b⁻¹ directamente
          -- a · inv(b) = g^m · (g^n)⁻¹
          -- Por gpow_inv: (g^n)⁻¹ = (g⁻¹)^n, y después gpow de inv(g)...
          -- Más sencillo: demostrar que a·b⁻¹ ∈ cyclicCarrier via testigo add m n
          -- porque a·b⁻¹ = g^m · (g^n)⁻¹ = g^m · g^(-n)
          -- Pero no tenemos gpow negativo. Sin embargo, a·b⁻¹ = op a (inv b)
          -- = op (gpow g m) (inv (gpow g n))
          -- = op (gpow g m) (gpow (inv g) n)
          -- = gpow g m · (inv g)^n
          -- Esto no es directamente gpow g k para algún k entero...
          -- ALTERNATIVA: mostrar cierre directo construyendo el subgrupo de otra forma.
          -- El criterio op_inv_closed necesita a·b⁻¹ ∈ S.
          -- Tenemos: a·b⁻¹ ∈ G (trivial), y necesitamos el testigo de índice.
          -- Si m ≥ n: a·b⁻¹ = g^m · g^{-n} = g^{m-n} ... si tuviéramos sub-potencia
          -- Si m < n: a·b⁻¹ = g^{m + (ord - n)} ... requiere orden de g
          -- CONCLUSIÓN: cyclicSubgroup requiere B2.3 (orden del elemento) para probar
          -- cierre por la relación a·b⁻¹. Por ahora, lo construimos directamente
          -- como subgrupo via los tres axiomas (op_closed, inv_closed, id_in)
          -- en lugar de via subgroup_of_op_inv_closed.
          -- Esto requiere cambiar la definición a continuación.
          sorry)

    /-- El subgrupo cíclico generado por `g` (construcción directa). -/
    def cyclicSubgroup' (G : FinGroup) (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
        Subgroup G where
      carrier    := cyclicCarrier G g
      nonempty   := ⟨G.id, cyclicCarrier_id_in G g⟩
      subset     := fun a ha => (List.mem_filter.mp ha).1
      id_in      := cyclicCarrier_id_in G g
      op_closed  := fun a b ha hb => by
        obtain ⟨ha_G, m, hm_idx, hm⟩ := (cyclicCarrier_mem_iff G g a).mp ha
        obtain ⟨hb_G, n, hn_idx, hn⟩ := (cyclicCarrier_mem_iff G g b).mp hb
        rw [cyclicCarrier_mem_iff]
        refine ⟨op_mem G ha_G hb_G, add m n, ?_, ?_⟩
        · -- add m n ∈ Fin₀Set(σ card)? No necesariamente...
          -- Necesitamos que el índice add m n esté en el conjunto de índices.
          -- Esto falla si add m n ≥ σ card. Usamos periodicidad implícita aquí.
          -- Como G es finito, por Pigeonhole, gpow G g (add m n) = gpow G g k
          -- para algún k < σ card. Pero demostrar eso requiere B2.3 (orden).
          sorry
        · rw [gpow_add G hg, hm, hn]
      inv_closed := fun a ha => by
        obtain ⟨ha_G, n, hn_idx, hn⟩ := (cyclicCarrier_mem_iff G g a).mp ha
        rw [cyclicCarrier_mem_iff]
        -- G.inv a = G.inv (gpow G g n) por hn
        -- = gpow G (G.inv g) n por gpow_inv
        -- Pero gpow G (G.inv g) n es una potencia de G.inv g, no de g.
        -- Sin orden de g, no podemos reducir (G.inv g)^n a g^k.
        -- Se deja como sorry hasta B2.3.
        exact ⟨inv_mem G ha_G, n, hn_idx, by sorry⟩

    /-!
    # § 5d. Normalidad
    !-/

    /-- Un subgrupo `N` de `G` es normal si es cerrado bajo conjugación:
        `∀ g ∈ G, ∀ n ∈ N, g·n·g⁻¹ ∈ N`. -/
    def Subgroup.IsNormal {G : FinGroup} (N : Subgroup G) : Prop :=
      ∀ g n, g ∈ G.carrier.elems → n ∈ N.carrier.elems →
        G.op (G.op g n) (G.inv g) ∈ N.carrier.elems

    /-- El subgrupo trivial es normal. -/
    theorem trivialSubgroup_normal (G : FinGroup) :
        (trivialSubgroup G).IsNormal := by
      intro g n hg hn
      simp only [trivialSubgroup, ℕ₀FSet.singleton, FSet.singleton,
                 List.mem_singleton] at hn ⊢
      rw [hn, (G.op_id g hg).1, (G.op_inv g hg).1]

    /-- El subgrupo impropio es normal. -/
    theorem improperSubgroup_normal (G : FinGroup) :
        (improperSubgroup G).IsNormal := by
      intro g n hg hn
      exact op_mem G (op_mem G hg hn) (inv_mem G hg)

    /-!
    # § 5e. Intersección de subgrupos
    !-/

    /-- Intersección de dos subgrupos. -/
    def Subgroup.inter {G : FinGroup} (H₁ H₂ : Subgroup G) : Subgroup G where
      carrier  :=
        ℕ₀FSet.filter
          (fun x => decide (x ∈ H₁.carrier) && decide (x ∈ H₂.carrier))
          G.carrier
      nonempty := ⟨G.id, List.mem_filter.mpr
        ⟨G.id_in, by
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          exact ⟨H₁.id_in, H₂.id_in⟩⟩⟩
      subset   := fun a ha => (List.mem_filter.mp ha).1
      id_in    := List.mem_filter.mpr
        ⟨G.id_in, by
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          exact ⟨H₁.id_in, H₂.id_in⟩⟩
      op_closed := fun a b ha hb => by
        obtain ⟨ha_G, ha_and⟩ := List.mem_filter.mp ha
        obtain ⟨hb_G, hb_and⟩ := List.mem_filter.mp hb
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ha_and hb_and
        exact List.mem_filter.mpr
          ⟨op_mem G ha_G hb_G, by
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
            exact ⟨H₁.op_closed a b ha_and.1 hb_and.1,
                   H₂.op_closed a b ha_and.2 hb_and.2⟩⟩
      inv_closed := fun a ha => by
        obtain ⟨ha_G, ha_and⟩ := List.mem_filter.mp ha
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ha_and
        exact List.mem_filter.mpr
          ⟨inv_mem G ha_G, by
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
            exact ⟨H₁.inv_closed a ha_and.1, H₂.inv_closed a ha_and.2⟩⟩

    /-- La intersección está contenida en ambos subgrupos. -/
    theorem Subgroup.inter_subset_left {G : FinGroup} (H₁ H₂ : Subgroup G)
        {a : ℕ₀} (ha : a ∈ (H₁.inter H₂).carrier.elems) :
        a ∈ H₁.carrier.elems := by
      obtain ⟨_, ha_and⟩ := List.mem_filter.mp ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha_and
      exact ha_and.1

    theorem Subgroup.inter_subset_right {G : FinGroup} (H₁ H₂ : Subgroup G)
        {a : ℕ₀} (ha : a ∈ (H₁.inter H₂).carrier.elems) :
        a ∈ H₂.carrier.elems := by
      obtain ⟨_, ha_and⟩ := List.mem_filter.mp ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha_and
      exact ha_and.2

    /-- La intersección de dos subgrupos normales es normal. -/
    theorem Subgroup.inter_normal_of_normal {G : FinGroup} {H₁ H₂ : Subgroup G}
        (hn₁ : H₁.IsNormal) (hn₂ : H₂.IsNormal) :
        (H₁.inter H₂).IsNormal := by
      intro g n hg hn
      have h₁ := hn₁ g n hg (inter_subset_left H₁ H₂ hn)
      have h₂ := hn₂ g n hg (inter_subset_right H₁ H₂ hn)
      have h_G := op_mem G (op_mem G hg ((H₁.inter H₂).subset n hn)) (inv_mem G hg)
      exact List.mem_filter.mpr
        ⟨h_G, by
          rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          exact ⟨h₁, h₂⟩⟩

    /-!
    # § 6. Homomorfismos
    !-/

    /--
    Un morfismo de grupos finitos es una función que respeta la operación, el neutro y la inversa.
    -/
    structure GroupHom (G H : FinGroup) where
      map : MapOn G.carrier H.carrier
      map_op : ∀ a b, a ∈ G.carrier.elems → b ∈ G.carrier.elems →
        map (G.op a b) = H.op (map a) (map b)
      map_id : map G.id = H.id
      map_inv : ∀ a, a ∈ G.carrier.elems → map (G.inv a) = H.inv (map a)

    /-!
    # § 7. Grupo Simétrico

    El grupo simétrico `Sym(A)` requiere codificar permutaciones como
    elementos de `ℕ₀FSet`. Las permutaciones como tipo están disponibles
    en `FSetFunction.Perm`. Su representación como `FinGroup` es trabajo
    futuro (necesita Lehmer codes o una generalización polimorfa de FinGroup).
    -/

  end Group
end Peano
