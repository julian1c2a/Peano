/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean
-- Acción de un grupo finito sobre un conjunto finito.
--
-- § 1. GroupAction  — definición de acción (izquierda)
-- § 2. Órbitas      — órbita de un elemento bajo la acción
-- § 3. Estabilizador — subgrupo estabilizador de un elemento
-- § 4. Teorema Órbita–Estabilizador: |Orb(x)| · |Stab(x)| = |G|
-- § 5. Ecuación de clases

import Peano.PeanoNat
import Peano.PeanoNat.Mul
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets
import Peano.PeanoNat.Combinatorics.Summation
import Peano.PeanoNat.Combinatorics.GroupTheory.NormalSubgroup

set_option autoImplicit false

namespace Peano
  namespace Action

    open Peano.FSet
    open Peano.FSetFunction
    open Peano.Group
    open Peano.Mul
    open Peano.Cosets
    open Peano.NormalSubgroup

    /-!
    # § 1. GroupAction — acción (izquierda) de un FinGroup sobre un FSet
    -/

    /-- Una acción (izquierda) de `G` sobre un conjunto finito `X`:
        un homomorfismo de grupos de `G` al grupo simétrico de `X`,
        equivalente a una función `α : G × X → X` que satisface:
        - `α(e, x) = x`  para todo `x`,
        - `α(g, α(h, x)) = α(g·h, x)`  para todo `g, h, x`.

        `α` tiene tipo `α → β → β` donde `G : FinGroup α` y `X : FSet β`. -/
    structure GroupAction
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        (G : FinGroup α) (X : FSet β) where
      /-- La función de acción: dados `g ∈ G` y `x ∈ X`, devuelve `g·x ∈ X`. -/
      act        : α → β → β
      act_closed : ∀ g x, g ∈ G.carrier.elems → x ∈ X.elems → act g x ∈ X.elems
      act_id     : ∀ x, x ∈ X.elems → act G.id x = x
      act_compat : ∀ g h x,
                     g ∈ G.carrier.elems → h ∈ G.carrier.elems → x ∈ X.elems →
                     act g (act h x) = act (G.op g h) x

    /-!
    # § 2. Órbita de un elemento
    -/

    /-- La órbita de `x ∈ X` bajo la acción `α`:
        `Orb(x) = { α(g, x) | g ∈ G }`.
        Se construye filtrando `X` por los `y` que tienen preimagen en `G`. -/
    def GroupAction.orb
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        {G : FinGroup α} {X : FSet β}
        (ψ : GroupAction G X) (x : β) : FSet β :=
      FSet.filter (fun y => G.carrier.elems.any (fun g => decide (ψ.act g x = y))) X

    /-- `y ∈ Orb(x)` si y solo si existe `g ∈ G` tal que `ψ(g, x) = y`. -/
    theorem mem_orb_iff
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        {G : FinGroup α} {X : FSet β}
        (ψ : GroupAction G X) (x y : β) (hx : x ∈ X.elems) :
        y ∈ (ψ.orb x).elems ↔ ∃ g, g ∈ G.carrier.elems ∧ ψ.act g x = y := by
      constructor
      · intro hy
        have hf := List.mem_filter.mp hy
        rw [List.any_eq_true] at hf
        obtain ⟨_, g, hg, hd⟩ := hf
        exact ⟨g, hg, by rwa [decide_eq_true_eq] at hd⟩
      · rintro ⟨g, hg, heq⟩
        exact List.mem_filter.mpr
          ⟨heq ▸ ψ.act_closed g x hg hx,
           List.any_eq_true.mpr ⟨g, hg, decide_eq_true_eq.mpr heq⟩⟩

    /-!
    # § 3. Estabilizador de un elemento
    -/

    /-- El estabilizador de `x` en `G`:
        `Stab(x) = { g ∈ G | ψ(g, x) = x }`. -/
    def GroupAction.stab
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        {G : FinGroup α} {X : FSet β}
        (ψ : GroupAction G X) (x : β) (hx : x ∈ X.elems) : Subgroup G where
      carrier := FSet.filter (fun g => decide (ψ.act g x = x)) G.carrier
      nonempty := ⟨G.id, List.mem_filter.mpr ⟨G.id_in, decide_eq_true_eq.mpr (ψ.act_id x hx)⟩⟩
      subset := fun a ha => (List.mem_filter.mp ha).1
      op_closed := fun a b ha hb => by
        have ⟨ha_mem, ha_fix⟩ := List.mem_filter.mp ha
        have ⟨hb_mem, hb_fix⟩ := List.mem_filter.mp hb
        rw [decide_eq_true_eq] at ha_fix hb_fix
        exact List.mem_filter.mpr
          ⟨op_mem G ha_mem hb_mem,
           decide_eq_true_eq.mpr (by
            rw [← ψ.act_compat a b x ha_mem hb_mem hx, hb_fix, ha_fix])⟩
      id_in := List.mem_filter.mpr ⟨G.id_in, decide_eq_true_eq.mpr (ψ.act_id x hx)⟩
      inv_closed := fun a ha => by
        have ⟨ha_mem, ha_fix⟩ := List.mem_filter.mp ha
        rw [decide_eq_true_eq] at ha_fix
        exact List.mem_filter.mpr
          ⟨inv_mem G ha_mem,
           decide_eq_true_eq.mpr (by
            have h := ψ.act_compat (G.inv a) a x (inv_mem G ha_mem) ha_mem hx
            rw [(G.op_inv a ha_mem).2, ψ.act_id x hx] at h
            rw [ha_fix] at h; exact h)⟩

    /-!
    # § 4. Teorema Órbita–Estabilizador

    `|Orb(x)| · |Stab(x)| = |G|`

    Requiere cosets y el isomorfismo G/Stab(x) ≅ Orb(x).
    La prueba completa depende de Sylow/Cosets.lean.
    -/

    /-- Teorema órbita–estabilizador: `|Orb(x)| · |Stab(x)| = |G|`. -/
    theorem orbit_stabilizer
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        {G : FinGroup α} {X : FSet β}
        (ψ : GroupAction G X) (x : β) (hx : x ∈ X.elems) :
        mul (ψ.orb x).card (ψ.stab x hx).carrier.card = G.carrier.card :=
      by
        let S := ψ.stab x hx
        let f : MapOn G.carrier (ψ.orb x) := {
          toFun := fun g => ψ.act g x
          map_carrier := fun g hg =>
            (mem_orb_iff ψ x (ψ.act g x) hx).mpr ⟨g, hg, rfl⟩
        }

        have h_fiber : ∀ y, y ∈ (ψ.orb x).elems → (f.fiber y).card = S.carrier.card := by
          intro y hy
          obtain ⟨gy, hgy, hgyx⟩ := (mem_orb_iff ψ x y hx).mp hy

          have h_fiber_eq_coset : f.fiber y = leftCoset G S gy := by
            apply FSet.eq_of_mem_iff'
            intro g
            constructor
            · intro hgFib
              have hgData := (MapOn.mem_fiber_iff f y g).mp hgFib
              have hg_mem : g ∈ G.carrier.elems := hgData.1
              have hg_eq : ψ.act g x = y := hgData.2

              let h : α := G.op (G.inv gy) g
              have hhG : h ∈ G.carrier.elems :=
                op_mem G (inv_mem G hgy) hg_mem
              have hh_fix : ψ.act h x = x := by
                have hInvY : ψ.act (G.inv gy) y = x := by
                  calc
                    ψ.act (G.inv gy) y = ψ.act (G.inv gy) (ψ.act gy x) := by
                      rw [← hgyx]
                    _ = ψ.act (G.op (G.inv gy) gy) x := by
                      rw [ψ.act_compat (G.inv gy) gy x (inv_mem G hgy) hgy hx]
                    _ = ψ.act G.id x := by rw [(G.op_inv gy hgy).2]
                    _ = x := ψ.act_id x hx
                calc
                  ψ.act h x = ψ.act (G.inv gy) (ψ.act g x) := by
                    unfold h
                    rw [ψ.act_compat (G.inv gy) g x (inv_mem G hgy) hg_mem hx]
                  _ = ψ.act (G.inv gy) y := by rw [hg_eq]
                  _ = x := hInvY

              have hhS : h ∈ S.carrier.elems := by
                exact List.mem_filter.mpr ⟨hhG, decide_eq_true_eq.mpr hh_fix⟩

              have hrep : G.op gy h = g := by
                calc
                  G.op gy h = G.op gy (G.op (G.inv gy) g) := by rfl
                  _ = G.op (G.op gy (G.inv gy)) g := by
                    rw [← G.op_assoc gy (G.inv gy) g hgy (inv_mem G hgy) hg_mem]
                  _ = G.op G.id g := by rw [(G.op_inv gy hgy).1]
                  _ = g := by simpa using (G.op_id g hg_mem).2

              exact (mem_leftCoset_iff G S gy g hgy).mpr ⟨h, hhS, hrep⟩

            · intro hgCos
              obtain ⟨h, hhS, hEq⟩ := (mem_leftCoset_iff G S gy g hgy).mp hgCos
              have hhG : h ∈ G.carrier.elems := S.subset h hhS
              have hh_fix : ψ.act h x = x := by
                exact decide_eq_true_eq.mp ((List.mem_filter.mp hhS).2)
              have hg_mem : g ∈ G.carrier.elems := by
                rw [← hEq]
                exact op_mem G hgy hhG
              have hact : ψ.act g x = y := by
                rw [← hEq,
                    ← ψ.act_compat gy h x hgy hhG hx,
                    hh_fix,
                    hgyx]
              exact (MapOn.mem_fiber_iff f y g).mpr ⟨hg_mem, hact⟩

          calc
            (f.fiber y).card = (leftCoset G S gy).card := by rw [h_fiber_eq_coset]
            _ = S.carrier.card := coset_card_eq_subgroup_card G S gy hgy

        have h_card :=
          FSetFunction.card_eq_mul_of_uniform_fibers f S.carrier.card h_fiber

        calc
          mul (ψ.orb x).card S.carrier.card = mul S.carrier.card (ψ.orb x).card := by
            rw [mul_comm]
          _ = G.carrier.card := Eq.symm h_card

    /-!
    # § 5. Ecuación de clases

    `|G| = |Z(G)| + Σ [G : C_G(x)]`
    donde la suma recorre representantes de órbitas no triviales.

    Estructura pendiente; requiere la fórmula de Burnside o la ecuación de clases
    para continuar hacia los teoremas de Sylow.
    -/

    /-- Partición de X en órbitas. -/
    theorem orbits_partition
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        {G : FinGroup α} {X : FSet β}
        (ψ : GroupAction G X) :
        -- Toda x ∈ X pertenece a exactamente una órbita
        (∀ x, x ∈ X.elems → ∃ y, y ∈ X.elems ∧ x ∈ (ψ.orb y).elems) ∧
        -- Dos órbitas son iguales o disjuntas
        (∀ x y, x ∈ X.elems → y ∈ X.elems →
          (ψ.orb x).elems = (ψ.orb y).elems ∨
          ∀ z, z ∉ (ψ.orb x).elems ∨ z ∉ (ψ.orb y).elems) := by
      constructor
      · intro x hx
        exact ⟨x, hx, (mem_orb_iff ψ x x hx).mpr ⟨G.id, G.id_in, ψ.act_id x hx⟩⟩
      · intro x y hx hy
        rcases Classical.em (∃ z, z ∈ (ψ.orb x).elems ∧ z ∈ (ψ.orb y).elems) with h | h
        · left
          obtain ⟨z, hzx, hzy⟩ := h
          obtain ⟨g₁, hg₁, hg₁_eq⟩ := (mem_orb_iff ψ x z hx).mp hzx
          obtain ⟨g₂, hg₂, hg₂_eq⟩ := (mem_orb_iff ψ y z hy).mp hzy
          have hxy_mem : x ∈ (ψ.orb y).elems := by
            refine (mem_orb_iff ψ y x hy).mpr ?_
            refine ⟨G.op (G.inv g₁) g₂, op_mem G (inv_mem G hg₁) hg₂, ?_⟩
            have hzx' : ψ.act g₁ x = ψ.act g₂ y := by
              exact hg₁_eq.trans hg₂_eq.symm
            calc
              ψ.act (G.op (G.inv g₁) g₂) y = ψ.act (G.inv g₁) (ψ.act g₂ y) := by
                rw [ψ.act_compat (G.inv g₁) g₂ y (inv_mem G hg₁) hg₂ hy]
              _ = ψ.act (G.inv g₁) (ψ.act g₁ x) := by rw [hzx']
              _ = ψ.act (G.op (G.inv g₁) g₁) x := by
                rw [ψ.act_compat (G.inv g₁) g₁ x (inv_mem G hg₁) hg₁ hx]
              _ = ψ.act G.id x := by rw [(G.op_inv g₁ hg₁).2]
              _ = x := ψ.act_id x hx

          have hyx_mem : y ∈ (ψ.orb x).elems := by
            refine (mem_orb_iff ψ x y hx).mpr ?_
            refine ⟨G.op (G.inv g₂) g₁, op_mem G (inv_mem G hg₂) hg₁, ?_⟩
            have hzy' : ψ.act g₂ y = ψ.act g₁ x := by
              exact hg₂_eq.trans hg₁_eq.symm
            calc
              ψ.act (G.op (G.inv g₂) g₁) x = ψ.act (G.inv g₂) (ψ.act g₁ x) := by
                rw [ψ.act_compat (G.inv g₂) g₁ x (inv_mem G hg₂) hg₁ hx]
              _ = ψ.act (G.inv g₂) (ψ.act g₂ y) := by rw [hzy']
              _ = ψ.act (G.op (G.inv g₂) g₂) y := by
                rw [ψ.act_compat (G.inv g₂) g₂ y (inv_mem G hg₂) hg₂ hy]
              _ = ψ.act G.id y := by rw [(G.op_inv g₂ hg₂).2]
              _ = y := ψ.act_id y hy

          have horb_eq : ψ.orb x = ψ.orb y := by
            apply FSet.eq_of_mem_iff'
            intro w
            constructor
            · intro hwx
              obtain ⟨g, hg, hgw⟩ := (mem_orb_iff ψ x w hx).mp hwx
              obtain ⟨k, hk, hkx⟩ := (mem_orb_iff ψ y x hy).mp hxy_mem
              exact (mem_orb_iff ψ y w hy).mpr
                ⟨G.op g k, op_mem G hg hk, by
                  rw [← ψ.act_compat g k y hg hk hy, hkx, hgw]⟩
            · intro hwy
              obtain ⟨g, hg, hgw⟩ := (mem_orb_iff ψ y w hy).mp hwy
              obtain ⟨k, hk, hky⟩ := (mem_orb_iff ψ x y hx).mp hyx_mem
              exact (mem_orb_iff ψ x w hx).mpr
                ⟨G.op g k, op_mem G hg hk, by
                  rw [← ψ.act_compat g k x hg hk hx, hky, hgw]⟩

          exact congrArg FSet.elems horb_eq
        · right
          intro z
          rcases Classical.em (z ∈ (ψ.orb x).elems) with hzx | hzx
          · exact Or.inr (fun hzy => absurd ⟨z, hzx, hzy⟩ h)
          · exact Or.inl hzx


    -- ── Auxiliar: partición de card por predicado booleano ────────────────────────
    private theorem card_split_filter (q : ℕ₀ → Bool) (s : ℕ₀FSet) :
        s.card = add (FSet.filter q s).card ((FSet.filter (fun x => !q x) s).card) := by
      suffices h : ∀ (l : List ℕ₀),
          lengthₚ l = add (lengthₚ (l.filter q)) (lengthₚ (l.filter (fun x => !q x))) by
        simpa [FSet.card, FSet.filter] using h s.elems
      intro l; induction l with
      | nil => simp [lengthₚ_nil, zero_add]
      | cons x xs ih =>
        cases hq : q x with
        | false =>
          have h1 : (x :: xs).filter q = xs.filter q := by simp [hq]
          have h2 : (x :: xs).filter (fun y => !q y) = x :: xs.filter (fun y => !q y) := by simp [hq]
          simp only [h1, h2, lengthₚ_cons, ih, ← add_succ]
        | true =>
          have h1 : (x :: xs).filter q = x :: xs.filter q := by simp [hq]
          have h2 : (x :: xs).filter (fun y => !q y) = xs.filter (fun y => !q y) := by simp [hq]
          simp only [h1, h2, lengthₚ_cons, ih, ← succ_add]

    -- ── Auxiliar: conmutatividad de filtros ───────────────────────────────────────
    private theorem filter_filter_card (p q : ℕ₀ → Bool) (s : ℕ₀FSet) :
        (FSet.filter p (FSet.filter q s)).card = (FSet.filter q (FSet.filter p s)).card := by
      congr 1
      apply FSet.eq_of_mem_iff
      intro z
      simp only [FSet.filter, List.mem_filter]
      exact ⟨fun ⟨⟨hz, hq⟩, hp⟩ => ⟨⟨hz, hp⟩, hq⟩,
             fun ⟨⟨hz, hp⟩, hq⟩ => ⟨⟨hz, hq⟩, hp⟩⟩

    -- ── Acción de conjugación (standalone) ───────────────────────────────────────
    def conjugAction (G : FinGroup ℕ₀) : GroupAction G G.carrier where
      act := fun g x => G.op (G.op g x) (G.inv g)
      act_closed := fun g x hg hx => op_mem G (op_mem G hg hx) (inv_mem G hg)
      act_id := fun x hx => by
        show G.op (G.op G.id x) (G.inv G.id) = x
        rw [inv_id_eq G, (G.op_id x hx).2, (G.op_id x hx).1]
      act_compat := fun g h x hg hh hx => by
        show G.op (G.op g (G.op (G.op h x) (G.inv h))) (G.inv g) =
             G.op (G.op (G.op g h) x) (G.inv (G.op g h))
        rw [inv_op_eq G hg hh]
        have hghx : G.op (G.op g h) x ∈ G.carrier.elems := op_mem G (op_mem G hg hh) hx
        have hhx  : G.op h x ∈ G.carrier.elems := op_mem G hh hx
        have hhinv : G.inv h ∈ G.carrier.elems := inv_mem G hh
        have hginv : G.inv g ∈ G.carrier.elems := inv_mem G hg
        calc G.op (G.op g (G.op (G.op h x) (G.inv h))) (G.inv g)
            = G.op (G.op (G.op g (G.op h x)) (G.inv h)) (G.inv g) := by
                  rw [← G.op_assoc g (G.op h x) (G.inv h) hg hhx hhinv]
          _ = G.op (G.op (G.op (G.op g h) x) (G.inv h)) (G.inv g) := by
                  rw [← G.op_assoc g h x hg hh hx]
          _ = G.op (G.op (G.op g h) x) (G.op (G.inv h) (G.inv g)) :=
                  G.op_assoc _ _ _ hghx hhinv hginv

    -- ── isFixed predicate ─────────────────────────────────────────────────────────
    private def isFixed (G : FinGroup ℕ₀) : ℕ₀ → Bool :=
      fun x => G.carrier.elems.all (fun g => decide ((conjugAction G).act g x = x))

    -- ── Z(G) = puntos fijos de conjugAction ──────────────────────────────────────
    private theorem isFixed_iff_center (G : FinGroup ℕ₀) (x : ℕ₀) (hx : x ∈ G.carrier.elems) :
        isFixed G x = true ↔ x ∈ (center G).carrier.elems := by
      simp only [isFixed, List.all_eq_true, decide_eq_true_eq]
      constructor
      · intro h_all
        rw [mem_center_iff]
        refine ⟨hx, fun g hg => ?_⟩
        have hact : G.op (G.op g x) (G.inv g) = x := h_all g hg
        have hgx : G.op g x ∈ G.carrier.elems := op_mem G hg hx
        have hginv : G.inv g ∈ G.carrier.elems := inv_mem G hg
        calc G.op x g
            = G.op (G.op (G.op g x) (G.inv g)) g := by rw [hact]
          _ = G.op (G.op g x) (G.op (G.inv g) g) :=
                  G.op_assoc (G.op g x) (G.inv g) g hgx hginv hg
          _ = G.op (G.op g x) G.id := by rw [(G.op_inv g hg).2]
          _ = G.op g x := (G.op_id (G.op g x) hgx).1
      · intro hmem g hg
        obtain ⟨_, hcomm⟩ := (mem_center_iff G x).mp hmem
        show G.op (G.op g x) (G.inv g) = x
        have hgx := op_mem G hg hx
        have hginv := inv_mem G hg
        rw [← hcomm g hg, G.op_assoc x g (G.inv g) hx hg hginv,
            (G.op_inv g hg).1, (G.op_id x hx).1]

    -- ── |Z(G)| = card of fixed-point filter ──────────────────────────────────────
    private theorem center_card_eq_fixed (G : FinGroup ℕ₀) :
        (center G).carrier.card = (FSet.filter (isFixed G) G.carrier).card := by
      congr 1
      apply FSet.eq_of_mem_iff
      intro z
      simp only [FSet.filter, List.mem_filter]
      constructor
      · intro hz
        exact ⟨(center G).subset z hz, (isFixed_iff_center G z ((center G).subset z hz)).mpr hz⟩
      · intro ⟨hz_G, hfixed⟩
        exact (isFixed_iff_center G z hz_G).mp hfixed

    -- ── Ecuación de clases: forma de split ───────────────────────────────────────
    /-- La primera forma de la ecuación de clases: el cardinal de G se parte en
        el cardinal de Z(G) y el cardinal de los elementos no centrales. -/
    theorem class_equation_split (G : FinGroup ℕ₀) :
        G.carrier.card =
          add (center G).carrier.card
              (FSet.filter (fun x => !(isFixed G x)) G.carrier).card := by
      rw [center_card_eq_fixed]
      exact card_split_filter (isFixed G) G.carrier

    -- ── isFixed se preserva bajo conjugación ─────────────────────────────────────
    private theorem isFixed_conj (G : FinGroup ℕ₀) (g y : ℕ₀)
        (hg : g ∈ G.carrier.elems) (hy : y ∈ G.carrier.elems) :
        isFixed G ((conjugAction G).act g y) = isFixed G y := by
      have hact_mem : (conjugAction G).act g y ∈ G.carrier.elems :=
        (conjugAction G).act_closed g y hg hy
      cases hfy : isFixed G y with
      | true =>
        -- y ∈ Z(G), so conj(g,y) = y
        simp only [isFixed, List.all_eq_true, decide_eq_true_eq] at hfy ⊢
        intro k hk
        have hconj_eq : (conjugAction G).act g y = y := hfy g hg
        rw [hconj_eq]; exact hfy k hk
      | false =>
        -- conj(g,y) ∉ Z(G): contrapositive — if conj(g,y) ∈ Z(G) then y ∈ Z(G)
        cases h_conj : isFixed G ((conjugAction G).act g y) with
        | false => rfl
        | true =>
          exfalso
          simp only [isFixed, List.all_eq_true, decide_eq_true_eq] at h_conj
          -- h_conj : ∀ k ∈ G, act k (conj g y) = conj g y
          -- y = act(g⁻¹, conj g y)
          have hy_eq : y = (conjugAction G).act (G.inv g) ((conjugAction G).act g y) := by
            have h := (conjugAction G).act_compat (G.inv g) g y (inv_mem G hg) hg hy
            rw [(G.op_inv g hg).2, (conjugAction G).act_id y hy] at h
            exact h.symm
          -- act k y = act(k*g⁻¹, conj g y) = conj g y for all k ∈ G
          have h_all_z : ∀ k ∈ G.carrier.elems,
              (conjugAction G).act k y = (conjugAction G).act g y := by
            intro k hk
            have h_compat := (conjugAction G).act_compat k (G.inv g)
                  ((conjugAction G).act g y) hk (inv_mem G hg) hact_mem
            rw [← hy_eq] at h_compat
            rw [h_compat]
            exact h_conj (G.op k (G.inv g)) (op_mem G hk (inv_mem G hg))
          -- Setting k = id: y = conj g y
          have hy_eq_z : y = (conjugAction G).act g y := by
            have := h_all_z G.id G.id_in
            rwa [(conjugAction G).act_id y hy] at this
          -- y is also fixed (since act k y = conj g y = y for all k)
          have hy_fixed : isFixed G y = true := by
            simp only [isFixed, List.all_eq_true, decide_eq_true_eq]
            intro k hk
            rw [hy_eq_z]; exact h_conj k hk
          simp [hfy] at hy_fixed

    -- ── Descomposición orbital de subconjunto G-invariante ───────────────────────
    private theorem nonfixed_orb_decomp (G : FinGroup ℕ₀) :
        ∀ (n : Nat) (X : ℕ₀FSet),
          X.elems.length ≤ n →
          (∀ y ∈ X.elems, y ∈ G.carrier.elems) →
          (∀ y ∈ X.elems, ∀ g ∈ G.carrier.elems, (conjugAction G).act g y ∈ X.elems) →
          ∃ reps : List ℕ₀,
            (∀ r ∈ reps, r ∈ X.elems) ∧
            X.card = sum_list (reps.map (fun r => ((conjugAction G).orb r).card)) := by
      intro n; induction n with
      | zero =>
        intro X hlen _ _
        have hnil : X.elems = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
        refine ⟨[], fun r hr => absurd hr (by simp), ?_⟩
        simp only [List.map_nil, sum_list_nil]
        show lengthₚ X.elems = 𝟘; rw [hnil]; exact lengthₚ_nil
      | succ n' ih =>
        intro X hlen h_sub h_closed
        cases hX : X.elems with
        | nil =>
          refine ⟨[], fun r hr => absurd hr (by simp), ?_⟩
          simp only [List.map_nil, sum_list_nil]
          show lengthₚ X.elems = 𝟘; rw [hX]; exact lengthₚ_nil
        | cons x₀ rest =>
          have hx₀ : x₀ ∈ X.elems := by rw [hX]; exact List.Mem.head rest
          have hx₀_G : x₀ ∈ G.carrier.elems := h_sub x₀ hx₀
          -- Órbita-predicado para x₀
          let inOrb₀ : ℕ₀ → Bool :=
            fun z => G.carrier.elems.any (fun g => decide ((conjugAction G).act g x₀ = z))
          have hx₀_inOrb : inOrb₀ x₀ = true := by
            simp only [inOrb₀, List.any_eq_true, decide_eq_true_eq]
            exact ⟨G.id, G.id_in, (conjugAction G).act_id x₀ hx₀_G⟩
          -- X' = X sin la órbita de x₀
          let X' := FSet.filter (fun y => !inOrb₀ y) X
          have hfilt_x₀ : X'.elems = rest.filter (fun y => !inOrb₀ y) := by
            show X.elems.filter (fun y => !inOrb₀ y) = rest.filter (fun y => !inOrb₀ y)
            rw [hX]; simp [hx₀_inOrb]
          have hX'_len : X'.elems.length ≤ n' := by
            rw [hfilt_x₀]
            apply Nat.le_trans (List.length_filter_le _ _)
            have h := hlen; rw [hX] at h
            exact Nat.le_of_succ_le_succ h
          -- |filter inOrb₀ X| = |orb x₀|
          have h_inOrb_eq_orb :
              (FSet.filter inOrb₀ X).card = ((conjugAction G).orb x₀).card := by
            congr 1; apply FSet.eq_of_mem_iff; intro z
            constructor
            · intro hz
              simp only [FSet.filter, List.mem_filter, inOrb₀,
                         List.any_eq_true, decide_eq_true_eq] at hz
              obtain ⟨hz_X, g, hg, hgz⟩ := hz
              exact (mem_orb_iff (conjugAction G) x₀ z hx₀_G).mpr ⟨g, hg, hgz⟩
            · intro hz_orb
              obtain ⟨g, hg, hgz⟩ := (mem_orb_iff (conjugAction G) x₀ z hx₀_G).mp hz_orb
              simp only [FSet.filter, List.mem_filter, inOrb₀,
                         List.any_eq_true, decide_eq_true_eq]
              exact ⟨hgz ▸ h_closed x₀ hx₀ g hg, g, hg, hgz⟩
          -- |X| = |orb x₀| + |X'|
          have h_X_split : X.card = add ((conjugAction G).orb x₀).card X'.card := by
            have h_split := card_split_filter inOrb₀ X
            rw [h_inOrb_eq_orb] at h_split; exact h_split
          -- X' es G-invariante
          have hX'_sub : ∀ y ∈ X'.elems, y ∈ G.carrier.elems :=
            fun y hy => h_sub y (List.mem_filter.mp hy).1
          have hX'_closed : ∀ y ∈ X'.elems, ∀ g ∈ G.carrier.elems,
              (conjugAction G).act g y ∈ X'.elems := by
            intro y hy g hg
            simp only [X', FSet.filter] at hy ⊢
            obtain ⟨hy_X, hy_nOrb⟩ := List.mem_filter.mp hy
            have hy_false : inOrb₀ y = false := by
              cases h : inOrb₀ y with | false => rfl | true => simp [h] at hy_nOrb
            refine List.mem_filter.mpr ⟨h_closed y hy_X g hg, ?_⟩
            cases h_try : inOrb₀ ((conjugAction G).act g y) with
            | false => simp
            | true =>
              exfalso
              simp only [inOrb₀, List.any_eq_true, decide_eq_true_eq] at h_try
              obtain ⟨h, hh_G, hh_eq⟩ := h_try
              have hginv := inv_mem G hg; have hy_G := h_sub y hy_X
              have h_reaches : (conjugAction G).act (G.op (G.inv g) h) x₀ = y := by
                rw [← (conjugAction G).act_compat (G.inv g) h x₀ hginv hh_G hx₀_G,
                    hh_eq, (conjugAction G).act_compat (G.inv g) g y hginv hg hy_G,
                    (G.op_inv g hg).2, (conjugAction G).act_id y hy_G]
              have h_inOrb_y : inOrb₀ y = true := by
                simp only [inOrb₀, List.any_eq_true, decide_eq_true_eq]
                exact ⟨G.op (G.inv g) h, op_mem G hginv hh_G, h_reaches⟩
              simp [hy_false] at h_inOrb_y
          -- IH
          obtain ⟨reps', hrall', hrsum'⟩ := ih X' hX'_len hX'_sub hX'_closed
          -- Concluir: reps = x₀ :: reps'
          refine ⟨x₀ :: reps',
            fun r hr => by
              rcases List.mem_cons.mp hr with rfl | hr'
              · exact hX ▸ hx₀
              · exact hX ▸ (List.mem_filter.mp (hrall' r hr')).1,
            by rw [List.map_cons, sum_list_cons, ← hrsum', ← h_X_split]⟩

    -- ── Ecuación de clases ────────────────────────────────────────────────────────
    /-- **Ecuación de clases**: `|G| = |Z(G)| + Σ |Orb(r)|` donde la suma corre
        sobre representantes de órbitas de conjugación fuera del centro. -/
    theorem class_equation (G : FinGroup ℕ₀) :
        ∃ reps : List ℕ₀,
          (∀ r ∈ reps, r ∈ G.carrier.elems ∧ r ∉ (center G).carrier.elems) ∧
          G.carrier.card =
            add (center G).carrier.card
                (sum_list (reps.map (fun r => ((conjugAction G).orb r).card))) := by
      let X := FSet.filter (fun x => !isFixed G x) G.carrier
      have hX_sub : ∀ y ∈ X.elems, y ∈ G.carrier.elems :=
        fun y hy => (List.mem_filter.mp hy).1
      have hX_closed : ∀ y ∈ X.elems, ∀ g ∈ G.carrier.elems,
          (conjugAction G).act g y ∈ X.elems := by
        intro y hy g hg
        simp only [X, FSet.filter, List.mem_filter] at hy ⊢
        obtain ⟨hy_G, hy_nf⟩ := hy
        exact ⟨(conjugAction G).act_closed g y hg hy_G,
               isFixed_conj G g y hg hy_G ▸ hy_nf⟩
      obtain ⟨reps, hrall, hrsum⟩ :=
        nonfixed_orb_decomp G X.elems.length X (Nat.le_refl _) hX_sub hX_closed
      refine ⟨reps, fun r hr => ?_, ?_⟩
      · -- r ∈ G y r ∉ Z(G)
        have hr_X := hrall r hr
        obtain ⟨hr_G, hr_nf⟩ := List.mem_filter.mp hr_X
        refine ⟨hr_G, fun hr_center => ?_⟩
        -- isFixed G r = false (from hr_nf), but r ∈ Z(G) → isFixed G r = true
        have hr_fixed : isFixed G r = true := (isFixed_iff_center G r hr_G).mpr hr_center
        simp [hr_fixed] at hr_nf
      · -- |G| = |Z(G)| + sum
        rw [class_equation_split, hrsum]

  end Action
end Peano

export Peano.Action (
  GroupAction
  GroupAction.orb
  mem_orb_iff
  GroupAction.stab
  orbit_stabilizer
  orbits_partition
  conjugAction
  class_equation_split
  class_equation
)
