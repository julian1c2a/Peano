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

set_option autoImplicit false

namespace Peano
  namespace GroupTheory

    open Peano.FSet
    open Peano.FSetFunction
    open Peano.Group
    open Peano.Mul

    /-!
    # § 1. GroupAction — acción (izquierda) de un FinGroup sobre un ℕ₀FSet
    -/

    /-- Una acción (izquierda) de `G` sobre un conjunto finito `X`:
        un homomorfismo de grupos de `G` al grupo simétrico de `X`,
        equivalente a una función `α : G × X → X` que satisface:
        - `α(e, x) = x`  para todo `x`,
        - `α(g, α(h, x)) = α(g·h, x)`  para todo `g, h, x`. -/
    structure GroupAction (G : FinGroup) (X : ℕ₀FSet) where
      /-- La función de acción: dados `g ∈ G` y `x ∈ X`, devuelve `g·x ∈ X`. -/
      act        : ℕ₀ → ℕ₀ → ℕ₀
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
    def GroupAction.orb {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) (x : ℕ₀) : ℕ₀FSet :=
      ℕ₀FSet.filter (fun y => G.carrier.elems.any (fun g => decide (α.act g x = y))) X

    /-- `y ∈ Orb(x)` si y solo si existe `g ∈ G` tal que `α(g, x) = y`. -/
    theorem mem_orb_iff {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) (x y : ℕ₀) (hx : x ∈ X.elems) :
        y ∈ (α.orb x).elems ↔ ∃ g, g ∈ G.carrier.elems ∧ α.act g x = y := by
      constructor
      · intro hy
        have hf := List.mem_filter.mp hy
        rw [List.any_eq_true] at hf
        obtain ⟨_, g, hg, hd⟩ := hf
        exact ⟨g, hg, by rwa [decide_eq_true_eq] at hd⟩
      · rintro ⟨g, hg, heq⟩
        exact List.mem_filter.mpr
          ⟨heq ▸ α.act_closed g x hg hx,
           List.any_eq_true.mpr ⟨g, hg, decide_eq_true_eq.mpr heq⟩⟩

    /-!
    # § 3. Estabilizador de un elemento
    -/

    /-- El estabilizador de `x` en `G`:
        `Stab(x) = { g ∈ G | α(g, x) = x }`. -/
    def GroupAction.stab {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) (x : ℕ₀) (hx : x ∈ X.elems) : Subgroup G where
      carrier := ℕ₀FSet.filter (fun g => decide (α.act g x = x)) G.carrier
      nonempty := ⟨G.id, List.mem_filter.mpr ⟨G.id_in, decide_eq_true_eq.mpr (α.act_id x hx)⟩⟩
      subset := fun a ha => (List.mem_filter.mp ha).1
      op_closed := fun a b ha hb => by
        have ⟨ha_mem, ha_fix⟩ := List.mem_filter.mp ha
        have ⟨hb_mem, hb_fix⟩ := List.mem_filter.mp hb
        rw [decide_eq_true_eq] at ha_fix hb_fix
        exact List.mem_filter.mpr
          ⟨op_mem G ha_mem hb_mem,
           decide_eq_true_eq.mpr (by
            rw [← α.act_compat a b x ha_mem hb_mem hx, hb_fix, ha_fix])⟩
      id_in := List.mem_filter.mpr ⟨G.id_in, decide_eq_true_eq.mpr (α.act_id x hx)⟩
      inv_closed := fun a ha => by
        have ⟨ha_mem, ha_fix⟩ := List.mem_filter.mp ha
        rw [decide_eq_true_eq] at ha_fix
        exact List.mem_filter.mpr
          ⟨inv_mem G ha_mem,
           decide_eq_true_eq.mpr (by
            have h := α.act_compat (G.inv a) a x (inv_mem G ha_mem) ha_mem hx
            rw [(G.op_inv a ha_mem).2, α.act_id x hx] at h
            rw [ha_fix] at h; exact h)⟩

    /-!
    # § 4. Teorema Órbita–Estabilizador

    `|Orb(x)| · |Stab(x)| = |G|`

    Requiere cosets y el isomorfismo G/Stab(x) ≅ Orb(x).
    La prueba completa depende de Sylow/Cosets.lean.
    -/

    /-- Teorema órbita–estabilizador: `|Orb(x)| · |Stab(x)| = |G|`. -/
    theorem orbit_stabilizer {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) (x : ℕ₀) (hx : x ∈ X.elems) :
        mul (α.orb x).card (α.stab x hx).carrier.card = G.carrier.card :=
      sorry  -- requiere Lagrange + biyección G/Stab(x) ≅ Orb(x)

    /-!
    # § 5. Ecuación de clases

    `|G| = |Z(G)| + Σ [G : C_G(x)]`
    donde la suma recorre representantes de órbitas no triviales.

    Estructura pendiente; requiere la fórmula de Burnside o la ecuación de clases
    para continuar hacia los teoremas de Sylow.
    -/

    /-- Partición de X en órbitas. -/
    theorem orbits_partition {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) :
        -- Toda x ∈ X pertenece a exactamente una órbita
        (∀ x, x ∈ X.elems → ∃ y, y ∈ X.elems ∧ x ∈ (α.orb y).elems) ∧
        -- Dos órbitas son iguales o disjuntas
        (∀ x y, x ∈ X.elems → y ∈ X.elems →
          (α.orb x).elems = (α.orb y).elems ∨
          ∀ z, z ∉ (α.orb x).elems ∨ z ∉ (α.orb y).elems) := by
      constructor
      · -- Parte 1: x ∈ orb(x) vía α(e, x) = x
        intro x hx
        exact ⟨x, hx, (mem_orb_iff α x x hx).mpr ⟨G.id, G.id_in, α.act_id x hx⟩⟩
      · -- Parte 2: orb(x) = orb(y)  o  disjuntas
        -- Si ∃ z ∈ orb(x) ∩ orb(y), entonces orb(x) = orb(y);
        -- si no, son disjuntas.
        intro x y hx hy
        rcases Classical.em (∃ z, z ∈ (α.orb x).elems ∧ z ∈ (α.orb y).elems) with h | h
        · left
          obtain ⟨z, hzx, hzy⟩ := h
          obtain ⟨g₁, hg₁, hg₁_eq⟩ := (mem_orb_iff α x z hx).mp hzx
          obtain ⟨g₂, hg₂, hg₂_eq⟩ := (mem_orb_iff α y z hy).mp hzy
          sorry  -- requiere pairwise-sorted extensionality
        · right
          intro z
          rcases Classical.em (z ∈ (α.orb x).elems) with hzx | hzx
          · exact Or.inr (fun hzy => absurd ⟨z, hzx, hzy⟩ h)
          · exact Or.inl hzx

  end GroupTheory
end Peano
