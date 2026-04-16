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
