import Peano.Prelim
import Peano.PeanoNat
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
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
    open Peano.Sub
    open Peano.StrictOrder

    /-!
    # § 4. Estructura de Grupo Finito
    -/

    /-- Grupo finito sobre un tipo `α` con igualdad decidible, orden estricto
        y orden lineal estricto. El portador es un `FSet α`. -/
    structure FinGroup (α : Type) [DecidableEq α] [LT α] [StrictLinearOrder α] where
      carrier : FSet α
      op : BinOpOn carrier
      id : α
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

    /-- Alias de compatibilidad hacia atrás: `ℕ₀FinGroup = FinGroup ℕ₀`. -/
    abbrev ℕ₀FinGroup := FinGroup ℕ₀

    /--
    En cualquier `FinGroup`, el elemento neutro es único.
    -/
    theorem id_unique {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (e' : α)
        (h_e'_in : e' ∈ G.carrier.elems)
        (h_is_id : ∀ a, a ∈ G.carrier.elems → G.op a e' = a ∧ G.op e' a = a) :
        e' = G.id := by
      let h_id_op_e' := (h_is_id G.id G.id_in).left
      let h_e'_op_id := (G.op_id e' h_e'_in).right
      exact h_e'_op_id.symm.trans h_id_op_e'

    /-!
    # § 4b. Lemas auxiliares de grupo
    -/

    /-- Pertenencia del inverso al carrier. -/
    theorem inv_mem {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {a : α} (ha : a ∈ G.carrier.elems) :
        G.inv a ∈ G.carrier.elems :=
      G.inv.map_carrier a ha

    /-- Pertenencia del producto al carrier. -/
    theorem op_mem {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {a b : α}
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems) :
        G.op a b ∈ G.carrier.elems :=
      G.op.map_carrier a b ha hb

    /-- Cancelación izquierda: `a·x = a·y → x = y`. -/
    theorem op_cancel_left {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {a x y : α}
        (ha : a ∈ G.carrier.elems) (hx : x ∈ G.carrier.elems) (hy : y ∈ G.carrier.elems)
        (h : G.op a x = G.op a y) : x = y := by
      have ha' := inv_mem G ha
      have h1 : G.op (G.inv a) (G.op a x) = G.op (G.inv a) (G.op a y) := by rw [h]
      rw [← G.op_assoc (G.inv a) a x ha' ha hx,
          ← G.op_assoc (G.inv a) a y ha' ha hy,
          (G.op_inv a ha).2, (G.op_id x hx).2, (G.op_id y hy).2] at h1
      exact h1

    /-- Cancelación derecha: `x·a = y·a → x = y`. -/
    theorem op_cancel_right {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {a x y : α}
        (ha : a ∈ G.carrier.elems) (hx : x ∈ G.carrier.elems) (hy : y ∈ G.carrier.elems)
        (h : G.op x a = G.op y a) : x = y := by
      have ha' := inv_mem G ha
      have h1 : G.op (G.op x a) (G.inv a) = G.op (G.op y a) (G.inv a) := by rw [h]
      rw [G.op_assoc x a (G.inv a) hx ha ha',
          G.op_assoc y a (G.inv a) hy ha ha',
          (G.op_inv a ha).1, (G.op_id x hx).1, (G.op_id y hy).1] at h1
      exact h1

    /-- `inv(inv(a)) = a`. -/
    theorem inv_inv_eq {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {a : α} (ha : a ∈ G.carrier.elems) :
        G.inv (G.inv a) = a := by
      apply op_cancel_right G (inv_mem G ha) (inv_mem G (inv_mem G ha)) ha
      rw [(G.op_inv (G.inv a) (inv_mem G ha)).2, (G.op_inv a ha).1]

    /-- `inv(id) = id`. -/
    theorem inv_id_eq {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) : G.inv G.id = G.id := by
      have h1 : G.op G.id (G.inv G.id) = G.id := (G.op_inv G.id G.id_in).1
      have h2 : G.op G.id (G.inv G.id) = G.inv G.id :=
        (G.op_id (G.inv G.id) (inv_mem G G.id_in)).2
      exact h2.symm.trans h1

    /-- `inv(a·b) = inv(b)·inv(a)`. -/
    theorem inv_op_eq {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {a b : α}
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
    theorem inv_unique {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {a b : α}
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
    def gpow {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) : ℕ₀ → α
      | .zero   => G.id
      | .succ n => G.op (gpow G g n) g

    @[simp] theorem gpow_zero {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) :
        gpow G g 𝟘 = G.id := rfl

    @[simp] theorem gpow_succ {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (n : ℕ₀) :
        gpow G g (σ n) = G.op (gpow G g n) g := rfl

    theorem gpow_one {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        gpow G g 𝟙 = g :=
      (G.op_id g hg).2

    /-- `g^n ∈ G` para todo `n`. -/
    theorem gpow_mem {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {g : α} (hg : g ∈ G.carrier.elems) :
        ∀ n : ℕ₀, gpow G g n ∈ G.carrier.elems
      | .zero   => G.id_in
      | .succ n => op_mem G (gpow_mem G hg n) hg

    /-- `g^(m+n) = g^m · g^n`. -/
    theorem gpow_add {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {g : α} (hg : g ∈ G.carrier.elems)
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
    theorem gpow_comm_single {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {g : α} (hg : g ∈ G.carrier.elems)
        (n : ℕ₀) : G.op g (gpow G g n) = G.op (gpow G g n) g := by
      calc G.op g (gpow G g n)
          = G.op (gpow G g 𝟙) (gpow G g n) := by rw [gpow_one G g hg]
        _ = gpow G g (add 𝟙 n)              := by rw [← gpow_add G hg 𝟙 n]
        _ = gpow G g (σ n)                   := by congr 1; exact add_comm 𝟙 n
        _ = G.op (gpow G g n) g              := gpow_succ G g n

    /-- `(g⁻¹)^n = (g^n)⁻¹`. -/
    theorem gpow_inv {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {g : α} (hg : g ∈ G.carrier.elems)
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
    # § 4d. Orden de un elemento (B2.3)
    !-/

    /-- Si `g^i = g^j` y `j < i`, entonces `g^(i-j) = id`. -/
    private theorem gpow_sub_eq_id {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {g : α} (hg : g ∈ G.carrier.elems)
        {i j : ℕ₀} (h_lt : lt₀ j i) (h_eq : gpow G g i = gpow G g j) :
        gpow G g (sub i j) = G.id := by
      have h_le : le₀ j i := lt_imp_le j i h_lt
      have h_add : add (sub i j) j = i := sub_k_add_k i j h_le
      apply op_cancel_right G (gpow_mem G hg j) (gpow_mem G hg (sub i j)) G.id_in
      rw [← gpow_add G hg, h_add, h_eq, (G.op_id (gpow G g j) (gpow_mem G hg j)).2]

    /-- Existencia del orden: ∃ n > 0, `g^n = id` y `n ≤ |G|`. -/
    private theorem orderExists {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {g : α} (hg : g ∈ G.carrier.elems) :
        ∃ n : ℕ₀, lt₀ 𝟘 n ∧ gpow G g n = G.id ∧ le₀ n G.carrier.card := by
      let A := ℕ₀FSet.Fin₀Set (σ G.carrier.card)
      let f : MapOn A G.carrier :=
        { toFun := fun i => gpow G g i
          map_carrier := fun i _ => gpow_mem G hg i }
      have hcard_lt : lt₀ G.carrier.card A.card := by
        simp only [A, ℕ₀FSet.Fin₀Set_card]
        exact lt_succ_self G.carrier.card
      obtain ⟨i₁, i₂, hi₁, hi₂, h_ne, h_eq⟩ := collision_of_card_lt f hcard_lt
      simp only [f] at h_eq
      have hi₁_le : le₀ i₁ G.carrier.card :=
        (lt_succ_iff_le i₁ G.carrier.card).mp
          ((ℕ₀FSet.mem_Fin₀Set_iff (σ G.carrier.card) i₁).mp hi₁)
      have hi₂_le : le₀ i₂ G.carrier.card :=
        (lt_succ_iff_le i₂ G.carrier.card).mp
          ((ℕ₀FSet.mem_Fin₀Set_iff (σ G.carrier.card) i₂).mp hi₂)
      rcases lt_or_ge i₁ i₂ with h₁₂ | h₂₁
      · exact ⟨sub i₂ i₁, sub_pos_of_lt h₁₂,
               gpow_sub_eq_id G hg h₁₂ h_eq.symm,
               le_trans _ i₂ _ (sub_le_self i₂ i₁) hi₂_le⟩
      · rcases h₂₁ with h_lt | rfl
        · exact ⟨sub i₁ i₂, sub_pos_of_lt h_lt,
                 gpow_sub_eq_id G hg h_lt h_eq,
                 le_trans _ i₁ _ (sub_le_self i₁ i₂) hi₁_le⟩
        · exact absurd rfl h_ne

    /-- Especificación del orden (via WOP). -/
    private noncomputable def order_wop {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        ExistsUnique (fun n : ℕ₀ =>
          (lt₀ 𝟘 n ∧ gpow G g n = G.id) ∧
          ∀ m : ℕ₀, (lt₀ 𝟘 m ∧ gpow G g m = G.id) → le₀ n m) :=
      well_ordering_principle (fun n => lt₀ 𝟘 n ∧ gpow G g n = G.id)
        (let ⟨n, hn1, hn2, _⟩ := orderExists G hg; ⟨n, hn1, hn2⟩)

    /-- El orden de `g` en `G`: el mínimo `n > 0` tal que `g^n = id`. -/
    noncomputable def order {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) : ℕ₀ :=
      choose_unique (order_wop G g hg)

    private theorem order_spec {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        (lt₀ 𝟘 (order G g hg) ∧ gpow G g (order G g hg) = G.id) ∧
        ∀ m : ℕ₀, (lt₀ 𝟘 m ∧ gpow G g m = G.id) → le₀ (order G g hg) m :=
      choose_spec_unique (order_wop G g hg)

    theorem order_pos {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        lt₀ 𝟘 (order G g hg) := (order_spec G g hg).1.1

    theorem gpow_order_eq_id {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        gpow G g (order G g hg) = G.id := (order_spec G g hg).1.2

    theorem order_ne_zero {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        order G g hg ≠ 𝟘 := (ne_of_lt 𝟘 _ (order_pos G g hg)).symm

    theorem order_minimal {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems)
        {m : ℕ₀} (hm_pos : lt₀ 𝟘 m) (hm_eq : gpow G g m = G.id) :
        le₀ (order G g hg) m := (order_spec G g hg).2 m ⟨hm_pos, hm_eq⟩

    theorem order_le_card {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        le₀ (order G g hg) G.carrier.card := by
      obtain ⟨n, hn_pos, hn_eq, hn_le⟩ := orderExists G hg
      exact le_trans _ n _ (order_minimal G g hg hn_pos hn_eq) hn_le

    /-- `g^(k · ord) = id` para todo `k`. -/
    theorem gpow_mul_order_eq_id {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {g : α} (hg : g ∈ G.carrier.elems)
        (k : ℕ₀) : gpow G g (mul k (order G g hg)) = G.id := by
      induction k with
      | zero => rw [zero_mul, gpow_zero]
      | succ k ih =>
          rw [succ_mul, gpow_add G hg, ih,
              (G.op_id _ (gpow_mem G hg (order G g hg))).2,
              gpow_order_eq_id G g hg]

    /-- `g^n = g^(n mod ord)`: periodicidad del orden. -/
    theorem gpow_mod_order {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) {g : α} (hg : g ∈ G.carrier.elems) (n : ℕ₀) :
        gpow G g n = gpow G g (mod n (order G g hg)) := by
      have hord_ne : order G g hg ≠ 𝟘 := order_ne_zero G g hg
      have h_dec : n = add (mul (div n (order G g hg)) (order G g hg)) (mod n (order G g hg)) :=
        divMod_spec n (order G g hg) hord_ne
      have h_key : gpow G g (add (mul (div n (order G g hg)) (order G g hg))
                                  (mod n (order G g hg))) =
                   gpow G g (mod n (order G g hg)) := by
        rw [gpow_add G hg, gpow_mul_order_eq_id G hg]
        exact (G.op_id _ (gpow_mem G hg _)).2
      rw [← h_key, ← h_dec]

    /-!
    # § 5. Subgrupos
    !-/

    /--
    Un subgrupo de un grupo finito G es un subconjunto no vacío cerrado por la operación y la inversa, con la misma operación.
    -/
    structure Subgroup {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) where
      carrier : FSet α
      nonempty : ∃ a, a ∈ carrier.elems
      subset : ∀ a, a ∈ carrier.elems → a ∈ G.carrier.elems
      op_closed : ∀ a b, a ∈ carrier.elems → b ∈ carrier.elems → G.op a b ∈ carrier.elems
      id_in : G.id ∈ carrier.elems
      inv_closed : ∀ a, a ∈ carrier.elems → G.inv a ∈ carrier.elems

    /-- Criterio de un paso: `H ≤ G` si y solo si `H ⊆ G`, `H ≠ ∅` y
        `∀ a b ∈ H, a · b⁻¹ ∈ H`. -/
    theorem Subgroup.op_inv_closed {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (H : Subgroup G)
        (a b : α) (ha : a ∈ H.carrier.elems) (hb : b ∈ H.carrier.elems) :
        G.op a (G.inv b) ∈ H.carrier.elems :=
      H.op_closed a (G.inv b) ha (H.inv_closed b hb)

    /-- Recíproco: si `S ⊆ G` es no vacío y cerrado bajo `a · b⁻¹`,
        entonces `S` es subgrupo de `G`. -/
    def subgroup_of_op_inv_closed {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α)
        (S : FSet α)
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
        have key : G.op a b = G.op a (G.inv (G.inv b)) := by
          rw [inv_inv_eq G (h_sub b hb)]
        rw [key]
        exact h_cl a (G.inv b) ha hb'

    /-!
    # § 5b. Tipos especiales de subgrupos
    !-/

    /-- El subgrupo trivial `{e}`. -/
    def trivialSubgroup {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) : Subgroup G where
      carrier  := FSet.singleton G.id
      nonempty := ⟨G.id, List.mem_cons.mpr (Or.inl rfl)⟩
      subset   := fun a ha => by
        simp only [FSet.singleton, List.mem_singleton] at ha
        exact ha ▸ G.id_in
      op_closed := fun a b ha hb => by
        simp only [FSet.singleton, List.mem_singleton] at ha hb ⊢
        rw [ha, hb, (G.op_id G.id G.id_in).1]
      id_in    := List.mem_cons.mpr (Or.inl rfl)
      inv_closed := fun a ha => by
        simp only [FSet.singleton, List.mem_singleton] at ha ⊢
        rw [ha, inv_id_eq]

    /-- El subgrupo impropio `G` como subgrupo de sí mismo. -/
    def improperSubgroup {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) : Subgroup G where
      carrier    := G.carrier
      nonempty   := ⟨G.id, G.id_in⟩
      subset     := fun _ ha => ha
      op_closed  := fun _a _b ha hb => op_mem G ha hb
      id_in      := G.id_in
      inv_closed := fun _a ha => inv_mem G ha

    /-- Un subgrupo es trivial si tiene exactamente un elemento. -/
    def Subgroup.IsTrivial {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} (H : Subgroup G) : Prop :=
      H.carrier.card = 𝟙

    /-- Un subgrupo es propio si no es el grupo entero. -/
    def Subgroup.IsProper {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} (H : Subgroup G) : Prop :=
      H.carrier.card ≠ G.carrier.card

    /-!
    # § 5c. Subgrupo cíclico
    !-/

    def cyclicCarrier {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) : FSet α :=
      FSet.filter
        (fun x => (ℕ₀FSet.Fin₀Set (σ G.carrier.card)).elems.any
                    (fun i => decide (gpow G g i = x)))
        G.carrier

    theorem cyclicCarrier_id_in {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) :
        G.id ∈ (cyclicCarrier G g).elems :=
      List.mem_filter.mpr ⟨G.id_in,
        List.any_eq_true.mpr ⟨𝟘,
          (ℕ₀FSet.mem_Fin₀Set_iff (σ G.carrier.card) 𝟘).mpr
            (by unfold Peano.StrictOrder.lt₀; trivial),
          decide_eq_true_eq.mpr (gpow_zero G g)⟩⟩

    theorem cyclicCarrier_mem_iff {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g x : α) :
        x ∈ (cyclicCarrier G g).elems ↔
          x ∈ G.carrier.elems ∧
          ∃ i ∈ (ℕ₀FSet.Fin₀Set (σ G.carrier.card)).elems, gpow G g i = x := by
      simp only [cyclicCarrier, FSet.filter, List.mem_filter,
                 List.any_eq_true, decide_eq_true_eq]

    /-- El subgrupo cíclico generado por `g`, definido mediante el criterio de un paso. -/
    def cyclicSubgroup {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        Subgroup G :=
      subgroup_of_op_inv_closed G
        (cyclicCarrier G g)
        (fun a ha => (List.mem_filter.mp ha).1)
        ⟨G.id, cyclicCarrier_id_in G g⟩
        (fun a b ha hb => by
          obtain ⟨ha_G, m, _hm_idx, hm⟩ := (cyclicCarrier_mem_iff G g a).mp ha
          obtain ⟨hb_G, n, _hn_idx, hn⟩ := (cyclicCarrier_mem_iff G g b).mp hb
          have hord_ne : order G g hg ≠ 𝟘 := order_ne_zero G g hg
          have h_n_le : le₀ n (mul (σ n) (order G g hg)) :=
            succ_mul n (order G g hg) ▸
              le_trans n (mul n (order G g hg)) (add (mul n (order G g hg)) (order G g hg))
                (mul_le_right n (order G g hg) hord_ne)
                (le_self_add (mul n (order G g hg)) (order G g hg))
          have h_inv_b : G.inv b = gpow G g (sub (mul (σ n) (order G g hg)) n) := by
            rw [← hn]
            apply (inv_unique G (gpow_mem G hg n)
                    (gpow_mem G hg (sub (mul (σ n) (order G g hg)) n)) _).symm
            exact ⟨by rw [← gpow_add G hg, add_comm n _,
                           sub_k_add_k (mul (σ n) (order G g hg)) n h_n_le,
                           gpow_mul_order_eq_id G hg (σ n)],
                   by rw [← gpow_add G hg,
                           sub_k_add_k (mul (σ n) (order G g hg)) n h_n_le,
                           gpow_mul_order_eq_id G hg (σ n)]⟩
          rw [cyclicCarrier_mem_iff]
          refine ⟨op_mem G ha_G (by rw [← hn]; exact inv_mem G (gpow_mem G hg n)),
                  mod (add m (sub (mul (σ n) (order G g hg)) n)) (order G g hg), ?_, ?_⟩
          · rw [ℕ₀FSet.mem_Fin₀Set_iff, lt_succ_iff_le]
            exact le_trans _ (order G g hg) _
              (lt_imp_le _ _ (mod_lt _ (order G g hg) hord_ne))
              (order_le_card G g hg)
          · rw [h_inv_b, ← hm, ← gpow_add G hg,
                ← gpow_mod_order G hg (add m (sub (mul (σ n) (order G g hg)) n))])

    /-- El subgrupo cíclico generado por `g` (construcción directa). -/
    def cyclicSubgroup' {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) (g : α) (hg : g ∈ G.carrier.elems) :
        Subgroup G where
      carrier    := cyclicCarrier G g
      nonempty   := ⟨G.id, cyclicCarrier_id_in G g⟩
      subset     := fun a ha => (List.mem_filter.mp ha).1
      id_in      := cyclicCarrier_id_in G g
      op_closed  := fun a b ha hb => by
        obtain ⟨ha_G, m, hm_idx, hm⟩ := (cyclicCarrier_mem_iff G g a).mp ha
        obtain ⟨hb_G, n, hn_idx, hn⟩ := (cyclicCarrier_mem_iff G g b).mp hb
        rw [cyclicCarrier_mem_iff]
        have hord_ne : order G g hg ≠ 𝟘 := order_ne_zero G g hg
        refine ⟨op_mem G ha_G hb_G, mod (add m n) (order G g hg), ?_, ?_⟩
        · rw [ℕ₀FSet.mem_Fin₀Set_iff, lt_succ_iff_le]
          exact le_trans _ (order G g hg) _
            (lt_imp_le _ _ (mod_lt _ (order G g hg) hord_ne))
            (order_le_card G g hg)
        · rw [← hm, ← hn, ← gpow_add G hg, ← gpow_mod_order G hg (add m n)]
      inv_closed := fun a ha => by
        obtain ⟨ha_G, n, hn_idx, hn⟩ := (cyclicCarrier_mem_iff G g a).mp ha
        rw [cyclicCarrier_mem_iff]
        have hord_ne : order G g hg ≠ 𝟘 := order_ne_zero G g hg
        have h_n_le : le₀ n (mul (σ n) (order G g hg)) :=
          succ_mul n (order G g hg) ▸
            le_trans n (mul n (order G g hg)) (add (mul n (order G g hg)) (order G g hg))
              (mul_le_right n (order G g hg) hord_ne)
              (le_self_add (mul n (order G g hg)) (order G g hg))
        have h_inv_a : G.inv a = gpow G g (sub (mul (σ n) (order G g hg)) n) := by
          rw [← hn]
          apply (inv_unique G (gpow_mem G hg n)
                  (gpow_mem G hg (sub (mul (σ n) (order G g hg)) n)) _).symm
          exact ⟨by rw [← gpow_add G hg, add_comm n _,
                         sub_k_add_k (mul (σ n) (order G g hg)) n h_n_le,
                         gpow_mul_order_eq_id G hg (σ n)],
                 by rw [← gpow_add G hg,
                         sub_k_add_k (mul (σ n) (order G g hg)) n h_n_le,
                         gpow_mul_order_eq_id G hg (σ n)]⟩
        refine ⟨inv_mem G ha_G,
                mod (sub (mul (σ n) (order G g hg)) n) (order G g hg), ?_, ?_⟩
        · rw [ℕ₀FSet.mem_Fin₀Set_iff, lt_succ_iff_le]
          exact le_trans _ (order G g hg) _
            (lt_imp_le _ _ (mod_lt _ (order G g hg) hord_ne))
            (order_le_card G g hg)
        · rw [h_inv_a, ← gpow_mod_order G hg (sub (mul (σ n) (order G g hg)) n)]

    /-!
    # § 5d. Normalidad
    !-/

    /-- Un subgrupo `N` de `G` es normal si es cerrado bajo conjugación:
        `∀ g ∈ G, ∀ n ∈ N, g·n·g⁻¹ ∈ N`. -/
    def Subgroup.IsNormal {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} (N : Subgroup G) : Prop :=
      ∀ g n, g ∈ G.carrier.elems → n ∈ N.carrier.elems →
        G.op (G.op g n) (G.inv g) ∈ N.carrier.elems

    /-- El subgrupo trivial es normal. -/
    theorem trivialSubgroup_normal {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) :
        (trivialSubgroup G).IsNormal := by
      intro g n hg hn
      simp only [trivialSubgroup, FSet.singleton, List.mem_singleton] at hn ⊢
      rw [hn, (G.op_id g hg).1, (G.op_inv g hg).1]

    /-- El subgrupo impropio es normal. -/
    theorem improperSubgroup_normal {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G : FinGroup α) :
        (improperSubgroup G).IsNormal := by
      intro g n hg hn
      exact op_mem G (op_mem G hg hn) (inv_mem G hg)

    /-!
    # § 5e. Intersección de subgrupos
    !-/

    /-- Intersección de dos subgrupos. -/
    def Subgroup.inter {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} (H₁ H₂ : Subgroup G) : Subgroup G where
      carrier  :=
        FSet.filter
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
    theorem Subgroup.inter_subset_left {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} (H₁ H₂ : Subgroup G)
        {a : α} (ha : a ∈ (H₁.inter H₂).carrier.elems) :
        a ∈ H₁.carrier.elems := by
      obtain ⟨_, ha_and⟩ := List.mem_filter.mp ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha_and
      exact ha_and.1

    theorem Subgroup.inter_subset_right {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} (H₁ H₂ : Subgroup G)
        {a : α} (ha : a ∈ (H₁.inter H₂).carrier.elems) :
        a ∈ H₂.carrier.elems := by
      obtain ⟨_, ha_and⟩ := List.mem_filter.mp ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha_and
      exact ha_and.2

    /-- La intersección de dos subgrupos normales es normal. -/
    theorem Subgroup.inter_normal_of_normal {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} {H₁ H₂ : Subgroup G}
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
    structure GroupHom {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (G H : FinGroup α) where
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

    /-!
    # § 8. Instancias de orden y decidibilidad para `Subgroup G`

    Para que `FSet (Subgroup G)` y `FinGroup (Subgroup G)` sean posibles,
    necesitamos `DecidableEq`, `LT` y `StrictLinearOrder` sobre subgrupos.
    El orden se hereda del orden sobre `FSet α` (orden del soporte).
    -/

    /-- Extensionalidad de subgrupos: igualdad de soportes implica igualdad. -/
    theorem Subgroup.ext_carrier {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} {H₁ H₂ : Subgroup G}
        (h : H₁.carrier = H₂.carrier) : H₁ = H₂ := by
      rcases H₁ with ⟨c₁, ne₁, sub₁, op₁, id₁, inv₁⟩
      rcases H₂ with ⟨c₂, ne₂, sub₂, op₂, id₂, inv₂⟩
      cases h
      have h1 : ne₁  = ne₂  := proof_irrel ne₁  ne₂
      have h2 : sub₁ = sub₂ := proof_irrel sub₁ sub₂
      have h3 : op₁  = op₂  := proof_irrel op₁  op₂
      have h4 : id₁  = id₂  := proof_irrel id₁  id₂
      have h5 : inv₁ = inv₂ := proof_irrel inv₁ inv₂
      subst h1; subst h2; subst h3; subst h4; subst h5
      rfl

    /-- Proyección del soporte preserva la igualdad. -/
    theorem Subgroup.carrier_inj {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} {H₁ H₂ : Subgroup G}
        (h : H₁ = H₂) : H₁.carrier = H₂.carrier :=
      congrArg Subgroup.carrier h

    /-- Igualdad decidible de subgrupos, heredada del soporte. -/
    instance instDecidableEqSubgroup {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} : DecidableEq (Subgroup G) :=
      fun H₁ H₂ =>
        if h : H₁.carrier = H₂.carrier then
          isTrue (Subgroup.ext_carrier h)
        else
          isFalse (fun heq => h (Subgroup.carrier_inj heq))

    /-- Orden estricto sobre subgrupos: `H₁ < H₂ ↔ H₁.carrier < H₂.carrier`. -/
    instance instLTSubgroup {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} : LT (Subgroup G) where
      lt := fun H₁ H₂ => H₁.carrier < H₂.carrier

    /-- `StrictLinearOrder` sobre subgrupos, heredado del orden sobre soportes. -/
    instance instStrictLinearOrderSubgroup {α : Type} [DecidableEq α] [LT α]
        [slo : StrictLinearOrder α] {G : FinGroup α} :
        StrictLinearOrder (Subgroup G) where
      decLt  := fun H₁ H₂ =>
        (instStrictLinearOrderFSet (α := α)).decLt H₁.carrier H₂.carrier
      irrefl := fun H h =>
        (instStrictLinearOrderFSet (α := α)).irrefl H.carrier h
      trans  := fun {_a _b _c} hab hbc =>
        (instStrictLinearOrderFSet (α := α)).trans hab hbc
      trich  := fun H₁ H₂ h₁ h₂ =>
        Subgroup.ext_carrier
          ((instStrictLinearOrderFSet (α := α)).trich H₁.carrier H₂.carrier h₁ h₂)

  end Group
end Peano

export Peano.Group (
  FinGroup
  ℕ₀FinGroup
  id_unique
  inv_mem
  op_mem
  op_cancel_left
  op_cancel_right
  inv_inv_eq
  inv_id_eq
  inv_op_eq
  inv_unique
  gpow
  gpow_zero
  gpow_succ
  gpow_one
  gpow_mem
  gpow_add
  gpow_comm_single
  gpow_inv
  order
  order_pos
  gpow_order_eq_id
  order_ne_zero
  order_minimal
  order_le_card
  gpow_mul_order_eq_id
  gpow_mod_order
  Subgroup
  Subgroup.op_inv_closed
  subgroup_of_op_inv_closed
  trivialSubgroup
  improperSubgroup
  Subgroup.IsTrivial
  Subgroup.IsProper
  cyclicCarrier
  cyclicCarrier_id_in
  cyclicCarrier_mem_iff
  cyclicSubgroup
  cyclicSubgroup'
  Subgroup.IsNormal
  trivialSubgroup_normal
  improperSubgroup_normal
  Subgroup.inter
  Subgroup.inter_subset_left
  Subgroup.inter_subset_right
  Subgroup.inter_normal_of_normal
  GroupHom
  Subgroup.ext_carrier
  Subgroup.carrier_inj
  instDecidableEqSubgroup
  instLTSubgroup
  instStrictLinearOrderSubgroup
)
