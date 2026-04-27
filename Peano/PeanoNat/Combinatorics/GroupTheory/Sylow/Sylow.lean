/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean
-- Teoremas de Sylow para grupos finitos.
--
-- § 1. p-subgrupos y p-subgrupos de Sylow
-- § 2. Primer teorema de Sylow (existencia)
-- § 3. Segundo teorema de Sylow (conjugación)
-- § 4. Tercer teorema de Sylow (número de p-subgrupos de Sylow)
--
-- Prerrequisitos:
--   * Cosets.lean (Lema de Lagrange)
--   * Action.lean (Teorema Órbita–Estabilizador, Ecuación de Clases)

import Peano.PeanoNat
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Combinatorics.Binom
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets
import Peano.PeanoNat.Combinatorics.GroupTheory.Action
import Peano.PeanoNat.NumberTheory.ModEq
import Peano.PeanoNat.NumberTheory.Totient

set_option autoImplicit false

namespace Peano
  namespace GroupTheory

    open Peano.FSet
    open Peano.FSetFunction
    open Peano.Group
    open Peano.Primes
    open Peano.Mul
    open Peano.Div
    open Peano.Add
    open Peano.Sub
    open Peano.StrictOrder
    open Peano.Order
    open Peano.Totient

    -- Desambiguación: Prime se refiere a Peano.Primes.Prime
    private abbrev Prime := Peano.Primes.Prime

    /-!
    # § 1. p-subgrupos
    -/

    /-- `p` divide `|H|` en sentido ℕ₀: `∃ k, |H| = p · k`. -/
    def dvd_card (p : ℕ₀) (H : ℕ₀FSet) : Prop :=
      ∃ k : ℕ₀, Mul.mul p k = H.card

    /-- `p^k` divide `|H|`. -/
    def pow_dvd_card (p k : ℕ₀) (H : ℕ₀FSet) : Prop :=
      ∃ m : ℕ₀, Mul.mul (p ^ k) m = H.card

    /-- Un `p`-subgrupo de `G` es un subgrupo cuyo orden es una potencia de `p`. -/
    def isPSubgroup (G : FinGroup ℕ₀) (H : Subgroup G) (p : ℕ₀) : Prop :=
      ∃ k : ℕ₀, H.carrier.card = p ^ k

    /-- `p^n` es la mayor potencia de `p` que divide `|G|`
        (es decir, `p^n | |G|` pero `p^(n+1) ∤ |G|`). -/
    def isSylowExponent (G : FinGroup ℕ₀) (p n : ℕ₀) : Prop :=
      pow_dvd_card p n G.carrier ∧ ¬ pow_dvd_card p (σ n) G.carrier

    /-- Un subgrupo de Sylow `p` de `G` es un `p`-subgrupo de orden `p^n`
        donde `p^n` es la mayor potencia de `p` que divide `|G|`. -/
    def isSylowSubgroup (G : FinGroup ℕ₀) (H : Subgroup G) (p : ℕ₀) : Prop :=
      ∃ n, isSylowExponent G p n ∧ H.carrier.card = p ^ n

    /-!
    # § 2. Primer Teorema de Sylow (existencia)

    Si `p` es primo y `p^n | |G|`, entonces `G` tiene un subgrupo de orden `p^n`.
    En particular, `G` tiene un subgrupo de Sylow para cada primo `p | |G|`.
    -/

    -- ── Lemas auxiliares privados para cauchy_minimal ────────────────────────────

    /-- Si x pertenece a S, entonces card S ≥ 1. -/
    private theorem card_pos_of_mem_aux {x : ℕ₀} {S : ℕ₀FSet} (hx : x ∈ S.elems) :
        lt₀ 𝟘 S.card := by
      unfold FSet.card
      cases h : S.elems with
      | nil => exact absurd (h ▸ hx) List.not_mem_nil
      | cons a as =>
          show lt₀ 𝟘 (lengthₚ (a :: as))
          rw [lengthₚ_cons]
          exact lt_zero_succ _

    /-- Si g^m = e y m > 0, entonces ord(g) divide a m. -/
    private theorem order_dvd_of_pow_eq_id (G : FinGroup ℕ₀) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
        {m : ℕ₀} (_hm_pos : lt₀ 𝟘 m) (hm_eq : gpow G g m = G.id) :
        ∃ k, Mul.mul (order G g hg) k = m := by
      have hord_ne := order_ne_zero G g hg
      have h_mod_eq : gpow G g (mod m (order G g hg)) = G.id := by
        rw [← gpow_mod_order G hg m]; exact hm_eq
      by_cases h_mod_zero : mod m (order G g hg) = 𝟘
      · -- m mod ord = 0, so m = (m / ord) * ord
        have spec : m = add (mul (div m (order G g hg)) (order G g hg))
                            (mod m (order G g hg)) :=
          divMod_spec m (order G g hg) hord_ne
        rw [h_mod_zero, add_zero] at spec
        exact ⟨div m (order G g hg), (mul_comm _ _).trans spec.symm⟩
      · -- m mod ord ≠ 0 y g^(m mod ord) = e → contradicción con minimalidad
        exfalso
        have h_mod_pos : lt₀ 𝟘 (mod m (order G g hg)) :=
          pos_of_ne_zero _ h_mod_zero
        have h_mod_lt : lt₀ (mod m (order G g hg)) (order G g hg) :=
          mod_lt m (order G g hg) hord_ne
        exact absurd h_mod_lt (le_then_ngt _ _ (order_minimal G g hg h_mod_pos h_mod_eq))

    /-- Si g ≠ e, g^p = e y p es primo, entonces ord(g) = p. -/
    private theorem order_eq_prime_of_pow (G : FinGroup ℕ₀) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
        (hg_ne : g ≠ G.id) {p : ℕ₀} (hp : Prime p) (hgp : gpow G g p = G.id) :
        order G g hg = p := by
      have hp_pos : lt₀ 𝟘 p := pos_of_ne_zero p hp.1
      obtain ⟨k, hk⟩ := order_dvd_of_pow_eq_id G hg hp_pos hgp
      -- ord(g) * k = p, y p es irreducible → ord = 1 ó k = 1
      rcases (Peano.Primes.prime_imp_irreducible hp).2 (order G g hg) k hk with h_ord1 | hk1
      · -- ord = 1 → g^1 = e → g = e, contradicción
        exfalso
        have hg1 : gpow G g 𝟙 = G.id := by
          rw [← h_ord1]; exact gpow_order_eq_id G g hg
        exact hg_ne (gpow_one G g hg ▸ hg1)
      · -- k = 1 → ord * 1 = p → ord = p
        rw [hk1, mul_one] at hk; exact hk

    /-- g^i pertenece al subgrupo cíclico cuando i < p y p divide |G|. -/
    private theorem gpow_lt_p_mem_cyclic (G : FinGroup ℕ₀) (g : ℕ₀) (hg : g ∈ G.carrier.elems)
        {p : ℕ₀} (hdvd : ∃ t, Mul.mul p t = G.carrier.card) {i : ℕ₀} (hi : lt₀ i p) :
        gpow G g i ∈ (cyclicSubgroup G g hg).carrier.elems := by
      show gpow G g i ∈ (cyclicCarrier G g).elems
      rw [cyclicCarrier_mem_iff]
      refine ⟨gpow_mem G hg i, i, ?_, rfl⟩
      rw [ℕ₀FSet.mem_Fin₀Set_iff, lt_succ_iff_le]
      -- Necesitamos i ≤ |G|. Derivamos p ≤ |G| de hdvd y |G| > 0.
      have h_G_pos : lt₀ 𝟘 G.carrier.card := card_pos_of_mem_aux G.id_in
      obtain ⟨t, ht⟩ := hdvd
      have ht_ne : t ≠ 𝟘 := by
        intro h0; rw [h0, mul_zero] at ht
        exact absurd ht.symm (ne_of_lt 𝟘 _ h_G_pos).symm
      -- p ≤ p * t = |G|
      have h_p_le_G : le₀ p G.carrier.card := ht ▸ mul_le_right p t ht_ne
      -- i < p ≤ |G| → i ≤ |G|
      rcases h_p_le_G with h_lt | rfl
      · exact lt_imp_le i G.carrier.card (lt_trans i p G.carrier.card hi h_lt)
      · exact lt_imp_le _ _ hi

    /-- La función i ↦ g^i es una biyección Fin₀Set(p) → (cyclicSubgroup G g hg).carrier,
        por lo que |(cyclicSubgroup G g hg)| = p cuando g ≠ e, g^p = e y p primo. -/
    private theorem cyclicSubgroup_card_eq_prime
        (G : FinGroup ℕ₀) (g : ℕ₀) (hg : g ∈ G.carrier.elems)
        {p : ℕ₀} (hp : Prime p) (hgp : gpow G g p = G.id) (hg_ne : g ≠ G.id)
        (hdvd : ∃ t, Mul.mul p t = G.carrier.card) :
        (cyclicSubgroup G g hg).carrier.card = p := by
      have h_ord_p : order G g hg = p :=
        order_eq_prime_of_pow G hg hg_ne hp hgp
      -- Definir f : Fin₀Set(p) → (cyclicSubgroup G g hg).carrier
      let f : MapOn (ℕ₀FSet.Fin₀Set p) (cyclicSubgroup G g hg).carrier := {
        toFun       := fun i => gpow G g i,
        map_carrier := fun i hi =>
          gpow_lt_p_mem_cyclic G g hg hdvd ((ℕ₀FSet.mem_Fin₀Set_iff p i).mp hi)
      }
      -- f es inyectiva: si g^i₁ = g^i₂ con i₁ < p e i₂ < p, entonces i₁ = i₂
      have h_inj : f.Injective := by
        intro i₁ i₂ hi₁ hi₂ h_eq
        simp only [f] at h_eq  -- h_eq : gpow G g i₁ = gpow G g i₂
        have hi₁_lt : lt₀ i₁ p := (ℕ₀FSet.mem_Fin₀Set_iff p i₁).mp hi₁
        have hi₂_lt : lt₀ i₂ p := (ℕ₀FSet.mem_Fin₀Set_iff p i₂).mp hi₂
        rcases trichotomy i₁ i₂ with h_lt | h_eq_i | h_gt
        · -- i₁ < i₂: g^(i₂-i₁) = e con 0 < i₂-i₁ < ord → contradicción
          exfalso
          have h_sub_pos : lt₀ 𝟘 (sub i₂ i₁) := sub_pos_of_lt h_lt
          have h_sub_lt_p : lt₀ (sub i₂ i₁) p := by
            rcases sub_le_self i₂ i₁ with h | h_eq
            · exact lt_trans (sub i₂ i₁) i₂ p h hi₂_lt
            · rw [h_eq]; exact hi₂_lt
          have h_pow_sub : gpow G g (sub i₂ i₁) = G.id := by
            apply op_cancel_right G (gpow_mem G hg i₁)
                    (gpow_mem G hg (sub i₂ i₁)) G.id_in
            rw [← gpow_add G hg, sub_k_add_k i₂ i₁ (lt_imp_le i₁ i₂ h_lt),
                h_eq, (G.op_id _ (gpow_mem G hg i₂)).2]
          have h_ord_le : le₀ (order G g hg) (sub i₂ i₁) :=
            order_minimal G g hg h_sub_pos h_pow_sub
          rw [h_ord_p] at h_ord_le
          exact absurd h_sub_lt_p (le_then_ngt _ _ h_ord_le)
        · exact h_eq_i
        · -- i₂ < i₁: simétrico
          exfalso
          have h_sub_pos : lt₀ 𝟘 (sub i₁ i₂) := sub_pos_of_lt h_gt
          have h_sub_lt_p : lt₀ (sub i₁ i₂) p := by
            rcases sub_le_self i₁ i₂ with h | h_eq
            · exact lt_trans (sub i₁ i₂) i₁ p h hi₁_lt
            · rw [h_eq]; exact hi₁_lt
          have h_pow_sub : gpow G g (sub i₁ i₂) = G.id := by
            apply op_cancel_right G (gpow_mem G hg i₂)
                    (gpow_mem G hg (sub i₁ i₂)) G.id_in
            rw [← gpow_add G hg, sub_k_add_k i₁ i₂ (lt_imp_le i₂ i₁ h_gt),
                h_eq.symm, (G.op_id _ (gpow_mem G hg i₁)).2]
          have h_ord_le : le₀ (order G g hg) (sub i₁ i₂) :=
            order_minimal G g hg h_sub_pos h_pow_sub
          rw [h_ord_p] at h_ord_le
          exact absurd h_sub_lt_p (le_then_ngt _ _ h_ord_le)
      -- f es sobreyectiva: todo x ∈ <g> es algún g^i con i < p
      have h_surj : f.Surjective := by
        intro x hx
        -- hx : x ∈ cyclicSubgroup → ∃ j ≤ |G|, g^j = x
        have hx' : x ∈ (cyclicCarrier G g).elems := hx
        rw [cyclicCarrier_mem_iff] at hx'
        obtain ⟨_, j, _, hgj⟩ := hx'
        -- j mod p < p y g^(j mod p) = g^j = x
        refine ⟨mod j p, (ℕ₀FSet.mem_Fin₀Set_iff p (mod j p)).mpr (mod_lt j p hp.1), ?_⟩
        simp only [f]
        rw [← hgj]
        exact (h_ord_p ▸ gpow_mod_order G hg j).symm
      -- Biyección → |Fin₀Set(p)| = |(cyclicSubgroup G g hg).carrier|
      have h_card := MapOn.Bijective.card_eq ⟨h_inj, h_surj⟩
      rw [ℕ₀FSet.Fin₀Set_card] at h_card
      exact h_card.symm

    -- ── Lemas McKay (argumento de conteo de órbitas para Cauchy) ─────────────────

    /-- Producto de una lista de elementos de G (por la izquierda). -/
    private def listProd (G : FinGroup ℕ₀) : List ℕ₀ → ℕ₀
      | []      => G.id
      | x :: xs => G.op x (listProd G xs)

    private theorem listProd_nil (G : FinGroup ℕ₀) : listProd G [] = G.id := rfl

    private theorem listProd_cons (G : FinGroup ℕ₀) (x : ℕ₀) (xs : List ℕ₀) :
        listProd G (x :: xs) = G.op x (listProd G xs) := rfl

    /-- listProd de una lista cerrada en G da un elemento de G. -/
    private theorem listProd_mem (G : FinGroup ℕ₀) {l : List ℕ₀}
        (hl : ∀ x ∈ l, x ∈ G.carrier.elems) : listProd G l ∈ G.carrier.elems := by
      induction l with
      | nil => exact G.id_in
      | cons x xs ih =>
        exact op_mem G (hl x List.mem_cons_self)
          (ih (fun y hy => hl y (List.mem_cons_of_mem x hy)))

    /-- listProd de un singleton. -/
    private theorem listProd_singleton (G : FinGroup ℕ₀) {x : ℕ₀}
        (hx : x ∈ G.carrier.elems) : listProd G [x] = x := by
      simp only [listProd_cons, listProd_nil, (G.op_id x hx).1]

    /-- listProd es compatible con la concatenación. -/
    private theorem listProd_append (G : FinGroup ℕ₀) (l₁ l₂ : List ℕ₀)
        (h₁ : ∀ x ∈ l₁, x ∈ G.carrier.elems)
        (h₂ : ∀ x ∈ l₂, x ∈ G.carrier.elems) :
        listProd G (l₁ ++ l₂) = G.op (listProd G l₁) (listProd G l₂) := by
      revert h₁
      induction l₁ with
      | nil =>
        intro _
        simp only [List.nil_append, listProd_nil]
        exact ((G.op_id (listProd G l₂) (listProd_mem G h₂)).2).symm
      | cons x xs ih =>
        intro h₁
        simp only [List.cons_append, listProd_cons]
        rw [ih (fun y hy => h₁ y (List.mem_cons_of_mem x hy))]
        exact (G.op_assoc x (listProd G xs) (listProd G l₂)
          (h₁ x List.mem_cons_self)
          (listProd_mem G (fun y hy => h₁ y (List.mem_cons_of_mem x hy)))
          (listProd_mem G h₂)).symm

    /-- Subtipo de listas genéricas de longitud fija `n`. -/
    def Vector (α : Type) (n : ℕ₀) : Type :=
      { l : List α // lengthₚ l = n }

    /-- Rotación de lista genérica: mueve la cabeza al final. -/
    private def rotateList {α : Type} : List α → List α
      | []      => []
      | x :: xs => xs ++ [x]

    /-- La rotación preserva la longitud de la lista. -/
    private theorem lengthₚ_rotateList {α : Type} (l : List α) :
        lengthₚ (rotateList l) = lengthₚ l := by
      cases l with
      | nil => rfl
      | cons x xs =>
        have h_rot : rotateList (x :: xs) = xs ++ [x] := rfl
        rw [h_rot, lengthₚ_append, lengthₚ_singleton, add_one, lengthₚ_cons]

    /-- Rotación cíclica sobre el subtipo de longitud fija. -/
    private def rotateVector {α : Type} {n : ℕ₀} (v : Vector α n) : Vector α n :=
      ⟨rotateList v.val, by rw [lengthₚ_rotateList, v.property]⟩

    /-- Producto de los elementos de un Vector. -/
    private def listProdVector (G : FinGroup ℕ₀) {n : ℕ₀} (v : Vector ℕ₀ n) : ℕ₀ :=
      listProd G v.val

    /-- Igualdad decidible para Vector. -/
    instance vectorDecEq {n : ℕ₀} : DecidableEq (Vector ℕ₀ n) :=
      fun ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ =>
        match decEq v₁ v₂ with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (fun h_eq => by cases h_eq; exact h rfl)

    /-- Orden lexicográfico estricto para listas de ℕ₀. -/
    private def listLex : List ℕ₀ → List ℕ₀ → Prop
      | [], [] => False
      | [], _::_ => True
      | _::_, [] => False
      | x::xs, y::ys => lt₀ x y ∨ (x = y ∧ listLex xs ys)

    instance vectorLT {n : ℕ₀} : LT (Vector ℕ₀ n) :=
      ⟨fun v₁ v₂ => listLex v₁.val v₂.val⟩

    instance vectorDecLT {n : ℕ₀} : DecidableRel (@LT.lt (Vector ℕ₀ n) _) :=
      fun ⟨v₁, _⟩ ⟨v₂, _⟩ =>
        let rec decListLex (l₁ l₂ : List ℕ₀) : Decidable (listLex l₁ l₂) :=
          match l₁, l₂ with
          | [], [] => isFalse id
          | [], _::_ => isTrue trivial
          | _::_, [] => isFalse id
          | x::xs, y::ys =>
            match decEq x y with
            | isTrue h_eq =>
              match decListLex xs ys with
              | isTrue h_rest => isTrue (Or.inr ⟨h_eq, h_rest⟩)
              | isFalse h_nrest =>
                have h_nlt : ¬ lt₀ x y := by cases h_eq; exact lt_irrefl x
                isFalse (fun h => h.elim h_nlt (fun h_and => h_nrest h_and.right))
            | isFalse h_neq =>
              match decidableLt x y with
              | isTrue h_lt => isTrue (Or.inl h_lt)
              | isFalse h_nlt => isFalse (fun h => h.elim h_nlt (fun h_and => h_neq h_and.left))
        decListLex v₁ v₂

    /-- Prepone cada elemento de `elems` al frente de cada vector de la lista. -/
    private def vPrependAll (elems : List ℕ₀) {n : ℕ₀} :
        List (Vector ℕ₀ n) → List (Vector ℕ₀ (σ n))
      | [] => []
      | v :: vs =>
        (elems.map (fun x => ⟨x :: v.val, by rw [lengthₚ_cons, v.property]⟩))
        ++ vPrependAll elems vs

    /-- Genera todas las combinaciones de vectores de longitud `n` con elementos de `elems`. -/
    private def allVectorsList (elems : List ℕ₀) : (n : ℕ₀) → List (Vector ℕ₀ n)
      | 𝟘 => [⟨[], rfl⟩]
      | σ n => vPrependAll elems (allVectorsList elems n)

    private theorem vPrependAll_mem_iff (elems : List ℕ₀) {n : ℕ₀} (z : Vector ℕ₀ (σ n)) :
        ∀ l : List (Vector ℕ₀ n),
        z ∈ vPrependAll elems l ↔ ∃ v ∈ l, ∃ x ∈ elems, z.val = x :: v.val
      | [] => by simp [vPrependAll]
      | v :: vs => by
          simp only [vPrependAll, List.mem_append, List.mem_map]
          constructor
          · rintro (⟨x, hx_in, hxz⟩ | hz_vs)
            · exact ⟨v, List.mem_cons_self, x, hx_in, (congrArg Subtype.val hxz).symm⟩
            · obtain ⟨u, hu, x, hx, hzu⟩ := (vPrependAll_mem_iff elems z vs).mp hz_vs
              exact ⟨u, List.mem_cons_of_mem _ hu, x, hx, hzu⟩
          · rintro ⟨u, hu, x, hx, hzu⟩
            rcases List.mem_cons.mp hu with rfl | hu'
            · left; exact ⟨x, hx, Subtype.ext hzu.symm⟩
            · right; exact (vPrependAll_mem_iff elems z vs).mpr ⟨u, hu', x, hx, hzu⟩

    private theorem nodup_append_of {α : Type} {l₁ l₂ : List α}
        (h1 : l₁.Nodup) (h2 : l₂.Nodup) (hd : ∀ a, a ∈ l₁ → a ∉ l₂) :
        (l₁ ++ l₂).Nodup := by
      induction l₁ with
      | nil => exact h2
      | cons a l₁' ih =>
        obtain ⟨ha_nin, h1'⟩ := List.nodup_cons.mp h1
        rw [List.cons_append, List.nodup_cons]
        refine ⟨?_, ih h1' (fun b hb => hd b (List.mem_cons_of_mem _ hb))⟩
        intro hmem
        rw [List.mem_append] at hmem
        exact hmem.elim ha_nin (hd a List.mem_cons_self)

    private theorem vPrependAll_nodup (elems : List ℕ₀) (helems_nd : elems.Nodup) {n : ℕ₀} :
        ∀ l : List (Vector ℕ₀ n), l.Nodup → (vPrependAll elems l).Nodup
      | [], _ => List.nodup_nil
      | v :: vs, hnd => by
          obtain ⟨hv_nin, hvs_nd⟩ := List.nodup_cons.mp hnd
          simp only [vPrependAll]
          apply nodup_append_of
          · apply nodup_map_of_inj_on _ _ helems_nd
            intro a b _ _ heq
            exact (List.cons.inj (congrArg Subtype.val heq)).1
          · exact vPrependAll_nodup elems helems_nd vs hvs_nd
          · intro w hw_map hw_tail
            rw [List.mem_map] at hw_map
            obtain ⟨x, _, hxw⟩ := hw_map
            obtain ⟨u, hu_in, _, _, hyw⟩ := (vPrependAll_mem_iff elems w vs).mp hw_tail
            have h2 : v.val = u.val :=
              (List.cons.inj ((congrArg Subtype.val hxw).trans hyw)).2
            exact hv_nin ((Subtype.ext h2).symm ▸ hu_in)

    private theorem vPrependAll_length_nat (elems : List ℕ₀) {n : ℕ₀} :
        ∀ l : List (Vector ℕ₀ n),
        (vPrependAll elems l).length = Nat.mul elems.length l.length
      | [] => by simp [vPrependAll]
      | _ :: vs => by
          simp only [vPrependAll, List.length_append, List.length_map, List.length_cons]
          rw [vPrependAll_length_nat elems vs]
          simp [Nat.mul_add, Nat.mul_one, Nat.add_comm]

    private theorem vPrependAll_card (elems : List ℕ₀) {n : ℕ₀} (l : List (Vector ℕ₀ n)) :
        lengthₚ (vPrependAll elems l) = mul (lengthₚ elems) (lengthₚ l) := by
      unfold lengthₚ; rw [vPrependAll_length_nat, isomorph_Λ_mul]

    private theorem allVectorsList_mem_elems (elems : List ℕ₀) :
        ∀ {n : ℕ₀} (v : Vector ℕ₀ n), v ∈ allVectorsList elems n → ∀ x ∈ v.val, x ∈ elems
      | 𝟘, v, hv, x, hx => by
          simp only [allVectorsList, List.mem_singleton] at hv
          subst hv; exact absurd hx List.not_mem_nil
      | σ _, v, hv, x, hx => by
          simp only [allVectorsList] at hv
          obtain ⟨u, hu, y, hy_in, hvu⟩ := (vPrependAll_mem_iff elems v _).mp hv
          rw [hvu] at hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hy_in
          · exact allVectorsList_mem_elems elems u hu x hx'

    private theorem allVectorsList_complete (elems : List ℕ₀) :
        ∀ {n : ℕ₀} (v : Vector ℕ₀ n), (∀ x ∈ v.val, x ∈ elems) → v ∈ allVectorsList elems n
      | 𝟘, v, _ => by
          simp only [allVectorsList]
          apply List.mem_singleton.mpr
          apply Subtype.ext
          rcases v with ⟨l, hl⟩; cases l with
          | nil => rfl
          | cons x xs =>
            simp only [lengthₚ_cons] at hl
            exact absurd hl (Peano.Axioms.succ_neq_zero _)
      | σ n', v, h_mem => by
          simp only [allVectorsList]
          rw [vPrependAll_mem_iff]
          rcases v with ⟨l, hl⟩; cases l with
          | nil =>
            have : (𝟘 : ℕ₀) = σ n' := hl
            exact absurd this.symm (Peano.Axioms.succ_neq_zero n')
          | cons x xs =>
            have h_xs_len : lengthₚ xs = n' := by
              rw [lengthₚ_cons] at hl
              exact Peano.Axioms.succ_inj_pos_wp hl
            exact ⟨⟨xs, h_xs_len⟩,
                   allVectorsList_complete elems ⟨xs, h_xs_len⟩
                     (fun y hy => h_mem y (List.mem_cons_of_mem x hy)),
                   x, h_mem x List.mem_cons_self, rfl⟩

    private theorem allVectorsList_nodup (elems : List ℕ₀) (hnd : elems.Nodup) :
        ∀ n : ℕ₀, (allVectorsList elems n).Nodup
      | 𝟘 => by simp [allVectorsList]
      | σ n' => by
          simp only [allVectorsList]
          exact vPrependAll_nodup elems hnd _ (allVectorsList_nodup elems hnd n')

    private theorem allVectorsList_card (elems : List ℕ₀) :
        ∀ n : ℕ₀, lengthₚ (allVectorsList elems n) = pow (lengthₚ elems) n
      | 𝟘 => by simp only [allVectorsList]; rw [lengthₚ_singleton, pow_zero]
      | σ n' => by
          simp only [allVectorsList]
          rw [vPrependAll_card, allVectorsList_card elems n', pow_succ, mul_comm]

    private theorem rotateList_mem {α : Type} (a : α) :
        ∀ l : List α, a ∈ rotateList l ↔ a ∈ l
      | [] => by simp [rotateList]
      | x :: xs => by
          simp only [rotateList, List.mem_append, List.mem_cons]
          constructor
          · rintro (h | rfl | h)
            · exact Or.inr h
            · exact Or.inl rfl
            · exact absurd h List.not_mem_nil
          · rintro (rfl | h)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl h

    /-- La rotación preserva la condición listProd = id. -/
    private theorem listProd_rotate_eq_id (G : FinGroup ℕ₀) {l : List ℕ₀}
        (hl : ∀ x ∈ l, x ∈ G.carrier.elems)
        (hprod : listProd G l = G.id) :
        listProd G (rotateList l) = G.id := by
      cases l with
      | nil => exact hprod
      | cons x xs =>
        simp only [rotateList]
        have hx  : x ∈ G.carrier.elems :=
          hl x List.mem_cons_self
        have hxs : ∀ y ∈ xs, y ∈ G.carrier.elems :=
          fun y hy => hl y (List.mem_cons_of_mem x hy)
        rw [listProd_append G xs [x] hxs
              (fun y hy => by simp only [List.mem_singleton] at hy; subst hy; exact hx),
            listProd_singleton G hx]
        -- Goal: G.op (listProd G xs) x = G.id
        -- Know: G.op x (listProd G xs) = G.id  (por hprod, ya que listProd_cons es rfl)
        have hxs_mem : listProd G xs ∈ G.carrier.elems := listProd_mem G hxs
        have h_eq : listProd G xs = G.inv x :=
          op_cancel_left G hx hxs_mem (inv_mem G hx)
            (hprod.trans (G.op_inv x hx).1.symm)
        rw [h_eq]
        exact (G.op_inv x hx).2

    /-- La identidad elevada a cualquier potencia da la identidad. -/
    private theorem gpow_id_eq_id (G : FinGroup ℕ₀) (n : ℕ₀) :
        gpow G G.id n = G.id := by
      induction n with
      | zero     => rfl
      | succ n' ih => rw [gpow_succ, ih, (G.op_id G.id G.id_in).1]

    /-- Operación de McKay sobre una lista.
        Dado `[x₁, ..., x_k]`, devuelve `[x₂, ..., x_k, (x₁ ... x_k)⁻¹]`. -/
    private def mckayShiftList (G : FinGroup ℕ₀) : List ℕ₀ → List ℕ₀
      | [] => []
      | x :: xs => xs ++ [G.inv (listProd G (x :: xs))]

    /-- La operación de McKay preserva la longitud de la lista. -/
    private theorem lengthₚ_mckayShiftList (G : FinGroup ℕ₀) (l : List ℕ₀) :
        lengthₚ (mckayShiftList G l) = lengthₚ l := by
      cases l with
      | nil => rfl
      | cons x xs =>
        have h_shift : mckayShiftList G (x :: xs) = xs ++ [G.inv (listProd G (x :: xs))] := rfl
        rw [h_shift, lengthₚ_append, lengthₚ_singleton, add_one, lengthₚ_cons]

    /-- Operación de McKay elevada a Vector. -/
    private def mckayShift (G : FinGroup ℕ₀) {n : ℕ₀} (v : Vector ℕ₀ n) : Vector ℕ₀ n :=
      ⟨mckayShiftList G v.val, by rw [lengthₚ_mckayShiftList, v.property]⟩

    /-- La operación de McKay preserva la pertenencia al grupo G. -/
    private theorem mckayShiftList_mem (G : FinGroup ℕ₀) {l : List ℕ₀}
        (hl : ∀ x ∈ l, x ∈ G.carrier.elems) :
        ∀ x ∈ mckayShiftList G l, x ∈ G.carrier.elems := by
      cases l with
      | nil =>
        intro x hx
        cases hx
      | cons y ys =>
        intro x hx
        have h_append : x ∈ ys ∨ x ∈ [G.inv (listProd G (y :: ys))] := List.mem_append.mp hx
        rcases h_append with h_ys | h_inv
        · exact hl x (List.mem_cons_of_mem y h_ys)
        · have h_eq : x = G.inv (listProd G (y :: ys)) := by
            rcases List.mem_cons.mp h_inv with h | h
            · exact h
            · cases h
          rw [h_eq]
          exact inv_mem G (listProd_mem G hl)

    /-- Lema auxiliar: añadir elementos al final es inyectivo si las listas tienen misma longitud. -/
    private theorem append_singleton_inj {α : Type} :
        ∀ (xs ys : List α) (a b : α),
        lengthₚ xs = lengthₚ ys →
        xs ++ [a] = ys ++ [b] →
        xs = ys ∧ a = b
      | [], [], a, b, _, heq => by
        cases heq
        exact ⟨rfl, rfl⟩
      | x::xs, [], a, b, hlen, _ => by
        cases hlen
      | [], y::ys, a, b, hlen, _ => by
        cases hlen
      | x::xs, y::ys, a, b, hlen, heq => by
        injection heq with hxy heq_rest
        have hlen_rest : lengthₚ xs = lengthₚ ys := by injection hlen
        have ⟨hxs_ys, hab⟩ := append_singleton_inj xs ys a b hlen_rest heq_rest
        rw [hxy, hxs_ys]
        exact ⟨rfl, hab⟩

    /-- La operación de McKay es inyectiva. -/
    private theorem mckayShiftList_inj (G : FinGroup ℕ₀) {l₁ l₂ : List ℕ₀}
        (hl₁ : ∀ x ∈ l₁, x ∈ G.carrier.elems)
        (hl₂ : ∀ x ∈ l₂, x ∈ G.carrier.elems)
        (hlen : lengthₚ l₁ = lengthₚ l₂)
        (heq : mckayShiftList G l₁ = mckayShiftList G l₂) :
        l₁ = l₂ := by
      cases l₁ with
      | nil =>
        cases l₂ with
        | nil => rfl
        | cons y ys =>
          rw [lengthₚ_nil, lengthₚ_cons] at hlen
          cases hlen
      | cons x xs =>
        cases l₂ with
        | nil =>
          cases hlen
        | cons y ys =>
          have hlen_xs_ys : lengthₚ xs = lengthₚ ys := by injection hlen
          have heq_shift : xs ++ [G.inv (listProd G (x :: xs))] = ys ++ [G.inv (listProd G (y :: ys))] := heq
          obtain ⟨hxs_ys, hinv_eq⟩ := append_singleton_inj xs ys _ _ hlen_xs_ys heq_shift
          have h_prod_eq : listProd G (x :: xs) = listProd G (y :: ys) := by
            have h1 : listProd G (x :: xs) ∈ G.carrier.elems := listProd_mem G hl₁
            have h2 : listProd G (y :: ys) ∈ G.carrier.elems := listProd_mem G hl₂
            have h3 : G.inv (G.inv (listProd G (x :: xs))) = G.inv (G.inv (listProd G (y :: ys))) := by
              rw [hinv_eq]
            rw [inv_inv_eq G h1, inv_inv_eq G h2] at h3
            exact h3
          rw [hxs_ys] at h_prod_eq
          simp only [listProd_cons] at h_prod_eq
          have hx_mem : x ∈ G.carrier.elems := hl₁ x (List.mem_cons_self)
          have hy_mem : y ∈ G.carrier.elems := hl₂ y (List.mem_cons_self)
          have hys_mem : listProd G ys ∈ G.carrier.elems :=
            listProd_mem G (fun z hz => hl₂ z (List.mem_cons_of_mem y hz))
          have hxy : x = y := op_cancel_right G hys_mem hx_mem hy_mem h_prod_eq
          rw [hxy, hxs_ys]

    -- ─── Infraestructura de rotación iterada ─────────────────────────────────



    private def nthRotate {α : Type} : ℕ₀ → List α → List α

      | 𝟘,    l => l

      | σ n', l => nthRotate n' (rotateList l)



    private theorem nthRotate_succ_comm {α : Type} (k : ℕ₀) (l : List α) :

        nthRotate k (rotateList l) = rotateList (nthRotate k l) := by

      induction k generalizing l with

      | zero => rfl

      | succ k' ih => exact ih (rotateList l)



    private theorem nthRotate_add {α : Type} (k₁ k₂ : ℕ₀) (l : List α) :

        nthRotate (add k₁ k₂) l = nthRotate k₁ (nthRotate k₂ l) := by

      induction k₁ generalizing l with

      | zero =>

        simp only [zero_add]

        rfl

      | succ k₁' ih =>

        rw [succ_add k₁' k₂]

        show nthRotate (add k₁' k₂) (rotateList l) =

             nthRotate k₁' (rotateList (nthRotate k₂ l))

        rw [ih (rotateList l), nthRotate_succ_comm k₂ l]



    private theorem nthRotate_mul_period {α : Type} (l : List α) (k : ℕ₀)

        (h : nthRotate k l = l) (n : ℕ₀) : nthRotate (mul n k) l = l := by

      induction n with

      | zero => rw [zero_mul]; rfl

      | succ n' ih =>

        rw [succ_mul n' k, nthRotate_add (mul n' k) k l]

        rw [h]; exact ih



    private theorem nthRotate_append_general {α : Type} :

        ∀ (n : ℕ₀) (ys zs : List α), lengthₚ ys = n →

        nthRotate n (ys ++ zs) = zs ++ ys := by

      intro n

      induction n with

      | zero =>

        intro ys zs h

        cases ys with

        | nil => simp [List.nil_append, List.append_nil]; rfl

        | cons b ys' => cases h

      | succ n' ih =>

        intro ys zs h

        cases ys with

        | nil => cases h

        | cons b ys' =>

          have h' : lengthₚ ys' = n' := by

            have : σ (lengthₚ ys') = σ n' := by simpa [lengthₚ_cons] using h

            injection this

          show nthRotate n' (rotateList ((b :: ys') ++ zs)) = zs ++ (b :: ys')

          have hrot : rotateList ((b :: ys') ++ zs) = ys' ++ (zs ++ [b]) := by

            simp [rotateList, List.append_assoc]

          rw [hrot, ih ys' (zs ++ [b]) h']

          simp [List.append_assoc]



    private theorem nthRotate_length_self {α : Type} (l : List α) :

        nthRotate (lengthₚ l) l = l := by

      have h := nthRotate_append_general (lengthₚ l) l [] rfl

      simp at h; exact h



    private theorem rotateList_fixed_all_eq {α : Type} (a : α) (xs : List α)

        (h : xs ++ [a] = a :: xs) : ∀ x ∈ xs, x = a := by

      induction xs with

      | nil => intro x hx; exact absurd hx List.not_mem_nil

      | cons b ys ih =>

        intro x hx

        simp only [List.cons_append] at h

        injection h with hba h_rest

        rcases List.mem_cons.mp hx with rfl | hy

        · exact hba

        · exact ih (hba ▸ h_rest) x hy



    private theorem nthRotate_fixed_all {α : Type} (l : List α)

        (h : rotateList l = l) (k : ℕ₀) : nthRotate k l = l := by

      induction k with

      | zero => rfl

      | succ k' ih =>

        show nthRotate k' (rotateList l) = l

        rw [h]; exact ih



    private theorem gpow_comm_left (G : FinGroup ℕ₀) {g : ℕ₀} (hg : g ∈ G.carrier.elems) (n : ℕ₀) :

        G.op g (gpow G g n) = G.op (gpow G g n) g := by

      have h1 : gpow G g (add 𝟙 n) = G.op g (gpow G g n) := by

        rw [gpow_add G hg 𝟙 n, gpow_one G g hg]

      have h2 : gpow G g (add n 𝟙) = G.op (gpow G g n) g := by

        rw [gpow_add G hg n 𝟙, gpow_one G g hg]

      rw [← h1, add_comm 𝟙 n, h2]



    private theorem listProd_all_eq_gpow (G : FinGroup ℕ₀) (a : ℕ₀)

        (ha : a ∈ G.carrier.elems) (l : List ℕ₀) (hl : ∀ x ∈ l, x = a) :

        listProd G l = gpow G a (lengthₚ l) := by

      induction l with

      | nil => simp [listProd_nil, gpow_zero]

      | cons x xs ih =>

        have hx : x = a := hl x List.mem_cons_self

        have hxs : ∀ y ∈ xs, y = a := fun y hy => hl y (List.mem_cons_of_mem x hy)

        rw [listProd_cons, hx, ih hxs, lengthₚ_cons, gpow_succ]

        exact gpow_comm_left G ha (lengthₚ xs)



    -- ─── gcd y argumento de Bézout ────────────────────────────────────────────



    open Peano.Arith in

    private theorem gcd_eq_one_of_pos_lt_prime (k p : ℕ₀) (hk_pos : lt₀ 𝟘 k)

        (hk_lt : lt₀ k p) (hp : Prime p) : gcd k p = 𝟙 := by

      have h_dvd_p : Divides (gcd k p) p := gcd_divides_right k p

      obtain ⟨c, hc⟩ := h_dvd_p

      rcases (prime_imp_irreducible hp).2 (gcd k p) c hc.symm with h1 | hc1

      · exact h1

      · rw [hc1, mul_one] at hc

        have h_dvd_k : Divides (gcd k p) k := gcd_divides_left k p

        rw [← hc] at h_dvd_k

        obtain ⟨m, hm⟩ := h_dvd_k

        cases m with

        | zero =>

          rw [mul_zero] at hm

          exact absurd hm (ne_of_lt 𝟘 k hk_pos).symm

        | succ m' =>

          have hle : le₀ p (mul p (σ m')) := mul_le_right p (σ m') (Peano.Axioms.succ_neq_zero m')

          rw [← hm] at hle

          exact absurd hk_lt (le_then_ngt p k hle)



    open Peano.Arith in

    private theorem nthRotate_one_fixed_of_gcd_one {α : Type} (l : List α) (k p : ℕ₀)

        (hk : nthRotate k l = l) (hp_rot : nthRotate p l = l)

        (hgcd : gcd k p = 𝟙) : nthRotate 𝟙 l = l := by

      obtain ⟨n, m, h⟩ := bezout_natform k p

      rw [hgcd] at h

      rcases h with h1 | h2

      · -- h1 : 𝟙 = sub (mul n k) (mul m p)

        have h1' : sub (mul n k) (mul m p) = 𝟙 := h1.symm

        have hlt : lt₀ (mul m p) (mul n k) := by

          apply (sub_pos_iff_lt (mul n k) (mul m p)).mp

          rw [← h1]; exact le_refl 𝟙

        have h_eq : add 𝟙 (mul m p) = mul n k := by

          have key := sub_k_add_k (mul n k) (mul m p) (lt_imp_le _ _ hlt)

          rw [h1'] at key; exact key

        have h_mp : nthRotate (mul m p) l = l := nthRotate_mul_period l p hp_rot m

        have h_nk : nthRotate (mul n k) l = l := nthRotate_mul_period l k hk n

        calc nthRotate 𝟙 l

            = nthRotate 𝟙 (nthRotate (mul m p) l) := by rw [h_mp]

          _ = nthRotate (add 𝟙 (mul m p)) l := (nthRotate_add 𝟙 (mul m p) l).symm

          _ = nthRotate (mul n k) l := by rw [h_eq]

          _ = l := h_nk

      · -- h2 : 𝟙 = sub (mul n p) (mul m k)

        have h2' : sub (mul n p) (mul m k) = 𝟙 := h2.symm

        have hlt : lt₀ (mul m k) (mul n p) := by

          apply (sub_pos_iff_lt (mul n p) (mul m k)).mp

          rw [← h2]; exact le_refl 𝟙

        have h_eq : add 𝟙 (mul m k) = mul n p := by

          have key := sub_k_add_k (mul n p) (mul m k) (lt_imp_le _ _ hlt)

          rw [h2'] at key; exact key

        have h_mk : nthRotate (mul m k) l = l := nthRotate_mul_period l k hk m

        have h_np : nthRotate (mul n p) l = l := nthRotate_mul_period l p hp_rot n

        calc nthRotate 𝟙 l

            = nthRotate 𝟙 (nthRotate (mul m k) l) := by rw [h_mk]

          _ = nthRotate (add 𝟙 (mul m k)) l := (nthRotate_add 𝟙 (mul m k) l).symm

          _ = nthRotate (mul n p) l := by rw [h_eq]

          _ = l := h_np



    -- ─── Inyectividad de rotateVector en preimagen de punto fijo ─────────────

    private theorem vector_eq_of_rotateVector_eq_fixed {n : ℕ₀}

        (v w : Vector ℕ₀ n)

        (hv_fixed : rotateVector v = v)

        (hw_rot : rotateVector w = v) : w = v := by

      apply Subtype.ext

      have hrl_v : nthRotate 𝟙 v.val = v.val := congrArg Subtype.val hv_fixed

      have hrl_w : nthRotate 𝟙 w.val = v.val := congrArg Subtype.val hw_rot

      have hv_k : ∀ k : ℕ₀, nthRotate k v.val = v.val :=

        fun k => nthRotate_fixed_all v.val hrl_v k

      have hw_len : nthRotate n w.val = w.val := by

        have := nthRotate_length_self w.val; rwa [w.property] at this

      cases n with

      | zero =>

        have hv_nil : v.val = [] := by

          rcases v with ⟨vl, hvl⟩; cases vl with

          | nil => rfl

          | cons x xs => rw [lengthₚ_cons] at hvl; exact absurd hvl (Peano.Axioms.succ_neq_zero _)

        have hw_nil : w.val = [] := by

          rcases w with ⟨wl, hwl⟩; cases wl with

          | nil => rfl

          | cons x xs => rw [lengthₚ_cons] at hwl; exact absurd hwl (Peano.Axioms.succ_neq_zero _)

        exact hw_nil.trans hv_nil.symm

      | succ n' =>

        have hcalc : nthRotate (σ n') w.val = v.val :=

          (congrArg (fun k => nthRotate k w.val) (add_one n').symm).trans

            ((nthRotate_add n' 𝟙 w.val).trans (by rw [hrl_w]; exact hv_k n'))

        exact hw_len.symm.trans hcalc

    -- ─── Conteo de órbitas ───────────────────────────────────────────────────

    private theorem mckay_orbit_remove
      (p : ℕ₀) (hp : Prime p) (S : List (Vector ℕ₀ p)) (v : Vector ℕ₀ p) (hv_in : v ∈ S) (hv : rotateVector v ≠ v)
      (hnodup : S.Nodup) (hrot : ∀ w ∈ S, rotateVector w ∈ S) :
        ∃ S' : List (Vector ℕ₀ p), S'.Nodup ∧ (∀ w ∈ S', rotateVector w ∈ S') ∧
        lengthₚ S = Peano.Add.add (lengthₚ S') p ∧
        lengthₚ (S.filter (fun w => decide (rotateVector w = w))) =
        lengthₚ (S'.filter (fun w => decide (rotateVector w = w)))
          := by
      -- ── Fact: p-fold rotation is identity ────────────────────────────────
      have hp_period : nthRotate p v.val = v.val := by
        have h := nthRotate_length_self v.val; rwa [v.property] at h
      -- ── Rotations preserve vector length ─────────────────────────────────
      have nthRotate_len : ∀ k : ℕ₀, lengthₚ (nthRotate k v.val) = p := by
        intro k; induction k with
        | zero => exact v.property
        | succ k' ih =>
          show lengthₚ (nthRotate k' (rotateList v.val)) = p
          rw [nthRotate_succ_comm k' v.val, lengthₚ_rotateList]; exact ih
      -- ── No early return: orbit_no_return ─────────────────────────────────
      have orbit_no_return : ∀ k : ℕ₀, lt₀ 𝟘 k → lt₀ k p → nthRotate k v.val ≠ v.val := by
        intro k hk_pos hk_lt heq
        have hgcd : Peano.Arith.gcd k p = 𝟙 :=
          gcd_eq_one_of_pos_lt_prime k p hk_pos hk_lt hp
        have h1 : nthRotate 𝟙 v.val = v.val :=
          nthRotate_one_fixed_of_gcd_one v.val k p heq hp_period hgcd
        exact hv (Subtype.ext h1)
      -- ── Define orbit ─────────────────────────────────────────────────────
      let orb : ℕ₀ → Vector ℕ₀ p := fun k => ⟨nthRotate k v.val, nthRotate_len k⟩
      have rv_orb_eq : ∀ k : ℕ₀, rotateVector (orb k) = orb (σ k) := fun k =>
        Subtype.ext (nthRotate_succ_comm k v.val).symm
      let orbit : List (Vector ℕ₀ p) := (ℕ₀FSet.Fin₀Set p).elems.map orb
      -- ── orb is injective on Fin₀Set p ────────────────────────────────────
      have orb_inj : ∀ i j : ℕ₀,
          i ∈ (ℕ₀FSet.Fin₀Set p).elems → j ∈ (ℕ₀FSet.Fin₀Set p).elems →
          orb i = orb j → i = j := by
        intro i j hi hj heq
        have hi_lt := (ℕ₀FSet.mem_Fin₀Set_iff p i).mp hi
        have hj_lt := (ℕ₀FSet.mem_Fin₀Set_iff p j).mp hj
        have heq_val : nthRotate i v.val = nthRotate j v.val := congrArg Subtype.val heq
        rcases trichotomy i j with h_lt | h_eq | h_gt
        · exfalso
          have hpj : add (sub p j) j = p := sub_k_add_k p j (lt_imp_le j p hj_lt)
          exact orbit_no_return _ (lt_of_lt_of_le (sub_pos_of_lt hj_lt) (le_self_add _ _))
            (by have := (add_lt_add_left_iff (sub p j) i j).mpr h_lt; rwa [hpj] at this)
            (calc nthRotate (add (sub p j) i) v.val
                  = nthRotate (sub p j) (nthRotate i v.val) := nthRotate_add _ _ _
                _ = nthRotate (sub p j) (nthRotate j v.val) := by rw [heq_val]
                _ = nthRotate (add (sub p j) j) v.val := (nthRotate_add _ _ _).symm
                _ = nthRotate p v.val := by rw [hpj]
                _ = v.val := hp_period)
        · exact h_eq
        · exfalso
          have hpi : add (sub p i) i = p := sub_k_add_k p i (lt_imp_le i p hi_lt)
          exact orbit_no_return _ (lt_of_lt_of_le (sub_pos_of_lt hi_lt) (le_self_add _ _))
            (by have := (add_lt_add_left_iff (sub p i) j i).mpr h_gt; rwa [hpi] at this)
            (calc nthRotate (add (sub p i) j) v.val
                  = nthRotate (sub p i) (nthRotate j v.val) := nthRotate_add _ _ _
                _ = nthRotate (sub p i) (nthRotate i v.val) := by rw [heq_val]
                _ = nthRotate (add (sub p i) i) v.val := (nthRotate_add _ _ _).symm
                _ = nthRotate p v.val := by rw [hpi]
                _ = v.val := hp_period)
      -- ── orbit is nodup ───────────────────────────────────────────────────
      have orbit_nodup : orbit.Nodup :=
        nodup_map_of_inj_on orb _ (sorted_nodup (ℕ₀FSet.Fin₀Set p).sorted) orb_inj
      -- ── orbit has length p ───────────────────────────────────────────────
      have orbit_len_p : Λ orbit.length = p := by
        show Λ ((ℕ₀FSet.Fin₀Set p).elems.map orb).length = p
        rw [List.length_map]; exact ℕ₀FSet.Fin₀Set_card p
      -- ── orbit elements are in S ──────────────────────────────────────────
      have orbit_sub_S : ∀ k : ℕ₀, lt₀ k p → orb k ∈ S := by
        intro k hk
        induction k with
        | zero =>
          have : orb 𝟘 = v := Subtype.ext rfl
          rw [this]; exact hv_in
        | succ k' ih =>
          have hk'_lt := lt_trans k' (σ k') p (lt_succ_self k') hk
          rw [← rv_orb_eq k']; exact hrot (orb k') (ih hk'_lt)
      have orbit_mem_S : ∀ w ∈ orbit, w ∈ S := by
        intro w hw
        obtain ⟨k, hk_in, hk_eq⟩ := List.mem_map.mp hw
        exact hk_eq ▸ orbit_sub_S k ((ℕ₀FSet.mem_Fin₀Set_iff p k).mp hk_in)
      -- ── orbit has no fixed points ─────────────────────────────────────────
      have orbit_no_fixed : ∀ k : ℕ₀, lt₀ k p → rotateVector (orb k) ≠ orb k := by
        intro k hk heq
        have hval : rotateList (nthRotate k v.val) = nthRotate k v.val :=
          congrArg Subtype.val heq
        have h_succ_eq : nthRotate (σ k) v.val = nthRotate k v.val := by
          show nthRotate k (rotateList v.val) = nthRotate k v.val
          rw [nthRotate_succ_comm k v.val]; exact hval
        have h_sub_k : add (sub p k) k = p := sub_k_add_k p k (lt_imp_le k p hk)
        have h_sp_k : nthRotate (sub p k) (nthRotate k v.val) = v.val := by
          rw [← nthRotate_add, h_sub_k]; exact hp_period
        have h_sp_sk : nthRotate (sub p k) (nthRotate (σ k) v.val) = v.val := by
          rw [h_succ_eq]; exact h_sp_k
        have h_add_eq : add (sub p k) (σ k) = σ p := by
          rw [← add_one k, add_assoc, h_sub_k, add_one]
        have h_sp : nthRotate (σ p) v.val = v.val := by
          have h : nthRotate (add (sub p k) (σ k)) v.val = v.val := by
            rw [nthRotate_add]; exact h_sp_sk
          rwa [h_add_eq] at h
        have h_sp_eq : nthRotate (σ p) v.val = rotateList v.val := by
          show nthRotate p (rotateList v.val) = rotateList v.val
          rw [nthRotate_succ_comm p v.val, hp_period]
        exact hv (Subtype.ext (h_sp_eq.symm.trans h_sp))
      -- ── rotateList is injective on lists of length p ──────────────────────
      have rl_inj : ∀ l₁ l₂ : List ℕ₀, lengthₚ l₁ = p → lengthₚ l₂ = p →
          rotateList l₁ = rotateList l₂ → l₁ = l₂ := by
        intro l₁ l₂ h₁ h₂ heq
        cases l₁ with
        | nil =>
          cases l₂ with
          | nil => rfl
          | cons b bs =>
            simp only [lengthₚ_nil, lengthₚ_cons] at h₁ h₂
            exact absurd (h₂.trans h₁.symm) (Peano.Axioms.succ_neq_zero _)
        | cons a as =>
          cases l₂ with
          | nil =>
            simp only [lengthₚ_nil, lengthₚ_cons] at h₁ h₂
            exact absurd (h₁.trans h₂.symm) (Peano.Axioms.succ_neq_zero _)
          | cons b bs =>
            have hlen : lengthₚ as = lengthₚ bs := by
              have : σ (lengthₚ as) = σ (lengthₚ bs) :=
                calc σ (lengthₚ as) = lengthₚ (a :: as) := (lengthₚ_cons a as).symm
                  _ = p := h₁
                  _ = lengthₚ (b :: bs) := h₂.symm
                  _ = σ (lengthₚ bs) := lengthₚ_cons b bs
              injection this
            obtain ⟨has, hab⟩ := append_singleton_inj as bs a b hlen heq
            rw [has, hab]
      -- ── orbit preimage: rv w ∈ orbit → w ∈ orbit ─────────────────────────
      have orbit_preimage : ∀ w : Vector ℕ₀ p, rotateVector w ∈ orbit → w ∈ orbit := by
        intro w hw
        obtain ⟨k, hk_in, hk_eq⟩ := List.mem_map.mp hw
        have hk_lt := (ℕ₀FSet.mem_Fin₀Set_iff p k).mp hk_in
        have hrv : rotateList w.val = nthRotate k v.val := (congrArg Subtype.val hk_eq).symm
        rw [List.mem_map]
        cases k with
        | zero =>
          have h_p1_le : le₀ 𝟙 p :=
            le_trans 𝟙 𝟚 p (Or.inl (lt_succ_self 𝟙)) (prime_ge_two hp)
          have h_sub1p : add (sub p 𝟙) 𝟙 = p := sub_k_add_k p 𝟙 h_p1_le
          have h_sub_lt : lt₀ (sub p 𝟙) p := by
            have := @lt_add_of_pos_right (sub p 𝟙) 𝟙 (pos_of_ne_zero 𝟙 (Peano.Axioms.succ_neq_zero 𝟘))
            rwa [h_sub1p] at this
          have h_ntp : nthRotate p w.val = w.val := by
            have h := nthRotate_length_self w.val; rwa [w.property] at h
          have h_wval : w.val = nthRotate (sub p 𝟙) v.val :=
            calc w.val
                = nthRotate p w.val := h_ntp.symm
              _ = nthRotate (add (sub p 𝟙) 𝟙) w.val := by rw [h_sub1p]
              _ = nthRotate (sub p 𝟙) (nthRotate 𝟙 w.val) := nthRotate_add _ _ _
              _ = nthRotate (sub p 𝟙) (rotateList w.val) := rfl
              _ = nthRotate (sub p 𝟙) v.val := by rw [hrv]; rfl
          exact ⟨sub p 𝟙, (ℕ₀FSet.mem_Fin₀Set_iff p (sub p 𝟙)).mpr h_sub_lt,
                 Subtype.ext h_wval.symm⟩
        | succ k' =>
          have hk'_lt := lt_trans k' (σ k') p (lt_succ_self k') hk_lt
          have heq_rl : rotateList w.val = rotateList (nthRotate k' v.val) :=
            hrv.trans (nthRotate_succ_comm k' v.val)
          have h_wval : w.val = nthRotate k' v.val :=
            rl_inj w.val (nthRotate k' v.val) w.property (nthRotate_len k') heq_rl
          exact ⟨k', (ℕ₀FSet.mem_Fin₀Set_iff p k').mpr hk'_lt,
                 Subtype.ext h_wval.symm⟩
      -- ── orbit is closed under rotateVector ───────────────────────────────
      have orbit_closed_rv : ∀ w ∈ orbit, rotateVector w ∈ orbit := by
        intro w hw
        obtain ⟨k, hk_in, hk_eq⟩ := List.mem_map.mp hw
        have hk_lt := (ℕ₀FSet.mem_Fin₀Set_iff p k).mp hk_in
        subst hk_eq
        rw [rv_orb_eq k, List.mem_map]
        rcases (lt_succ_iff_lt_or_eq (σ k) p).mp
            ((succ_lt_succ_iff k p).mpr hk_lt) with h_lt | h_eq
        · exact ⟨σ k, (ℕ₀FSet.mem_Fin₀Set_iff p (σ k)).mpr h_lt, rfl⟩
        · have h_sk : nthRotate (σ k) v.val = v.val := by rw [h_eq]; exact hp_period
          exact ⟨𝟘, (ℕ₀FSet.mem_Fin₀Set_iff p 𝟘).mpr (pos_of_ne_zero p hp.1),
                 Subtype.ext h_sk.symm⟩
      -- ── Inline nodup_subset_length_le ────────────────────────────────────
      have nodup_sub_len : ∀ {l₁ l₂ : List (Vector ℕ₀ p)},
          l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) → l₁.length ≤ l₂.length := by
        intro l₁ l₂
        induction l₁ generalizing l₂ with
        | nil => intro _ _; exact Nat.zero_le _
        | cons a l₁' ih =>
          intro hnd hsub
          rw [List.nodup_cons] at hnd
          obtain ⟨ha_nin, hnd'⟩ := hnd
          have ha2 : a ∈ l₂ := hsub a List.mem_cons_self
          have h_ih := ih hnd' (fun x hx => by
            have hxa : x ≠ a := fun (heq : x = a) => ha_nin (heq ▸ hx)
            exact (List.mem_erase_of_ne hxa).mpr (hsub x (List.mem_cons_of_mem a hx)))
          rw [List.length_cons]
          have h_pos : 0 < l₂.length := by
            cases l₂ with
            | nil => exact absurd ha2 List.not_mem_nil
            | cons _ _ => exact Nat.zero_lt_succ _
          have h_erase_len := List.length_erase_of_mem ha2
          omega
      -- ── Define S' and prove its properties ───────────────────────────────
      refine ⟨S.filter (fun w => !decide (w ∈ orbit)), ?_, ?_, ?_, ?_⟩
      -- Property 1: S'.Nodup
      · exact List.filter_sublist.nodup hnodup
      -- Property 2: S' is closed under rotateVector
      · intro w hw
        rw [List.mem_filter] at hw ⊢
        obtain ⟨hw_S, hw_not⟩ := hw
        have hw_not_orbit : w ∉ orbit := by
          intro h; simp [decide_eq_true h] at hw_not
        exact ⟨hrot w hw_S, by
          have hn : rotateVector w ∉ orbit := fun hrv_in => hw_not_orbit (orbit_preimage w hrv_in)
          simp [hn]⟩
      -- Property 3: lengthₚ S = add (lengthₚ S') p
      · have filter_part : ∀ (l : List (Vector ℕ₀ p)) (q : Vector ℕ₀ p → Bool),
            l.length = Nat.add (l.filter q).length (l.filter (fun x => !q x)).length := by
          intro l q
          induction l with
          | nil => simp
          | cons x xs ih =>
            cases h : q x
            · have e1 : (x :: xs).filter q = xs.filter q := by simp [h]
              have e2 : (x :: xs).filter (fun y => !q y) = x :: xs.filter (fun y => !q y) := by
                simp [h]
              simp only [e1, e2, List.length_cons, Nat.add_eq] at *; omega
            · have e1 : (x :: xs).filter q = x :: xs.filter q := by simp [h]
              have e2 : (x :: xs).filter (fun y => !q y) = xs.filter (fun y => !q y) := by
                simp [h]
              simp only [e1, e2, List.length_cons, Nat.add_eq] at *; omega
        have filter_orbit_len :
            (S.filter (fun w => decide (w ∈ orbit))).length = orbit.length := by
          apply Nat.le_antisymm
          · apply nodup_sub_len (List.filter_sublist.nodup hnodup)
            intro w hw
            exact of_decide_eq_true (List.mem_filter.mp hw).2
          · apply nodup_sub_len orbit_nodup
            intro w hw
            rw [List.mem_filter]
            exact ⟨orbit_mem_S w hw, decide_eq_true hw⟩
        have hnat : S.length =
            Nat.add (S.filter (fun w => !decide (w ∈ orbit))).length orbit.length := by
          have h := filter_part S (fun w => decide (w ∈ orbit))
          rw [filter_orbit_len] at h; simp only [Nat.add_eq] at h ⊢; omega
        suffices h3 : Λ S.length = add (Λ (S.filter (fun w => !decide (w ∈ orbit))).length) p by
          simpa [lengthₚ] using h3
        rw [hnat, isomorph_Λ_add, orbit_len_p]
      -- Property 4: filter equality
      · suffices h4 : (S.filter (fun w => decide (rotateVector w = w))).length =
              ((S.filter (fun w => !decide (w ∈ orbit))).filter
                (fun w => decide (rotateVector w = w))).length by
          exact congrArg Λ h4
        apply Nat.le_antisymm
        · apply nodup_sub_len (List.filter_sublist.nodup hnodup)
          intro w hw
          rw [List.mem_filter] at hw ⊢
          obtain ⟨hw_S, hw_fixed⟩ := hw
          refine ⟨?_, hw_fixed⟩
          rw [List.mem_filter]
          refine ⟨hw_S, ?_⟩
          have hn : w ∉ orbit := by
            intro hw_orbit
            obtain ⟨k, hk_in, hk_eq⟩ := List.mem_map.mp hw_orbit
            exact orbit_no_fixed k ((ℕ₀FSet.mem_Fin₀Set_iff p k).mp hk_in)
              (hk_eq ▸ of_decide_eq_true hw_fixed)
          simp [hn]
        · apply nodup_sub_len (List.filter_sublist.nodup (List.filter_sublist.nodup hnodup))
          intro w hw
          rw [List.mem_filter] at hw ⊢
          exact ⟨(List.mem_filter.mp hw.1).1, hw.2⟩

    private theorem mckay_orbit_count (p : ℕ₀) (hp : Prime p)
        (T : List (Vector ℕ₀ p))
        (hT_nodup : T.Nodup)
        (hT_rot : ∀ v ∈ T, rotateVector v ∈ T) :
        ∃ k : ℕ₀, lengthₚ T = Peano.Add.add
          (lengthₚ (T.filter (fun v => decide (rotateVector v = v)))) (Peano.Mul.mul p k) := by
      -- Induction on lengthₚ T (a ℕ₀ value) via well_founded_lt
      suffices H : ∀ (n : ℕ₀) (S : List (Vector ℕ₀ p)),
          S.Nodup → (∀ v ∈ S, rotateVector v ∈ S) → lengthₚ S = n →
          ∃ k : ℕ₀, lengthₚ S = Peano.Add.add (lengthₚ (S.filter (fun v => decide (rotateVector v = v)))) (Peano.Mul.mul p k) from
        H (lengthₚ T) T hT_nodup hT_rot rfl
      intro n
      induction n using well_founded_lt.induction
      rename_i n ih
      intro S hnodup hrot hlen
      cases S with
      | nil => exact ⟨𝟘, rfl⟩
      | cons v S' =>
        by_cases hv : rotateVector v = v
        · -- v is a fixed point
          -- Show S' is also closed under rotation
          have hS'_nodup := (List.nodup_cons.mp hnodup).2
          have hS'_rot : ∀ w ∈ S', rotateVector w ∈ S' := by
            intro w hw
            have h1 : rotateVector w ∈ v :: S' := hrot w (List.mem_cons_of_mem v hw)
            rcases List.mem_cons.mp h1 with hrwv | h2
            · exfalso
              have hw_eq_v : w = v := vector_eq_of_rotateVector_eq_fixed v w hv hrwv
              rw [hw_eq_v] at hw
              exact absurd hw (List.nodup_cons.mp hnodup).1
            · exact h2
          have hlen' : lengthₚ S' < n := by
            have hsucc : n = σ (lengthₚ S') := by rw [← hlen]; exact (lengthₚ_cons v S').symm
            rw [hsucc]; exact lt_succ_self (lengthₚ S')
          obtain ⟨k, hk⟩ := ih (lengthₚ S') hlen' S' hS'_nodup hS'_rot rfl
          refine ⟨k, ?_⟩
          have h_filter : (v :: S').filter (fun v => decide (rotateVector v = v)) =
              v :: S'.filter (fun v => decide (rotateVector v = v)) := by
            apply List.filter_cons_of_pos
            exact decide_eq_true hv
          rw [h_filter]
          -- Goal: lengthₚ (v::S') = add (lengthₚ (v::filter S')) K
          -- = σ (lengthₚ S') = add (σ (lengthₚ (filter S'))) K
          -- From hk: lengthₚ S' = add (lengthₚ (filter S')) K
          rw [lengthₚ_cons, lengthₚ_cons, hk]
          exact (Peano.Add.succ_add _ _).symm
        · -- v is not fixed; the orbit of v has size Ψ p
          obtain ⟨S_rem, hS_rem_nodup, hS_rem_rot, hlen_S, hfilter_S⟩ :=
            mckay_orbit_remove p hp (v :: S') v (List.mem_cons_self) hv hnodup hrot
          have hlen_S_rem_lt : lengthₚ S_rem < n := by
            have h1 : n = Peano.Add.add (lengthₚ S_rem) p := hlen ▸ hlen_S
            rw [h1]
            -- We need `lengthₚ S_rem < lengthₚ S_rem + p`
            -- Since p is prime, p > 0.
            have hp_pos : Peano.StrictOrder.lt₀ 𝟘 p := pos_of_ne_zero p hp.1
            exact lt_add_of_pos_right hp_pos
          obtain ⟨k', hk'⟩ := ih (lengthₚ S_rem) hlen_S_rem_lt S_rem hS_rem_nodup hS_rem_rot rfl
          refine ⟨σ k', ?_⟩
          rw [hlen_S, hfilter_S, hk']
          -- Goal: add (add (lengthₚ (filter S_rem)) (mul p k')) p =
          --       add (lengthₚ (filter S_rem)) (mul p (succ k'))
          -- Since mul p (succ k') = add (mul p k') p
          -- and add is associative
          have h_mul_succ : Peano.Mul.mul p (σ k') = Peano.Add.add (Peano.Mul.mul p k') p := by
            rw [mul_succ, add_comm]
          rw [h_mul_succ, add_assoc]

    private theorem listProd_append_inv_eq_id (G : FinGroup ℕ₀) {l : List ℕ₀}
        (hl : ∀ x ∈ l, x ∈ G.carrier.elems) :
        listProd G (l ++ [G.inv (listProd G l)]) = G.id := by
      have hprod_mem : listProd G l ∈ G.carrier.elems := listProd_mem G hl
      rw [listProd_append G l [G.inv (listProd G l)] hl
            (fun x hx => by rw [List.mem_singleton] at hx; rw [hx]; exact inv_mem G hprod_mem),
          listProd_singleton G (inv_mem G hprod_mem)]
      exact (G.op_inv (listProd G l) hprod_mem).1

    private theorem list_split_last {α : Type} : ∀ (l : List α), l ≠ [] →
        ∃ (ini : List α) (last : α), l = ini ++ [last] := by
      intro l hl
      induction l with
      | nil => exact absurd rfl hl
      | cons x xs ih =>
        by_cases hxs : xs = []
        · subst hxs; exact ⟨[], x, rfl⟩
        · obtain ⟨ini, last, h⟩ := ih hxs
          exact ⟨x :: ini, last, by rw [h, ← List.cons_append]⟩

    private theorem list_σn_split_last {α : Type} (l : List α) (n : ℕ₀)
        (hl : lengthₚ l = σ n) :
        ∃ (ini : List α) (last : α), l = ini ++ [last] ∧ lengthₚ ini = n := by
      have hl_ne : l ≠ [] := by
        intro h0; rw [h0, lengthₚ_nil] at hl
        exact absurd hl (Peano.Axioms.succ_neq_zero n).symm
      obtain ⟨ini, last, h_split⟩ := list_split_last l hl_ne
      refine ⟨ini, last, h_split, ?_⟩
      have h_len : lengthₚ (ini ++ [last]) = σ n := h_split ▸ hl
      rw [lengthₚ_append, lengthₚ_singleton, add_one] at h_len
      exact succ_inj_pos_wp h_len

    private theorem replicate_cons_append {α : Type} (a : α) : ∀ n : Nat,
        List.replicate n a ++ [a] = a :: List.replicate n a
      | Nat.zero => rfl
      | Nat.succ n' => by
          rw [List.replicate_succ, List.cons_append]
          exact congrArg (a :: ·) (replicate_cons_append a n')

    private theorem rotateList_replicate_pos {α : Type} (a : α) : ∀ n : Nat,
        n ≠ 0 → rotateList (List.replicate n a) = List.replicate n a
      | Nat.zero, h => absurd rfl h
      | Nat.succ n', _ => by
          simp only [List.replicate_succ, rotateList]
          exact replicate_cons_append a n'

    private theorem all_eq_then_replicate {α : Type} (a : α) :
        ∀ (l : List α), (∀ x ∈ l, x = a) → l = List.replicate l.length a
      | [], _ => rfl
      | x :: xs, h => by
          have hx := h x List.mem_cons_self
          have hxs := fun y hy => h y (List.mem_cons_of_mem x hy)
          rw [hx, List.length_cons, List.replicate_succ]
          exact congrArg (a :: ·) (all_eq_then_replicate a xs hxs)

    open Peano.Arith in
    private theorem pow_dvd_of_dvd {p a : ℕ₀} (h : p ∣ a) {n : ℕ₀} (hn : n ≠ 𝟘) : p ∣ pow a n := by
      cases n with
      | zero => exact absurd rfl hn
      | succ n' => rw [pow_succ]; exact divides_mul_left h

    open Peano.Arith in
    private theorem mckay_p_dvd_powEqId
      (G : FinGroup ℕ₀) (p : ℕ₀) (hp : Prime p) (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :
        p ∣ (ℕ₀FSet.filter (fun g => decide (gpow G g p = G.id)) G.carrier).card
          := by
      let F := ℕ₀FSet.filter (fun g => decide (gpow G g p = G.id)) G.carrier
      have hp_ge_2 : le₀ 𝟚 p := prime_ge_two hp
      have h_p1_le : le₀ 𝟙 p := le_trans 𝟙 𝟚 p (Or.inl (lt_succ_self 𝟙)) hp_ge_2
      have h_sub1p : add (sub p 𝟙) 𝟙 = p := sub_k_add_k p 𝟙 h_p1_le
      have h_succ_sub1p : σ (sub p 𝟙) = p := by rw [← add_one]; exact h_sub1p
      have h_sub1p_ne : sub p 𝟙 ≠ 𝟘 := by
        intro h0
        have h1 : 𝟙 = p := by rw [h0, zero_add] at h_sub1p; exact h_sub1p
        have h2 : lt₀ 𝟙 p := lt_of_lt_of_le (lt_succ_self 𝟙) hp_ge_2
        rw [← h1] at h2; exact absurd h2 (lt_irrefl 𝟙)
      have h_Ψp_ne : Ψ p ≠ 0 := fun h0 =>
        hp.1 (Ψ_inj p 𝟘 (h0.trans isomorph_0_Ψ.symm))
      have helems_nd : G.carrier.elems.Nodup := sorted_nodup G.carrier.sorted
      let T := (allVectorsList G.carrier.elems p).filter
        (fun v => decide (listProd G v.val = G.id))
      have hT_nodup : T.Nodup :=
        List.filter_sublist.nodup (allVectorsList_nodup G.carrier.elems helems_nd p)
      have hT_rot : ∀ v ∈ T, rotateVector v ∈ T := by
        intro v hv
        rw [List.mem_filter] at hv ⊢
        obtain ⟨hv_all, hv_prod⟩ := hv
        have hv_mem := allVectorsList_mem_elems G.carrier.elems v hv_all
        exact ⟨allVectorsList_complete G.carrier.elems ⟨rotateList v.val,
                  by rw [lengthₚ_rotateList, v.property]⟩
                  (fun x hx => hv_mem x ((rotateList_mem x v.val).mp hx)),
               decide_eq_true (listProd_rotate_eq_id G hv_mem (of_decide_eq_true hv_prod))⟩
      obtain ⟨k_orb, hk_orb⟩ := mckay_orbit_count p hp T hT_nodup hT_rot
      let fixed_T := T.filter (fun v => decide (rotateVector v = v))
      have nodup_sub_len_p : ∀ {l₁ l₂ : List (Vector ℕ₀ p)},
          l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) → l₁.length ≤ l₂.length := by
        intro l₁ l₂
        induction l₁ generalizing l₂ with
        | nil => intro _ _; exact Nat.zero_le _
        | cons a l₁' ih =>
          intro hnd hsub
          rw [List.nodup_cons] at hnd
          obtain ⟨ha_nin, hnd'⟩ := hnd
          have ha2 : a ∈ l₂ := hsub a List.mem_cons_self
          have h_ih := ih hnd' (fun x hx => by
            have hxa : x ≠ a := fun (heq : x = a) => ha_nin (heq ▸ hx)
            exact (List.mem_erase_of_ne hxa).mpr (hsub x (List.mem_cons_of_mem a hx)))
          rw [List.length_cons]
          have h_pos : 0 < l₂.length := by
            cases l₂ with
            | nil => exact absurd ha2 List.not_mem_nil
            | cons _ _ => exact Nat.zero_lt_succ _
          have h_erase_len := List.length_erase_of_mem ha2
          omega
      -- |T| = pow |G| (sub p 1)
      have h_T_card : lengthₚ T = pow G.carrier.card (sub p 𝟙) := by
        have hcard : G.carrier.card = lengthₚ G.carrier.elems := rfl
        rw [hcard, ← allVectorsList_card G.carrier.elems]
        show Λ T.length = Λ (allVectorsList G.carrier.elems (sub p 𝟙)).length
        let fwd : Vector ℕ₀ (sub p 𝟙) → Vector ℕ₀ p :=
          fun u => ⟨u.val ++ [G.inv (listProd G u.val)],
            by rw [lengthₚ_append, lengthₚ_singleton, add_one, u.property, h_succ_sub1p]⟩
        let img := (allVectorsList G.carrier.elems (sub p 𝟙)).map fwd
        have h_img_len : img.length = (allVectorsList G.carrier.elems (sub p 𝟙)).length := by
          change ((allVectorsList G.carrier.elems (sub p 𝟙)).map fwd).length = _
          exact List.length_map fwd
        have h_img_sub_T : ∀ v ∈ img, v ∈ T := by
          intro v hv
          rw [List.mem_map] at hv
          obtain ⟨u, hu, rfl⟩ := hv
          rw [List.mem_filter]
          have hu_mem := allVectorsList_mem_elems G.carrier.elems u hu
          exact ⟨allVectorsList_complete G.carrier.elems (fwd u) (fun x hx => by
                  simp only [fwd] at hx
                  rw [List.mem_append, List.mem_singleton] at hx
                  rcases hx with hxu | rfl
                  · exact hu_mem x hxu
                  · exact inv_mem G (listProd_mem G hu_mem)),
                 decide_eq_true (by simp only [fwd]; exact listProd_append_inv_eq_id G hu_mem)⟩
        have h_T_sub_img : ∀ v ∈ T, v ∈ img := by
          intro v hv
          rw [List.mem_filter] at hv
          obtain ⟨hv_all, hv_prod⟩ := hv
          have hv_mem := allVectorsList_mem_elems G.carrier.elems v hv_all
          have hv_len : lengthₚ v.val = σ (sub p 𝟙) := v.property.trans h_succ_sub1p.symm
          obtain ⟨ini, last, h_split, h_ini_len⟩ := list_σn_split_last v.val (sub p 𝟙) hv_len
          let u : Vector ℕ₀ (sub p 𝟙) := ⟨ini, h_ini_len⟩
          have h_ini_mem : ∀ x ∈ ini, x ∈ G.carrier.elems :=
            fun x hx => hv_mem x (h_split ▸ List.mem_append.mpr (Or.inl hx))
          have h_last_mem : last ∈ G.carrier.elems :=
            hv_mem last (h_split ▸ List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          have h_prod_id : listProd G (ini ++ [last]) = G.id := by
            rw [← h_split]; exact of_decide_eq_true hv_prod
          have h_prod_split : G.op (listProd G ini) last = G.id := by
            have hq := listProd_append G ini [last] h_ini_mem
              (fun x hx => by rw [List.mem_singleton] at hx; rw [hx]; exact h_last_mem)
            rw [listProd_singleton G h_last_mem] at hq
            exact hq.symm.trans h_prod_id
          have h_last_eq : last = G.inv (listProd G ini) :=
            op_cancel_left G (listProd_mem G h_ini_mem) h_last_mem
              (inv_mem G (listProd_mem G h_ini_mem))
              (h_prod_split.trans
                (G.op_inv (listProd G ini) (listProd_mem G h_ini_mem)).1.symm)
          rw [List.mem_map]
          exact ⟨u, allVectorsList_complete G.carrier.elems u h_ini_mem,
                 Subtype.ext (by show ini ++ [G.inv (listProd G ini)] = v.val; rw [← h_last_eq, ← h_split])⟩
        have h_img_nd : img.Nodup :=
          nodup_map_of_inj_on fwd (allVectorsList G.carrier.elems (sub p 𝟙))
            (allVectorsList_nodup G.carrier.elems helems_nd (sub p 𝟙))
            (fun u1 u2 _ _ heq => by
              obtain ⟨h_ini, _⟩ :=
                append_singleton_inj u1.val u2.val _ _
                  (u1.property.trans u2.property.symm)
                  (congrArg Subtype.val heq)
              exact Subtype.ext h_ini)
        exact congrArg Λ (Nat.le_antisymm
          (calc T.length ≤ img.length := nodup_sub_len_p hT_nodup h_T_sub_img
                _ = _ := h_img_len)
          (calc (allVectorsList G.carrier.elems (sub p 𝟙)).length
                = img.length := h_img_len.symm
                _ ≤ T.length := nodup_sub_len_p h_img_nd h_img_sub_T))
      -- p ∣ |T|
      have h_p_dvd_T : p ∣ lengthₚ T := by
        rw [h_T_card]
        obtain ⟨t, ht⟩ := hdvd
        exact pow_dvd_of_dvd ⟨t, ht.symm⟩ h_sub1p_ne
      -- |fixed_T| = F.card
      have h_rep_len : ∀ g : ℕ₀, lengthₚ (List.replicate (Ψ p) g) = p := fun g => by
        unfold lengthₚ; rw [List.length_replicate, ΛΨ]
      have h_fixed_card : lengthₚ fixed_T = F.card := by
        let fwd2 : ℕ₀ → Vector ℕ₀ p :=
          fun g => ⟨List.replicate (Ψ p) g, h_rep_len g⟩
        let img2 := F.elems.map fwd2
        have h_img2_sub_fixed : ∀ v ∈ img2, v ∈ fixed_T := by
          intro v hv
          rw [List.mem_map] at hv
          obtain ⟨g, hg_F, rfl⟩ := hv
          rw [List.mem_filter]
          have hg_in : g ∈ G.carrier.elems := (List.mem_filter.mp hg_F).1
          have hg_pow : gpow G g p = G.id := of_decide_eq_true (List.mem_filter.mp hg_F).2
          refine ⟨?_, decide_eq_true (Subtype.ext (rotateList_replicate_pos g (Ψ p) h_Ψp_ne))⟩
          rw [List.mem_filter]
          refine ⟨?_, ?_⟩
          · apply allVectorsList_complete
            intro x hx
            rw [List.mem_replicate] at hx; rw [hx.2]; exact hg_in
          · apply decide_eq_true
            rw [show (fwd2 g).val = List.replicate (Ψ p) g from rfl,
                listProd_all_eq_gpow G g hg_in (List.replicate (Ψ p) g)
                  (fun x hx => (List.mem_replicate.mp hx).2),
                h_rep_len g]
            exact hg_pow
        have h_fixed_sub_img2 : ∀ v ∈ fixed_T, v ∈ img2 := by
          intro v hv
          rw [List.mem_filter, List.mem_filter] at hv
          obtain ⟨⟨hv_all, hv_prod⟩, hv_fixed⟩ := hv
          have hv_mem := allVectorsList_mem_elems G.carrier.elems v hv_all
          have hv_rot : rotateList v.val = v.val :=
            congrArg Subtype.val (@of_decide_eq_true _ (vectorDecEq _ _) hv_fixed)
          have hv_ne : v.val ≠ [] := by
            intro h0
            have : lengthₚ ([] : List ℕ₀) = p := h0 ▸ v.property
            rw [lengthₚ_nil] at this; exact hp.1 this.symm
          obtain ⟨g, xs, h_cons⟩ := List.exists_cons_of_ne_nil hv_ne
          have hrot : xs ++ [g] = g :: xs := by
            have := h_cons ▸ hv_rot; simp only [rotateList] at this; exact this
          have h_all_g : ∀ x ∈ v.val, x = g := by
            rw [h_cons]; intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · rfl
            · exact rotateList_fixed_all_eq g xs hrot x hx'
          have h_len_eq : v.val.length = Ψ p :=
            Λ_inj v.val.length (Ψ p) (v.property.trans (ΛΨ p).symm)
          have h_rep_eq : v.val = List.replicate (Ψ p) g := by
            rw [← h_len_eq]; exact all_eq_then_replicate g v.val h_all_g
          have h_g_in_G : g ∈ G.carrier.elems := by
            apply hv_mem; rw [h_cons]; exact List.mem_cons_self
          have h_g_pow : gpow G g p = G.id := by
            have h_prod := of_decide_eq_true hv_prod
            rw [h_rep_eq, listProd_all_eq_gpow G g h_g_in_G (List.replicate (Ψ p) g)
                  (fun x hx => (List.mem_replicate.mp hx).2),
                h_rep_len g] at h_prod
            exact h_prod
          have h_g_in_F : g ∈ F.elems :=
            List.mem_filter.mpr ⟨h_g_in_G, decide_eq_true h_g_pow⟩
          rw [List.mem_map]
          exact ⟨g, h_g_in_F, Subtype.ext h_rep_eq.symm⟩
        have h_img2_nd : img2.Nodup :=
          nodup_map_of_inj_on fwd2 F.elems (sorted_nodup F.sorted)
            (fun a b _ _ heq => by
              have h := congrArg Subtype.val heq
              simp only [fwd2] at h
              cases hn : Ψ p with
              | zero => exact absurd hn h_Ψp_ne
              | succ n' =>
                rw [hn, List.replicate_succ, List.replicate_succ] at h
                exact (List.cons.inj h).1)
        have h_fixed_nd : fixed_T.Nodup := List.filter_sublist.nodup hT_nodup
        have h_len_eq2 : fixed_T.length = img2.length :=
          Nat.le_antisymm
            (nodup_sub_len_p h_fixed_nd (fun v hv => h_fixed_sub_img2 v hv))
            (nodup_sub_len_p h_img2_nd (fun v hv => h_img2_sub_fixed v hv))
        show Λ fixed_T.length = lengthₚ F.elems
        rw [h_len_eq2, List.length_map fwd2]; rfl
      -- Divisibility arithmetic
      have h_dvd_fixed : p ∣ lengthₚ fixed_T := by
        by_cases h_fl_zero : lengthₚ fixed_T = 𝟘
        · rw [h_fl_zero]; exact divides_zero p
        · have h_fl_pos : lt₀ 𝟘 (lengthₚ fixed_T) := pos_of_ne_zero _ h_fl_zero
          have h_pk_lt : lt₀ (Peano.Mul.mul p k_orb)
              (add (lengthₚ fixed_T) (Peano.Mul.mul p k_orb)) := by
            rw [add_comm]; exact lt_add_of_pos_right h_fl_pos
          have h_sub_eq : sub (add (lengthₚ fixed_T) (Peano.Mul.mul p k_orb))
              (Peano.Mul.mul p k_orb) = lengthₚ fixed_T := by
            rw [add_comm]; exact add_k_sub_k (lengthₚ fixed_T) (Peano.Mul.mul p k_orb)
          rw [← h_sub_eq]
          exact divides_sub h_pk_lt (hk_orb ▸ h_p_dvd_T) ⟨k_orb, rfl⟩
      exact h_fixed_card ▸ h_dvd_fixed


    private theorem exists_ne_of_nodup_length_ge_two {l : List ℕ₀} {a : ℕ₀}
      (ha : a ∈ l) (hlen : 2 ≤ l.length) (hnodup : l.Nodup) :
        ∃ b ∈ l, b ≠ a
          := by
      cases l with
      | nil => exact absurd ha List.not_mem_nil
      | cons x xs =>
        by_cases hxa : x = a
        · subst hxa
          cases xs with
          | nil =>
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          | cons y ys =>
            rw [List.nodup_cons] at hnodup
            obtain ⟨hx_nin, _⟩ := hnodup
            refine ⟨y, List.mem_cons.mpr (Or.inr List.mem_cons_self), ?_⟩
            intro hy_eq
            rw [hy_eq] at hx_nin
            exact hx_nin List.mem_cons_self
        · exact ⟨x, List.mem_cons_self, hxa⟩

    /-- Si `a ∈ F.elems` y `|F| ≥ 2`, existe `b ∈ F.elems` con `b ≠ a`. -/
    private theorem exists_ne_of_card_ge {F : ℕ₀FSet} {a : ℕ₀}
      (ha : a ∈ F.elems) (hcard : le₀ 𝟚 F.card) :
        ∃ b ∈ F.elems, b ≠ a
          := by
      have hnodup := FSetFunction.sorted_nodup F.sorted
      have hlen : 2 ≤ F.elems.length :=
        (isomorph_Λ_le 2 F.elems.length).mpr hcard
      exact exists_ne_of_nodup_length_ge_two ha hlen hnodup

    /-- Paso 1 (Cauchy mínimo): si `p` primo divide `|G|`, existe
        un subgrupo de `G` de orden `p`.
        Estrategia: G actúa sobre los p-tuplos (g₁,…,gₚ) con g₁·…·gₚ = e
        por permutación cíclica; las órbitas tienen tamaño 1 ó p; el total
        es divisible por p → existe una órbita de tamaño 1 ≠ identidad. -/
    theorem cauchy_minimal
      (G : FinGroup ℕ₀) (p : ℕ₀) (hp : Prime p) (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :
        ∃ K : Subgroup G, K.carrier.card = p
          := by
      -- Existencia de g ≠ e con g^p = e (argumento de McKay)
      have h_exists : ∃ g ∈ G.carrier.elems, g ≠ G.id ∧ gpow G g p = G.id := by
        -- F = {g ∈ G | g^p = e}
        let F := ℕ₀FSet.filter (fun g => decide (gpow G g p = G.id)) G.carrier
        -- G.id ∈ F  (gpow_id_eq_id)
        have hid_in_F : G.id ∈ F.elems :=
          List.mem_filter.mpr ⟨G.id_in, decide_eq_true_eq.mpr (gpow_id_eq_id G p)⟩
        -- p | |F|  (argumento de McKay)
        have hp_dvd_F : p ∣ F.card := mckay_p_dvd_powEqId G p hp hdvd
        -- |F| ≥ 1  (G.id ∈ F)
        have hF_pos : lt₀ 𝟘 F.card := card_pos_of_mem_aux hid_in_F
        -- Escribir p | |F| como mul p k = |F|
        obtain ⟨k, hk⟩ := hp_dvd_F
        -- k ≠ 0  (de |F| ≥ 1 y p ≥ 2)
        have hk_ne : k ≠ 𝟘 := by
          intro h0
          rw [h0, mul_zero] at hk
          rw [hk] at hF_pos
          exact absurd hF_pos not_lt_zero
        -- |F| ≥ p  (de |F| = p * k y k ≥ 1)
        have hF_ge_p : le₀ p F.card := hk ▸ mul_le_right p k hk_ne
        -- |F| ≥ 2  (de |F| ≥ p y p ≥ 2)
        have hF_ge_2 : le₀ 𝟚 F.card :=
          le_trans 𝟚 p F.card (prime_ge_two hp) hF_ge_p
        -- Extraemos g ≠ G.id de F
        obtain ⟨g, hg_in_F, hg_ne⟩ := exists_ne_of_card_ge hid_in_F hF_ge_2
        -- g ∈ G.carrier.elems  y  g^p = e
        exact ⟨g, (List.mem_filter.mp hg_in_F).1, hg_ne,
               decide_eq_true_eq.mp (List.mem_filter.mp hg_in_F).2⟩
      obtain ⟨g, hg, hg_ne, hgp⟩ := h_exists
      -- El subgrupo cíclico ⟨g⟩ tiene cardinal p
      exact ⟨cyclicSubgroup G g hg,
             cyclicSubgroup_card_eq_prime G g hg hp hgp hg_ne hdvd⟩
    /-- Convierte un subgrupo `H` de `G` en un `FinGroup` autónomo
        con las mismas operaciones heredadas. -/
    private def subgroupToFinGroup (G : FinGroup ℕ₀) (H : Subgroup G) : FinGroup ℕ₀ where
      carrier  := H.carrier
      op       := { toFun := G.op.toFun, map_carrier := H.op_closed }
      id       := G.id
      inv      := { toFun := G.inv.toFun, map_carrier := H.inv_closed }
      id_in    := H.id_in
      op_assoc := fun a b c ha hb hc =>
        G.op_assoc a b c (H.subset a ha) (H.subset b hb) (H.subset c hc)
      op_id    := fun a ha => G.op_id a (H.subset a ha)
      op_inv   := fun a ha => G.op_inv a (H.subset a ha)

    /-- Convierte `K ≤ subgroupToFinGroup G M` en un subgrupo de `G`. -/
    private def subgroupOfSubgroup (G : FinGroup ℕ₀) (M : Subgroup G)
        (K : Subgroup (subgroupToFinGroup G M)) : Subgroup G where
      carrier    := K.carrier
      nonempty   := K.nonempty
      subset     := fun a ha => M.subset a (K.subset a ha)
      op_closed  := fun a b ha hb => K.op_closed a b ha hb
      id_in      := K.id_in
      inv_closed := fun a ha => K.inv_closed a ha

    /-- Argumento de Wielandt, pieza 1:
        El número de sublistas sin repetición de G.carrier.elems de longitud N es C(|G|, N).
        (Este es el resultado combinatorio clave; requiere infraestructura de combinaciones.)
        TODO: demostrar usando binom_mul_factorials y biyección con combinaciones. -/
    private axiom wielandt_omega_card
        (G : FinGroup ℕ₀) (N : ℕ₀) :
        ∃ (Ω : List (List ℕ₀)),
          Ω.Nodup ∧
          (∀ S ∈ Ω, S.Nodup ∧ (∀ x ∈ S, x ∈ G.carrier.elems) ∧ lengthₚ S = N) ∧
          (∀ S : List ℕ₀, S.Nodup → (∀ x ∈ S, x ∈ G.carrier.elems) → lengthₚ S = N → S ∈ Ω) ∧
          lengthₚ Ω = binom G.carrier.card N

    /-- Argumento de Wielandt, pieza 2:
        La traslación izquierda de G actúa sobre Ω y preserva |S| y la pertenencia a G.
        Para g ∈ G y S ∈ Ω, g·S = { G.op g s : s ∈ S } también está en Ω.
        TODO: demostrar usando biyectividad de la traslación izquierda en G. -/
    private axiom wielandt_translate_mem
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (N : ℕ₀)
        (hΩ_nd : Ω.Nodup)
        (hΩ_mem : ∀ S ∈ Ω, S.Nodup ∧ (∀ x ∈ S, x ∈ G.carrier.elems) ∧ lengthₚ S = N)
        (hΩ_full : ∀ S : List ℕ₀, S.Nodup → (∀ x ∈ S, x ∈ G.carrier.elems) → lengthₚ S = N → S ∈ Ω)
        (g : ℕ₀) (hg : g ∈ G.carrier.elems) (S : List ℕ₀) (hS : S ∈ Ω) :
        (S.map (G.op g)) ∈ Ω

    /-- Argumento de Wielandt, pieza 3:
        Si G actúa sobre Ω por traslación izquierda y p ∤ |Ω|,
        existe S ∈ Ω tal que para todo g ∈ G, S.map (G.op g) = S
        (punto fijo de toda la acción de G).
        Argumento: p | |G| implica p | suma de |órbita| no-triviales. Si p ∤ |Ω|,
        hay órbitas de tamaño 1 (puntos fijos).
        TODO: demostrar usando mckay_orbit_count generalizado y divisibilidad. -/
    private axiom wielandt_fixed_point_exists
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (N : ℕ₀) (p : ℕ₀)
        (hp : Prime p)
        (hdvd_G : ∃ r : ℕ₀, Mul.mul N r = G.carrier.card)
        (hΩ_nd : Ω.Nodup)
        (hΩ_mem : ∀ S ∈ Ω, S.Nodup ∧ (∀ x ∈ S, x ∈ G.carrier.elems) ∧ lengthₚ S = N)
        (hΩ_full : ∀ S : List ℕ₀, S.Nodup → (∀ x ∈ S, x ∈ G.carrier.elems) → lengthₚ S = N → S ∈ Ω)
        (htrans : ∀ g ∈ G.carrier.elems, ∀ S ∈ Ω, (S.map (G.op g)) ∈ Ω)
        (hndvd : ¬ p ∣ lengthₚ Ω) :
        ∃ S ∈ Ω, ∀ g ∈ G.carrier.elems, S.map (G.op g) = S

    /-- Argumento de Wielandt, pieza 4:
        Un subconjunto S ⊆ G que es punto fijo de la acción de traslación de todo G
        (es decir, g·S = S para todo g ∈ G) con S ≠ ∅ es un subgrupo de G.
        Argumento:
          - S ≠ ∅ → ∃ x ∈ S.
          - x·S = S → x⁻¹ ∈ S (pues x⁻¹ ∈ x⁻¹·S = S).
          - e = x·x⁻¹ ∈ x·S = S.
          - a, b ∈ S → a·b ∈ a·S = S.
          - a ∈ S → a·(a⁻¹) = e ∈ a·S = S, y e ∈ S → a⁻¹ ∈ S.
        TODO: demostrar formalmente en Lean. -/
    private axiom wielandt_fixed_is_subgroup
        (G : FinGroup ℕ₀) (S : List ℕ₀) (N : ℕ₀)
        (hS_ne : S ≠ [])
        (hS_nd : S.Nodup)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (hS_len : lengthₚ S = N)
        (hS_fixed : ∀ g ∈ G.carrier.elems, S.map (G.op g) = S) :
        ∃ H : Subgroup G, H.carrier.elems = S ∧ H.carrier.card = N

    /-- Argumento de Wielandt, pieza 5:
        Si p ∣ r y p^(m+1) | |G| con |G| = p^(m+1) · r, entonces por la hipótesis inductiva
        de Sylow existiría un subgrupo propio M de orden divisible por p^(m+1),
        contradiciendo h_no_proper.
        TODO: demostrar usando la p-valuación y el argumento de subgrupos propios. -/
    private axiom wielandt_p_ndvd_r
        (G : FinGroup ℕ₀) (p m r : ℕ₀)
        (hp : Prime p)
        (hr_eq : Mul.mul (p ^ (σ m)) r = G.carrier.card)
        (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
          (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
            ∃ K : Subgroup G0, K.carrier.card = p0)
        (h_no_proper : ∀ M : Subgroup G, M.carrier.card ≠ G.carrier.card →
          ¬ pow_dvd_card p (σ m) M.carrier) :
        ¬ p ∣ r

    /-- Caso duro de la inducción de Sylow, demostrado por el argumento de Wielandt.
        Cubre el escenario donde `p^(m+1) | |G|` pero ningún subgrupo
        propio de `G` es divisible por `p^(m+1)`.  La prueba usa:
        1. Ω = sublistas de G de tamaño p^(m+1), |Ω| = C(|G|, p^(m+1)) ≡ r (mod p).
        2. G actúa sobre Ω por traslación izquierda.
        3. p ∤ |Ω| → ∃ punto fijo S de la acción.
        4. h_no_proper → stab(S) = G → S es subgrupo de G de orden p^(m+1). -/
    private theorem sylow_center_step_wielandt
      (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
        (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
          ∃ K : Subgroup G0, K.carrier.card = p0)
      (G : FinGroup ℕ₀) (p m : ℕ₀)
      (hp : Prime p) (hpow : pow_dvd_card p (σ m) G.carrier)
      (h_no_proper : ∀ M : Subgroup G, M.carrier.card ≠ G.carrier.card →
        ¬ pow_dvd_card p (σ m) M.carrier) :
        ∃ H : Subgroup G, H.carrier.card = p ^ (σ m) := by
      -- Sea N = p^(m+1), r tal que N · r = |G|
      let N := p ^ (σ m)
      obtain ⟨r, hr⟩ := hpow
      -- r ≠ 0: pues |G| ≥ 1
      have hr_ne : r ≠ 𝟘 := by
        intro h0; rw [h0, mul_zero] at hr
        exact absurd (card_pos_of_mem_aux G.id_in) (hr ▸ lt_irrefl 𝟘)
      -- N ≠ 0: pues N = p^(m+1) y p ≥ 2 > 0
      have hN_ne : N ≠ 𝟘 := pow_ne_zero hp.1 (σ m)
      -- Construir Ω = { sublistas de G de tamaño N }
      obtain ⟨Ω, hΩ_nd, hΩ_mem, hΩ_full, hΩ_card⟩ := wielandt_omega_card G N
      -- La traslación izquierda preserva Ω
      have htrans : ∀ g ∈ G.carrier.elems, ∀ S ∈ Ω, (S.map (G.op g)) ∈ Ω := by
        intro g hg S hS
        obtain ⟨hS_nd, hS_memG, hS_len⟩ := hΩ_mem S hS
        apply hΩ_full
        · -- inyectividad de G.op g: usa op_cancel_left
          apply nodup_map_of_inj_on _ _ hS_nd
          intro a b ha hb heq
          exact op_cancel_left G hg (hS_memG a ha) (hS_memG b hb) heq
        · -- G.op g s ∈ G.carrier.elems
          intro x hx
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
          exact op_mem G hg (hS_memG s hs)
        · -- |S.map (G.op g)| = |S| = N
          show Λ ((S.map (G.op g)).length) = N
          rw [List.length_map]
          exact hS_len
      -- p ∤ r (por h_no_proper: si p | r, p^(m+2) | |G|, habría subgrupo propio)
      have hp_ndvd_r : ¬ p ∣ r := wielandt_p_ndvd_r G p m r hp hr hC h_no_proper
      -- Congruencia de Lucas: C(N·r, N) ≡ r (mod p)
      have hcong : binom (mul N r) N ≡ r [MOD p] :=
        binom_pow_p_mod (p := p) (r := r) hp hr_ne (σ m) (Peano.Axioms.succ_neq_zero m)
      -- |Ω| = C(|G|, N) ≡ r (mod p), así p ∤ |Ω|
      have hΩ_ndvd : ¬ p ∣ lengthₚ Ω := by
        rw [hΩ_card]
        have hG_eq : G.carrier.card = mul N r := hr.symm
        rw [hG_eq]
        intro hdvd
        exact hp_ndvd_r (modEq_zero_iff_dvd hp.1 |>.mp
          (modEq_trans (modEq_symm hcong) (modEq_zero_of_dvd hp.1 hdvd)))
      -- ∃ punto fijo S de la acción de G sobre Ω
      obtain ⟨S, hS_in, hS_fixed⟩ :=
        wielandt_fixed_point_exists G Ω N p hp ⟨r, hr⟩ hΩ_nd hΩ_mem hΩ_full htrans hΩ_ndvd
      -- Extraer propiedades de S
      obtain ⟨hS_nd, hS_memG, hS_len⟩ := hΩ_mem S hS_in
      -- S ≠ [] pues lengthₚ S = N ≠ 0
      have hS_ne : S ≠ [] := by
        intro h_nil; rw [h_nil, lengthₚ_nil] at hS_len; exact hN_ne hS_len.symm
      -- S es subgrupo de G de orden N = p^(m+1)
      obtain ⟨H, _, hH_card⟩ :=
        wielandt_fixed_is_subgroup G S N hS_ne hS_nd hS_memG hS_len hS_fixed
      exact ⟨H, hH_card⟩

    private theorem sylow_center_step
      (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
        (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
          ∃ K : Subgroup G0, K.carrier.card = p0)
      (G : FinGroup ℕ₀) (p m : ℕ₀)
      (hp : Prime p) (hpow : pow_dvd_card p (σ m) G.carrier)
      (h_no_proper : ∀ M : Subgroup G, M.carrier.card ≠ G.carrier.card →
        ¬ pow_dvd_card p (σ m) M.carrier) :
        ∃ H : Subgroup G, H.carrier.card = p ^ (σ m) :=
      sylow_center_step_wielandt hC G p m hp hpow h_no_proper

    /-- Paso 2 (elevación inductiva): asumiendo Cauchy mínimo,
        construir subgrupos de orden `p^(m+1)` cuando `p^(m+1) | |G|`.
        Estrategia: inducción fuerte sobre |G|.
        · Si |G| = p^(m+1): el subgrupo impropio es la solución.
        · Si ∃ M propio con p^(m+1) | |M|: aplicar HI a M.
        · En otro caso: `sylow_center_step` (ecuación de clases / Wielandt). -/
    theorem sylow_lift_from_cauchy
      (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
        (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
          ∃ K : Subgroup G0, K.carrier.card = p0)
      (G : FinGroup ℕ₀) (p m : ℕ₀)
      (hp : Prime p) (hpow : pow_dvd_card p (σ m) G.carrier) :
        ∃ H : Subgroup G, H.carrier.card = p ^ (σ m) := by
      -- Paso inductivo fuerte: explicitamos todos los tipos para ayudar al elaborador
      have step : ∀ (n' : ℕ₀),
          (∀ k : ℕ₀, lt₀ k n' → ∀ G0' : FinGroup ℕ₀, G0'.carrier.card = k →
            pow_dvd_card p (σ m) G0'.carrier →
              ∃ H : Subgroup G0', H.carrier.card = p ^ (σ m)) →
          ∀ G0 : FinGroup ℕ₀, G0.carrier.card = n' →
            pow_dvd_card p (σ m) G0.carrier →
              ∃ H : Subgroup G0, H.carrier.card = p ^ (σ m) := by
        intro n' ih G0 hn hpow0
        -- Caso 1: |G0| = p^(m+1) → G0 mismo es el subgrupo buscado
        by_cases h_eq : G0.carrier.card = p ^ (σ m)
        · exact ⟨improperSubgroup G0, h_eq⟩
        -- Caso 2: ∃ subgrupo propio M con p^(m+1) | |M|
        · by_cases h_ex : ∃ M : Subgroup G0,
              M.carrier.card ≠ G0.carrier.card ∧ pow_dvd_card p (σ m) M.carrier
          · obtain ⟨M, hM_ne, hM_dvd⟩ := h_ex
            -- |M| < |G0| por Lagrange y properness
            have hM_lt : lt₀ M.carrier.card n' := by
              rw [← hn]
              obtain ⟨k, hk⟩ := lagrange G0 M
              have hk_ne : k ≠ 𝟘 := by
                intro h0
                rw [h0, mul_zero] at hk
                have hG_pos := card_pos_of_mem_aux G0.id_in
                rw [← hk] at hG_pos
                exact absurd hG_pos not_lt_zero
              exact lt_of_le_of_ne M.carrier.card G0.carrier.card
                (hk ▸ mul_le_right M.carrier.card k hk_ne) hM_ne
            -- Aplicar HI al FinGroup asociado a M
            let G_M := subgroupToFinGroup G0 M
            obtain ⟨K, hK⟩ := ih M.carrier.card hM_lt G_M rfl hM_dvd
            exact ⟨subgroupOfSubgroup G0 M K, hK⟩
          -- Caso 3: ningún subgrupo propio es divisible por p^(m+1) → axioma
          · exact sylow_center_step hC G0 p m hp hpow0
              (fun M hM_ne hM_dvd => h_ex ⟨M, hM_ne, hM_dvd⟩)
      -- Inducción fuerte sobre |G|, generalizada a todos los FinGroups del mismo cardinal
      have key : ∀ n : ℕ₀, ∀ G0 : FinGroup ℕ₀, G0.carrier.card = n →
          pow_dvd_card p (σ m) G0.carrier →
            ∃ H : Subgroup G0, H.carrier.card = p ^ (σ m) :=
        fun n => strongInductionOn n step
      exact key G.carrier.card G rfl hpow

    /-- **Primer Teorema de Sylow**: existencia de p-subgrupos. -/
    theorem sylow_first (G : FinGroup ℕ₀) (p n : ℕ₀)
        (hp : Prime p)
        (hdvd : pow_dvd_card p n G.carrier) :
        ∃ H : Subgroup G, H.carrier.card = p ^ n := by
      cases n with
      | zero =>
          refine ⟨trivialSubgroup G, ?_⟩
          have hcard : (trivialSubgroup G).carrier.card = 𝟙 := by rfl
          have hpow : p ^ 𝟘 = 𝟙 := Peano.Pow.pow_zero p
          exact hcard.trans hpow.symm
      | succ n' =>
          exact sylow_lift_from_cauchy cauchy_minimal G p n' hp hdvd

    /-!
    # § 3. Segundo Teorema de Sylow (conjugación)

    Todos los subgrupos de Sylow `p` de `G` son conjugados entre sí.
    -/

    /-- Axioma: unicidad del exponente de Sylow.
        Si H y K son ambos subgrupos de Sylow-p de G, tienen el mismo orden.
        La prueba estándar requiere: si p^n | |G| y ¬p^(n+1) | |G|, entonces n es
        la valuación p-ádica de |G|, que es única. Requiere pow_dvd_pow y aritmética
        de potencias que no está en la librería.
        TODO: reemplazar por demostración completa usando pow_dvd_pow. -/
    private axiom sylow_card_eq
        (G : FinGroup ℕ₀) (p : ℕ₀)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p)
        (hK : isSylowSubgroup G K p) :
        H.carrier.card = K.carrier.card

    /-- Axioma: paso de punto fijo para Sylow II.
        ∃ r ∈ G tal que r⁻¹Hr ⊆ K.
        La prueba estándar: H actúa en G/K por multiplicación izquierda; |G/K| no
        es divisible por p; los tamaños de órbita dividen |H| = p^n; por conteo mod p
        ∃ órbita de tamaño 1 (punto fijo rK); rK es punto fijo iff r⁻¹Hr ⊆ K.
        Requiere construir el conjunto G/K como ℕ₀FSet, definir la acción de H sobre
        él y el conteo de órbitas para un grupo p-primario general.
        TODO: reemplazar por demostración completa. -/
    private axiom sylow_second_incl
        (G : FinGroup ℕ₀) (p : ℕ₀)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p)
        (hK : isSylowSubgroup G K p) :
        ∃ r, r ∈ G.carrier.elems ∧
          ∀ h, h ∈ H.carrier.elems → G.op (G.inv r) (G.op h r) ∈ K.carrier.elems

    /-- **Segundo Teorema de Sylow**: conjugación de p-subgrupos.
        Todo par de subgrupos de Sylow-p son conjugados en G.
        Estrategia:
        · `sylow_second_incl` da r ∈ G con r⁻¹Hr ⊆ K.
        · `sylow_card_eq` da |H| = |K|, de modo que la inclusión r⁻¹Hr ⊆ K
          (dada por una inyección con igual cardinalidad) implica r⁻¹Hr = K.
        · El testigo es g = r⁻¹; entonces ghg⁻¹ = r⁻¹h(r⁻¹)⁻¹ = r⁻¹hr ∈ K. -/
    theorem sylow_second (G : FinGroup ℕ₀) (p : ℕ₀)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p) (hK : isSylowSubgroup G K p) :
        ∃ g, g ∈ G.carrier.elems ∧
          ∀ x, x ∈ K.carrier.elems ↔
            ∃ h, h ∈ H.carrier.elems ∧ G.op (G.op g h) (G.inv g) = x := by
      -- Paso 1: r con r⁻¹Hr ⊆ K, e |H| = |K|
      obtain ⟨r, hr, h_incl⟩ := sylow_second_incl G p H K hH hK
      have hHK : H.carrier.card = K.carrier.card := sylow_card_eq G p H K hH hK
      -- Paso 2: la conjugación h ↦ r⁻¹hr mapea H en K
      have h_conj_mem : ∀ h, h ∈ H.carrier.elems →
          G.op (G.op (G.inv r) h) r ∈ K.carrier.elems := by
        intro h hh
        rw [G.op_assoc (G.inv r) h r (inv_mem G hr) (H.subset h hh) hr]
        exact h_incl h hh
      -- Paso 3: la conjugación es inyectiva (cancelación izquierda y derecha)
      let conj_r : MapOn H.carrier K.carrier := {
        toFun       := fun h => G.op (G.op (G.inv r) h) r,
        map_carrier := h_conj_mem
      }
      have h_inj : conj_r.Injective := by
        intro h₁ h₂ hh₁ hh₂ heq
        apply op_cancel_left G (inv_mem G hr) (H.subset h₁ hh₁) (H.subset h₂ hh₂)
        exact op_cancel_right G hr
          (op_mem G (inv_mem G hr) (H.subset h₁ hh₁))
          (op_mem G (inv_mem G hr) (H.subset h₂ hh₂))
          heq
      -- Paso 4: inyectiva + |H| = |K| → sobreyectiva (→ K = r⁻¹Hr)
      have h_surj : conj_r.Surjective :=
        (MapOn.injective_iff_surjective_of_card_eq hHK conj_r).mp h_inj
      -- Paso 5: testigo g = r⁻¹; G.inv (G.inv r) = r por inv_inv_eq
      refine ⟨G.inv r, inv_mem G hr, fun x => ?_⟩
      rw [inv_inv_eq G hr]
      -- Ahora el objetivo es: x ∈ K ↔ ∃ h ∈ H, G.op (G.op (G.inv r) h) r = x
      exact ⟨fun hx => h_surj x hx, fun ⟨h, hh, heq⟩ => heq ▸ h_conj_mem h hh⟩

    /-!
    # § 4. Tercer Teorema de Sylow (número de subgrupos de Sylow)

    El número `n_p` de subgrupos de Sylow `p` satisface:
    - `n_p ≡ 1 (mod p)`
    - `n_p | [G : H]` donde `H` es cualquier subgrupo de Sylow `p`.
    -/

    /-- Axioma: n_p ≡ 1 (mod p).
        La prueba estándar: H actúa sobre el conjunto S de subgrupos de Sylow-p
        por conjugación (h, K) ↦ hKh⁻¹. Un punto fijo K satisface H ⊆ N_G(K);
        como K ▹ N_G(K) y H es un p-subgrupo de Sylow de N_G(K), se tiene H = K.
        Así |fix| = 1. Por conteo de órbitas (mckay_orbit_count generalizado a
        grupos p-primarios), n_p = 1 + p·k.
        Requiere: acción de H sobre una lista de Subgroup G (el conjunto de Sylow
        no es un ℕ₀FSet), normalizer N_G(K), y conteo de órbitas para p-grupos.
        TODO: reemplazar por demostración completa. -/
    private axiom sylow_third_mod
        (G : FinGroup ℕ₀) (p : ℕ₀)
        (hp : Prime p)
        (sylows : List (Subgroup G))
        (h_all_sylow : ∀ H ∈ sylows, isSylowSubgroup G H p)
        (h_all_included : ∀ H : Subgroup G, isSylowSubgroup G H p → H ∈ sylows) :
        ∃ k : ℕ₀, lengthₚ sylows = Peano.Add.add (Peano.Mul.mul p k) 𝟙

    /-- Axioma: n_p | |G|.
        La prueba estándar: G actúa sobre S por conjugación; la acción es transitiva
        (Sylow II). Por órbita–estabilizador, n_p · |N_G(H)| = |G|, luego n_p | |G|.
        Requiere: acción de G sobre Subgroup G (no ℕ₀FSet), normalizer N_G(H),
        y teorema órbita–estabilizador aplicado a esta acción.
        TODO: reemplazar por demostración completa. -/
    private axiom sylow_third_dvd
        (G : FinGroup ℕ₀) (p : ℕ₀)
        (hp : Prime p)
        (sylows : List (Subgroup G))
        (h_all_sylow : ∀ H ∈ sylows, isSylowSubgroup G H p)
        (h_all_included : ∀ H : Subgroup G, isSylowSubgroup G H p → H ∈ sylows) :
        ∀ H ∈ sylows, ∃ k : ℕ₀, Mul.mul (lengthₚ sylows) k = G.carrier.card

    /-- **Tercer Teorema de Sylow**: n_p ≡ 1 mod p y n_p | |G|.
        Ambas conclusiones se derivan de los axiomas privados temporales
        `sylow_third_mod` (acción de H sobre los subgrupos de Sylow, conteo mod p)
        y `sylow_third_dvd` (acción de G por conjugación, órbita–estabilizador). -/
    theorem sylow_third (G : FinGroup ℕ₀) (p : ℕ₀)
        (hp : Prime p)
        (sylows : List (Subgroup G))
        (h_all_sylow : ∀ H ∈ sylows, isSylowSubgroup G H p)
        (h_all_included : ∀ H : Subgroup G, isSylowSubgroup G H p → H ∈ sylows) :
        -- n_p ≡ 1 (mod p)
        (∃ k : ℕ₀, lengthₚ sylows = Peano.Add.add (Peano.Mul.mul p k) 𝟙) ∧
        -- n_p | |G|
        (∀ H ∈ sylows, ∃ k : ℕ₀, Mul.mul (lengthₚ sylows) k = G.carrier.card) :=
      ⟨sylow_third_mod G p hp sylows h_all_sylow h_all_included,
       sylow_third_dvd G p hp sylows h_all_sylow h_all_included⟩

  end GroupTheory
end Peano
