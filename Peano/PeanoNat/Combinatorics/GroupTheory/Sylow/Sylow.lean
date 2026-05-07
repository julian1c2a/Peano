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
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.CosetAction
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

    /-- Si dos listas Nodup tienen los mismos elementos, tienen el mismo cardinal. -/
    private theorem nodup_same_card {l₁ l₂ : List ℕ₀}
        (h1 : l₁.Nodup) (h2 : l₂.Nodup)
        (h12 : ∀ x, x ∈ l₁ → x ∈ l₂) (h21 : ∀ x, x ∈ l₂ → x ∈ l₁) :
        l₁.length = l₂.length := by
      have nodup_sub : ∀ {a b : List ℕ₀}, a.Nodup → (∀ x, x ∈ a → x ∈ b) → a.length ≤ b.length := by
        intro a b hnd hsub
        induction a generalizing b with
        | nil => exact Nat.zero_le _
        | cons x a' ih =>
          rw [List.nodup_cons] at hnd; obtain ⟨hx_nin, hnd'⟩ := hnd
          have hx2 := hsub x List.mem_cons_self
          have h_ih := ih hnd' (fun y hy => by
            have hyx : y ≠ x := fun heq => hx_nin (heq ▸ hy)
            exact (List.mem_erase_of_ne hyx).mpr (hsub y (List.mem_cons_of_mem x hy)))
          rw [List.length_cons]
          have h_pos : 0 < b.length := by
            cases b with
            | nil => exact absurd hx2 List.not_mem_nil
            | cons _ _ => exact Nat.zero_lt_succ _
          have h_erase_len := List.length_erase_of_mem hx2
          omega
      exact Nat.le_antisymm (nodup_sub h1 h12) (nodup_sub h2 h21)

    -- ══════════════════════════════════════════════════════════════════
    -- § Wielandt: sublistsOfLength e infraestructura
    -- ══════════════════════════════════════════════════════════════════

    /-- Genera todas las sub-listas de `elems` con longitud exactamente `n`.
        Cuando `elems` está ordenada, cada resultado también lo está. -/
    private def sublistsOfLength : List ℕ₀ → ℕ₀ → List (List ℕ₀)
      | _,       𝟘   => [[]]
      | [],      σ _ => []
      | x :: xs, σ n =>
          (sublistsOfLength xs n).map (x :: ·) ++ sublistsOfLength xs (σ n)

    private theorem sublistsOfLength_mem_len :
        ∀ (elems : List ℕ₀) (n : ℕ₀) (l : List ℕ₀),
        l ∈ sublistsOfLength elems n → lengthₚ l = n := by
      intro elems
      induction elems with
      | nil =>
        intro n l hl
        cases n with
        | zero =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) 𝟘 = [[]] := rfl
          rw [h_eq] at hl
          rcases List.mem_singleton.mp hl with rfl
          exact lengthₚ_nil
        | succ n' =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) (σ n') = [] := rfl
          rw [h_eq] at hl
          exact absurd hl List.not_mem_nil
      | cons x xs ih =>
        intro n l hl
        cases n with
        | zero =>
          have h_eq : sublistsOfLength (x :: xs) 𝟘 = [[]] := rfl
          rw [h_eq] at hl
          rcases List.mem_singleton.mp hl with rfl
          exact lengthₚ_nil
        | succ n' =>
          have h_eq : sublistsOfLength (x :: xs) (σ n') =
              (sublistsOfLength xs n').map (x :: ·) ++ sublistsOfLength xs (σ n') := rfl
          rw [h_eq] at hl
          rcases List.mem_append.mp hl with h_left | h_right
          · obtain ⟨l', hl'_in, rfl⟩ := List.mem_map.mp h_left
            rw [lengthₚ_cons, ih n' l' hl'_in]
          · exact ih (σ n') l h_right

    private theorem sublistsOfLength_mem_sub :
        ∀ (elems : List ℕ₀) (n : ℕ₀) (l : List ℕ₀),
        l ∈ sublistsOfLength elems n → ∀ y ∈ l, y ∈ elems := by
      intro elems
      induction elems with
      | nil =>
        intro n l hl y hy
        cases n with
        | zero =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) 𝟘 = [[]] := rfl
          rw [h_eq] at hl
          rcases List.mem_singleton.mp hl with rfl
          exact absurd hy List.not_mem_nil
        | succ n' =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) (σ n') = [] := rfl
          rw [h_eq] at hl
          exact absurd hl List.not_mem_nil
      | cons x' xs ih =>
        intro n l hl y hy
        cases n with
        | zero =>
          have h_eq : sublistsOfLength (x' :: xs) 𝟘 = [[]] := rfl
          rw [h_eq] at hl
          rcases List.mem_singleton.mp hl with rfl
          exact absurd hy List.not_mem_nil
        | succ n' =>
          have h_eq : sublistsOfLength (x' :: xs) (σ n') =
              (sublistsOfLength xs n').map (x' :: ·) ++ sublistsOfLength xs (σ n') := rfl
          rw [h_eq] at hl
          rcases List.mem_append.mp hl with h_left | h_right
          · obtain ⟨l', hl'_in, rfl⟩ := List.mem_map.mp h_left
            cases List.mem_cons.mp hy with
            | inl heq =>
              rw [heq]
              exact List.mem_cons_self
            | inr hy' => exact List.mem_cons_of_mem x' (ih n' l' hl'_in y hy')
          · exact List.mem_cons_of_mem x' (ih (σ n') l h_right y hy)

    private theorem sublistsOfLength_mem_sorted :
        ∀ (elems : List ℕ₀), Sorted (· < ·) elems →
        ∀ (n : ℕ₀) (l : List ℕ₀),
        l ∈ sublistsOfLength elems n → Sorted (· < ·) l := by
      intro elems
      induction elems with
      | nil =>
        intro _h_sorted n l hl
        cases n with
        | zero =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) 𝟘 = [[]] := rfl
          rw [h_eq] at hl
          rcases List.mem_singleton.mp hl with rfl
          exact List.Pairwise.nil
        | succ n' =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) (σ n') = [] := rfl
          rw [h_eq] at hl
          exact absurd hl List.not_mem_nil
      | cons x xs ih =>
        intro h_sorted n l hl
        obtain ⟨h_hall, h_xs_sorted⟩ := List.pairwise_cons.mp h_sorted
        cases n with
        | zero =>
          have h_eq : sublistsOfLength (x :: xs) 𝟘 = [[]] := rfl
          rw [h_eq] at hl
          rcases List.mem_singleton.mp hl with rfl
          exact List.Pairwise.nil
        | succ n' =>
          have h_eq : sublistsOfLength (x :: xs) (σ n') =
              (sublistsOfLength xs n').map (x :: ·) ++ sublistsOfLength xs (σ n') := rfl
          rw [h_eq] at hl
          rcases List.mem_append.mp hl with h_left | h_right
          · obtain ⟨l', hl'_in, rfl⟩ := List.mem_map.mp h_left
            apply List.Pairwise.cons
            · intro y hy
              exact h_hall y (sublistsOfLength_mem_sub xs n' l' hl'_in y hy)
            · exact ih h_xs_sorted n' l' hl'_in
          · exact ih h_xs_sorted (σ n') l h_right

    private theorem sublistsOfLength_nodup_result :
        ∀ (elems : List ℕ₀), Sorted (· < ·) elems →
        ∀ (n : ℕ₀), (sublistsOfLength elems n).Nodup := by
      intro elems
      induction elems with
      | nil =>
        intro _h_sorted n
        cases n with
        | zero =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) 𝟘 = [[]] := rfl
          rw [h_eq]; exact List.Pairwise.cons (fun _ hb => nomatch hb) List.Pairwise.nil
        | succ n' =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) (σ n') = [] := rfl
          rw [h_eq]; exact List.nodup_nil
      | cons x xs ih =>
        intro h_sorted n
        obtain ⟨h_hall, h_xs_sorted⟩ := List.pairwise_cons.mp h_sorted
        cases n with
        | zero =>
          have h_eq : sublistsOfLength (x :: xs) 𝟘 = [[]] := rfl
          rw [h_eq]; exact List.Pairwise.cons (fun _ hb => nomatch hb) List.Pairwise.nil
        | succ n' =>
          have h_eq : sublistsOfLength (x :: xs) (σ n') =
              (sublistsOfLength xs n').map (x :: ·) ++ sublistsOfLength xs (σ n') := rfl
          rw [h_eq]
          apply nodup_append_of
          · apply nodup_map_of_inj_on _ _ (ih h_xs_sorted n')
            intro a b _ _ heq
            exact (List.cons.inj heq).2
          · exact ih h_xs_sorted (σ n')
          · intro l hl_map hl_right
            obtain ⟨l', _hl'_in, rfl⟩ := List.mem_map.mp hl_map
            have hx_in_xs : x ∈ xs :=
              sublistsOfLength_mem_sub xs (σ n') (x :: l') hl_right x List.mem_cons_self
            exact absurd (h_hall x hx_in_xs) (nlt_self x)

    private theorem sublistsOfLength_complete :
        ∀ (elems : List ℕ₀), Sorted (· < ·) elems →
        ∀ (n : ℕ₀) (l : List ℕ₀),
        Sorted (· < ·) l → (∀ y ∈ l, y ∈ elems) → lengthₚ l = n →
        l ∈ sublistsOfLength elems n := by
      intro elems
      induction elems with
      | nil =>
        intro _h_sorted n l _h_lsorted h_memnil h_len
        cases l with
        | nil =>
          cases n with
          | zero =>
            have h_eq : sublistsOfLength ([] : List ℕ₀) 𝟘 = [[]] := rfl
            rw [h_eq]; exact List.mem_singleton.mpr rfl
          | succ n' =>
            rw [lengthₚ_nil] at h_len
            exact absurd h_len.symm (Peano.Axioms.succ_neq_zero n')
        | cons a _ =>
          exact absurd (h_memnil a List.mem_cons_self) List.not_mem_nil
      | cons x xs ih =>
        intro h_sorted n l h_lsorted h_mems h_len
        obtain ⟨h_hall, h_xs_sorted⟩ := List.pairwise_cons.mp h_sorted
        cases n with
        | zero =>
          cases l with
          | nil =>
            have h_eq : sublistsOfLength (x :: xs) 𝟘 = [[]] := rfl
            rw [h_eq]; exact List.mem_singleton.mpr rfl
          | cons a l' =>
            rw [lengthₚ_cons] at h_len
            exact absurd h_len (Peano.Axioms.succ_neq_zero _)
        | succ n' =>
          cases l with
          | nil =>
            rw [lengthₚ_nil] at h_len
            exact absurd h_len.symm (Peano.Axioms.succ_neq_zero _)
          | cons a l' =>
            have h_eq : sublistsOfLength (x :: xs) (σ n') =
                (sublistsOfLength xs n').map (x :: ·) ++ sublistsOfLength xs (σ n') := rfl
            rw [h_eq]
            apply List.mem_append.mpr
            cases (List.mem_cons.mp (h_mems a List.mem_cons_self)) with
            | inl ha_eq =>
              -- ha_eq : a = x, so l = a :: l' with a = x
              left
              apply List.mem_map.mpr
              have h_l'sorted : Sorted (· < ·) l' := (List.pairwise_cons.mp h_lsorted).2
              have h_l'mems : ∀ y ∈ l', y ∈ xs := by
                intro y hy
                have hmem : y ∈ x :: xs := h_mems y (List.mem_cons_of_mem a hy)
                have hlt : a < y := (List.pairwise_cons.mp h_lsorted).1 y hy
                cases List.mem_cons.mp hmem with
                | inl heq =>
                  rw [heq, ← ha_eq] at hlt
                  exact absurd hlt (nlt_self a)
                | inr hys => exact hys
              have h_l'len : lengthₚ l' = n' := by
                have hc : lengthₚ (a :: l') = σ n' := h_len
                rw [lengthₚ_cons] at hc
                exact Peano.Axioms.succ_inj _ _ hc
              have h_in : l' ∈ sublistsOfLength xs n' :=
                ih h_xs_sorted n' l' h_l'sorted h_l'mems h_l'len
              exact ⟨l', h_in, by rw [ha_eq]⟩
            | inr ha_xs =>
              -- a ∈ xs: todos los elementos están en xs, usar IH para a :: l' en xs
              right
              apply ih h_xs_sorted (σ n') (a :: l') h_lsorted
              · intro y hy
                have hmem : y ∈ x :: xs := h_mems y hy
                cases List.mem_cons.mp hmem with
                | inl heq =>
                  rw [heq] at hy
                  have hxa : x < a := h_hall a ha_xs
                  cases List.mem_cons.mp hy with
                  | inl hax =>
                    rw [hax] at hxa
                    exact absurd hxa (nlt_self a)
                  | inr hxl' =>
                    have h_ax : a < x := (List.pairwise_cons.mp h_lsorted).1 x hxl'
                    exact absurd (lt_trans_wp hxa h_ax) (nlt_self x)
                | inr hys => exact hys
              · exact h_len

    private theorem sublistsOfLength_card :
        ∀ (elems : List ℕ₀) (n : ℕ₀),
        lengthₚ (sublistsOfLength elems n) = binom (lengthₚ elems) n := by
      intro elems
      induction elems with
      | nil =>
        intro n
        cases n with
        | zero =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) 𝟘 = [[]] := rfl
          simp only [h_eq, lengthₚ_cons, lengthₚ_nil, binom_n_zero]; rfl
        | succ n' =>
          have h_eq : sublistsOfLength ([] : List ℕ₀) (σ n') = [] := rfl
          simp only [h_eq, lengthₚ_nil, binom_zero_succ]
      | cons x xs ih =>
        intro n
        cases n with
        | zero =>
          have h_eq : sublistsOfLength (x :: xs) 𝟘 = [[]] := rfl
          simp only [h_eq, lengthₚ_cons, lengthₚ_nil, binom_n_zero]; rfl
        | succ n' =>
          have h_eq : sublistsOfLength (x :: xs) (σ n') =
              (sublistsOfLength xs n').map (x :: ·) ++ sublistsOfLength xs (σ n') := rfl
          rw [h_eq]
          have h_len_map : lengthₚ ((sublistsOfLength xs n').map (x :: ·)) =
              lengthₚ (sublistsOfLength xs n') := by
            unfold lengthₚ; rw [List.length_map]
          rw [lengthₚ_append, h_len_map, ih n', ih (σ n'), lengthₚ_cons, ← binom_pascal]

    /-- Argumento de Wielandt, pieza 1:
        Ω = sublistas ordenadas de G.carrier.elems de longitud N (representantes canónicos
        de N-subconjuntos de G). |Ω| = C(|G|, N). -/
    private theorem wielandt_omega_card
        (G : FinGroup ℕ₀) (N : ℕ₀) :
        ∃ (Ω : List (List ℕ₀)),
          Ω.Nodup ∧
          (∀ S ∈ Ω, S.Nodup ∧ Sorted (· < ·) S ∧
            (∀ x ∈ S, x ∈ G.carrier.elems) ∧ lengthₚ S = N) ∧
          (∀ S : List ℕ₀, S.Nodup → Sorted (· < ·) S →
            (∀ x ∈ S, x ∈ G.carrier.elems) → lengthₚ S = N → S ∈ Ω) ∧
          lengthₚ Ω = binom G.carrier.card N := by
      refine ⟨sublistsOfLength G.carrier.elems N, ?_, ?_, ?_, ?_⟩
      · exact sublistsOfLength_nodup_result G.carrier.elems G.carrier.sorted N
      · intro S hS
        exact ⟨sorted_nodup (sublistsOfLength_mem_sorted G.carrier.elems G.carrier.sorted N S hS),
               sublistsOfLength_mem_sorted G.carrier.elems G.carrier.sorted N S hS,
               sublistsOfLength_mem_sub G.carrier.elems N S hS,
               sublistsOfLength_mem_len G.carrier.elems N S hS⟩
      · intro S hS_nd hS_sorted hS_memG hS_len
        exact sublistsOfLength_complete G.carrier.elems G.carrier.sorted N S
          hS_sorted hS_memG hS_len
      · show lengthₚ (sublistsOfLength G.carrier.elems N) = binom G.carrier.card N
        exact sublistsOfLength_card G.carrier.elems N

    /-- Argumento de Wielandt, pieza 2:
        Para g ∈ G y S ∈ Ω, el representante ordenado del conjunto g·S
        (= G.carrier filtrado por membresía en {G.op g s | s ∈ S}) también está en Ω. -/
    private theorem wielandt_translate_mem
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (N : ℕ₀)
        (_hΩ_nd : Ω.Nodup)
        (hΩ_mem : ∀ S ∈ Ω, S.Nodup ∧ Sorted (· < ·) S ∧
          (∀ x ∈ S, x ∈ G.carrier.elems) ∧ lengthₚ S = N)
        (hΩ_full : ∀ S : List ℕ₀, S.Nodup → Sorted (· < ·) S →
          (∀ x ∈ S, x ∈ G.carrier.elems) → lengthₚ S = N → S ∈ Ω)
        (g : ℕ₀) (hg : g ∈ G.carrier.elems) (S : List ℕ₀) (hS : S ∈ Ω) :
        (G.carrier.filter (fun x => decide (x ∈ S.map (G.op g)))).elems ∈ Ω := by
      obtain ⟨hS_nd, _hS_sorted, hS_memG, hS_len⟩ := hΩ_mem S hS
      let T := G.carrier.filter (fun x => decide (x ∈ S.map (G.op g)))
      -- S.map (G.op g) es Nodup con todos sus elementos en G
      have hmap_nd : (S.map (G.op g)).Nodup :=
        nodup_map_of_inj_on _ _ hS_nd (fun a b ha hb heq =>
          op_cancel_left G hg (hS_memG a ha) (hS_memG b hb) heq)
      have hmap_G : ∀ x ∈ S.map (G.op g), x ∈ G.carrier.elems := fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx; exact op_mem G hg (hS_memG s hs)
      -- T.elems y S.map tienen los mismos elementos → mismo cardinal
      have hlen : lengthₚ T.elems = N := by
        show Λ T.elems.length = N
        have heq : T.elems.length = (S.map (G.op g)).length :=
          nodup_same_card
            (sorted_nodup T.sorted) hmap_nd
            (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)
            (fun x hx => List.mem_filter.mpr ⟨hmap_G x hx, decide_eq_true hx⟩)
        rw [heq, List.length_map]; exact hS_len
      apply hΩ_full
      · exact sorted_nodup T.sorted
      · exact T.sorted
      · exact fun x hx => (List.mem_filter.mp hx).1
      · exact hlen

    -- ══════════════════════════════════════════════════════════════════
    -- § Wielandt: acción wieldandtAct y lemas básicos (Pasos 1–2)
    -- ══════════════════════════════════════════════════════════════════

    /-- Dos listas ℕ₀ estrictamente ordenadas con los mismos elementos son iguales.
        Auxiliar local (copia de `sorted_nodup_unique_list` en FSet.lean). -/
    private theorem w4_sorted_unique :
        ∀ {l₁ l₂ : List ℕ₀},
        List.Pairwise (· < ·) l₁ → List.Pairwise (· < ·) l₂ →
        (∀ z : ℕ₀, z ∈ l₁ ↔ z ∈ l₂) → l₁ = l₂
      | [], [], _, _, _ => rfl
      | [], y :: _, _, _, hmem =>
          absurd ((hmem y).mpr List.mem_cons_self) List.not_mem_nil
      | x :: _, [], _, _, hmem =>
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
                  (lt_trans_wp
                    (List.rel_of_pairwise_cons hs₁ hy_xs)
                    (List.rel_of_pairwise_cons hs₂ hx_ys))
                  (nlt_self x)
          have htail : xs = ys := by
            apply w4_sorted_unique hxs₁.2 hxs₂.2
            intro z
            constructor
            · intro hz
              have hzy := (hmem z).mp (List.mem_cons.mpr (Or.inr hz))
              rcases List.mem_cons.mp hzy with h_eq | h
              · have h_lt : lt₀ x z := List.rel_of_pairwise_cons hs₁ hz
                rw [h_eq, ← hxy] at h_lt
                exact absurd h_lt (nlt_self x)
              · exact h
            · intro hz
              have hzx := (hmem z).mpr (List.mem_cons.mpr (Or.inr hz))
              rcases List.mem_cons.mp hzx with h_eq | h
              · have h_lt : lt₀ y z := List.rel_of_pairwise_cons hs₂ hz
                rw [h_eq, hxy] at h_lt
                exact absurd h_lt (nlt_self y)
              · exact h
          Eq.trans (congrArg (List.cons x) htail) (congrArg (· :: ys) hxy)

    /-- Acción de Wielandt: g ∈ G actúa sobre S ⊆ G por multiplicación izquierda,
        devolviendo la sublista canónica ordenada de G.carrier. -/
    private def wieldandtAct (G : FinGroup ℕ₀) (g : ℕ₀) (S : List ℕ₀) : List ℕ₀ :=
      (G.carrier.filter (fun x => decide (x ∈ S.map (G.op g)))).elems

    /-- La acción de Wielandt por el elemento neutro es la identidad. -/
    private theorem wieldandtAct_id
        (G : FinGroup ℕ₀) (S : List ℕ₀)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems) :
        wieldandtAct G G.id S = S := by
      show (G.carrier.filter (fun x => decide (x ∈ S.map (G.op G.id)))).elems = S
      have hmap : S.map (G.op G.id) = S := by
        induction S with
        | nil => rfl
        | cons x xs ih =>
          rw [List.map_cons, (G.op_id x (hS_mem x List.mem_cons_self)).2]
          congr 1
          exact ih (List.pairwise_cons.mp hS_sorted).2
                   (fun y hy => hS_mem y (List.mem_cons_of_mem x hy))
      rw [hmap]
      apply w4_sorted_unique
      · exact List.Pairwise.filter _ G.carrier.sorted
      · exact hS_sorted
      · intro z
        constructor
        · intro hz; exact of_decide_eq_true (List.mem_filter.mp hz).2
        · intro hz; exact List.mem_filter.mpr ⟨hS_mem z hz, decide_eq_true hz⟩

    /-- La acción de Wielandt es compatible con la composición del grupo. -/
    private theorem wieldandtAct_comp
        (G : FinGroup ℕ₀) (g h : ℕ₀) (S : List ℕ₀)
        (hg : g ∈ G.carrier.elems) (hh : h ∈ G.carrier.elems)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems) :
        wieldandtAct G g (wieldandtAct G h S) = wieldandtAct G (G.op g h) S := by
      show (G.carrier.filter (fun x => decide (x ∈ (wieldandtAct G h S).map (G.op g)))).elems =
           (G.carrier.filter (fun x => decide (x ∈ S.map (G.op (G.op g h))))).elems
      apply w4_sorted_unique
      · exact List.Pairwise.filter _ G.carrier.sorted
      · exact List.Pairwise.filter _ G.carrier.sorted
      · intro z
        constructor
        · intro hz
          obtain ⟨hzG, hzt⟩ := List.mem_filter.mp hz
          obtain ⟨t, ht_act, rfl⟩ := List.mem_map.mp (of_decide_eq_true hzt)
          have ht_filter := List.mem_filter.mp ht_act
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (of_decide_eq_true ht_filter.2)
          apply List.mem_filter.mpr
          exact ⟨op_mem G hg (op_mem G hh (hS_mem s hs)),
                 decide_eq_true (List.mem_map.mpr ⟨s, hs,
                   G.op_assoc g h s hg hh (hS_mem s hs)⟩)⟩
        · intro hz
          obtain ⟨hzG, hzs⟩ := List.mem_filter.mp hz
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (of_decide_eq_true hzs)
          have hassoc : G.op (G.op g h) s = G.op g (G.op h s) :=
            G.op_assoc g h s hg hh (hS_mem s hs)
          have ht_G : G.op h s ∈ G.carrier.elems := op_mem G hh (hS_mem s hs)
          have ht_act : G.op h s ∈ wieldandtAct G h S := by
            show G.op h s ∈ (G.carrier.filter (fun x => decide (x ∈ S.map (G.op h)))).elems
            exact List.mem_filter.mpr ⟨ht_G, decide_eq_true (List.mem_map.mpr ⟨s, hs, rfl⟩)⟩
          rw [hassoc]
          apply List.mem_filter.mpr
          exact ⟨op_mem G hg ht_G,
                 decide_eq_true (List.mem_map.mpr ⟨G.op h s, ht_act, rfl⟩)⟩

    /-- wieldandtAct preserva la pertenencia a Ω. -/
    private theorem wieldandtAct_mem_omega
        (G : FinGroup ℕ₀) (N : ℕ₀) (Ω : List (List ℕ₀))
        (hΩ_nd : Ω.Nodup)
        (hΩ_mem : ∀ S ∈ Ω, S.Nodup ∧ Sorted (· < ·) S ∧
          (∀ x ∈ S, x ∈ G.carrier.elems) ∧ lengthₚ S = N)
        (hΩ_full : ∀ S : List ℕ₀, S.Nodup → Sorted (· < ·) S →
          (∀ x ∈ S, x ∈ G.carrier.elems) → lengthₚ S = N → S ∈ Ω)
        (g : ℕ₀) (hg : g ∈ G.carrier.elems) (S : List ℕ₀) (hS : S ∈ Ω) :
        wieldandtAct G g S ∈ Ω :=
      wielandt_translate_mem G Ω N hΩ_nd hΩ_mem hΩ_full g hg S hS


    /-- Argumento de Wielandt, pieza 4:
        Un subconjunto S ⊆ G que es punto fijo SET-LEVEL (g·s ∈ S para todo g ∈ G, s ∈ S)
        es un subgrupo de G de orden N = |S|. -/
    private theorem wielandt_fixed_is_subgroup
        (G : FinGroup ℕ₀) (S : List ℕ₀) (N : ℕ₀)
        (hS_ne : S ≠ [])
        (hS_nd : S.Nodup)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (hS_len : lengthₚ S = N)
        (hS_fixed : ∀ g ∈ G.carrier.elems, ∀ x ∈ S, G.op g x ∈ S) :
        ∃ H : Subgroup G, H.carrier.card = N := by
      cases S with
      | nil => exact absurd rfl hS_ne
      | cons x₀ S' =>
        have hx₀_G : x₀ ∈ G.carrier.elems := hS_mem x₀ List.mem_cons_self
        have hx₀inv_G : G.inv x₀ ∈ G.carrier.elems := inv_mem G hx₀_G
        -- G.id ∈ x₀ :: S': G.inv x₀ · x₀ = G.id ∈ S
        have hid_in_S : G.id ∈ x₀ :: S' := by
          have := hS_fixed (G.inv x₀) hx₀inv_G x₀ List.mem_cons_self
          rwa [(G.op_inv x₀ hx₀_G).2] at this
        -- b ∈ S → G.inv b ∈ S: G.inv b · G.id = G.inv b ∈ (G.inv b)·S ⊆ S
        have hinv_in_S : ∀ b, b ∈ x₀ :: S' → G.inv b ∈ x₀ :: S' := by
          intro b hb
          have hbinv_G := inv_mem G (hS_mem b hb)
          have := hS_fixed (G.inv b) hbinv_G G.id hid_in_S
          rwa [(G.op_id (G.inv b) hbinv_G).1] at this
        -- Inline nodup_sub_len para el argumento de cardinalidad
        have nodup_sub_len : ∀ {l₁ l₂ : List ℕ₀},
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
        -- Construir carrier = G.carrier ∩ (x₀ :: S')
        let S_fset : FSet ℕ₀ := G.carrier.filter (fun x => decide (x ∈ x₀ :: S'))
        have hmem_fset : ∀ x, x ∈ S_fset.elems ↔ x ∈ G.carrier.elems ∧ x ∈ x₀ :: S' := by
          intro x
          show x ∈ G.carrier.elems.filter (fun y => decide (y ∈ x₀ :: S')) ↔
              x ∈ G.carrier.elems ∧ x ∈ x₀ :: S'
          constructor
          · intro hx
            exact ⟨(List.mem_filter.mp hx).1, of_decide_eq_true (List.mem_filter.mp hx).2⟩
          · intro ⟨h1, h2⟩
            exact List.mem_filter.mpr ⟨h1, decide_eq_true h2⟩
        refine ⟨subgroup_of_op_inv_closed G S_fset
          (fun x hx => (hmem_fset x).mp hx |>.1)
          ⟨x₀, (hmem_fset x₀).mpr ⟨hx₀_G, List.mem_cons_self⟩⟩
          (fun a b ha hb => by
            obtain ⟨ha_G, ha_S⟩ := (hmem_fset a).mp ha
            obtain ⟨hb_G, hb_S⟩ := (hmem_fset b).mp hb
            apply (hmem_fset _).mpr
            exact ⟨op_mem G ha_G (inv_mem G hb_G),
                   hS_fixed a ha_G (G.inv b) (hinv_in_S b hb_S)⟩),
          ?_⟩
        -- carrier.card = N
        show lengthₚ S_fset.elems = N
        show Λ (G.carrier.elems.filter (fun x => decide (x ∈ x₀ :: S'))).length = N
        have hlen_eq :
            (G.carrier.elems.filter (fun x => decide (x ∈ x₀ :: S'))).length =
            (x₀ :: S').length := by
          apply Nat.le_antisymm
          · apply nodup_sub_len
            · exact List.filter_sublist.nodup (sorted_nodup G.carrier.sorted)
            · intro x hx
              exact of_decide_eq_true (List.mem_filter.mp hx).2
          · apply nodup_sub_len hS_nd
            intro x hx
            exact List.mem_filter.mpr ⟨hS_mem x hx, decide_eq_true hx⟩
        exact (congrArg Λ hlen_eq).trans hS_len

    /-- Paso 3a: S punto fijo SET-LEVEL bajo wieldandtAct implica S es subgrupo de orden N. -/
    private theorem wieldandt_fixedPoint_is_subgroup
        (G : FinGroup ℕ₀) (S : List ℕ₀) (N : ℕ₀)
        (hS_ne : S ≠ [])
        (hS_nd : S.Nodup)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (hS_len : lengthₚ S = N)
        (hS_fixed : ∀ g ∈ G.carrier.elems, wieldandtAct G g S = S) :
        ∃ H : Subgroup G, H.carrier.card = N := by
      have hS_set_fixed : ∀ g ∈ G.carrier.elems, ∀ x ∈ S, G.op g x ∈ S := by
        intro g hg x hx
        have hact : wieldandtAct G g S = S := hS_fixed g hg
        have hgx_in_act : G.op g x ∈ wieldandtAct G g S := by
          show G.op g x ∈ (G.carrier.filter (fun z => decide (z ∈ S.map (G.op g)))).elems
          exact List.mem_filter.mpr
            ⟨op_mem G hg (hS_mem x hx),
             decide_eq_true (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩
        exact hact ▸ hgx_in_act
      exact wielandt_fixed_is_subgroup G S N hS_ne hS_nd hS_mem hS_len hS_set_fixed

    /-- Paso 3b: Si existe un punto fijo en Ω bajo wieldandtAct, existe subgrupo de orden N. -/
    private theorem wieldandt_fixedPoint_exists_of_fix_nonempty
        (G : FinGroup ℕ₀) (N : ℕ₀) (Ω : List (List ℕ₀))
        (hN_ne : N ≠ 𝟘)
        (hΩ_mem : ∀ S ∈ Ω, S.Nodup ∧ Sorted (· < ·) S ∧
          (∀ x ∈ S, x ∈ G.carrier.elems) ∧ lengthₚ S = N)
        (hfix : ∃ S ∈ Ω, ∀ g ∈ G.carrier.elems, wieldandtAct G g S = S) :
        ∃ H : Subgroup G, H.carrier.card = N := by
      obtain ⟨S, hS_Ω, hS_fixed⟩ := hfix
      obtain ⟨hS_nd, _hS_sorted, hS_mem, hS_len⟩ := hΩ_mem S hS_Ω
      have hS_ne : S ≠ [] := by
        intro h; rw [h, lengthₚ_nil] at hS_len; exact hN_ne hS_len.symm
      exact wieldandt_fixedPoint_is_subgroup G S N hS_ne hS_nd hS_mem hS_len hS_fixed

    -- ══════════════════════════════════════════════════════════════════
    -- § Wielandt Pieza B: elemento de orden p (de Cauchy)
    -- ══════════════════════════════════════════════════════════════════

    /-- Si p es primo y p ∣ |G|, existe g ∈ G con g^p = G.id y g ≠ G.id.
        Extrae el generador de orden p que produce cauchy_minimal internamente. -/
    private theorem wielandt_elem_order_p
        (G : FinGroup ℕ₀) (p : ℕ₀) (hp : Prime p)
        (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :
        ∃ g ∈ G.carrier.elems, g ≠ G.id ∧ gpow G g p = G.id := by
      let F := ℕ₀FSet.filter (fun g => decide (gpow G g p = G.id)) G.carrier
      have hid_in_F : G.id ∈ F.elems :=
        List.mem_filter.mpr ⟨G.id_in, decide_eq_true_eq.mpr (gpow_id_eq_id G p)⟩
      have hp_dvd_F : p ∣ F.card := mckay_p_dvd_powEqId G p hp hdvd
      have hF_pos : lt₀ 𝟘 F.card := card_pos_of_mem_aux hid_in_F
      obtain ⟨k, hk⟩ := hp_dvd_F
      have hk_ne : k ≠ 𝟘 := by
        intro h0; rw [h0, mul_zero] at hk; rw [hk] at hF_pos
        exact absurd hF_pos not_lt_zero
      have hF_ge_p : le₀ p F.card := hk ▸ mul_le_right p k hk_ne
      have hF_ge_2 : le₀ 𝟚 F.card := le_trans 𝟚 p F.card (prime_ge_two hp) hF_ge_p
      obtain ⟨g, hg_in_F, hg_ne⟩ := exists_ne_of_card_ge hid_in_F hF_ge_2
      exact ⟨g, (List.mem_filter.mp hg_in_F).1, hg_ne,
             decide_eq_true_eq.mp (List.mem_filter.mp hg_in_F).2⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § Wielandt Órbita–Estabilizador para listas
    -- ══════════════════════════════════════════════════════════════════

    /-- El estabilizador de S en G bajo wieldandtAct.
        Requiere que S sea un subconjunto de G (hS_mem) y esté ordenado (hS_sorted).
        Devuelve el subgrupo { g ∈ G | g·S = S }. -/
    private def wieldandtStab
        (G : FinGroup ℕ₀) (S : List ℕ₀)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems) : Subgroup G where
      carrier   := G.carrier.filter (fun g => decide (wieldandtAct G g S = S))
      nonempty  := ⟨G.id, List.mem_filter.mpr
                    ⟨G.id_in, decide_eq_true (wieldandtAct_id G S hS_sorted hS_mem)⟩⟩
      subset    := fun a ha => (List.mem_filter.mp ha).1
      op_closed := fun a b ha hb => by
        have ⟨ha_G, ha_fix⟩ := List.mem_filter.mp ha
        have ⟨hb_G, hb_fix⟩ := List.mem_filter.mp hb
        rw [decide_eq_true_eq] at ha_fix hb_fix
        refine List.mem_filter.mpr ⟨op_mem G ha_G hb_G, decide_eq_true ?_⟩
        rw [← wieldandtAct_comp G a b S ha_G hb_G hS_mem, hb_fix, ha_fix]
      id_in     := List.mem_filter.mpr
                    ⟨G.id_in, decide_eq_true (wieldandtAct_id G S hS_sorted hS_mem)⟩
      inv_closed := fun a ha => by
        have ⟨ha_G, ha_fix⟩ := List.mem_filter.mp ha
        rw [decide_eq_true_eq] at ha_fix
        refine List.mem_filter.mpr ⟨inv_mem G ha_G, decide_eq_true ?_⟩
        have hcomp :=
          wieldandtAct_comp G (G.inv a) a S (inv_mem G ha_G) ha_G hS_mem
        rw [ha_fix, (G.op_inv a ha_G).2] at hcomp
        exact hcomp.trans (wieldandtAct_id G S hS_sorted hS_mem)

    /-- La órbita de S ∈ Ω bajo G: sublista de Ω consistente en { g·S | g ∈ G }. -/
    private def wieldandtOrb (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (S : List ℕ₀) :
        List (List ℕ₀) :=
      Ω.filter (fun T => G.carrier.elems.any (fun g => decide (wieldandtAct G g S = T)))

    /-- Miembro de wieldandtOrb: T ∈ Orb(S) ↔ ∃ g ∈ G, g·S = T (y T ∈ Ω). -/
    private theorem mem_wieldandtOrb_iff
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (S T : List ℕ₀) :
        T ∈ wieldandtOrb G Ω S ↔
        (T ∈ Ω) ∧ ∃ g ∈ G.carrier.elems, wieldandtAct G g S = T := by
      simp only [wieldandtOrb, List.mem_filter, List.any_eq_true]
      constructor
      · rintro ⟨hT, g, hg, hd⟩
        exact ⟨hT, g, hg, of_decide_eq_true hd⟩
      · rintro ⟨hT, g, hg, heq⟩
        exact ⟨hT, g, hg, decide_eq_true heq⟩

    /-- S ∈ wieldandtOrb G Ω S cuando S ∈ Ω (el elemento neutro actúa trivialmente). -/
    private theorem wieldandtOrb_self_mem
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (S : List ℕ₀)
        (hS_Ω : S ∈ Ω)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems) :
        S ∈ wieldandtOrb G Ω S :=
      (mem_wieldandtOrb_iff G Ω S S).mpr
        ⟨hS_Ω, G.id, G.id_in,
         wieldandtAct_id G S hS_sorted hS_mem⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § Lemas de soporte para wieldandtStab
    -- ══════════════════════════════════════════════════════════════════

    /-- Criterio de membresía en el estabilizador:
        h ∈ Stab(S) ↔ h ∈ G ∧ h·S = S. -/
    private theorem mem_wieldandtStab_iff
        (G : FinGroup ℕ₀) (S : List ℕ₀)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (h : ℕ₀) :
        h ∈ (wieldandtStab G S hS_sorted hS_mem).carrier.elems ↔
        h ∈ G.carrier.elems ∧ wieldandtAct G h S = S := by
      show h ∈ (G.carrier.filter
            (fun g => decide (wieldandtAct G g S = S))).elems ↔
           h ∈ G.carrier.elems ∧ wieldandtAct G h S = S
      simp only [FSet.filter, List.mem_filter, decide_eq_true_eq]

    /-- Todo elemento del estabilizador fija S bajo wieldandtAct. -/
    private theorem wieldandtStab_fixes
        (G : FinGroup ℕ₀) (S : List ℕ₀)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (h : ℕ₀) (hh : h ∈ (wieldandtStab G S hS_sorted hS_mem).carrier.elems) :
        wieldandtAct G h S = S :=
      ((mem_wieldandtStab_iff G S hS_sorted hS_mem h).mp hh).2

    /-- Si h ∈ Stab(S) y s₀ ∈ S, entonces G.op h s₀ ∈ S.
        (La acción de un estabilizador permuta los elementos de S.) -/
    private theorem wieldandtStab_act_mem
        (G : FinGroup ℕ₀) (S : List ℕ₀)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (h s₀ : ℕ₀)
        (hh : h ∈ (wieldandtStab G S hS_sorted hS_mem).carrier.elems)
        (hs₀ : s₀ ∈ S) :
        G.op h s₀ ∈ S := by
      have hfix  := wieldandtStab_fixes G S hS_sorted hS_mem h hh
      have hh_G  := (wieldandtStab G S hS_sorted hS_mem).subset h hh
      have hs₀_G := hS_mem s₀ hs₀
      -- G.op h s₀ ∈ wieldandtAct G h S, y éste = S
      have hmem : G.op h s₀ ∈ wieldandtAct G h S := by
        show G.op h s₀ ∈
          (G.carrier.filter (fun x => decide (x ∈ S.map (G.op h)))).elems
        refine List.mem_filter.mpr ⟨op_mem G hh_G hs₀_G, decide_eq_true ?_⟩
        exact List.mem_map.mpr ⟨s₀, hs₀, rfl⟩
      rwa [hfix] at hmem

    /-- La órbita de S (como sublista de Ω) hereda la propiedad Nodup. -/
    private theorem wieldandtOrb_nodup
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (S : List ℕ₀)
        (hΩ_nd : Ω.Nodup) :
        (wieldandtOrb G Ω S).Nodup :=
      List.filter_sublist.nodup hΩ_nd

    /-- Todo elemento de wieldandtOrb G Ω S pertenece también a Ω. -/
    private theorem wieldandtOrb_sub
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (S T : List ℕ₀)
        (hT : T ∈ wieldandtOrb G Ω S) : T ∈ Ω :=
      ((mem_wieldandtOrb_iff G Ω S T).mp hT).1

    /-- Si Ω es cerrado bajo la acción de G y S ∈ Ω, entonces g·S ∈ wieldandtOrb G Ω S. -/
    private theorem wieldandtAct_mem_wieldandtOrb
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (S : List ℕ₀) (g : ℕ₀)
        (hg : g ∈ G.carrier.elems)
        (hS_Ω : S ∈ Ω)
        (hΩ_closed : ∀ T ∈ Ω, ∀ h ∈ G.carrier.elems, wieldandtAct G h T ∈ Ω) :
        wieldandtAct G g S ∈ wieldandtOrb G Ω S :=
      (mem_wieldandtOrb_iff G Ω S (wieldandtAct G g S)).mpr
        ⟨hΩ_closed S hS_Ω g hg, g, hg, rfl⟩

    /-- Dos elementos g, h ∈ G envían S al mismo resultado sii G.inv(g)·h ∈ Stab(S).
        Equivalencia clave para descomponer G en coclases de Stab. -/
    private theorem wieldandtAct_eq_iff_stab
        (G : FinGroup ℕ₀) (S : List ℕ₀)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (g h : ℕ₀)
        (hg : g ∈ G.carrier.elems) (hh : h ∈ G.carrier.elems) :
        wieldandtAct G g S = wieldandtAct G h S ↔
        G.op (G.inv g) h ∈ (wieldandtStab G S hS_sorted hS_mem).carrier.elems := by
      rw [mem_wieldandtStab_iff]
      constructor
      · intro heq
        refine ⟨op_mem G (inv_mem G hg) hh, ?_⟩
        -- (g⁻¹·h)·S = g⁻¹·(h·S) = g⁻¹·(g·S) = S
        have h1 := wieldandtAct_comp G (G.inv g) h S (inv_mem G hg) hh hS_mem
        have h2 := wieldandtAct_comp G (G.inv g) g S (inv_mem G hg) hg hS_mem
        rw [(G.op_inv g hg).2, wieldandtAct_id G S hS_sorted hS_mem] at h2
        rw [← heq] at h1
        -- h1 : wieldandtAct G (G.inv g) (wieldandtAct G g S) =
        --       wieldandtAct G (G.op (G.inv g) h) S
        -- h2 : wieldandtAct G (G.inv g) (wieldandtAct G g S) = S
        exact h1.symm.trans h2
      · rintro ⟨_, hfix⟩
        -- g·S = g·((g⁻¹·h)·S) = (g·g⁻¹·h)·S = h·S
        have h1 := wieldandtAct_comp G g (G.op (G.inv g) h) S hg
          (op_mem G (inv_mem G hg) hh) hS_mem
        rw [hfix] at h1
        -- h1 : wieldandtAct G g S = wieldandtAct G (G.op g (G.op (G.inv g) h)) S
        have hassoc : G.op g (G.op (G.inv g) h) = h := by
          rw [← G.op_assoc g (G.inv g) h hg (inv_mem G hg) hh,
              (G.op_inv g hg).1, (G.op_id h hh).2]
        rw [hassoc] at h1
        exact h1

    /-- Auxiliar: si l₁ es Nodup y hay una inyección l₁ → l₂, entonces |l₁| ≤ |l₂|.
        Versión para List ℕ₀, reutilizable en esta sección. -/
    private theorem wieldandt_nodup_sub_len : ∀ {l₁ l₂ : List ℕ₀},
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
          exact (List.mem_erase_of_ne hxa).mpr
            (hsub x (List.mem_cons_of_mem a hx)))
        rw [List.length_cons]
        have h_pos : 0 < l₂.length := by
          cases l₂ with
          | nil => exact absurd ha2 List.not_mem_nil
          | cons _ _ => exact Nat.zero_lt_succ _
        have h_erase_len := List.length_erase_of_mem ha2
        omega

    /-- La fibra { h ∈ G | h·S = T } tiene el mismo cardinal que Stab(S),
        para cualquier T ∈ wieldandtOrb G Ω S. -/
    private theorem wieldandtStab_fiber_card
        (G : FinGroup ℕ₀) (S T : List ℕ₀)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (g₀ : ℕ₀)
        (hg₀ : g₀ ∈ G.carrier.elems)
        (hg₀_act : wieldandtAct G g₀ S = T) :
        (G.carrier.filter (fun h => decide (wieldandtAct G h S = T))).card =
        (wieldandtStab G S hS_sorted hS_mem).carrier.card := by
      -- Notación local (transparente por ser `let`)
      let fL := G.carrier.elems.filter (fun h => decide (wieldandtAct G h S = T))
      let sL := (wieldandtStab G S hS_sorted hS_mem).carrier.elems
      show lengthₚ fL = lengthₚ sL
      -- ── Nodup de ambas listas
      have fL_nodup : fL.Nodup :=
        List.filter_sublist.nodup (sorted_nodup G.carrier.sorted)
      have sL_nodup : sL.Nodup :=
        sorted_nodup (wieldandtStab G S hS_sorted hS_mem).carrier.sorted
      -- ── Mapa φ : fL → sL,  h ↦ G.op (G.inv g₀) h
      let φ := fun h => G.op (G.inv g₀) h
      -- φ envía fL a sL: si h·S = T = g₀·S, entonces (g₀⁻¹·h)·S = S
      have φ_img : ∀ h, h ∈ fL → φ h ∈ sL := by
        intro h hh
        have hh_G : h ∈ G.carrier.elems := (List.mem_filter.mp hh).1
        have hh_T : wieldandtAct G h S = T :=
          of_decide_eq_true (List.mem_filter.mp hh).2
        -- g₀·S = h·S
        have h_eq : wieldandtAct G g₀ S = wieldandtAct G h S :=
          hg₀_act.trans hh_T.symm
        exact (wieldandtAct_eq_iff_stab G S hS_sorted hS_mem g₀ h hg₀ hh_G).mp h_eq
      -- φ es inyectiva (cancelación izquierda por G.inv g₀)
      have φ_nodup : (fL.map φ).Nodup :=
        nodup_map_of_inj_on φ fL fL_nodup
          (fun a b ha hb heq =>
            op_cancel_left G (inv_mem G hg₀)
              (List.mem_filter.mp ha).1 (List.mem_filter.mp hb).1 heq)
      -- |fL| ≤ |sL|
      have h1 : fL.length ≤ sL.length := by
        have h := wieldandt_nodup_sub_len φ_nodup
                    (fun x hx => by
                      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
                      exact φ_img h hh)
        rwa [List.length_map] at h
      -- ── Mapa ψ : sL → fL,  k ↦ G.op g₀ k
      let ψ := fun k => G.op g₀ k
      -- ψ envía sL a fL: si k·S = S, entonces (g₀·k)·S = g₀·(k·S) = g₀·S = T
      have ψ_img : ∀ k, k ∈ sL → ψ k ∈ fL := by
        intro k hk
        have hk_G : k ∈ G.carrier.elems :=
          (wieldandtStab G S hS_sorted hS_mem).subset k hk
        have hk_fix : wieldandtAct G k S = S :=
          wieldandtStab_fixes G S hS_sorted hS_mem k hk
        have h_comp := wieldandtAct_comp G g₀ k S hg₀ hk_G hS_mem
        rw [hk_fix] at h_comp
        -- h_comp : wieldandtAct G g₀ S = wieldandtAct G (G.op g₀ k) S
        have h_act : wieldandtAct G (ψ k) S = T := h_comp.symm.trans hg₀_act
        exact List.mem_filter.mpr ⟨op_mem G hg₀ hk_G, decide_eq_true h_act⟩
      -- ψ es inyectiva (cancelación izquierda por g₀)
      have ψ_nodup : (sL.map ψ).Nodup :=
        nodup_map_of_inj_on ψ sL sL_nodup
          (fun a b ha hb heq =>
            op_cancel_left G hg₀
              ((wieldandtStab G S hS_sorted hS_mem).subset a ha)
              ((wieldandtStab G S hS_sorted hS_mem).subset b hb) heq)
      -- |sL| ≤ |fL|
      have h2 : sL.length ≤ fL.length := by
        have h := wieldandt_nodup_sub_len ψ_nodup
                    (fun x hx => by
                      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
                      exact ψ_img k hk)
        rwa [List.length_map] at h
      -- |fL| = |sL| → lengthₚ fL = lengthₚ sL
      exact congrArg Λ (Nat.le_antisymm h1 h2)

    /-- Auxiliar: conteo por fibras uniformes, versión especializada para codomain List (List ℕ₀).
        Evita requerir una instancia LT en el tipo codomain.
        Espejo directo de card_eq_mul_fibers_aux (private en FSetFunction). -/
    private theorem wielandt_card_mul_fibers_aux
        (f : ℕ₀ → List ℕ₀) (k : ℕ₀) :
        ∀ (A : FSet ℕ₀) (bs : List (List ℕ₀)), bs.Nodup →
        (∀ a, a ∈ A.elems → f a ∈ bs) →
        (∀ b, b ∈ bs → (A.filter (fun a => decide (f a = b))).card = k) →
        A.card = mul k (lengthₚ bs)
      | A, [], _, h_cover, _ => by
        simp only [FSet.card, lengthₚ]
        cases h_elems : A.elems with
        | nil => rfl
        | cons a _ =>
          exact absurd (h_cover a (h_elems ▸ List.mem_cons_self)) List.not_mem_nil
      | A, b :: rest, h_nodup, h_cover, h_uniform => by
        have hb_nd : b ∉ rest := (List.nodup_cons.mp h_nodup).1
        have hrest_nd : rest.Nodup := (List.nodup_cons.mp h_nodup).2
        let p  : ℕ₀ → Bool := fun a => decide (f a = b)
        let np : ℕ₀ → Bool := not ∘ p
        -- Partición por filtros (aritmética Nat pura; misma estructura que filter_part en §5)
        have h_filter_split : ∀ (l : List ℕ₀),
            l.length = Nat.add (l.filter p).length (l.filter np).length := by
          intro l; induction l with
          | nil => simp
          | cons x xs ih =>
            cases h : p x
            · have e1 : (x :: xs).filter p = xs.filter p := by simp [h]
              have e2 : (x :: xs).filter np = x :: xs.filter np := by simp [np, h]
              simp only [e1, e2, List.length_cons, Nat.add_eq] at *; omega
            · have e1 : (x :: xs).filter p = x :: xs.filter p := by simp [h]
              have e2 : (x :: xs).filter np = xs.filter np := by simp [np, h]
              simp only [e1, e2, List.length_cons, Nat.add_eq] at *; omega
        have h_split : A.card = add (A.filter p).card (A.filter np).card := by
          simp only [FSet.card, FSet.filter, lengthₚ]
          rw [← isomorph_Λ_add]
          exact congrArg Λ (h_filter_split A.elems)
        have h_fb : (A.filter p).card = k := h_uniform b List.mem_cons_self
        have h_cover_rest : ∀ a, a ∈ (A.filter np).elems → f a ∈ rest := by
          intro a ha
          simp [FSet.filter, np, p, decide_eq_false_iff_not] at ha
          obtain ⟨ha_A, hfane⟩ := ha
          rcases List.mem_cons.mp (h_cover a ha_A) with rfl | h_rest
          · exact absurd rfl hfane
          · exact h_rest
        have h_uniform_rest : ∀ b', b' ∈ rest →
            ((A.filter np).filter (fun a => decide (f a = b'))).card = k := by
          intro b' hb'
          have hb'_ne : b' ≠ b := fun heq => hb_nd (heq ▸ hb')
          -- (decide(fa=b') && np(a)) = decide(fa=b')
          -- porque si fa=b'≠b, entonces np(a)=¬(fa=b)=¬(fa=b')=true
          have hpred : ∀ a, (decide (f a = b') && np a) = decide (f a = b') := by
            intro a; by_cases hq : f a = b'
            · have hpfalse : decide (f a = b) = false := by
                apply decide_eq_false_iff_not.mpr
                intro hgb; exact hb'_ne (hq.symm.trans hgb)
              have hnp_true : np a = true := by simp [np, p, hpfalse]
              simp [hq, hnp_true]
            · have hfalse : decide (f a = b') = false := decide_eq_false_iff_not.mpr hq
              simp [hfalse]
          have hlist : (A.elems.filter np).filter (fun a => decide (f a = b')) =
              A.elems.filter (fun a => decide (f a = b')) := by
            simp [List.filter_filter, hpred]
          have hcard_eq : ((A.filter np).filter (fun a => decide (f a = b'))).card =
              (A.filter (fun a => decide (f a = b'))).card := by
            unfold FSet.card FSet.filter
            simpa using congrArg lengthₚ hlist
          rw [hcard_eq]
          exact h_uniform b' (List.mem_cons.mpr (Or.inr hb'))
        have h_ih := wielandt_card_mul_fibers_aux f k (A.filter np) rest
          hrest_nd h_cover_rest h_uniform_rest
        rw [h_split, h_fb, h_ih, lengthₚ_cons, mul_succ, add_comm]

    /-- Órbita–estabilizador para wieldandtAct:
        |wieldandtOrb G Ω S| · |(wieldandtStab G S hS_sorted hS_mem).carrier| = |G|. -/
    private theorem wielandt_orbit_stab
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (S : List ℕ₀) (N : ℕ₀)
        (hΩ_nd : Ω.Nodup)
        (hΩ_mem : ∀ T ∈ Ω, T.Nodup ∧ Sorted (· < ·) T ∧
          (∀ x ∈ T, x ∈ G.carrier.elems) ∧ lengthₚ T = N)
        (hΩ_full : ∀ T : List ℕ₀, T.Nodup → Sorted (· < ·) T →
          (∀ x ∈ T, x ∈ G.carrier.elems) → lengthₚ T = N → T ∈ Ω)
        (hS_Ω : S ∈ Ω)
        (hS_sorted : Sorted (· < ·) S)
        (hS_memG : ∀ x ∈ S, x ∈ G.carrier.elems) :
        Mul.mul (lengthₚ (wieldandtOrb G Ω S))
                (wieldandtStab G S hS_sorted hS_memG).carrier.card =
        G.carrier.card := by
      let k := (wieldandtStab G S hS_sorted hS_memG).carrier.card
      -- Ω es cerrado bajo la acción de G (derivado de hΩ_full via wieldandtAct_mem_omega)
      have hΩ_closed : ∀ T ∈ Ω, ∀ h ∈ G.carrier.elems, wieldandtAct G h T ∈ Ω :=
        fun T hT h hh => wieldandtAct_mem_omega G N Ω hΩ_nd hΩ_mem hΩ_full h hh T hT
      -- Todo g ∈ G envía S a algún elemento de la órbita
      have h_cover : ∀ g, g ∈ G.carrier.elems → wieldandtAct G g S ∈ wieldandtOrb G Ω S :=
        fun g hg => wieldandtAct_mem_wieldandtOrb G Ω S g hg hS_Ω hΩ_closed
      -- La órbita es Nodup
      have h_orb_nd := wieldandtOrb_nodup G Ω S hΩ_nd
      -- Cada fibra { g ∈ G | g·S = T } tiene tamaño k = |Stab(S)|
      have h_fiber : ∀ T, T ∈ wieldandtOrb G Ω S →
          (G.carrier.filter (fun g => decide (wieldandtAct G g S = T))).card = k := by
        intro T hT
        obtain ⟨hT_Ω, g₀, hg₀, hg₀_act⟩ := (mem_wieldandtOrb_iff G Ω S T).mp hT
        exact wieldandtStab_fiber_card G S T hS_sorted hS_memG g₀ hg₀ hg₀_act
      -- Conteo por fibras: |G| = k · |Orb|
      have h_eq : G.carrier.card = mul k (lengthₚ (wieldandtOrb G Ω S)) :=
        wielandt_card_mul_fibers_aux (fun g => wieldandtAct G g S) k
          G.carrier (wieldandtOrb G Ω S) h_orb_nd h_cover h_fiber
      -- Reordenar: |Orb| · |Stab| = |G|
      exact (h_eq.trans (mul_comm k (lengthₚ (wieldandtOrb G Ω S)))).symm

    -- ══════════════════════════════════════════════════════════════════
    -- § Wielandt Pieza C: |Stab| = N cuando p ∤ |Orb|
    -- ══════════════════════════════════════════════════════════════════

    /-- Si S ∈ Ω, la función h ↦ h·s₀ inyecta wieldandtStab G S en S.
        Por tanto |(wieldandtStab G S hS_sorted hS_mem).carrier| ≤ |S| = N. -/
    private theorem wieldandtStab_card_le
        (G : FinGroup ℕ₀) (S : List ℕ₀) (N : ℕ₀)
        (hS_ne : S ≠ [])
        (_hS_nd : S.Nodup)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (hS_len : lengthₚ S = N) :
        le₀ (wieldandtStab G S hS_sorted hS_mem).carrier.card N := by
      -- Sea s₀ el primer elemento de S
      obtain ⟨s₀, S', hS_eq⟩ : ∃ s₀ S', S = s₀ :: S' :=
        List.exists_cons_of_ne_nil hS_ne
      have hs₀_in : s₀ ∈ S := hS_eq ▸ List.mem_cons_self
      -- La función h ↦ G.op h s₀ envía Stab → S (por wieldandtStab_act_mem)
      have h_img_S : ∀ h,
          h ∈ (wieldandtStab G S hS_sorted hS_mem).carrier.elems →
          G.op h s₀ ∈ S :=
        fun h hh => wieldandtStab_act_mem G S hS_sorted hS_mem h s₀ hh hs₀_in
      -- La función es inyectiva (cancelación derecha)
      have h_inj : ∀ h₁ h₂,
          h₁ ∈ (wieldandtStab G S hS_sorted hS_mem).carrier.elems →
          h₂ ∈ (wieldandtStab G S hS_sorted hS_mem).carrier.elems →
          G.op h₁ s₀ = G.op h₂ s₀ → h₁ = h₂ :=
        fun h₁ h₂ hh₁ hh₂ heq =>
          op_cancel_right G (hS_mem s₀ hs₀_in)
            ((wieldandtStab G S hS_sorted hS_mem).subset h₁ hh₁)
            ((wieldandtStab G S hS_sorted hS_mem).subset h₂ hh₂) heq
      -- Construir la lista imagen (Nodup por inyectividad)
      let img := (wieldandtStab G S hS_sorted hS_mem).carrier.elems.map
                   (fun h => G.op h s₀)
      have img_nodup : img.Nodup :=
        nodup_map_of_inj_on _ _
          (sorted_nodup (wieldandtStab G S hS_sorted hS_mem).carrier.sorted)
          (fun a b ha hb heq => h_inj a b ha hb heq)
      have img_sub_S : ∀ x, x ∈ img → x ∈ S := by
        intro x hx
        obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
        exact h_img_S h hh
      -- |Stab| = |img| ≤ |S| = N
      have h_le_nat :
          (wieldandtStab G S hS_sorted hS_mem).carrier.elems.length ≤ S.length := by
        have h_img_len : img.length =
            (wieldandtStab G S hS_sorted hS_mem).carrier.elems.length :=
          List.length_map _
        rw [← h_img_len]
        exact wieldandt_nodup_sub_len img_nodup img_sub_S
      -- Convertir de Nat a ℕ₀ usando isomorph_Λ_le
      rw [← hS_len]
      exact (isomorph_Λ_le
          (wieldandtStab G S hS_sorted hS_mem).carrier.elems.length
          S.length).mp h_le_nat

    open Peano.Arith in
    /-- Dado p ∤ |wieldandtOrb G Ω S₀|, N = p^(m+1), y órbita-estabilizador,
        wieldandtStab G S₀ es un subgrupo de G de orden N. -/
    private theorem wielandt_stab_card_eq_N
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (S₀ : List ℕ₀) (N p m : ℕ₀)
        (hp : Prime p)
        (hN_eq : N = p ^ (σ m))
        (hdvd_G : ∃ r, Mul.mul N r = G.carrier.card)
        (hS₀_sorted : Sorted (· < ·) S₀)
        (hS₀_nd : S₀.Nodup)
        (hS₀_ne : S₀ ≠ [])
        (hS₀_mem : ∀ x ∈ S₀, x ∈ G.carrier.elems)
        (hS₀_len : lengthₚ S₀ = N)
        (horb_stab : Mul.mul (lengthₚ (wieldandtOrb G Ω S₀))
                             (wieldandtStab G S₀ hS₀_sorted hS₀_mem).carrier.card =
                     G.carrier.card)
        (hndvd_orb : ¬ p ∣ lengthₚ (wieldandtOrb G Ω S₀)) :
        ∃ H : Subgroup G, H.carrier.card = N := by
      -- (0) Lema local: si d | p^n y d ≠ 𝟙 entonces p | d
      --     (copia privada de prime_dvd_of_dvd_prime_pow de CosetAction)
      have h_prime_dvd_dvd_pow : ∀ (n : ℕ₀) {d : ℕ₀}, d ∣ p ^ n → d ≠ 𝟙 → p ∣ d := by
        intro n
        induction n with
        | zero =>
          intro d hd hne
          change d ∣ 𝟙 at hd
          obtain ⟨k, hk⟩ := hd
          exact absurd (mul_eq_one hk.symm).1 hne
        | succ n' ih =>
          intro d hd hne
          change d ∣ mul (p ^ n') p at hd
          rcases prime_coprime_or_dvd hp (n := d) with hdvd | hcop
          · exact hdvd
          · have hcop' : Coprime d p := coprime_symm hcop
            have hd' : d ∣ mul p (p ^ n') := by rwa [mul_comm] at hd
            exact ih (coprime_dvd_of_dvd_mul hcop' hd') hne
      -- (1) G.id ∈ Stab → |Stab| ≠ 𝟘
      let K := wieldandtStab G S₀ hS₀_sorted hS₀_mem
      have h_id_stab : G.id ∈ K.carrier.elems :=
        (mem_wieldandtStab_iff G S₀ hS₀_sorted hS₀_mem G.id).mpr
          ⟨G.id_in, wieldandtAct_id G S₀ hS₀_sorted hS₀_mem⟩
      have h_stab_ne : K.carrier.card ≠ 𝟘 :=
        (ne_of_lt 𝟘 _ (card_pos_of_mem_aux h_id_stab)).symm
      -- (2) |Stab| ≤ N
      have h_stab_le : le₀ K.carrier.card N :=
        wieldandtStab_card_le G S₀ N hS₀_ne hS₀_nd hS₀_sorted hS₀_mem hS₀_len
      -- (3) N | |Orb| · |Stab|  (porque N | |G| = |Orb| · |Stab|)
      obtain ⟨r, hr⟩ := hdvd_G
      have h_N_dvd_prod : N ∣ Mul.mul (lengthₚ (wieldandtOrb G Ω S₀)) K.carrier.card :=
        ⟨r, horb_stab.trans hr.symm⟩
      -- (4) Coprime N |Orb|  (porque N = p^(m+1) y p ∤ |Orb|)
      have h_cop : Coprime N (lengthₚ (wieldandtOrb G Ω S₀)) := by
        unfold Coprime IsGCD
        refine ⟨one_divides N, one_divides _, ?_⟩
        intro c ⟨hc_N, hc_orb⟩
        by_cases hc1 : c = 𝟙
        · rw [hc1]; exact divides_refl 𝟙
        · have hc_pow : c ∣ p ^ (σ m) := hN_eq ▸ hc_N
          exact absurd (divides_trans (h_prime_dvd_dvd_pow (σ m) hc_pow hc1) hc_orb)
                       hndvd_orb
      -- (5) N | |Stab|  (Gauss: Coprime N |Orb|, N | |Orb| · |Stab|)
      have h_N_dvd_stab : N ∣ K.carrier.card :=
        coprime_dvd_of_dvd_mul h_cop h_N_dvd_prod
      -- (6) N ≤ |Stab|  (N | |Stab| y |Stab| ≠ 𝟘)
      have h_N_le_stab : le₀ N K.carrier.card := divides_le h_N_dvd_stab h_stab_ne
      -- (7) |Stab| = N  →  Stab es el p-subgrupo de Sylow buscado
      exact ⟨K, le_antisymm _ _ h_stab_le h_N_le_stab⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § wielandt_fixed_point_exists: helpers y prueba
    -- ══════════════════════════════════════════════════════════════════

    /-- Versión de nodup_same_card para List (List ℕ₀). -/
    private theorem nodup_same_card_ll {l₁ l₂ : List (List ℕ₀)}
        (h1 : l₁.Nodup) (h2 : l₂.Nodup)
        (h12 : ∀ x, x ∈ l₁ → x ∈ l₂) (h21 : ∀ x, x ∈ l₂ → x ∈ l₁) :
        l₁.length = l₂.length := by
      have nodup_sub : ∀ {a b : List (List ℕ₀)}, a.Nodup →
          (∀ x, x ∈ a → x ∈ b) → a.length ≤ b.length := by
        intro a b hnd hsub
        induction a generalizing b with
        | nil => exact Nat.zero_le _
        | cons x a' ih =>
          rw [List.nodup_cons] at hnd; obtain ⟨hx_nin, hnd'⟩ := hnd
          have hx2 := hsub x List.mem_cons_self
          have h_ih := ih hnd' (fun y hy => by
            have hyx : y ≠ x := fun heq => hx_nin (heq ▸ hy)
            exact (List.mem_erase_of_ne hyx).mpr
              (hsub y (List.mem_cons_of_mem x hy)))
          rw [List.length_cons]
          have h_pos : 0 < b.length := by
            cases b with
            | nil => exact absurd hx2 List.not_mem_nil
            | cons _ _ => exact Nat.zero_lt_succ _
          have h_erase_len := List.length_erase_of_mem hx2
          omega
      exact Nat.le_antisymm (nodup_sub h1 h12) (nodup_sub h2 h21)

    /-- Partición de una lista por un predicado booleano. -/
    private theorem filter_partition_nat {α : Type} (q : α → Bool) :
        ∀ l : List α, l.length = ((l.filter q).length + (l.filter (fun x => !q x)).length : Nat)
      | [] => rfl
      | x :: xs => by
          have ih := filter_partition_nat q xs
          cases hq : q x with
          | false =>
            have hf1 : (x :: xs).filter q = xs.filter q := by
              simp [List.filter_cons, hq]
            have hf2 : (x :: xs).filter (fun x => !q x) = x :: xs.filter (fun x => !q x) := by
              simp [List.filter_cons, hq, Bool.not_false]
            rw [List.length_cons, hf1, hf2, List.length_cons]; omega
          | true =>
            have hf1 : (x :: xs).filter q = x :: xs.filter q := by
              simp [List.filter_cons, hq]
            have hf2 : (x :: xs).filter (fun x => !q x) = xs.filter (fun x => !q x) := by
              simp [List.filter_cons, hq, Bool.not_true]
            rw [List.length_cons, hf1, hf2, List.length_cons]; omega

    open Peano.Add in
    /-- Inducción fuerte: dado p ∤ |Ω| y Ω cerrado bajo G, existe S₀ ∈ Ω con p ∤ |Orb(S₀)|. -/
    private theorem wielandt_exists_nondvd_orbit_aux
        (G : FinGroup ℕ₀) (p : ℕ₀) :
        ∀ n : Nat, ∀ Ω : List (List ℕ₀),
        Ω.length ≤ n →
        Ω.Nodup →
        (∀ S ∈ Ω, Sorted (· < ·) S ∧ ∀ x ∈ S, x ∈ G.carrier.elems) →
        (∀ S ∈ Ω, ∀ g ∈ G.carrier.elems, wieldandtAct G g S ∈ Ω) →
        ¬ p ∣ lengthₚ Ω →
        ∃ S₀ ∈ Ω, ¬ p ∣ lengthₚ (wieldandtOrb G Ω S₀) := by
      intro n
      induction n with
      | zero =>
        intro Ω hlen _ _ _ hndvd
        cases Ω with
        | nil => exact absurd (divides_zero p) hndvd
        | cons h t => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ n' ih =>
        intro Ω hlen hΩ_nd hΩ_prop hΩ_closed hndvd
        cases hΩ : Ω with
        | nil => subst hΩ; exact absurd (divides_zero p) hndvd
        | cons S₀ rest =>
          have hS₀_mem : S₀ ∈ Ω := hΩ.symm ▸ List.mem_cons_self
          obtain ⟨hS₀_sorted, hS₀_memG⟩ := hΩ_prop S₀ hS₀_mem
          rcases Classical.em (p ∣ lengthₚ (wieldandtOrb G Ω S₀)) with horb_dvd | horb_ndvd
          · -- p | |Orb(S₀)|: extract Ω' = Ω \ Orb(S₀) and apply IH
            let q₀ : List ℕ₀ → Bool :=
              fun T => G.carrier.elems.any (fun g => decide (wieldandtAct G g S₀ = T))
            -- wieldandtOrb G Ω S₀ = Ω.filter q₀ by definition
            have h_orb_eq : wieldandtOrb G Ω S₀ = Ω.filter q₀ := rfl
            let Ω' := Ω.filter (fun x => !q₀ x)
            have h_part : Ω.length = ((Ω.filter q₀).length + Ω'.length : Nat) :=
              filter_partition_nat q₀ Ω
            -- S₀ ∈ Orb(S₀), so |Orb(S₀)| ≥ 1
            have hS₀_orb : S₀ ∈ wieldandtOrb G Ω S₀ :=
              wieldandtOrb_self_mem G Ω S₀ hS₀_mem hS₀_sorted hS₀_memG
            have horb_pos : 0 < (Ω.filter q₀).length := by
              have : 0 < (wieldandtOrb G Ω S₀).length := by
                cases hww : wieldandtOrb G Ω S₀ with
                | nil => exact absurd (hww ▸ hS₀_orb) List.not_mem_nil
                | cons _ _ => exact Nat.zero_lt_succ _
              simpa [h_orb_eq] using this
            -- |Ω'| ≤ n'
            have hΩ'_len : Ω'.length ≤ n' := by omega
            -- lengthₚ Ω = add (lengthₚ (wieldandtOrb G Ω S₀)) (lengthₚ Ω')
            have h_len_eq : lengthₚ Ω = add (lengthₚ (wieldandtOrb G Ω S₀)) (lengthₚ Ω') := by
              show Λ Ω.length = add (Λ (Ω.filter q₀).length) (Λ Ω'.length)
              rw [h_part]; exact isomorph_Λ_add _ _
            -- p ∤ |Ω'|
            have hΩ'_ndvd : ¬ p ∣ lengthₚ Ω' := fun h' =>
              hndvd (h_len_eq ▸ divides_add horb_dvd h')
            -- Ω' is nodup
            have hΩ'_nd : Ω'.Nodup := List.filter_sublist.nodup hΩ_nd
            -- elements of Ω' have the right properties
            have hΩ'_prop : ∀ S ∈ Ω', Sorted (· < ·) S ∧ ∀ x ∈ S, x ∈ G.carrier.elems :=
              fun S hS => hΩ_prop S ((List.mem_filter.mp hS).1)
            -- Ω' is G-closed
            have hΩ'_closed : ∀ S ∈ Ω', ∀ g ∈ G.carrier.elems, wieldandtAct G g S ∈ Ω' := by
              intro S hS g hg
              have hS_Ω : S ∈ Ω := (List.mem_filter.mp hS).1
              have hgS_Ω : wieldandtAct G g S ∈ Ω := hΩ_closed S hS_Ω g hg
              -- S ∉ Orb(S₀): from hS ∈ Ω.filter (not q₀)
              have hS_not_orb : S ∉ wieldandtOrb G Ω S₀ := by
                rw [h_orb_eq]
                intro hS_in
                have hq : q₀ S = true := (List.mem_filter.mp hS_in).2
                have hnq : (!q₀ S) = true := (List.mem_filter.mp hS).2
                simp [hq] at hnq
              -- g·S ∉ Orb(S₀): by orbit disjointness
              have hgS_not_orb : wieldandtAct G g S ∉ wieldandtOrb G Ω S₀ := by
                intro hgS_in
                obtain ⟨_, h, hh, hh_eq⟩ :=
                  (mem_wieldandtOrb_iff G Ω S₀ (wieldandtAct G g S)).mp hgS_in
                obtain ⟨hS_sorted, hS_memG⟩ := hΩ'_prop S hS
                -- g⁻¹·(h·S₀) = g⁻¹·(g·S) = S
                have hinv_gS : wieldandtAct G (G.inv g) (wieldandtAct G g S) =
                               wieldandtAct G (G.op (G.inv g) g) S :=
                  wieldandtAct_comp G (G.inv g) g S (inv_mem G hg) hg hS_memG
                have h_invg_id : G.op (G.inv g) g = G.id := (G.op_inv g hg).2
                rw [h_invg_id, wieldandtAct_id G S hS_sorted hS_memG] at hinv_gS
                have hinv_hS₀ : wieldandtAct G (G.inv g) (wieldandtAct G h S₀) =
                                wieldandtAct G (G.op (G.inv g) h) S₀ :=
                  wieldandtAct_comp G (G.inv g) h S₀ (inv_mem G hg) hh hS₀_memG
                -- (g⁻¹·h)·S₀ = S
                have heq_S : wieldandtAct G (G.op (G.inv g) h) S₀ = S := by
                  rw [← hinv_hS₀, hh_eq, hinv_gS]
                exact hS_not_orb ((mem_wieldandtOrb_iff G Ω S₀ S).mpr
                  ⟨hS_Ω, G.op (G.inv g) h, op_mem G (inv_mem G hg) hh, heq_S⟩)
              -- g·S ∈ Ω' = Ω.filter (not q₀)
              apply List.mem_filter.mpr
              refine ⟨hgS_Ω, ?_⟩
              cases hbool : q₀ (wieldandtAct G g S) with
              | false => rfl
              | true =>
                exact absurd (h_orb_eq ▸ List.mem_filter.mpr ⟨hgS_Ω, hbool⟩) hgS_not_orb
            -- Apply IH to Ω'
            obtain ⟨S₁, hS₁_Ω', hS₁_ndvd⟩ :=
              ih Ω' hΩ'_len hΩ'_nd hΩ'_prop hΩ'_closed hΩ'_ndvd
            have hS₁_Ω : S₁ ∈ Ω := (List.mem_filter.mp hS₁_Ω').1
            -- S₁ ∉ Orb(S₀): from hS₁_Ω' ∈ Ω.filter (not q₀)
            have hS₁_not_orb_S₀ : S₁ ∉ wieldandtOrb G Ω S₀ := by
              rw [h_orb_eq]
              intro hS₁_in
              have hq : q₀ S₁ = true := (List.mem_filter.mp hS₁_in).2
              have hnq : (!q₀ S₁) = true := (List.mem_filter.mp hS₁_Ω').2
              simp [hq] at hnq
            -- wieldandtOrb G Ω S₁ ⊆ Ω' (orbit of S₁ avoids orbit of S₀)
            have h_Ω_orb_sub_Ω' : ∀ T, T ∈ wieldandtOrb G Ω S₁ → T ∈ wieldandtOrb G Ω' S₁ := by
              intro T hT
              obtain ⟨hT_Ω, g₁, hg₁, hg₁_eq⟩ := (mem_wieldandtOrb_iff G Ω S₁ T).mp hT
              -- T ∉ Orb(S₀): if T ∈ Orb(S₀), then S₁ ∈ Orb(S₀) — contradiction
              have hT_not_orb_S₀ : T ∉ wieldandtOrb G Ω S₀ := by
                intro hT_in_orb
                obtain ⟨_, h₂, hh₂, hh₂_eq⟩ := (mem_wieldandtOrb_iff G Ω S₀ T).mp hT_in_orb
                obtain ⟨hS₁_sorted, hS₁_memG⟩ := hΩ_prop S₁ hS₁_Ω
                -- g₁⁻¹·(h₂·S₀) = g₁⁻¹·(g₁·S₁) = S₁
                have hinv_g₁S₁ : wieldandtAct G (G.inv g₁) (wieldandtAct G g₁ S₁) =
                                  wieldandtAct G (G.op (G.inv g₁) g₁) S₁ :=
                  wieldandtAct_comp G (G.inv g₁) g₁ S₁ (inv_mem G hg₁) hg₁ hS₁_memG
                rw [(G.op_inv g₁ hg₁).2, wieldandtAct_id G S₁ hS₁_sorted hS₁_memG] at hinv_g₁S₁
                have hinv_h₂S₀ : wieldandtAct G (G.inv g₁) (wieldandtAct G h₂ S₀) =
                                  wieldandtAct G (G.op (G.inv g₁) h₂) S₀ :=
                  wieldandtAct_comp G (G.inv g₁) h₂ S₀ (inv_mem G hg₁) hh₂ hS₀_memG
                have heq_S₁ : wieldandtAct G (G.op (G.inv g₁) h₂) S₀ = S₁ := by
                  rw [← hinv_h₂S₀, hh₂_eq, ← hg₁_eq, hinv_g₁S₁]
                exact hS₁_not_orb_S₀ ((mem_wieldandtOrb_iff G Ω S₀ S₁).mpr
                  ⟨hS₁_Ω, G.op (G.inv g₁) h₂, op_mem G (inv_mem G hg₁) hh₂, heq_S₁⟩)
              -- T ∈ Ω'
              have hT_Ω' : T ∈ Ω' := by
                apply List.mem_filter.mpr
                refine ⟨hT_Ω, ?_⟩
                cases hbool : q₀ T with
                | false => rfl
                | true =>
                  exact absurd (h_orb_eq ▸ List.mem_filter.mpr ⟨hT_Ω, hbool⟩) hT_not_orb_S₀
              exact (mem_wieldandtOrb_iff G Ω' S₁ T).mpr ⟨hT_Ω', g₁, hg₁, hg₁_eq⟩
            -- wieldandtOrb G Ω' S₁ ⊆ wieldandtOrb G Ω S₁
            have h_Ω'_orb_sub_Ω : ∀ T, T ∈ wieldandtOrb G Ω' S₁ → T ∈ wieldandtOrb G Ω S₁ := by
              intro T hT
              obtain ⟨hT_Ω', g₁, hg₁, hg₁_eq⟩ := (mem_wieldandtOrb_iff G Ω' S₁ T).mp hT
              exact (mem_wieldandtOrb_iff G Ω S₁ T).mpr
                ⟨(List.mem_filter.mp hT_Ω').1, g₁, hg₁, hg₁_eq⟩
            -- |Orb(G,Ω,S₁)| = |Orb(G,Ω',S₁)|
            have h_orb_len : (wieldandtOrb G Ω S₁).length = (wieldandtOrb G Ω' S₁).length :=
              nodup_same_card_ll (wieldandtOrb_nodup G Ω S₁ hΩ_nd)
                (wieldandtOrb_nodup G Ω' S₁ hΩ'_nd) h_Ω_orb_sub_Ω' h_Ω'_orb_sub_Ω
            -- ¬ p ∣ lengthₚ (wieldandtOrb G Ω S₁)
            have hS₁_ndvd_Ω : ¬ p ∣ lengthₚ (wieldandtOrb G Ω S₁) := by
              rwa [show lengthₚ (wieldandtOrb G Ω S₁) = lengthₚ (wieldandtOrb G Ω' S₁) from
                congrArg Λ h_orb_len]
            exact ⟨S₁, hΩ ▸ hS₁_Ω, hΩ ▸ hS₁_ndvd_Ω⟩
          · -- ¬ p ∣ |Orb(S₀)|: we are done
            exact ⟨S₀, hΩ ▸ hS₀_mem, hΩ ▸ horb_ndvd⟩

    /-- Wielandt: si G actúa sobre Ω (N-subsets de G) y p ∤ |Ω|, ∃ H ≤ G con |H| = N = p^(m+1). -/
    private theorem wielandt_fixed_point_exists
        (G : FinGroup ℕ₀) (Ω : List (List ℕ₀)) (N : ℕ₀) (p : ℕ₀)
        (hp : Prime p)
        (hdvd_G : ∃ r : ℕ₀, Mul.mul N r = G.carrier.card)
        (hΩ_nd : Ω.Nodup)
        (hΩ_mem : ∀ S ∈ Ω, S.Nodup ∧ Sorted (· < ·) S ∧
          (∀ x ∈ S, x ∈ G.carrier.elems) ∧ lengthₚ S = N)
        (hΩ_full : ∀ S : List ℕ₀, S.Nodup → Sorted (· < ·) S →
          (∀ x ∈ S, x ∈ G.carrier.elems) → lengthₚ S = N → S ∈ Ω)
        (htrans : ∀ g ∈ G.carrier.elems, ∀ S ∈ Ω,
          (G.carrier.filter (fun x => decide (x ∈ S.map (G.op g)))).elems ∈ Ω)
        (hndvd : ¬ p ∣ lengthₚ Ω)
        (hN_pm : ∃ m : ℕ₀, N = p ^ (σ m)) :
        ∃ H : Subgroup G, H.carrier.card = N := by
      obtain ⟨m, hN_eq⟩ := hN_pm
      -- Ω is closed under G-action
      have hΩ_closed : ∀ S ∈ Ω, ∀ g ∈ G.carrier.elems, wieldandtAct G g S ∈ Ω :=
        fun S hS g hg => wieldandtAct_mem_omega G N Ω hΩ_nd hΩ_mem hΩ_full g hg S hS
      -- Properties of Ω elements (sorted + memG)
      have hΩ_prop : ∀ S ∈ Ω, Sorted (· < ·) S ∧ ∀ x ∈ S, x ∈ G.carrier.elems :=
        fun S hS => let ⟨_, hs, hm, _⟩ := hΩ_mem S hS; ⟨hs, hm⟩
      -- ∃ S₀ ∈ Ω with p ∤ |Orb(S₀)|
      obtain ⟨S₀, hS₀_Ω, hS₀_ndvd⟩ :=
        wielandt_exists_nondvd_orbit_aux G p Ω.length Ω (Nat.le_refl _)
          hΩ_nd hΩ_prop hΩ_closed hndvd
      obtain ⟨_, hS₀_sorted, hS₀_memG, hS₀_len⟩ := hΩ_mem S₀ hS₀_Ω
      have hS₀_nd : S₀.Nodup := (hΩ_mem S₀ hS₀_Ω).1
      have hS₀_ne : S₀ ≠ [] := by
        intro h
        rw [h] at hS₀_len
        simp only [lengthₚ_nil] at hS₀_len
        -- hS₀_len : 𝟘 = N, hN_eq : N = p ^ σ m
        have hpow_zero : p ^ (σ m) = 𝟘 := by rw [← hN_eq]; exact hS₀_len.symm
        exact pow_ne_zero hp.1 (σ m) hpow_zero
      -- Orbit-stabilizer: |Orb(S₀)| · |Stab(S₀)| = |G|
      have horb_stab :
          Mul.mul (lengthₚ (wieldandtOrb G Ω S₀))
                  (wieldandtStab G S₀ hS₀_sorted hS₀_memG).carrier.card =
          G.carrier.card :=
        wielandt_orbit_stab G Ω S₀ N hΩ_nd hΩ_mem hΩ_full hS₀_Ω hS₀_sorted hS₀_memG
      -- ∃ H ≤ G with |H| = N
      exact wielandt_stab_card_eq_N G Ω S₀ N p m hp hN_eq hdvd_G
        hS₀_sorted hS₀_nd hS₀_ne hS₀_memG hS₀_len horb_stab hS₀_ndvd

    -- ══════════════════════════════════════════════════════════════════
    -- § Wielandt Pieza A: infraestructura para la partición de órbitas
    -- ══════════════════════════════════════════════════════════════════

    /-- La acción iterada de g^(m+n) sobre S se descompone en dos aplicaciones sucesivas. -/
    private theorem wieldandtAct_gpow_add
        (G : FinGroup ℕ₀) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
        (S : List ℕ₀) (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (m n : ℕ₀) :
        wieldandtAct G (gpow G g (add m n)) S =
        wieldandtAct G (gpow G g m) (wieldandtAct G (gpow G g n) S) := by
      rw [gpow_add G hg m n]
      exact (wieldandtAct_comp G (gpow G g m) (gpow G g n) S
               (gpow_mem G hg m) (gpow_mem G hg n) hS_mem).symm

    open Peano.Arith in
    /-- Análogo de nthRotate_one_fixed_of_gcd_one para la acción de Wielandt.
        Si g^k·S = S, g^p·S = S y gcd(k,p) = 1, entonces g·S = S. -/
    private theorem wieldandtAct_gpow_fixed_of_gcd_one
        (G : FinGroup ℕ₀) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
        (S : List ℕ₀) (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (k p : ℕ₀)
        (hk : wieldandtAct G (gpow G g k) S = S)
        (hp_act : wieldandtAct G (gpow G g p) S = S)
        (hgcd : gcd k p = 𝟙) :
        wieldandtAct G g S = S := by
      obtain ⟨bn, bm, h⟩ := bezout_natform k p
      rw [hgcd] at h
      -- Helper: si g^base · S = S, entonces g^(t·base) · S = S para todo t
      have h_period_mul : ∀ (base : ℕ₀), wieldandtAct G (gpow G g base) S = S →
          ∀ (t : ℕ₀), wieldandtAct G (gpow G g (mul t base)) S = S := by
        intro base hbase t
        induction t with
        | zero =>
          rw [zero_mul, gpow_zero]
          exact wieldandtAct_id G S hS_sorted hS_mem
        | succ t' ih =>
          rw [succ_mul, wieldandtAct_gpow_add G hg S hS_mem (mul t' base) base, hbase]
          exact ih
      rcases h with h1 | h2
      · -- h1 : 𝟙 = sub (mul bn k) (mul bm p)
        have h1' : sub (mul bn k) (mul bm p) = 𝟙 := h1.symm
        have hlt : lt₀ (mul bm p) (mul bn k) := by
          apply (sub_pos_iff_lt (mul bn k) (mul bm p)).mp
          rw [← h1]; exact le_refl 𝟙
        have h_eq : add 𝟙 (mul bm p) = mul bn k := by
          have key := sub_k_add_k (mul bn k) (mul bm p) (lt_imp_le _ _ hlt)
          rw [h1'] at key; exact key
        have h_bmp := h_period_mul p hp_act bm
        have h_bnk := h_period_mul k hk bn
        have h_step : wieldandtAct G g (wieldandtAct G (gpow G g (mul bm p)) S) =
            wieldandtAct G (gpow G g (add 𝟙 (mul bm p))) S := by
          have := (wieldandtAct_gpow_add G hg S hS_mem 𝟙 (mul bm p)).symm
          rwa [gpow_one G g hg] at this
        calc wieldandtAct G g S
            = wieldandtAct G g (wieldandtAct G (gpow G g (mul bm p)) S) := by rw [h_bmp]
          _ = wieldandtAct G (gpow G g (add 𝟙 (mul bm p))) S := h_step
          _ = wieldandtAct G (gpow G g (mul bn k)) S := by rw [h_eq]
          _ = S := h_bnk
      · -- h2 : 𝟙 = sub (mul bn p) (mul bm k)
        have h2' : sub (mul bn p) (mul bm k) = 𝟙 := h2.symm
        have hlt : lt₀ (mul bm k) (mul bn p) := by
          apply (sub_pos_iff_lt (mul bn p) (mul bm k)).mp
          rw [← h2]; exact le_refl 𝟙
        have h_eq : add 𝟙 (mul bm k) = mul bn p := by
          have key := sub_k_add_k (mul bn p) (mul bm k) (lt_imp_le _ _ hlt)
          rw [h2'] at key; exact key
        have h_bmk := h_period_mul k hk bm
        have h_bnp := h_period_mul p hp_act bn
        have h_step : wieldandtAct G g (wieldandtAct G (gpow G g (mul bm k)) S) =
            wieldandtAct G (gpow G g (add 𝟙 (mul bm k))) S := by
          have := (wieldandtAct_gpow_add G hg S hS_mem 𝟙 (mul bm k)).symm
          rwa [gpow_one G g hg] at this
        calc wieldandtAct G g S
            = wieldandtAct G g (wieldandtAct G (gpow G g (mul bm k)) S) := by rw [h_bmk]
          _ = wieldandtAct G (gpow G g (add 𝟙 (mul bm k))) S := h_step
          _ = wieldandtAct G (gpow G g (mul bn p)) S := by rw [h_eq]
          _ = S := h_bnp

    /-- Análogo de mckay_orbit_remove para la acción wieldandtAct.
        Dado S ∈ Ω con g·S ≠ S y g de orden p primo, devuelve
        Ω' = Ω \ {g^k·S | k < p} con las propiedades necesarias
        para continuar la inducción en wielandt_orbit_partition. -/
    private theorem wielandt_orbit_remove
        (G : FinGroup ℕ₀) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
        (p : ℕ₀) (hp : Prime p) (hgp : gpow G g p = G.id)
        (Ω : List (List ℕ₀)) (S : List ℕ₀)
        (hS_in : S ∈ Ω)
        (hS_nfix : wieldandtAct G g S ≠ S)
        (hS_sorted : Sorted (· < ·) S)
        (hS_mem : ∀ x ∈ S, x ∈ G.carrier.elems)
        (hΩ_nd : Ω.Nodup)
        (hΩ_closed : ∀ T, T ∈ Ω → wieldandtAct G g T ∈ Ω)
        (hΩ_inj : ∀ T₁, T₁ ∈ Ω → ∀ T₂, T₂ ∈ Ω →
          wieldandtAct G g T₁ = wieldandtAct G g T₂ → T₁ = T₂) :
        ∃ Ω' : List (List ℕ₀),
          Ω'.Nodup ∧
          (∀ T, T ∈ Ω' → wieldandtAct G g T ∈ Ω') ∧
          (∀ T₁, T₁ ∈ Ω' → ∀ T₂, T₂ ∈ Ω' →
            wieldandtAct G g T₁ = wieldandtAct G g T₂ → T₁ = T₂) ∧
          lengthₚ Ω = Peano.Add.add (lengthₚ Ω') p ∧
          lengthₚ (Ω.filter (fun T => decide (wieldandtAct G g T = T))) =
          lengthₚ (Ω'.filter (fun T => decide (wieldandtAct G g T = T))) ∧
          (∀ T, T ∈ Ω' → T ∈ Ω) := by
      -- ── g^p · S = S ──────────────────────────────────────────────────
      have hgp_act : wieldandtAct G (gpow G g p) S = S := by
        rw [hgp]; exact wieldandtAct_id G S hS_sorted hS_mem
      -- ── No early return: g^k · S ≠ S for 0 < k < p ──────────────────
      have orbit_no_return : ∀ k : ℕ₀, lt₀ 𝟘 k → lt₀ k p →
          wieldandtAct G (gpow G g k) S ≠ S := by
        intro k hk_pos hk_lt heq
        exact hS_nfix (wieldandtAct_gpow_fixed_of_gcd_one G hg S hS_sorted hS_mem k p
                        heq hgp_act (gcd_eq_one_of_pos_lt_prime k p hk_pos hk_lt hp))
      -- ── Define orbit ─────────────────────────────────────────────────
      let orb : ℕ₀ → List ℕ₀ := fun k => wieldandtAct G (gpow G g k) S
      -- ── g · (orb k) = orb (σ k) ──────────────────────────────────────
      have rv_orb_eq : ∀ k : ℕ₀, wieldandtAct G g (orb k) = orb (σ k) := fun k => by
        show wieldandtAct G g (wieldandtAct G (gpow G g k) S) =
             wieldandtAct G (gpow G g (σ k)) S
        rw [gpow_succ, ← gpow_comm_single G hg k]
        exact wieldandtAct_comp G g (gpow G g k) S hg (gpow_mem G hg k) hS_mem
      let orbit : List (List ℕ₀) := (ℕ₀FSet.Fin₀Set p).elems.map orb
      -- ── orb is injective on Fin₀Set p ────────────────────────────────
      have orb_inj : ∀ i j : ℕ₀,
          i ∈ (ℕ₀FSet.Fin₀Set p).elems → j ∈ (ℕ₀FSet.Fin₀Set p).elems →
          orb i = orb j → i = j := by
        intro i j hi hj heq
        have hi_lt := (ℕ₀FSet.mem_Fin₀Set_iff p i).mp hi
        have hj_lt := (ℕ₀FSet.mem_Fin₀Set_iff p j).mp hj
        rcases trichotomy i j with h_lt | h_eq | h_gt
        · exfalso
          have hpj : add (sub p j) j = p := sub_k_add_k p j (lt_imp_le j p hj_lt)
          exact orbit_no_return _
            (lt_of_lt_of_le (sub_pos_of_lt hj_lt) (le_self_add _ _))
            (by have := (add_lt_add_left_iff (sub p j) i j).mpr h_lt; rwa [hpj] at this)
            (calc wieldandtAct G (gpow G g (add (sub p j) i)) S
                  = wieldandtAct G (gpow G g (sub p j)) (orb i) :=
                        wieldandtAct_gpow_add G hg S hS_mem (sub p j) i
                _ = wieldandtAct G (gpow G g (sub p j)) (orb j) := by rw [heq]
                _ = wieldandtAct G (gpow G g (add (sub p j) j)) S :=
                        (wieldandtAct_gpow_add G hg S hS_mem (sub p j) j).symm
                _ = wieldandtAct G (gpow G g p) S := by rw [hpj]
                _ = S := hgp_act)
        · exact h_eq
        · exfalso
          have hpi : add (sub p i) i = p := sub_k_add_k p i (lt_imp_le i p hi_lt)
          exact orbit_no_return _
            (lt_of_lt_of_le (sub_pos_of_lt hi_lt) (le_self_add _ _))
            (by have := (add_lt_add_left_iff (sub p i) j i).mpr h_gt; rwa [hpi] at this)
            (calc wieldandtAct G (gpow G g (add (sub p i) j)) S
                  = wieldandtAct G (gpow G g (sub p i)) (orb j) :=
                        wieldandtAct_gpow_add G hg S hS_mem (sub p i) j
                _ = wieldandtAct G (gpow G g (sub p i)) (orb i) := by rw [heq]
                _ = wieldandtAct G (gpow G g (add (sub p i) i)) S :=
                        (wieldandtAct_gpow_add G hg S hS_mem (sub p i) i).symm
                _ = wieldandtAct G (gpow G g p) S := by rw [hpi]
                _ = S := hgp_act)
      -- ── orbit is nodup ───────────────────────────────────────────────
      have orbit_nodup : orbit.Nodup :=
        nodup_map_of_inj_on orb _ (sorted_nodup (ℕ₀FSet.Fin₀Set p).sorted) orb_inj
      -- ── orbit has length p ───────────────────────────────────────────
      have orbit_len_p : Λ orbit.length = p := by
        show Λ ((ℕ₀FSet.Fin₀Set p).elems.map orb).length = p
        rw [List.length_map]; exact ℕ₀FSet.Fin₀Set_card p
      -- ── orbit elements are in Ω ──────────────────────────────────────
      have orbit_mem_Ω : ∀ k : ℕ₀, lt₀ k p → orb k ∈ Ω := by
        intro k hk
        induction k with
        | zero =>
          have : orb 𝟘 = S := by
            show wieldandtAct G (gpow G g 𝟘) S = S
            rw [gpow_zero]; exact wieldandtAct_id G S hS_sorted hS_mem
          rw [this]; exact hS_in
        | succ k' ih =>
          have hk'_lt := lt_trans k' (σ k') p (lt_succ_self k') hk
          rw [← rv_orb_eq k']; exact hΩ_closed (orb k') (ih hk'_lt)
      have orbit_mem_Ω' : ∀ T ∈ orbit, T ∈ Ω := fun T hT =>
        let ⟨k, hk_in, hk_eq⟩ := List.mem_map.mp hT
        hk_eq ▸ orbit_mem_Ω k ((ℕ₀FSet.mem_Fin₀Set_iff p k).mp hk_in)
      -- ── orbit has no fixed points ─────────────────────────────────────
      have orbit_no_fixed : ∀ k : ℕ₀, lt₀ k p → wieldandtAct G g (orb k) ≠ orb k := by
        intro k hk heq
        rw [rv_orb_eq k] at heq
        -- heq : orb (σ k) = orb k
        rcases (lt_succ_iff_lt_or_eq (σ k) p).mp ((succ_lt_succ_iff k p).mpr hk)
            with h_lt | h_eq
        · -- σ k < p: orb_inj gives σ k = k, contradicting lt_succ_self
          exact absurd (orb_inj (σ k) k
                    ((ℕ₀FSet.mem_Fin₀Set_iff p (σ k)).mpr h_lt)
                    ((ℕ₀FSet.mem_Fin₀Set_iff p k).mpr hk) heq).symm
                 (ne_of_lt k (σ k) (lt_succ_self k))
        · -- σ k = p: orb (σ k) = S, so g^k · S = S — contradicts orbit_no_return
          have h_k_pos : lt₀ 𝟘 k := by
            apply pos_of_ne_zero
            intro h0; subst h0
            exact absurd h_eq
              (ne_of_lt 𝟙 p (lt_of_lt_of_le (lt_succ_self 𝟙) (prime_ge_two hp)))
          have h_orbsk_S : orb (σ k) = S := by
            show wieldandtAct G (gpow G g (σ k)) S = S
            rw [h_eq]; exact hgp_act
          exact orbit_no_return k h_k_pos hk (h_orbsk_S ▸ heq).symm
      -- ── Orbit preimage: g · T ∈ orbit → T ∈ orbit ───────────────────
      have orbit_preimage : ∀ T, T ∈ Ω → wieldandtAct G g T ∈ orbit → T ∈ orbit := by
        intro T hT hw
        obtain ⟨k, hk_in, hk_eq⟩ := List.mem_map.mp hw
        have hk_lt := (ℕ₀FSet.mem_Fin₀Set_iff p k).mp hk_in
        rw [List.mem_map]
        cases k with
        | zero =>
          -- g · T = orb 0 = S; and g · (orb (p-1)) = orb p = S
          have h_p1_le : le₀ 𝟙 p :=
            le_trans 𝟙 𝟚 p (Or.inl (lt_succ_self 𝟙)) (prime_ge_two hp)
          have h_sub1p : add (sub p 𝟙) 𝟙 = p := sub_k_add_k p 𝟙 h_p1_le
          have h_sub_lt : lt₀ (sub p 𝟙) p := by
            have := @lt_add_of_pos_right (sub p 𝟙) 𝟙
                      (pos_of_ne_zero 𝟙 (Peano.Axioms.succ_neq_zero 𝟘))
            rwa [h_sub1p] at this
          have h_orb0_S : orb 𝟘 = S := by
            show wieldandtAct G (gpow G g 𝟘) S = S
            rw [gpow_zero]; exact wieldandtAct_id G S hS_sorted hS_mem
          have h_pred_act : wieldandtAct G g (orb (sub p 𝟙)) = S := by
            have h := rv_orb_eq (sub p 𝟙)
            have h_succ_eq : σ (sub p 𝟙) = p := by
              rw [← add_one (sub p 𝟙)]; exact h_sub1p
            rw [h_succ_eq] at h; rw [h]; exact hgp_act
          have h_eq_T : T = orb (sub p 𝟙) :=
            hΩ_inj T hT (orb (sub p 𝟙)) (orbit_mem_Ω (sub p 𝟙) h_sub_lt)
              (hk_eq.symm.trans (h_orb0_S.trans h_pred_act.symm))
          exact ⟨sub p 𝟙, (ℕ₀FSet.mem_Fin₀Set_iff p (sub p 𝟙)).mpr h_sub_lt, h_eq_T.symm⟩
        | succ k' =>
          have hk'_lt := lt_trans k' (σ k') p (lt_succ_self k') hk_lt
          have h_eq_T : T = orb k' :=
            hΩ_inj T hT (orb k') (orbit_mem_Ω k' hk'_lt)
              (hk_eq.symm.trans (rv_orb_eq k').symm)
          exact ⟨k', (ℕ₀FSet.mem_Fin₀Set_iff p k').mpr hk'_lt, h_eq_T.symm⟩
      -- ── orbit closed under g ─────────────────────────────────────────
      have orbit_closed : ∀ T ∈ orbit, wieldandtAct G g T ∈ orbit := by
        intro T hT
        obtain ⟨k, hk_in, hk_eq⟩ := List.mem_map.mp hT
        have hk_lt := (ℕ₀FSet.mem_Fin₀Set_iff p k).mp hk_in
        subst hk_eq
        rw [rv_orb_eq k, List.mem_map]
        rcases (lt_succ_iff_lt_or_eq (σ k) p).mp ((succ_lt_succ_iff k p).mpr hk_lt)
            with h_lt | h_eq
        · exact ⟨σ k, (ℕ₀FSet.mem_Fin₀Set_iff p (σ k)).mpr h_lt, rfl⟩
        · have h_sk : wieldandtAct G (gpow G g (σ k)) S = S := by rw [h_eq]; exact hgp_act
          have h_orb0_S : orb 𝟘 = S := by
            show wieldandtAct G (gpow G g 𝟘) S = S
            rw [gpow_zero]; exact wieldandtAct_id G S hS_sorted hS_mem
          exact ⟨𝟘, (ℕ₀FSet.mem_Fin₀Set_iff p 𝟘).mpr (pos_of_ne_zero p hp.1),
                 h_orb0_S.trans h_sk.symm⟩
      -- ── nodup_sub_len helper ──────────────────────────────────────────
      have nodup_sub_len : ∀ {l₁ l₂ : List (List ℕ₀)},
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
      -- ── Define Ω' and prove its properties ───────────────────────────
      refine ⟨Ω.filter (fun T => !decide (T ∈ orbit)), ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- Property 1: Ω'.Nodup
      · exact List.filter_sublist.nodup hΩ_nd
      -- Property 2: Ω' closed under g
      · intro T hT
        rw [List.mem_filter] at hT ⊢
        obtain ⟨hT_Ω, hT_not⟩ := hT
        have hT_not_orbit : T ∉ orbit := by
          intro h; simp [decide_eq_true h] at hT_not
        exact ⟨hΩ_closed T hT_Ω, by
          have hn : wieldandtAct G g T ∉ orbit :=
            fun h => hT_not_orbit (orbit_preimage T hT_Ω h)
          simp [hn]⟩
      -- Property 3: injectivity preserved
      · intro T₁ hT₁ T₂ hT₂ heq
        exact hΩ_inj T₁ (List.mem_filter.mp hT₁).1 T₂ (List.mem_filter.mp hT₂).1 heq
      -- Property 4: |Ω| = |Ω'| + p
      · have filter_part : ∀ (l : List (List ℕ₀)) (q : List ℕ₀ → Bool),
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
            (Ω.filter (fun T => decide (T ∈ orbit))).length = orbit.length := by
          apply Nat.le_antisymm
          · apply nodup_sub_len (List.filter_sublist.nodup hΩ_nd)
            intro T hT; exact of_decide_eq_true (List.mem_filter.mp hT).2
          · apply nodup_sub_len orbit_nodup
            intro T hT
            rw [List.mem_filter]
            exact ⟨orbit_mem_Ω' T hT, decide_eq_true hT⟩
        have hnat : Ω.length =
            Nat.add (Ω.filter (fun T => !decide (T ∈ orbit))).length orbit.length := by
          have h := filter_part Ω (fun T => decide (T ∈ orbit))
          rw [filter_orbit_len] at h; simp only [Nat.add_eq] at h ⊢; omega
        suffices h3 : Λ Ω.length = add (Λ (Ω.filter (fun T => !decide (T ∈ orbit))).length) p by
          simpa [lengthₚ] using h3
        rw [hnat, isomorph_Λ_add, orbit_len_p]
      -- Property 5: same fixed-point filter count
      · suffices h4 :
            (Ω.filter (fun T => decide (wieldandtAct G g T = T))).length =
            ((Ω.filter (fun T => !decide (T ∈ orbit))).filter
              (fun T => decide (wieldandtAct G g T = T))).length by
          exact congrArg Λ h4
        apply Nat.le_antisymm
        · apply nodup_sub_len (List.filter_sublist.nodup hΩ_nd)
          intro T hT
          rw [List.mem_filter] at hT ⊢
          obtain ⟨hT_Ω, hT_fixed⟩ := hT
          refine ⟨?_, hT_fixed⟩
          rw [List.mem_filter]
          refine ⟨hT_Ω, ?_⟩
          -- T is a fixed point → T ∉ orbit (orbit has no fixed points)
          have hn : T ∉ orbit := by
            intro hT_orb
            obtain ⟨k, hk_in, hk_eq⟩ := List.mem_map.mp hT_orb
            exact orbit_no_fixed k ((ℕ₀FSet.mem_Fin₀Set_iff p k).mp hk_in)
              (hk_eq ▸ of_decide_eq_true hT_fixed)
          simp [hn]
        · apply nodup_sub_len
              (List.filter_sublist.nodup (List.filter_sublist.nodup hΩ_nd))
          intro T hT
          rw [List.mem_filter] at hT ⊢
          exact ⟨(List.mem_filter.mp hT.1).1, hT.2⟩
      -- Property 6: Ω' ⊆ Ω
      · intro T hT; exact (List.mem_filter.mp hT).1

    -- ══════════════════════════════════════════════════════════════════
    -- § Wielandt Pieza A: partición de órbitas de ⟨g⟩ sobre Ω
    -- ══════════════════════════════════════════════════════════════════

    /-- La acción de g de orden p sobre Ω produce sólo órbitas de tamaño 1 ó p.
        |Ω| = |fix_g(Ω)| + p·k para algún k. -/
    private theorem wielandt_orbit_partition
        (G : FinGroup ℕ₀) (g : ℕ₀) (hg : g ∈ G.carrier.elems)
        (p : ℕ₀) (hp : Prime p) (hgp : gpow G g p = G.id) (hg_ne : g ≠ G.id)
        (Ω : List (List ℕ₀))
        (hΩ_nd : Ω.Nodup)
        (hΩ_closed : ∀ S, S ∈ Ω → wieldandtAct G g S ∈ Ω)
        (hΩ_inj : ∀ S, S ∈ Ω → ∀ T, T ∈ Ω →
          wieldandtAct G g S = wieldandtAct G g T → S = T)
        (hΩ_sorted : ∀ S, S ∈ Ω → Sorted (· < ·) S)
        (hΩ_mem : ∀ S, S ∈ Ω → ∀ x ∈ S, x ∈ G.carrier.elems) :
        ∃ k : ℕ₀, lengthₚ Ω = Peano.Add.add
          (lengthₚ (Ω.filter (fun S => decide (wieldandtAct G g S = S))))
          (Peano.Mul.mul p k) := by
      suffices H : ∀ (n : ℕ₀) (Ω' : List (List ℕ₀)),
          Ω'.Nodup →
          (∀ S, S ∈ Ω' → wieldandtAct G g S ∈ Ω') →
          (∀ S, S ∈ Ω' → ∀ T, T ∈ Ω' →
            wieldandtAct G g S = wieldandtAct G g T → S = T) →
          (∀ S, S ∈ Ω' → Sorted (· < ·) S) →
          (∀ S, S ∈ Ω' → ∀ x ∈ S, x ∈ G.carrier.elems) →
          lengthₚ Ω' = n →
          ∃ k : ℕ₀, lengthₚ Ω' = Peano.Add.add
            (lengthₚ (Ω'.filter (fun S => decide (wieldandtAct G g S = S))))
            (Peano.Mul.mul p k) from
        H (lengthₚ Ω) Ω hΩ_nd hΩ_closed hΩ_inj hΩ_sorted hΩ_mem rfl
      intro n
      induction n using well_founded_lt.induction
      rename_i n ih
      intro Ω' hΩ'_nd hΩ'_closed hΩ'_inj hΩ'_sorted hΩ'_mem hlen
      cases Ω' with
      | nil => exact ⟨𝟘, rfl⟩
      | cons S Ω'' =>
        by_cases hS_fix : wieldandtAct G g S = S
        · -- S es punto fijo: inducción en Ω''
          have hΩ''_nd := (List.nodup_cons.mp hΩ'_nd).2
          have hΩ''_closed : ∀ T, T ∈ Ω'' → wieldandtAct G g T ∈ Ω'' := by
            intro T hT
            have h1 := hΩ'_closed T (List.mem_cons_of_mem S hT)
            rcases List.mem_cons.mp h1 with h_eq | h
            · exfalso
              have h_inj_res := hΩ'_inj T (List.mem_cons_of_mem S hT)
                S List.mem_cons_self (h_eq.trans hS_fix.symm)
              exact (List.nodup_cons.mp hΩ'_nd).1 (h_inj_res ▸ hT)
            · exact h
          have hΩ''_inj : ∀ T₁, T₁ ∈ Ω'' → ∀ T₂, T₂ ∈ Ω'' →
              wieldandtAct G g T₁ = wieldandtAct G g T₂ → T₁ = T₂ :=
            fun T₁ h₁ T₂ h₂ heq =>
              hΩ'_inj T₁ (List.mem_cons_of_mem S h₁)
                T₂ (List.mem_cons_of_mem S h₂) heq
          have hlen'' : lengthₚ Ω'' < n := by
            have hsucc : n = σ (lengthₚ Ω'') := by
              rw [← hlen]; exact (lengthₚ_cons S Ω'').symm
            rw [hsucc]; exact lt_succ_self (lengthₚ Ω'')
          have hΩ''_sorted : ∀ T, T ∈ Ω'' → Sorted (· < ·) T :=
            fun T hT => hΩ'_sorted T (List.mem_cons_of_mem S hT)
          have hΩ''_mem : ∀ T, T ∈ Ω'' → ∀ x ∈ T, x ∈ G.carrier.elems :=
            fun T hT => hΩ'_mem T (List.mem_cons_of_mem S hT)
          obtain ⟨k, hk⟩ := ih (lengthₚ Ω'') hlen'' Ω'' hΩ''_nd hΩ''_closed hΩ''_inj
              hΩ''_sorted hΩ''_mem rfl
          refine ⟨k, ?_⟩
          have h_filter : (S :: Ω'').filter (fun T => decide (wieldandtAct G g T = T)) =
              S :: Ω''.filter (fun T => decide (wieldandtAct G g T = T)) :=
            List.filter_cons_of_pos (decide_eq_true hS_fix)
          rw [h_filter, lengthₚ_cons, lengthₚ_cons, hk]
          exact (Peano.Add.succ_add _ _).symm
        · -- S no es punto fijo: usar wielandt_orbit_remove
          have hS_sorted : Sorted (· < ·) S := hΩ'_sorted S List.mem_cons_self
          have hS_mem' : ∀ x ∈ S, x ∈ G.carrier.elems := hΩ'_mem S List.mem_cons_self
          obtain ⟨Ω_rem, hΩ_rem_nd, hΩ_rem_closed, hΩ_rem_inj, hlen_sum, hfilter_eq,
                   hΩ_rem_sub⟩ :=
            wielandt_orbit_remove G hg p hp hgp (S :: Ω'') S
              List.mem_cons_self hS_fix hS_sorted hS_mem'
              hΩ'_nd hΩ'_closed hΩ'_inj
          have hΩ_rem_sorted : ∀ T, T ∈ Ω_rem → Sorted (· < ·) T :=
            fun T hT => hΩ'_sorted T (hΩ_rem_sub T hT)
          have hΩ_rem_mem : ∀ T, T ∈ Ω_rem → ∀ x ∈ T, x ∈ G.carrier.elems :=
            fun T hT => hΩ'_mem T (hΩ_rem_sub T hT)
          have h_n_eq : n = add (lengthₚ Ω_rem) p := hlen.symm.trans hlen_sum
          have h_rem_lt : lengthₚ Ω_rem < n := by
            rw [h_n_eq]; exact lt_add_of_pos_right (pos_of_ne_zero p hp.1)
          obtain ⟨k', hk'⟩ := ih (lengthₚ Ω_rem) h_rem_lt Ω_rem hΩ_rem_nd hΩ_rem_closed
              hΩ_rem_inj hΩ_rem_sorted hΩ_rem_mem rfl
          refine ⟨σ k', ?_⟩
          calc lengthₚ (S :: Ω'')
              = add (lengthₚ Ω_rem) p := hlen_sum
            _ = add (add (lengthₚ (Ω_rem.filter (fun T => decide (wieldandtAct G g T = T))))
                        (mul p k')) p := by rw [hk']
            _ = add (lengthₚ (Ω_rem.filter (fun T => decide (wieldandtAct G g T = T))))
                    (add (mul p k') p) := by rw [← add_assoc]
            _ = add (lengthₚ (Ω_rem.filter (fun T => decide (wieldandtAct G g T = T))))
                    (mul p (σ k')) := by rw [← mul_succ]
            _ = add (lengthₚ ((S :: Ω'').filter (fun T => decide (wieldandtAct G g T = T))))
                    (mul p (σ k')) := by rw [hfilter_eq.symm]

    /-- Argumento de Wielandt, pieza 5:
        Si p ∣ r y p^(m+1) | |G| con |G| = p^(m+1) · r, y ningún subgrupo propio de G
        es divisible por p^(m+1), entonces ¬ p ∣ r.
        Caso m = 0: demostrado via Cauchy + h_no_proper.
        Caso m ≥ 1: HI disponible (Sylow First para grupos de orden < |G|), pero la ruta
          natural pasa por G/K (cociente), que es FinGroup ℕ₀FSet, no FinGroup ℕ₀.
          Bloqueador actual: tipo mismatch FinGroup ℕ₀ vs FinGroup ℕ₀FSet al aplicar HI. -/
    private theorem wielandt_p_ndvd_r
        (G : FinGroup ℕ₀) (p m r : ℕ₀)
        (hp : Prime p)
        (hr_eq : Mul.mul (p ^ (σ m)) r = G.carrier.card)
        (HI : ∀ G' : FinGroup ℕ₀, lt₀ G'.carrier.card G.carrier.card →
          pow_dvd_card p (σ m) G'.carrier →
          ∃ K : Subgroup G', K.carrier.card = p ^ (σ m))
        (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
          (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
            ∃ K : Subgroup G0, K.carrier.card = p0)
        (h_no_proper : ∀ M : Subgroup G, M.carrier.card ≠ G.carrier.card →
          ¬ pow_dvd_card p (σ m) M.carrier) :
        ¬ p ∣ r := by
      cases m with
      | zero =>
        intro ⟨r', hr'⟩
        -- p^(σ 0) = p
        have hp1 : p ^ (σ 𝟘) = p := (pow_succ p 𝟘).trans (by rw [pow_zero, one_mul])
        -- p * r = |G|
        have hr_eq' : Mul.mul p r = G.carrier.card := hp1 ▸ hr_eq
        -- r' ≠ 0 (si no, r = 0 y |G| = 0, imposible)
        have hr'_ne : r' ≠ 𝟘 := by
          intro h0
          rw [h0, mul_zero] at hr'
          rw [hr', mul_zero] at hr_eq'
          exact absurd (card_pos_of_mem_aux G.id_in) (hr_eq'.symm ▸ lt_irrefl 𝟘)
        -- 1 < r (para mul_lt_left)
        have hr_gt_one : lt₀ 𝟙 r := by
          rw [hr']
          have h_le : le₀ p (Mul.mul p r') := mul_le_right p r' hr'_ne
          rcases h_le with h_lt | h_eq
          · exact lt_trans 𝟙 p (Mul.mul p r') (one_lt_prime hp) h_lt
          · rw [← h_eq]; exact one_lt_prime hp
        -- p ∣ |G| con testigo p * r'
        have hG_p_dvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card :=
          ⟨Mul.mul p r', by rw [← hr_eq', hr']⟩
        -- Por Cauchy: ∃ K ≤ G con |K| = p
        obtain ⟨K, hK_card⟩ := hC G p hp hG_p_dvd
        -- K es propio: p < p * r = |G|
        have hK_lt : lt₀ K.carrier.card G.carrier.card := by
          rw [hK_card, ← hr_eq']
          exact mul_lt_left p r hp.1 hr_gt_one
        have hK_ne : K.carrier.card ≠ G.carrier.card :=
          ne_of_lt K.carrier.card G.carrier.card hK_lt
        -- Contradicción: pow_dvd_card p (σ 0) K.carrier con t=1 vs. h_no_proper
        exact absurd ⟨𝟙, by rw [hp1, mul_one]; exact hK_card.symm⟩ (h_no_proper K hK_ne)
      | succ m' =>
        -- HI disponible: ∀ G' : FinGroup ℕ₀, |G'| < |G| → p^(σm) | |G'| → ∃ K ≤ G', |K| = p^(σm).
        -- Argumento: asumir p ∣ r. Cauchy da K ≤ G con |K| = p (propio).
        -- HI no aplica a K directamente (p^(σ(σm')) ∤ p, ya que σ(σm') ≥ 2).
        -- Ruta natural: cociente G/K — pero G/K es FinGroup ℕ₀FSet, no FinGroup ℕ₀.
        -- Bloqueador: tipo mismatch FinGroup ℕ₀ vs FinGroup ℕ₀FSet al aplicar HI a G/K.
        sorry

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
      (HI : ∀ G' : FinGroup ℕ₀, lt₀ G'.carrier.card G.carrier.card →
        pow_dvd_card p (σ m) G'.carrier →
        ∃ K : Subgroup G', K.carrier.card = p ^ (σ m))
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
      -- La traslación izquierda preserva Ω (representante ordenado del conjunto imagen)
      have htrans : ∀ g ∈ G.carrier.elems, ∀ S ∈ Ω,
          (G.carrier.filter (fun x => decide (x ∈ S.map (G.op g)))).elems ∈ Ω := by
        intro g hg S hS
        obtain ⟨hS_nd, _hS_sorted, hS_memG, hS_len⟩ := hΩ_mem S hS
        let T := G.carrier.filter (fun x => decide (x ∈ S.map (G.op g)))
        have hmap_nd : (S.map (G.op g)).Nodup :=
          nodup_map_of_inj_on _ _ hS_nd (fun a b ha hb heq =>
            op_cancel_left G hg (hS_memG a ha) (hS_memG b hb) heq)
        have hmap_G : ∀ x ∈ S.map (G.op g), x ∈ G.carrier.elems := fun x hx => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx; exact op_mem G hg (hS_memG s hs)
        apply hΩ_full
        · exact sorted_nodup T.sorted
        · exact T.sorted
        · exact fun x hx => (List.mem_filter.mp hx).1
        · show Λ T.elems.length = N
          have heq : T.elems.length = (S.map (G.op g)).length :=
            nodup_same_card (sorted_nodup T.sorted) hmap_nd
              (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)
              (fun x hx => List.mem_filter.mpr ⟨hmap_G x hx, decide_eq_true hx⟩)
          rw [heq, List.length_map]; exact hS_len
      -- p ∤ r (por h_no_proper: si p | r, p^(m+2) | |G|, habría subgrupo propio)
      have hp_ndvd_r : ¬ p ∣ r := wielandt_p_ndvd_r G p m r hp hr HI hC h_no_proper
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
      -- ∃ subgrupo H de G de orden N = p^(m+1)
      exact wielandt_fixed_point_exists G Ω N p hp ⟨r, hr⟩ hΩ_nd hΩ_mem hΩ_full htrans hΩ_ndvd ⟨m, rfl⟩

    private theorem sylow_center_step
      (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
        (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
          ∃ K : Subgroup G0, K.carrier.card = p0)
      (G : FinGroup ℕ₀) (p m : ℕ₀)
      (HI : ∀ G' : FinGroup ℕ₀, lt₀ G'.carrier.card G.carrier.card →
        pow_dvd_card p (σ m) G'.carrier →
        ∃ K : Subgroup G', K.carrier.card = p ^ (σ m))
      (hp : Prime p) (hpow : pow_dvd_card p (σ m) G.carrier)
      (h_no_proper : ∀ M : Subgroup G, M.carrier.card ≠ G.carrier.card →
        ¬ pow_dvd_card p (σ m) M.carrier) :
        ∃ H : Subgroup G, H.carrier.card = p ^ (σ m) :=
      sylow_center_step_wielandt hC G p m HI hp hpow h_no_proper

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
          · let HI : ∀ G' : FinGroup ℕ₀, lt₀ G'.carrier.card G0.carrier.card →
                pow_dvd_card p (σ m) G'.carrier →
                ∃ K : Subgroup G', K.carrier.card = p ^ (σ m) :=
              fun G' hlt hpow' => ih G'.carrier.card (hn ▸ hlt) G' rfl hpow'
            exact sylow_center_step hC G0 p m HI hp hpow0
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

    /-- Si `le₀ a b` y `p^b | |S|`, entonces `p^a | |S|`.
        Consecuencia de `p^a | p^b` usando `pow_add_eq_mul_pow`. -/
    private theorem pow_dvd_card_of_le (p a b : ℕ₀) (S : ℕ₀FSet)
        (h : le₀ a b) (h_dvd : pow_dvd_card p b S) : pow_dvd_card p a S := by
      obtain ⟨m, hm⟩ := h_dvd
      obtain ⟨c, hc⟩ := (le_iff_exists_add a b).mp h
      -- hc : b = add a c, hm : mul (p^b) m = S.card
      -- mul (p^a) (p^c) = p^(add a c) = p^b  (en modo término: eq. definitional)
      have h3 : mul (p ^ a) (p ^ c) = p ^ b :=
        (pow_add_eq_mul_pow p a c).symm.trans (congrArg (Peano.Pow.pow p) hc.symm)
      -- mul (p^a) (mul (p^c) m) = mul (mul (p^a) (p^c)) m = mul (p^b) m = S.card
      exact ⟨mul (p ^ c) m, by rw [← mul_assoc, h3]; exact hm⟩

    /-- La valuación p-ádica de |G| es única: si H y K son subgrupos de Sylow-p de G,
        entonces |H| = |K|.
        Prueba: si n₁ ≠ n₂, suponemos (sin pérdida de generalidad) n₁ < n₂;
        entonces p^(n₁+1) | p^n₂ | |G|, contradiciendo ¬p^(n₁+1) | |G|. -/
    private theorem sylow_card_eq
        (G : FinGroup ℕ₀) (p : ℕ₀)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p)
        (hK : isSylowSubgroup G K p) :
        H.carrier.card = K.carrier.card := by
      obtain ⟨n₁, hn₁_exp, hn₁_card⟩ := hH
      obtain ⟨n₂, hn₂_exp, hn₂_card⟩ := hK
      obtain ⟨hdvd₁, hndvd₁⟩ := hn₁_exp
      obtain ⟨hdvd₂, hndvd₂⟩ := hn₂_exp
      have hn_eq : n₁ = n₂ := by
        rcases trichotomy n₁ n₂ with h | h | h
        · exact absurd
            (pow_dvd_card_of_le p (σ n₁) n₂ G.carrier
              (lt_nm_then_le_nm n₁ n₂ h) hdvd₂)
            hndvd₁
        · exact h
        · exact absurd
            (pow_dvd_card_of_le p (σ n₂) n₁ G.carrier
              (lt_nm_then_le_nm n₂ n₁ h) hdvd₁)
            hndvd₂
      exact hn₁_card.trans ((congrArg (p ^ ·) hn_eq).trans hn₂_card.symm)

    /-- H actúa sobre G/K por multiplicación izquierda; p∤|G/K|; el teorema de punto
        fijo para p-grupos da un coset fijo rK, equivalente a r⁻¹Hr ⊆ K. -/
    private theorem sylow_second_incl
        (G : FinGroup ℕ₀) (p : ℕ₀)
        (hp : Prime p)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p)
        (hK : isSylowSubgroup G K p) :
        ∃ r, r ∈ G.carrier.elems ∧
          ∀ h, h ∈ H.carrier.elems → G.op (G.inv r) (G.op h r) ∈ K.carrier.elems := by
      obtain ⟨n,   hn_exp,   hn_H_card⟩ := hH
      obtain ⟨n_K, hn_K_exp, hn_K_card⟩ := hK
      obtain ⟨hdvd,   hndvd_pn1⟩   := hn_exp
      obtain ⟨hdvd_K, hndvd_K_pn1⟩ := hn_K_exp
      -- unique Sylow exponent (hdvd / hdvd_K must survive until here)
      have hn_eq : n = n_K := by
        rcases trichotomy n n_K with h | h | h
        · exact absurd
            (pow_dvd_card_of_le p (σ n) n_K G.carrier
              (lt_nm_then_le_nm n n_K h) hdvd_K) hndvd_pn1
        · exact h
        · exact absurd
            (pow_dvd_card_of_le p (σ n_K) n G.carrier
              (lt_nm_then_le_nm n_K n h) hdvd) hndvd_K_pn1
      have hn_K_card' : K.carrier.card = pow p n := hn_eq ▸ hn_K_card
      obtain ⟨k, hGk⟩ := hdvd
      -- p ∤ k  (maximality: p ∣ k → p^(n+1) ∣ |G|, contradicting hndvd_pn1)
      have hndvd_k : ¬ p ∣ k := by
        intro ⟨j, hj⟩
        apply hndvd_pn1
        refine ⟨j, ?_⟩
        have hps : p ^ (σ n) = Mul.mul (p ^ n) p := pow_succ p n
        rw [hps, mul_assoc, ← hj]
        exact hGk
      exact coset_conjugate_exists G H K p n k hp hn_H_card hn_K_card' hGk hndvd_k

    /-- **Segundo Teorema de Sylow**: conjugación de p-subgrupos.
        Todo par de subgrupos de Sylow-p son conjugados en G.
        Estrategia:
        · `sylow_second_incl` da r ∈ G con r⁻¹Hr ⊆ K.
        · `sylow_card_eq` da |H| = |K|, de modo que la inclusión r⁻¹Hr ⊆ K
          (dada por una inyección con igual cardinalidad) implica r⁻¹Hr = K.
        · El testigo es g = r⁻¹; entonces ghg⁻¹ = r⁻¹h(r⁻¹)⁻¹ = r⁻¹hr ∈ K. -/
    theorem sylow_second (G : FinGroup ℕ₀) (p : ℕ₀)
        (hp : Prime p)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p) (hK : isSylowSubgroup G K p) :
        ∃ g, g ∈ G.carrier.elems ∧
          ∀ x, x ∈ K.carrier.elems ↔
            ∃ h, h ∈ H.carrier.elems ∧ G.op (G.op g h) (G.inv g) = x := by
      -- Paso 1: r con r⁻¹Hr ⊆ K, e |H| = |K|
      obtain ⟨r, hr, h_incl⟩ := sylow_second_incl G p hp H K hH hK
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
