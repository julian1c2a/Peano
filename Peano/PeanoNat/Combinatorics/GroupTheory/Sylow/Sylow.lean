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
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets
import Peano.PeanoNat.Combinatorics.GroupTheory.Action
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
    def isPSubgroup (G : FinGroup) (H : Subgroup G) (p : ℕ₀) : Prop :=
      ∃ k : ℕ₀, H.carrier.card = p ^ k

    /-- `p^n` es la mayor potencia de `p` que divide `|G|`
        (es decir, `p^n | |G|` pero `p^(n+1) ∤ |G|`). -/
    def isSylowExponent (G : FinGroup) (p n : ℕ₀) : Prop :=
      pow_dvd_card p n G.carrier ∧ ¬ pow_dvd_card p (σ n) G.carrier

    /-- Un subgrupo de Sylow `p` de `G` es un `p`-subgrupo de orden `p^n`
        donde `p^n` es la mayor potencia de `p` que divide `|G|`. -/
    def isSylowSubgroup (G : FinGroup) (H : Subgroup G) (p : ℕ₀) : Prop :=
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
    private theorem order_dvd_of_pow_eq_id (G : FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
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
    private theorem order_eq_prime_of_pow (G : FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems)
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
    private theorem gpow_lt_p_mem_cyclic (G : FinGroup) (g : ℕ₀) (hg : g ∈ G.carrier.elems)
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
        (G : FinGroup) (g : ℕ₀) (hg : g ∈ G.carrier.elems)
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
    private def listProd (G : FinGroup) : List ℕ₀ → ℕ₀
      | []      => G.id
      | x :: xs => G.op x (listProd G xs)

    private theorem listProd_nil (G : FinGroup) : listProd G [] = G.id := rfl

    private theorem listProd_cons (G : FinGroup) (x : ℕ₀) (xs : List ℕ₀) :
        listProd G (x :: xs) = G.op x (listProd G xs) := rfl

    /-- listProd de una lista cerrada en G da un elemento de G. -/
    private theorem listProd_mem (G : FinGroup) {l : List ℕ₀}
        (hl : ∀ x ∈ l, x ∈ G.carrier.elems) : listProd G l ∈ G.carrier.elems := by
      induction l with
      | nil => exact G.id_in
      | cons x xs ih =>
        exact op_mem G (hl x List.mem_cons_self)
          (ih (fun y hy => hl y (List.mem_cons_of_mem x hy)))

    /-- listProd de un singleton. -/
    private theorem listProd_singleton (G : FinGroup) {x : ℕ₀}
        (hx : x ∈ G.carrier.elems) : listProd G [x] = x := by
      simp only [listProd_cons, listProd_nil, (G.op_id x hx).1]

    /-- listProd es compatible con la concatenación. -/
    private theorem listProd_append (G : FinGroup) (l₁ l₂ : List ℕ₀)
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
    private def listProdVector (G : FinGroup) {n : ℕ₀} (v : Vector ℕ₀ n) : ℕ₀ :=
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

    /-- Genera todas las combinaciones de vectores de longitud `n` con elementos de `elems`. -/
    private def allVectorsList (elems : List ℕ₀) : (n : ℕ₀) → List (Vector ℕ₀ n)
      | 𝟘 => [⟨[], rfl⟩]
      | σ n =>
        let recs := allVectorsList elems n
        let rec flatMapAux (l : List (Vector ℕ₀ n)) : List (Vector ℕ₀ (σ n)) :=
          match l with
          | [] => []
          | v :: vs => (List.map (fun x => ⟨x :: v.val, by rw [lengthₚ_cons, v.property]⟩) elems) ++ flatMapAux vs
        flatMapAux recs

    /-- La rotación preserva la condición listProd = id. -/
    private theorem listProd_rotate_eq_id (G : FinGroup) {l : List ℕ₀}
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
    private theorem gpow_id_eq_id (G : FinGroup) (n : ℕ₀) :
        gpow G G.id n = G.id := by
      induction n with
      | zero     => rfl
      | succ n' ih => rw [gpow_succ, ih, (G.op_id G.id G.id_in).1]

    /-- Operación de McKay sobre una lista.
        Dado `[x₁, ..., x_k]`, devuelve `[x₂, ..., x_k, (x₁ ... x_k)⁻¹]`. -/
    private def mckayShiftList (G : FinGroup) : List ℕ₀ → List ℕ₀
      | [] => []
      | x :: xs => xs ++ [G.inv (listProd G (x :: xs))]

    /-- La operación de McKay preserva la longitud de la lista. -/
    private theorem lengthₚ_mckayShiftList (G : FinGroup) (l : List ℕ₀) :
        lengthₚ (mckayShiftList G l) = lengthₚ l := by
      cases l with
      | nil => rfl
      | cons x xs =>
        have h_shift : mckayShiftList G (x :: xs) = xs ++ [G.inv (listProd G (x :: xs))] := rfl
        rw [h_shift, lengthₚ_append, lengthₚ_singleton, add_one, lengthₚ_cons]

    /-- Operación de McKay elevada a Vector. -/
    private def mckayShift (G : FinGroup) {n : ℕ₀} (v : Vector ℕ₀ n) : Vector ℕ₀ n :=
      ⟨mckayShiftList G v.val, by rw [lengthₚ_mckayShiftList, v.property]⟩

    /-- La operación de McKay preserva la pertenencia al grupo G. -/
    private theorem mckayShiftList_mem (G : FinGroup) {l : List ℕ₀}
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
    private theorem mckayShiftList_inj (G : FinGroup) {l₁ l₂ : List ℕ₀}
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



    private theorem gpow_comm_left (G : FinGroup) {g : ℕ₀} (hg : g ∈ G.carrier.elems) (n : ℕ₀) :

        G.op g (gpow G g n) = G.op (gpow G g n) g := by

      have h1 : gpow G g (add 𝟙 n) = G.op g (gpow G g n) := by

        rw [gpow_add G hg 𝟙 n, gpow_one G g hg]

      have h2 : gpow G g (add n 𝟙) = G.op (gpow G g n) g := by

        rw [gpow_add G hg n 𝟙, gpow_one G g hg]

      rw [← h1, add_comm 𝟙 n, h2]



    private theorem listProd_all_eq_gpow (G : FinGroup) (a : ℕ₀)

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

    private theorem mckay_orbit_count (p : ℕ₀) (hp : Prime p)

        (T : List (Vector ℕ₀ p))

        (hT_nodup : T.Nodup)

        (hT_rot : ∀ v ∈ T, rotateVector v ∈ T) :

        ∃ k : Nat, T.length = Nat.add
          (T.filter (fun v => decide (rotateVector v = v))).length (Nat.mul (Ψ p) k) := by

      -- Induction on lengthₚ T (a ℕ₀ value) via well_founded_lt

      suffices H : ∀ (n : ℕ₀) (S : List (Vector ℕ₀ p)),

          S.Nodup → (∀ v ∈ S, rotateVector v ∈ S) → lengthₚ S = n →

          ∃ k : Nat, S.length = Nat.add (S.filter (fun v => decide (rotateVector v = v))).length (Nat.mul (Ψ p) k) from

        H (lengthₚ T) T hT_nodup hT_rot rfl

      intro n

      induction n using well_founded_lt.induction

      rename_i n ih

      intro S hnodup hrot hlen

      cases S with

      | nil => exact ⟨0, rfl⟩

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

          -- Goal: (v::S').length = add (v::filter S').length K
          -- = succ S'.length = add (succ (filter S').length) K
          -- From hk: S'.length = add (filter S').length K

          exact (congrArg Nat.succ hk).trans (Nat.succ_add _ _).symm

        · -- v is not fixed; the orbit of v has size Ψ p

          -- Sorry: the orbit sub-argument is deferred

          sorry



    private theorem mckay_p_dvd_powEqId (G : FinGroup) (p : ℕ₀)

        (hp : Prime p) (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :

        p ∣ (ℕ₀FSet.filter (fun g => decide (gpow G g p = G.id)) G.carrier).card := by

      sorry


    private theorem exists_ne_of_nodup_length_ge_two {l : List ℕ₀} {a : ℕ₀}
        (ha : a ∈ l) (hlen : 2 ≤ l.length) (hnodup : l.Nodup) :
        ∃ b ∈ l, b ≠ a := by
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
        ∃ b ∈ F.elems, b ≠ a := by
      have hnodup := FSetFunction.sorted_nodup F.sorted
      have hlen : 2 ≤ F.elems.length :=
        (isomorph_Λ_le 2 F.elems.length).mpr hcard
      exact exists_ne_of_nodup_length_ge_two ha hlen hnodup

    /-- Paso 1 (Cauchy mínimo): si `p` primo divide `|G|`, existe
        un subgrupo de `G` de orden `p`.
        Estrategia: G actúa sobre los p-tuplos (g₁,…,gₚ) con g₁·…·gₚ = e
        por permutación cíclica; las órbitas tienen tamaño 1 ó p; el total
        es divisible por p → existe una órbita de tamaño 1 ≠ identidad. -/
    theorem cauchy_minimal (G : FinGroup) (p : ℕ₀)
        (hp : Prime p) (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :
        ∃ K : Subgroup G, K.carrier.card = p := by
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
    /-- Paso 2 (elevación inductiva): asumiendo Cauchy mínimo,
        construir subgrupos de orden `p^(m+1)` cuando `p^(m+1) | |G|`. -/
    theorem sylow_lift_from_cauchy
        (hC : ∀ (G0 : FinGroup) (p0 : ℕ₀), Prime p0 →
          (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
          ∃ K : Subgroup G0, K.carrier.card = p0)
        (G : FinGroup) (p m : ℕ₀)
        (hp : Prime p) (hpow : pow_dvd_card p (σ m) G.carrier) :
        ∃ H : Subgroup G, H.carrier.card = p ^ (σ m) := by
      have _ := hC
      have _ := hp
      have _ := hpow
      sorry

    /-- **Primer Teorema de Sylow**: existencia de p-subgrupos. -/
    theorem sylow_first (G : FinGroup) (p n : ℕ₀)
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

    /-- **Segundo Teorema de Sylow**: conjugación de p-subgrupos. -/
    theorem sylow_second (G : FinGroup) (p : ℕ₀)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p) (hK : isSylowSubgroup G K p) :
        ∃ g, g ∈ G.carrier.elems ∧
          ∀ x, x ∈ K.carrier.elems ↔
            ∃ h, h ∈ H.carrier.elems ∧ G.op (G.op g h) (G.inv g) = x :=
      sorry  -- acción de H sobre G/K por multiplicación izquierda, conteo mod p

    /-!
    # § 4. Tercer Teorema de Sylow (número de subgrupos de Sylow)

    El número `n_p` de subgrupos de Sylow `p` satisface:
    - `n_p ≡ 1 (mod p)`
    - `n_p | [G : H]` donde `H` es cualquier subgrupo de Sylow `p`.
    -/

    /-- **Tercer Teorema de Sylow**: n_p ≡ 1 mod p y n_p | [G:H]. -/
    theorem sylow_third (G : FinGroup) (p : ℕ₀)
        (hp : Prime p)
        (sylows : List (Subgroup G))
        (h_all_sylow : ∀ H ∈ sylows, isSylowSubgroup G H p)
        (h_all_included : ∀ H : Subgroup G, isSylowSubgroup G H p → H ∈ sylows) :
        -- n_p ≡ 1 (mod p)
        (∃ k : ℕ₀, lengthₚ sylows = Peano.Add.add (Peano.Mul.mul p k) 𝟙) ∧
        -- n_p | |G|/p^n
        (∀ H ∈ sylows, ∃ k : ℕ₀, Mul.mul (lengthₚ sylows) k = G.carrier.card) :=
      sorry  -- acción por conjugación + Sylow II + conteo mod p

  end GroupTheory
end Peano
