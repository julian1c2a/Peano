/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Pairing.lean
-- Función de emparejamiento de Cantor y su inversa.
--
-- § 1. Helpers privados
-- § 2. Número triangular (tri)
-- § 3. Emparejamiento de Cantor (cantorPair)
-- § 4. Inversa auxiliar (pairAux) e inversa (cantorUnpair)
-- § 5. Propiedades básicas
-- § 6. Especificación de pairAux
-- § 7. Round-trip
-- § 8. Exports

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub

set_option autoImplicit false

namespace Peano
  open Peano

  namespace Pairing
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.WellFounded
    open Peano.Add
    open Peano.Sub

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Helpers privados
    -- ══════════════════════════════════════════════════════════════════

    private theorem one_le_of_ne_zero {n : ℕ₀} (h : n ≠ 𝟘) : Le 𝟙 n := by
      cases n with
      | zero => exact absurd rfl h
      | succ n' =>
        cases n' with
        | zero => exact Or.inr rfl
        | succ _ => exact Or.inl (by unfold Lt; trivial)

    private theorem succ_sub_one {n : ℕ₀} (h : n ≠ 𝟘) : σ (sub n 𝟙) = n := by
      have h_le : Le 𝟙 n := one_le_of_ne_zero h
      have h_eq := sub_k_add_k n 𝟙 h_le
      rw [add_one] at h_eq
      exact h_eq

    private theorem sub_succ_one (x : ℕ₀) : sub (σ x) 𝟙 = x := by
      rw [← one_add x, add_k_sub_k]

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. Número triangular
    -- ══════════════════════════════════════════════════════════════════

    /-- Número triangular: `tri n = 0 + 1 + 2 + … + n = n(n+1)/2`. -/
    def tri : ℕ₀ → ℕ₀
      | 𝟘 => 𝟘
      | σ n => add (tri n) (σ n)

    @[simp] theorem tri_zero : tri 𝟘 = 𝟘 := rfl

    @[simp] theorem tri_succ (n : ℕ₀) :
        tri (σ n) = add (tri n) (σ n) := rfl

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Emparejamiento de Cantor
    -- ══════════════════════════════════════════════════════════════════

    /-- Función de emparejamiento de Cantor.
        `cantorPair a b = tri(a + b) + a`. -/
    def cantorPair (a b : ℕ₀) : ℕ₀ :=
      add (tri (add a b)) a

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Inversa auxiliar e inversa
    -- ══════════════════════════════════════════════════════════════════

    /-- Auxiliar para la inversa de Cantor.
        Devuelve `(w, r)` donde `n = tri w + r` y `r ≤ w`.
        Estructura idéntica a `sqrtMod`: cuenta el nivel diagonal. -/
    def pairAux (n : ℕ₀) : ℕ₀ × ℕ₀ :=
      if h_n : n = 𝟘 then (𝟘, 𝟘)
      else
        have _h_term : Lt (sub n 𝟙) n :=
          sub_lt_self n 𝟙 (one_le_of_ne_zero h_n) (succ_neq_zero 𝟘)
        let p := pairAux (sub n 𝟙)
        if p.2 = p.1 then (σ p.1, 𝟘)
        else (p.1, σ p.2)
    termination_by n
    decreasing_by exact _h_term

    /-- Inversa de la función de emparejamiento de Cantor.
        Si `pairAux n = (w, a)`, entonces `cantorUnpair n = (a, w − a)`. -/
    def cantorUnpair (n : ℕ₀) : ℕ₀ × ℕ₀ :=
      let p := pairAux n
      (p.2, sub p.1 p.2)

    -- ══════════════════════════════════════════════════════════════════
    -- § 5. Propiedades básicas
    -- ══════════════════════════════════════════════════════════════════

    @[simp] theorem cantorPair_zero_zero :
        cantorPair 𝟘 𝟘 = 𝟘 := by
      unfold cantorPair
      rw [add_zero, add_zero, tri_zero]

    @[simp] theorem cantorUnpair_zero :
        cantorUnpair 𝟘 = (𝟘, 𝟘) := by
      unfold cantorUnpair
      have hp : pairAux 𝟘 = (𝟘, 𝟘) := by unfold pairAux; rw [dif_pos rfl]
      simp [hp, sub_self]

    -- ══════════════════════════════════════════════════════════════════
    -- § 6. Especificación de pairAux
    -- ══════════════════════════════════════════════════════════════════

    /-- Especificación: `n = tri w + r` donde `(w, r) = pairAux n`. -/
    theorem pairAux_spec (n : ℕ₀) :
        n = add (tri (pairAux n).1) (pairAux n).2 := by
      induction n using well_founded_lt.induction with
      | h n ih =>
        unfold pairAux
        if h_n : n = 𝟘 then
          rw [dif_pos h_n]
          simp only []
          rw [h_n, tri_zero, add_zero]
        else
          rw [dif_neg h_n]
          simp only
          have h_term : Lt (sub n 𝟙) n :=
            sub_lt_self n 𝟙 (one_le_of_ne_zero h_n) (succ_neq_zero 𝟘)
          have h_ih := ih (sub n 𝟙) h_term
          if h_eq : (pairAux (sub n 𝟙)).2 = (pairAux (sub n 𝟙)).1 then
            rw [if_pos h_eq]
            simp only []
            rw [add_zero, tri_succ, add_succ]
            rw [h_eq] at h_ih
            rw [← h_ih]
            exact (succ_sub_one h_n).symm
          else
            rw [if_neg h_eq]
            simp only []
            rw [add_succ, ← h_ih]
            exact (succ_sub_one h_n).symm

    /-- Cota: la posición `r` no supera al índice diagonal `w`. -/
    theorem pairAux_bound (n : ℕ₀) :
        Le (pairAux n).2 (pairAux n).1 := by
      induction n using well_founded_lt.induction with
      | h n ih =>
        unfold pairAux
        if h_n : n = 𝟘 then
          rw [dif_pos h_n]
          simp only []
          exact le_refl 𝟘
        else
          rw [dif_neg h_n]
          simp only
          have h_term : Lt (sub n 𝟙) n :=
            sub_lt_self n 𝟙 (one_le_of_ne_zero h_n) (succ_neq_zero 𝟘)
          have h_ih := ih (sub n 𝟙) h_term
          if h_eq : (pairAux (sub n 𝟙)).2 = (pairAux (sub n 𝟙)).1 then
            rw [if_pos h_eq]
            simp only []
            exact zero_le (σ (pairAux (sub n 𝟙)).1)
          else
            rw [if_neg h_eq]
            simp only []
            have h_lt : Lt (pairAux (sub n 𝟙)).2 (pairAux (sub n 𝟙)).1 :=
              lt_of_le_of_ne _ _ h_ih h_eq
            exact (le_iff_lt_succ _ _).mpr
              ((succ_lt_succ_iff _ _).mpr h_lt)

    -- ══════════════════════════════════════════════════════════════════
    -- § 7. Round-trip
    -- ══════════════════════════════════════════════════════════════════

    /-- Round-trip derecho: `cantorPair (cantorUnpair n).1 (cantorUnpair n).2 = n`. -/
    theorem cantorPair_cantorUnpair (n : ℕ₀) :
        cantorPair (cantorUnpair n).1 (cantorUnpair n).2 = n := by
      unfold cantorUnpair cantorPair
      simp only []
      have h_le := pairAux_bound n
      have h_add : add (pairAux n).2 (sub (pairAux n).1 (pairAux n).2) = (pairAux n).1 := by
        rw [add_comm]
        exact sub_k_add_k (pairAux n).1 (pairAux n).2 h_le
      rw [h_add]
      exact (pairAux_spec n).symm

    /-- Lema clave: `pairAux` descompone correctamente `tri w + a` cuando `a ≤ w`. -/
    private theorem pairAux_of_tri_add (w : ℕ₀) :
        ∀ (a : ℕ₀), Le a w → pairAux (add (tri w) a) = (w, a) := by
      induction w with
      | zero =>
        intro a h_le
        have h_a0 : a = 𝟘 := le_antisymm a 𝟘 h_le (zero_le a)
        subst h_a0
        rw [tri_zero, add_zero]
        unfold pairAux; rw [dif_pos rfl]
      | succ w' ih_w =>
        intro a
        induction a with
        | zero =>
          intro _h_le
          rw [add_zero, tri_succ, add_succ]
          rw [pairAux.eq_def, dif_neg (succ_neq_zero _)]
          simp only []
          rw [sub_succ_one (add (tri w') w')]
          rw [ih_w w' (le_refl w')]
          simp only [ite_true]
        | succ a' ih_a =>
          intro h_le
          rw [add_succ]
          rw [pairAux.eq_def, dif_neg (succ_neq_zero _)]
          simp only []
          rw [sub_succ_one (add (tri (σ w')) a')]
          have h_le_a' : Le a' (σ w') :=
            le_trans a' (σ a') (σ w') (le_succ_self a') h_le
          rw [ih_a h_le_a']
          simp only []
          have h_a'_ne : a' ≠ σ w' := by
            intro heq; subst heq
            have h_bad := (succ_le_succ_iff (σ w') w').mp h_le
            exact absurd (lt_succ_self w') (nlt_of_le h_bad)
          rw [if_neg h_a'_ne]

    /-- Round-trip izquierdo: `cantorUnpair (cantorPair a b) = (a, b)`. -/
    theorem cantorUnpair_cantorPair (a b : ℕ₀) :
        cantorUnpair (cantorPair a b) = (a, b) := by
      unfold cantorUnpair cantorPair
      simp only []
      have h_le : Le a (add a b) := le_self_add a b
      rw [pairAux_of_tri_add (add a b) a h_le]
      simp only []
      congr 1
      exact add_k_sub_k b a

    /-- Inyectividad de `cantorPair`. -/
    theorem cantorPair_injective (a₁ b₁ a₂ b₂ : ℕ₀)
        (h : cantorPair a₁ b₁ = cantorPair a₂ b₂) :
        a₁ = a₂ ∧ b₁ = b₂ := by
      have h1 := cantorUnpair_cantorPair a₁ b₁
      have h2 := cantorUnpair_cantorPair a₂ b₂
      rw [h] at h1
      have h3 := h1.symm.trans h2
      exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩

  end Pairing

end Peano

export Peano.Pairing (
  tri
  cantorPair
  pairAux
  cantorUnpair
  tri_zero
  tri_succ
  cantorPair_zero_zero
  cantorUnpair_zero
  pairAux_spec
  pairAux_bound
  cantorPair_cantorUnpair
  cantorUnpair_cantorPair
  cantorPair_injective
)
