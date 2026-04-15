/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/NumberTheory/Totient.lean

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Arith
import Peano.PeanoNat.ListsAndSets.List
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.NumberSets
import Peano.PeanoNat.Primes

set_option autoImplicit false

namespace Peano
  open Peano

  namespace Totient
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.WellFounded
    open Peano.Add
    open Peano.Sub
    open Peano.Mul
    open Peano.Div
    open Peano.Arith
    open Peano.List
    open Peano.FSet
    open Peano.NumberSets


    /-!
    ## § 1. Auxiliary list lemmas

    Lemmas about `lengthₚ`, `List.filter`, and `range_from_one`
    needed for the totient function.
    !-/

    /-- Length of concatenated lists. -/
    theorem lengthₚ_append {α : Type} (l₁ l₂ : List α) :
        lengthₚ (l₁ ++ l₂) = add (lengthₚ l₁) (lengthₚ l₂) := by
      induction l₁ with
      | nil => simp [lengthₚ_nil, zero_add]
      | cons x xs ih =>
        simp only [List.cons_append, lengthₚ_cons]
        rw [ih, succ_add]

    /-- Length of a singleton list. -/
    theorem lengthₚ_singleton {α : Type} (x : α) :
        lengthₚ [x] = 𝟙 := by
      simp [lengthₚ_cons, lengthₚ_nil]; rfl

    /-- `lengthₚ (range_from_one n) = n`. -/
    theorem lengthₚ_range_from_one (n : ℕ₀) :
        lengthₚ (range_from_one n) = n := by
      induction n with
      | zero => rfl
      | succ n' ih =>
        simp only [range_from_one]
        rw [lengthₚ_append, lengthₚ_singleton, ih, add_one]

    /-- Filtering does not increase length. -/
    theorem lengthₚ_filter_le {α : Type} (p : α → Bool) (l : List α) :
        le₀ (lengthₚ (List.filter p l)) (lengthₚ l) := by
      induction l with
      | nil => exact le_refl 𝟘
      | cons x xs ih =>
        simp only [List.filter]
        split
        · simp only [lengthₚ_cons]
          exact (succ_le_succ_iff _ _).mpr ih
        · simp only [lengthₚ_cons]
          exact le_trans _ _ _ ih (Or.inl (lt_succ_self _))

    /-- Filtering an append-singleton. -/
    theorem filter_append_singleton {α : Type} (p : α → Bool)
        (l : List α) (x : α) :
        List.filter p (l ++ [x]) =
        if p x then List.filter p l ++ [x] else List.filter p l := by
      induction l with
      | nil =>
        simp [List.filter]
        split <;> simp [*]
      | cons y ys ih =>
        simp only [List.cons_append, List.filter]
        split
        · simp only [ih]; split <;> rfl
        · exact ih

    /-- If all elements satisfy `p`, filter is identity. -/
    theorem filter_all_true {α : Type} (p : α → Bool) (l : List α)
        (h : ∀ x, x ∈ l → p x = true) :
        List.filter p l = l := by
      induction l with
      | nil => rfl
      | cons x xs ih =>
        have hx := h x (List.Mem.head ..)
        simp only [List.filter, hx]
        congr 1
        exact ih (fun y hy => h y (List.Mem.tail x hy))

    /-- Every element of `range_from_one n` is nonzero. -/
    theorem mem_range_from_one_pos {k n : ℕ₀}
        (h : k ∈ range_from_one n) : k ≠ 𝟘 := by
      induction n with
      | zero => simp [range_from_one] at h
      | succ n' ih =>
        simp only [range_from_one, List.mem_append, List.mem_singleton] at h
        rcases h with h_left | h_right
        · exact ih h_left
        · rw [h_right]; exact succ_neq_zero n'

    /-- Every element of `range_from_one n` is `≤ n`. -/
    theorem mem_range_from_one_le {k n : ℕ₀}
        (h : k ∈ range_from_one n) : le₀ k n := by
      induction n with
      | zero => simp [range_from_one] at h
      | succ n' ih =>
        simp only [range_from_one, List.mem_append, List.mem_singleton] at h
        rcases h with h_left | h_right
        · exact le_trans k n' (σ n') (ih h_left) (Or.inl (lt_succ_self n'))
        · rw [h_right]; exact le_refl (σ n')

    /-- `le₀ k n → lt₀ k (σ n)`. -/
    private theorem le_imp_lt_succ {k n : ℕ₀} (h : le₀ k n) :
        lt₀ k (σ n) := by
      rcases h with h_lt | h_eq
      · exact lt_trans_wp h_lt (lt_succ_self n)
      · rw [h_eq]; exact lt_succ_self n


    /-!
    ## § 2. Definition

    `totient n` is Euler's φ function: the number of integers
    in `{1, …, n}` that are coprime with `n`.
    !-/

    /-- Euler's totient function: `φ(n)` = number of `k ∈ {1,…,n}`
        with `gcd(k, n) = 1`. -/
    def totient (n : ℕ₀) : ℕ₀ :=
      lengthₚ ((range_from_one n).filter (fun d => decide (gcd d n = 𝟙)))


    /-!
    ## § 3. Basic values
    !-/

    /-- `φ(0) = 0`. -/
    theorem totient_zero : totient 𝟘 = 𝟘 := by decide

    /-- `φ(1) = 1`. -/
    theorem totient_one : totient 𝟙 = 𝟙 := by native_decide

    /-- `φ(2) = 1`. -/
    theorem totient_two : totient 𝟚 = 𝟙 := by native_decide


    /-!
    ## § 4. Bounds
    !-/

    /-- `φ(n) ≤ n`. -/
    theorem totient_le (n : ℕ₀) : le₀ (totient n) n := by
      unfold totient
      have h1 := lengthₚ_filter_le (fun d => decide (gcd d n = 𝟙)) (range_from_one n)
      rw [lengthₚ_range_from_one] at h1
      exact h1

    /-- `𝟙 ∈ range_from_one n` for `n ≠ 𝟘`. -/
    private theorem one_mem_range_from_one {n : ℕ₀} (h : n ≠ 𝟘) :
        𝟙 ∈ range_from_one n := by
      cases n with
      | zero => exact absurd rfl h
      | succ n' =>
        simp only [range_from_one]
        rw [List.mem_append]
        cases n' with
        | zero => right; exact List.mem_singleton.mpr rfl
        | succ n'' => left; exact one_mem_range_from_one (succ_neq_zero n'')

    /-- If `x ∈ l` and `p x = true`, then `x ∈ filter p l`. -/
    private theorem mem_filter_of_mem {α : Type} (p : α → Bool) {l : List α}
        {x : α} (hm : x ∈ l) (hp : p x = true) : x ∈ List.filter p l := by
      induction l with
      | nil => simp at hm
      | cons y ys ih =>
        simp only [List.filter]
        cases hm with
        | head => rw [hp]; exact List.Mem.head ..
        | tail _ hm' =>
          split
          · exact List.Mem.tail _ (ih hm')
          · exact ih hm'

    /-- A nonempty list has `lengthₚ ≥ 1`. -/
    private theorem lengthₚ_pos_of_mem {α : Type} {l : List α} {x : α}
        (h : x ∈ l) : le₀ 𝟙 (lengthₚ l) := by
      cases l with
      | nil => simp at h
      | cons y ys =>
        simp only [lengthₚ_cons]
        exact (succ_le_succ_iff 𝟘 (lengthₚ ys)).mpr (zero_le (lengthₚ ys))

    /-- `φ(n) ≥ 1` for `n ≥ 1`. -/
    theorem totient_pos {n : ℕ₀} (h : n ≠ 𝟘) : le₀ 𝟙 (totient n) := by
      cases n with
      | zero => exact absurd rfl h
      | succ n' =>
        unfold totient
        apply lengthₚ_pos_of_mem (x := 𝟙)
        apply mem_filter_of_mem
        · exact one_mem_range_from_one (succ_neq_zero n')
        · simp only [decide_eq_true_eq]
          exact gcd_one_left (σ n')

    /-!
    ## § 5. Totient of a prime

    For prime `p`, `φ(p) = p − 1`.
    !-/

    /-- For `k < p` with `k ≠ 0` and `p` prime, `gcd(k, p) = 1`. -/
    private theorem gcd_eq_one_of_lt_prime {k p : ℕ₀}
        (hp : Arith.Prime p) (hk_pos : k ≠ 𝟘) (hk_lt : lt₀ k p) :
        gcd k p = 𝟙 := by
      have h_dvd_or_cop := @Peano.Primes.prime_coprime_or_dvd p k hp
      rcases h_dvd_or_cop with h_dvd | h_cop
      · exact absurd hk_lt (le_not_lt (divides_le h_dvd hk_pos))
      · have h_gcd := (Peano.Primes.gcd_eq_one_iff_coprime p k).mpr h_cop
        rw [gcd_comm] at h_gcd
        exact h_gcd

    /-- `gcd(p, p) ≠ 1` for prime `p`. -/
    private theorem gcd_self_ne_one_of_prime {p : ℕ₀}
        (hp : Arith.Prime p) : gcd p p ≠ 𝟙 := by
      rw [gcd_self]; exact hp.2.1

    /-- `φ(p) = p − 1` for any prime `p`. -/
    theorem totient_prime {p : ℕ₀} (hp : Arith.Prime p) :
        totient p = sub p 𝟙 := by
      cases p with
      | zero => exact absurd rfl (prime_ne_zero hp)
      | succ n' =>
        unfold totient
        simp only [range_from_one]
        rw [filter_append_singleton]
        have h_gcd_self : decide (gcd (σ n') (σ n') = 𝟙) = false := by
          simp only [decide_eq_false_iff_not]
          exact gcd_self_ne_one_of_prime hp
        rw [h_gcd_self, if_neg (Bool.false_ne_true)]
        have h_all : ∀ k, k ∈ range_from_one n' →
            decide (gcd k (σ n') = 𝟙) = true := by
          intro k hk
          simp only [decide_eq_true_eq]
          exact gcd_eq_one_of_lt_prime hp (mem_range_from_one_pos hk)
            (le_imp_lt_succ (mem_range_from_one_le hk))
        rw [filter_all_true _ _ h_all, lengthₚ_range_from_one]
        rw [sub_one]; rfl


    /-!
    ## § 6. Connection with FSet
    !-/

    /-- Decidability instance for `totient`. -/
    instance instDecidableEqTotient (n : ℕ₀) (m : ℕ₀) :
        Decidable (totient n = m) :=
      inferInstanceAs (Decidable (_ = m))


  end Totient
end Peano


-- § Exports
export Peano.Totient (
  lengthₚ_append
  lengthₚ_singleton
  lengthₚ_range_from_one
  lengthₚ_filter_le
  filter_append_singleton
  filter_all_true
  mem_range_from_one_pos
  mem_range_from_one_le
  totient
  totient_zero
  totient_one
  totient_two
  totient_le
  totient_pos
  totient_prime
  instDecidableEqTotient
)
