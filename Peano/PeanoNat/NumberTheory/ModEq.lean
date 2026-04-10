/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/NumberTheory/ModEq.lean

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
import Peano.PeanoNat.Combinatorics.Pow

set_option autoImplicit false

namespace Peano
  open Peano

  namespace ModEq
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.WellFounded
    open Peano.Add
    open Peano.Sub
    open Peano.Mul
    open Peano.Div
    open Peano.Arith
    open Peano.Pow


    /-!
    ## § 1. Auxiliary mod lemmas

    Lemmas about `mod` that are not in `Div.lean` but needed for modular equivalence.
    These are proved via the Ψ/Λ isomorphism with `Nat`.
    !-/

    /-- `mod a 𝟘 = 𝟘` (by definition of `divMod`). -/
    theorem mod_zero_right (a : ℕ₀) : mod a 𝟘 = 𝟘 := by
      unfold mod divMod
      rw [dif_pos rfl]

    /-- `mod 𝟘 n = 𝟘`. -/
    theorem mod_zero_left (n : ℕ₀) : mod 𝟘 n = 𝟘 := by
      unfold mod divMod
      if h : n = 𝟘 then
        rw [dif_pos h]
      else
        rw [dif_neg h, dif_pos rfl]

    /-- `mod n n = 𝟘`. -/
    theorem mod_self (n : ℕ₀) : mod n n = 𝟘 := by
      if h : n = 𝟘 then
        rw [h]; exact mod_zero_left 𝟘
      else
        have h_ψ := isomorph_Ψ_mod n n h
        have h_zero : Ψ (mod n n) = 0 := h_ψ.trans (Nat.mod_self (Ψ n))
        exact (Ψ_eq_zero_iff_eq_zero _).mp h_zero

    /-- `mod (mod a n) n = mod a n` (idempotency). -/
    theorem mod_mod (a n : ℕ₀) : mod (mod a n) n = mod a n := by
      if h : n = 𝟘 then
        rw [h, mod_zero_right, mod_zero_right]
      else
        exact mod_of_lt (mod a n) n (mod_lt a n h)

    /-- Transfer lemma: lift `Nat.add_mod` to ℕ₀. -/
    private theorem add_mod_aux (a b n : ℕ₀) (h_n : n ≠ 𝟘) :
        mod (add a b) n = mod (add (mod a n) (mod b n)) n := by
      have h1 := isomorph_Ψ_mod (add a b) n h_n
      have h2 := isomorph_Ψ_mod (add (mod a n) (mod b n)) n h_n
      rw [isomorph_Ψ_add] at h1 h2
      rw [isomorph_Ψ_mod a n h_n, isomorph_Ψ_mod b n h_n] at h2
      have h_nat := Nat.add_mod (Ψ a) (Ψ b) (Ψ n)
      have h_eq : Ψ (mod (add a b) n) = Ψ (mod (add (mod a n) (mod b n)) n) := by
        rw [h1, h2]; exact h_nat
      exact Ψ_inj _ _ h_eq

    /-- `mod (add a b) n = mod (add (mod a n) (mod b n)) n`. -/
    theorem add_mod (a b n : ℕ₀) :
        mod (add a b) n = mod (add (mod a n) (mod b n)) n := by
      if h : n = 𝟘 then
        subst h; simp only [mod_zero_right]
      else
        exact add_mod_aux a b n h

    /-- Transfer lemma: lift `Nat.mul_mod` to ℕ₀. -/
    private theorem mul_mod_aux (a b n : ℕ₀) (h_n : n ≠ 𝟘) :
        mod (mul a b) n = mod (mul (mod a n) (mod b n)) n := by
      have h1 := isomorph_Ψ_mod (mul a b) n h_n
      have h2 := isomorph_Ψ_mod (mul (mod a n) (mod b n)) n h_n
      rw [isomorph_Ψ_mul] at h1 h2
      rw [isomorph_Ψ_mod a n h_n, isomorph_Ψ_mod b n h_n] at h2
      have h_nat := Nat.mul_mod (Ψ a) (Ψ b) (Ψ n)
      have h_eq : Ψ (mod (mul a b) n) = Ψ (mod (mul (mod a n) (mod b n)) n) := by
        rw [h1, h2]; exact h_nat
      exact Ψ_inj _ _ h_eq

    /-- `mod (mul a b) n = mod (mul (mod a n) (mod b n)) n`. -/
    theorem mul_mod (a b n : ℕ₀) :
        mod (mul a b) n = mod (mul (mod a n) (mod b n)) n := by
      if h : n = 𝟘 then
        subst h; simp only [mod_zero_right]
      else
        exact mul_mod_aux a b n h


    /-!
    ## § 2. Definition

    `ModEq n a b` means `a ≡ b (mod n)`, i.e. `mod a n = mod b n`.
    !-/

    /-- Modular equivalence: `a ≡ b [MOD n]` iff `mod a n = mod b n`. -/
    def ModEq (n a b : ℕ₀) : Prop := mod a n = mod b n

    notation:50 a " ≡ " b " [MOD " n "]" => ModEq n a b


    /-!
    ## § 3. Equivalence relation
    !-/

    theorem modEq_refl (n a : ℕ₀) : a ≡ a [MOD n] := rfl

    theorem modEq_symm {n a b : ℕ₀} (h : a ≡ b [MOD n]) : b ≡ a [MOD n] :=
      h.symm

    theorem modEq_trans {n a b c : ℕ₀} (h1 : a ≡ b [MOD n]) (h2 : b ≡ c [MOD n]) :
        a ≡ c [MOD n] :=
      h1.trans h2


    /-!
    ## § 4. Compatibility with operations
    !-/

    /-- `a ≡ b → c ≡ d → a + c ≡ b + d [MOD n]`. -/
    theorem modEq_add {n a b c d : ℕ₀}
        (h1 : a ≡ b [MOD n]) (h2 : c ≡ d [MOD n]) :
        add a c ≡ add b d [MOD n] := by
      unfold ModEq at *
      rw [add_mod a c n, add_mod b d n, h1, h2]

    /-- `a ≡ b → c ≡ d → a * c ≡ b * d [MOD n]`. -/
    theorem modEq_mul {n a b c d : ℕ₀}
        (h1 : a ≡ b [MOD n]) (h2 : c ≡ d [MOD n]) :
        mul a c ≡ mul b d [MOD n] := by
      unfold ModEq at *
      rw [mul_mod a c n, mul_mod b d n, h1, h2]

    /-- `a ≡ b → a ^ k ≡ b ^ k [MOD n]`. -/
    theorem modEq_pow {n a b : ℕ₀} (k : ℕ₀)
        (h : a ≡ b [MOD n]) :
        pow a k ≡ pow b k [MOD n] := by
      induction k with
      | zero =>
        rw [pow_zero, pow_zero]
        exact modEq_refl n 𝟙
      | succ k' ih =>
        rw [pow_succ, pow_succ]
        exact modEq_mul ih h


    /-!
    ## § 5. Connection with divisibility
    !-/

    /-- `mod a n = 𝟘 ↔ n ∣ a` (when `n ≠ 𝟘`). -/
    theorem mod_eq_zero_iff_dvd {a n : ℕ₀} (h_n : n ≠ 𝟘) :
        mod a n = 𝟘 ↔ n ∣ a := by
      constructor
      · intro h_mod
        have h_spec := divMod_spec a n h_n
        have h_mod' : (divMod a n).2 = 𝟘 := h_mod
        rw [h_mod', add_zero] at h_spec
        exact ⟨(divMod a n).1, h_spec.trans (mul_comm _ _)⟩
      · intro ⟨k, hk⟩
        rw [hk]
        have h_ψ := isomorph_Ψ_mod (mul n k) n h_n
        rw [isomorph_Ψ_mul] at h_ψ
        have h_zero : Ψ (mod (mul n k) n) = 0 := by
          rw [h_ψ]; exact Nat.mul_mod_right (Ψ n) (Ψ k)
        exact (Ψ_eq_zero_iff_eq_zero _).mp h_zero

    /-- `a ≡ 𝟘 [MOD n] ↔ n ∣ a` (when `n ≠ 𝟘`). -/
    theorem modEq_zero_iff_dvd {a n : ℕ₀} (h_n : n ≠ 𝟘) :
        a ≡ 𝟘 [MOD n] ↔ n ∣ a := by
      unfold ModEq
      rw [mod_zero_left]
      exact mod_eq_zero_iff_dvd h_n

    /-- `n ∣ a → a ≡ 𝟘 [MOD n]`. -/
    theorem modEq_zero_of_dvd {a n : ℕ₀} (h_n : n ≠ 𝟘) (h : n ∣ a) :
        a ≡ 𝟘 [MOD n] :=
      (modEq_zero_iff_dvd h_n).mpr h


    /-!
    ## § 6. Additional properties
    !-/

    /-- `a ≡ mod a n [MOD n]`. -/
    theorem modEq_mod (a n : ℕ₀) : a ≡ mod a n [MOD n] := by
      unfold ModEq
      rw [mod_mod]

    /-- `a ≡ b [MOD 𝟙]` for all `a`, `b` (everything is congruent mod 1). -/
    theorem modEq_one (a b : ℕ₀) : a ≡ b [MOD 𝟙] := by
      unfold ModEq
      have h1 : (𝟙 : ℕ₀) ≠ 𝟘 := succ_neq_zero 𝟘
      have ha := mod_lt a 𝟙 h1
      have hb := mod_lt b 𝟙 h1
      have ha0 : mod a 𝟙 = 𝟘 := lt_b_1_then_b_eq_0 ha
      have hb0 : mod b 𝟙 = 𝟘 := lt_b_1_then_b_eq_0 hb
      rw [ha0, hb0]

    /-- `a ≡ a + n [MOD n]` (shifting by a multiple). -/
    theorem modEq_add_right (a n : ℕ₀) : a ≡ add a n [MOD n] := by
      if h : n = 𝟘 then
        rw [h, add_zero]
        exact modEq_refl 𝟘 a
      else
        unfold ModEq
        rw [add_mod a n n, mod_self, add_zero, mod_mod]

    /-- Decidability of `ModEq`. -/
    instance instDecidableModEq (n a b : ℕ₀) : Decidable (ModEq n a b) :=
      inferInstanceAs (Decidable (mod a n = mod b n))


  end ModEq
end Peano


-- § Exports
export Peano.ModEq (
  mod_zero_right
  mod_zero_left
  mod_self
  mod_mod
  add_mod
  mul_mod
  ModEq
  modEq_refl
  modEq_symm
  modEq_trans
  modEq_add
  modEq_mul
  modEq_pow
  mod_eq_zero_iff_dvd
  modEq_zero_iff_dvd
  modEq_zero_of_dvd
  modEq_mod
  modEq_one
  modEq_add_right
  instDecidableModEq
)
