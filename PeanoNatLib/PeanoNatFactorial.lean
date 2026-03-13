/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- PeanoNatLib/PeanoNatFactorial.lean
-- Factorial de naturales de Peano.
-- Nota: la notación n! no se define aquí porque en Lean 4 el lexer
-- trata `n!` como identificador único. Se usa `factorial n` directamente.

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatMul


namespace Peano
  open Peano

  namespace Factorial
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.Add
    open Peano.Mul

    /- Definición recursiva del factorial. -/
    def factorial : ℕ₀ → ℕ₀
      | 𝟘   => 𝟙
      | σ n => mul (factorial n) (σ n)

    -- ── Valores concretos ──────────────────────────────────────────

    theorem factorial_zero : factorial 𝟘 = 𝟙 := by rfl

    theorem factorial_succ (n : ℕ₀) : factorial (σ n) = mul (factorial n) (σ n) := by rfl

    theorem factorial_one : factorial 𝟙 = 𝟙 := by
      show mul (factorial 𝟘) 𝟙 = 𝟙
      rw [factorial_zero, mul_one]

    theorem factorial_two : factorial 𝟚 = 𝟚 := by
      show mul (factorial 𝟙) 𝟚 = 𝟚
      rw [factorial_one, one_mul]

    -- ── Positividad ────────────────────────────────────────────────

    theorem factorial_pos (n : ℕ₀) : factorial n > 𝟘 := by
      induction n with
      | zero    => rw [factorial_zero]; exact lt_succ_self 𝟘
      | succ n' ih =>
          rw [factorial_succ]
          exact mul_pos ih (lt_0_n (σ n') (succ_neq_zero n'))

    theorem factorial_ne_zero (n : ℕ₀) : factorial n ≠ 𝟘 := by
      intro h
      exact lt_zero 𝟘 (h ▸ factorial_pos n)

    theorem factorial_ge_one (n : ℕ₀) : factorial n ≥ 𝟙 := by
      rcases lt_0n_then_le_1n_wp (factorial_pos n) with h | h
      · exact Or.inl h
      · exact Or.inr h

    -- ── Monotonicidad ──────────────────────────────────────────────

    /- factorial n ≤ factorial (n+1). -/
    theorem factorial_le_succ (n : ℕ₀) : Le (factorial n) (factorial (σ n)) := by
      rw [factorial_succ]
      have h_ge1 : Le 𝟙 (σ n) := by
        rcases lt_0n_then_le_1n_wp (lt_0_n (σ n) (succ_neq_zero n)) with h | h
        · exact Or.inl h
        · exact Or.inr h
      have h := mul_le_mono_right (factorial n) h_ge1
      rwa [one_mul, mul_comm] at h

    /- m ≤ n → factorial m ≤ factorial n. -/
    theorem factorial_le_mono {m n : ℕ₀} (h : Le m n) : Le (factorial m) (factorial n) := by
      induction n with
      | zero    =>
          have hm : m = 𝟘 := by
            rcases (le_iff_lt_or_eq m 𝟘).mp h with h_lt | h_eq
            · exact absurd h_lt (lt_zero m)
            · exact h_eq
          subst hm; exact le_refl (factorial 𝟘)
      | succ n' ih =>
          rcases (le_iff_lt_or_eq m (σ n')).mp h with h_lt | h_eq
          · have h_le : Le m n' := (lt_succ_iff_le m n').mp h_lt
            exact le_trans (factorial m) (factorial n') (factorial (σ n'))
                    (ih h_le) (factorial_le_succ n')
          · subst h_eq; exact le_refl (factorial (σ n'))

  end Factorial
end Peano

export Peano.Factorial (
  factorial
  factorial_zero
  factorial_one
  factorial_two
  factorial_succ
  factorial_pos
  factorial_ne_zero
  factorial_ge_one
  factorial_le_succ
  factorial_le_mono
)
