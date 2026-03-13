/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- PeanoNatLib/PeanoNatBinom.lean
-- Coeficientes binomiales vía el triángulo de Pascal.
-- Preparación para el Teorema del Binomio de Newton.

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatFactorial


namespace Peano
  open Peano

  namespace Binom
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.Add
    open Peano.Mul
    open Peano.Factorial
    open Peano.Sub

    /- Coeficiente binomial C(n, k) por la recursión de Pascal.
       Termina por inducción estructural en el primer argumento n. -/
    def binom : ℕ₀ → ℕ₀ → ℕ₀
      | 𝟘,   𝟘   => 𝟙
      | 𝟘,   σ _ => 𝟘
      | σ _, 𝟘   => 𝟙
      | σ n, σ k => add (binom n k) (binom n (σ k))

    /- Notación C(n, k). -/
    notation "C(" n ", " k ")" => binom n k

    -- ── Valores base ──────────────────────────────────────────────────────────────

    theorem binom_zero_zero : C(𝟘, 𝟘) = 𝟙 := by rfl

    theorem binom_zero_succ (k : ℕ₀) : C(𝟘, σ k) = 𝟘 := by rfl

    theorem binom_succ_zero (n : ℕ₀) : C(σ n, 𝟘) = 𝟙 := by rfl

    /- Identidad de Pascal: C(n+1, k+1) = C(n, k) + C(n, k+1). -/
    theorem binom_pascal (n k : ℕ₀) :
        C(σ n, σ k) = add C(n, k) C(n, σ k) := by rfl

    theorem binom_n_zero (n : ℕ₀) : C(n, 𝟘) = 𝟙 := by
      cases n <;> rfl

    theorem binom_n_one (n : ℕ₀) : C(n, 𝟙) = n := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
        calc C(σ n', 𝟙)
            = add C(n', 𝟘) C(n', 𝟙)  := by rfl
          _ = add C(n', 𝟘) n'        := by rw [ih]
          _ = add 𝟙 n'               := by rw [binom_n_zero]
          _ = σ n'                    := by rw [add_comm, add_one]

    theorem binom_eq_zero_of_gt {n k : ℕ₀} (h : Lt n k) : C(n, k) = 𝟘 := by
      induction n generalizing k with
      | zero    =>
          cases k with
          | zero    => exact absurd h (lt_zero 𝟘)
          | succ k' => rfl
      | succ n' ih =>
          cases k with
          | zero    => exact absurd h (lt_zero (σ n'))
          | succ k' =>
              rw [binom_pascal]
              have h' : Lt n' k' := (succ_lt_succ_iff n' k').mp h
              have h'' : Lt n' (σ k') := lt_trans n' k' (σ k') h' (lt_succ_self k')
              rw [ih h', ih h'', add_zero]

    theorem binom_self (n : ℕ₀) : C(n, n) = 𝟙 := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [binom_pascal, ih, binom_eq_zero_of_gt (lt_succ_self n'), add_zero]

    theorem binom_self_self (n : ℕ₀) :
      C(n, n) = 𝟙
      := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
        calc C(σ n', σ n')
            = add C(n', n') C(n', σ n')  := by rfl
          _ = add 𝟙 C(n', σ n')          := by rw [ih]
          _ = add 𝟙 𝟘                    := by rw [binom_eq_zero_of_gt (lt_succ_self n')]
          _ = 𝟙                          := by rw [add_zero]
    -- ── Lema auxiliar: a ≤ a + b ──────────────────────────────────────────────────

    private theorem le_add_right (a b : ℕ₀) : Le a (add a b) := by
      induction b with
      | zero    => exact le_refl a
      | succ b' ih =>
          exact le_trans a (add a b') (σ (add a b')) ih
                  (lt_imp_le_wp (lt_succ_self (add a b')))

    -- ── C(n, k) > 0 cuando k ≤ n ──────────────────────────────────────────────────

    theorem binom_pos {n k : ℕ₀} (h : Le k n) : C(n, k) > 𝟘 := by
      induction n generalizing k with
      | zero    =>
          have hk : k = 𝟘 := by
            rcases (le_iff_lt_or_eq k 𝟘).mp h with h_lt | h_eq
            · exact absurd h_lt (lt_zero k)
            · exact h_eq
          subst hk; rw [binom_zero_zero]; exact lt_succ_self 𝟘
      | succ n' ih =>
          cases k with
          | zero    => rw [binom_succ_zero]; exact lt_succ_self 𝟘
          | succ k' =>
              rw [binom_pascal]
              have h_le : Le k' n' := by
                rcases (le_iff_lt_or_eq (σ k') (σ n')).mp h with h_lt | h_eq
                · exact lt_imp_le_wp ((succ_lt_succ_iff k' n').mp h_lt)
                · exact Or.inr (succ_inj k' n' h_eq)
              exact lt_of_lt_of_le (ih h_le)
                      (le_add_right C(n', k') C(n', σ k'))

    -- ── C(n, 1) = n (para n ≥ 1) ─────────────────────────────────────────────────────

    theorem binom_one (n : ℕ₀) : C(σ n, 𝟙) = σ n := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [show (𝟙 : ℕ₀) = σ 𝟘 from rfl, binom_pascal, binom_n_zero]
          rw [show (𝟙 : ℕ₀) = σ 𝟘 from rfl] at ih
          rw [ih, add_comm, add_one]

    theorem binom_succ_n_by_n (n : ℕ₀) : C(σ n, n) = σ n := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [binom_pascal (σ n') n', ih, binom_self (σ n'), add_one]

    -- ── Relación entre C(n, k) y factoriales ─────────────────────────────────────────────────

    /- Lema auxiliar de conmutación de factores: (a·b)·c = (a·c)·b. -/
    private theorem mul_swap_last (a b c : ℕ₀) : mul (mul a b) c = mul (mul a c) b := by
      rw [mul_assoc b a c, mul_comm b c, ← mul_assoc c a b]

    private theorem sub_eq_succ_of_lt {n k : ℕ₀} (h_lt : Lt k n) :
        sub n k = σ (sub n (σ k)) := by
      have h_sk_le_n : Le (σ k) n :=
        (lt_succ_iff_le (σ k) n).mp ((succ_lt_succ_iff k n).mpr h_lt)
      have h_sub_ne0 : sub n k ≠ 𝟘 := lt_b_a_then_sub_a_b_neq_0 n k h_lt
      have h_eq : sub n (σ k) = τ (sub n k) := succ_sub n k h_sk_le_n
      have h_eq2 : σ (sub n (σ k)) = sub n k := by
        rw [h_eq, tau_eq_rho_if_ne_zero _ h_sub_ne0, σ_ρ_eq_self]
      exact h_eq2.symm

    private theorem factorial_sub_succ {n k : ℕ₀} (h_lt : Lt k n) :
        factorial (sub n k) = mul (factorial (sub n (σ k))) (sub n k) := by
      have h_eq := sub_eq_succ_of_lt h_lt; rw [h_eq, factorial_succ, ← h_eq]

    private theorem add_succ_sub_self {n k : ℕ₀} (h_le : Le k n) :
        add (σ k) (sub n k) = σ n := by
      rw [succ_add, add_comm, sub_k_add_k n k h_le]

    /- Teorema principal: C(n, k) · k! · (n - k)! = n! para k ≤ n. -/
    theorem binom_mul_factorials {n k : ℕ₀} (h : Le k n) :
        mul (mul C(n, k) (factorial k)) (factorial (sub n k)) = factorial n := by
      induction n generalizing k with
      | zero =>
          have hk : k = 𝟘 := le_zero_eq k h
          subst hk
          rw [binom_zero_zero, sub_self, factorial_zero, mul_one, one_mul]
      | succ n' ih =>
          cases k with
          | zero =>
              rw [binom_succ_zero, sub_zero, factorial_zero, one_mul, one_mul]
          | succ k' =>
              have h_k'_le_n' : Le k' n' := (succ_le_succ_iff k' n').mp h
              rcases (le_iff_lt_or_eq k' n').mp h_k'_le_n' with h_lt | h_eq
              · -- Caso k' < n'
                have h_le_k' : Le k' n' := lt_imp_le_wp h_lt
                have h_le_sk' : Le (σ k') n' := (lt_succ_iff_le _ _).mp ((succ_lt_succ_iff _ _).mpr h_lt)
                rw [binom_pascal, mul_rdistr, sub_succ_succ_eq]
                have term1_rw : mul (mul (C(n', k')) (factorial (σ k'))) (factorial (sub n' k')) = mul (factorial n') (σ k') := by
                  rw [factorial_succ k', mul_assoc, mul_comm (factorial k'), ←mul_assoc, ←mul_assoc, ih h_le_k']
                have term2_rw : mul (mul (C( n' , (σ k'))) (factorial (σ k'))) (factorial (sub n' k')) = mul (factorial n') (sub n' k') := by
                  have h_fact : factorial (sub n' k') = mul (factorial (sub n' (σ k'))) (sub n' k') := factorial_sub_succ h_lt
                  rw [h_fact, ←mul_assoc, mul_comm (sub n' k'), ←mul_assoc]
                  rw [ih h_le_sk']
                rw [term1_rw, term2_rw, ←mul_ldistr, add_succ_sub_self h_le_k', factorial_succ]
              · -- Caso k' = n'
                subst h_eq
                rw [binom_self (σ k'), one_mul, sub_self, factorial_zero, mul_one]

  end Binom
end Peano

export Peano.Binom (
  binom
  binom_zero_zero
  binom_zero_succ
  binom_succ_zero
  binom_pascal
  binom_n_zero
  binom_n_one
  binom_eq_zero_of_gt
  binom_self
  binom_pos
  binom_one
  binom_succ_n_by_n
  binom_mul_factorials
)
