/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Summation.lean
-- Operador grande sumatorio: sumatorio finito sobre rangos y suma de listas.
--
-- § 1. Sumatorio finito (finSum): Σ_{k=0}^{n} f(k)
-- § 2. Propiedades básicas del sumatorio
-- § 3. Desplazamiento e inversión de índice
-- § 4. Suma de listas (sum_list)

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul


namespace Peano
  open Peano

  namespace Summation
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.Add
    open Peano.Sub
    open Peano.Mul

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Sumatorio finito (finSum): Σ_{k=0}^{n} f(k)
    -- ══════════════════════════════════════════════════════════════════

    /- `finSum f n` = Σ_{k=0}^{n} f(k).
       Computable. Terminado por recursión estructural en n. -/
    def finSum (f : ℕ₀ → ℕ₀) : ℕ₀ → ℕ₀
      | 𝟘   => f 𝟘
      | σ n => add (finSum f n) (f (σ n))

    /- Notación: `∑ k ≤ n, f k` = finSum (fun k => f k) n = Σ_{k=0}^{n} f(k).
       Uso: ∑ k ≤ n', C(n', k)  en lugar de  finSum (fun k => C(n', k)) n'. -/
    macro "∑ " k:ident " ≤ " n:term ", " f:term : term => `(finSum (fun $k => $f) $n)

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. Propiedades básicas del sumatorio
    -- ══════════════════════════════════════════════════════════════════

    theorem finSum_zero (f : ℕ₀ → ℕ₀) : finSum f 𝟘 = f 𝟘 := by rfl

    theorem finSum_succ (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum f (σ n) = add (finSum f n) (f (σ n)) := by rfl

    /- El sumatorio de la función cero es cero. -/
    theorem finSum_zero_fn (n : ℕ₀) : finSum (fun _ => 𝟘) n = 𝟘 := by
      induction n with
      | zero    => rfl
      | succ n' ih => rw [finSum_succ, ih, add_zero]

    /- Linealidad: Σ (f + g) = Σ f + Σ g. -/
    theorem finSum_add_fn (f g : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum (fun k => add (f k) (g k)) n = add (finSum f n) (finSum g n) := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          -- Objetivo tras rw ih: (A+B)+(C+D) = (A+C)+(B+D)  con A=ΣF, B=ΣG, C=f(σn'), D=g(σn')
          rw [finSum_succ, finSum_succ, finSum_succ, ih]
          rw [add_assoc, ← add_assoc (finSum f n'), add_comm (finSum g n'),
              add_assoc (finSum f n'), ← add_assoc]

    /- Factor constante: Σ (c · f) = c · Σ f. -/
    theorem finSum_mul_const (c : ℕ₀) (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum (fun k => mul c (f k)) n = mul c (finSum f n) := by
      induction n with
      | zero    => rfl
      | succ n' ih => rw [finSum_succ, finSum_succ, ih, mul_add]

    /- Distribución a derecha: (Σ f) · c = Σ (f · c). -/
    theorem finSum_mul_const_right (c : ℕ₀) (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        mul (finSum f n) c = finSum (fun k => mul (f k) c) n := by
      induction n with
      | zero    => rfl
      | succ n' ih => rw [finSum_succ, finSum_succ, add_mul, ← ih]

    /- Monotonía: si f ≤ g puntualmente entonces Σ f ≤ Σ g. -/
    theorem finSum_le_of_le (f g : ℕ₀ → ℕ₀) (h : ∀ k, Le (f k) (g k)) (n : ℕ₀) :
        Le (finSum f n) (finSum g n) := by
      induction n with
      | zero    => exact h 𝟘
      | succ n' ih =>
          rw [finSum_succ, finSum_succ]
          exact le_add_compat_wp ih (h (σ n'))

    /- Positividad: si f > 0 puntualmente entonces Σ f > 0. -/
    theorem finSum_pos (f : ℕ₀ → ℕ₀) (h : ∀ k, Lt 𝟘 (f k)) (n : ℕ₀) :
        Lt 𝟘 (finSum f n) := by
      induction n with
      | zero    => exact h 𝟘
      | succ n' ih =>
          rw [finSum_succ]
          exact lt_of_lt_of_le ih (le_self_add_r (finSum f n') (f (σ n')))

    /- La suma de una constante: Σ_{k=0}^{n} c = (n+1)·c. -/
    theorem finSum_const (c n : ℕ₀) :
        finSum (fun _ => c) n = mul (σ n) c := by
      induction n with
      | zero    => rw [finSum_zero]; exact (one_mul c).symm
      | succ n' ih =>
          rw [finSum_succ, ih, ← succ_mul]

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Desplazamiento e inversión de índice
    -- ══════════════════════════════════════════════════════════════════

    /- Desplazamiento a la izquierda:
       Σ_{k=0}^{n+1} f(k) = f(0) + Σ_{k=0}^{n} f(k+1). -/
    theorem finSum_succ_left (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum f (σ n) = add (f 𝟘) (finSum (fun k => f (σ k)) n) := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [finSum_succ, ih, finSum_succ, ← add_assoc]

    /- Invariancia por inversión del índice:
       Σ_{k=0}^{n} f(k) = Σ_{k=0}^{n} f(n-k).
       Esto expresa que el sumatorio no depende del orden de recorrido. -/
    theorem finSum_reverse (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum f n = finSum (fun k => f (sub n k)) n := by
      induction n with
      | zero    => rw [finSum_zero, finSum_zero, sub_self]
      | succ n' ih =>
          rw [finSum_succ, ih,
              finSum_succ_left (fun k => f (sub (σ n') k)),
              sub_zero]
          -- Meta: add (finSum (fun k => f (sub n' k)) n') (f (σ n'))
          --     = add (f (σ n')) (finSum (fun k => f (sub (σ n') (σ k))) n')
          have h_fn : (fun k => f (sub (σ n') (σ k))) = (fun k => f (sub n' k)) := by
            funext k; rw [← sub_succ_succ_eq]
          rw [h_fn, add_comm]

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Suma de listas (sum_list)
    -- ══════════════════════════════════════════════════════════════════

    /- `sum_list l` = Σ de los elementos de la lista l.
       Identidad: 𝟘 (neutro de add). -/
    def sum_list : List ℕ₀ → ℕ₀
      | []       => 𝟘
      | x :: xs => add x (sum_list xs)

    @[simp] theorem sum_list_nil : sum_list [] = 𝟘 := rfl

    @[simp] theorem sum_list_cons (x : ℕ₀) (xs : List ℕ₀) :
        sum_list (x :: xs) = add x (sum_list xs) := rfl

    theorem sum_list_append (l1 l2 : List ℕ₀) :
        sum_list (l1 ++ l2) = add (sum_list l1) (sum_list l2) := by
      induction l1 with
      | nil => simp [zero_add]
      | cons x xs ih => simp [ih, add_assoc]

    theorem sum_list_singleton (x : ℕ₀) :
        sum_list [x] = x := by
      simp [add_zero]

  end Summation
end Peano

export Peano.Summation (
  finSum
  finSum_zero
  finSum_succ
  finSum_zero_fn
  finSum_add_fn
  finSum_mul_const
  finSum_mul_const_right
  finSum_le_of_le
  finSum_pos
  finSum_const
  finSum_succ_left
  finSum_reverse
  sum_list
  sum_list_nil
  sum_list_cons
  sum_list_append
  sum_list_singleton
)
