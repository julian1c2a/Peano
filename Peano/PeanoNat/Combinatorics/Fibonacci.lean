/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Fibonacci.lean
-- Sucesión de Fibonacci con cálculo iterativo (sin doble recursión).
--
-- § 1. Lista de Fibonacci (fibList) y definición de fib
-- § 2. Propiedades básicas de fib

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.Add


namespace Peano
  open Peano

  namespace Fibonacci
    open Peano.Axioms
    open Peano.Add

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Lista de Fibonacci (fibList) y definición de fib
    -- ══════════════════════════════════════════════════════════════════

    /-- `fibPair n` devuelve `(fib n, fib (n+1))` calculado iterativamente.
        Evita la doble recursión del cómputo ingenuo. -/
    def fibPair : ℕ₀ → ℕ₀ × ℕ₀
      | .zero   => (𝟘, 𝟙)
      | .succ n => let (a, b) := fibPair n; (b, add a b)

    /-- `fib n` = n-ésimo número de Fibonacci.
        fib 0 = 0, fib 1 = 1, fib (n+2) = fib (n+1) + fib n.
        Calculado en tiempo lineal vía `fibPair`. -/
    def fib (n : ℕ₀) : ℕ₀ := (fibPair n).1

    /-- `fibList n` = [fib 0, fib 1, …, fib n].
        Construida iterativamente aprovechando `fibPair`. -/
    def fibList : ℕ₀ → List ℕ₀
      | .zero   => [𝟘]
      | .succ n => fibList n ++ [fib (σ n)]

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. Propiedades básicas de fib
    -- ══════════════════════════════════════════════════════════════════

    theorem fib_zero : fib 𝟘 = 𝟘 := rfl

    theorem fib_one : fib 𝟙 = 𝟙 := rfl

    theorem fib_succ_succ (n : ℕ₀) :
        fib (σ (σ n)) = add (fib n) (fib (σ n)) := by
      show (fibPair (σ (σ n))).1 = add (fibPair n).1 (fibPair (σ n)).1
      simp only [fibPair]

    theorem fib_two : fib 𝟚 = 𝟙 := rfl

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Propiedades de fibList
    -- ══════════════════════════════════════════════════════════════════

    theorem fibList_zero : fibList 𝟘 = [𝟘] := rfl

    theorem fibList_succ (n : ℕ₀) :
        fibList (σ n) = fibList n ++ [fib (σ n)] := rfl

  end Fibonacci
end Peano

export Peano.Fibonacci (
  fibPair
  fib
  fibList
  fib_zero
  fib_one
  fib_succ_succ
  fib_two
  fibList_zero
  fibList_succ
)
