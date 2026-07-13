/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Peano.PeanoNat.Arith
import Peano.PeanoNat.ListsAndSets.FSet

-- Peano/PeanoNat/NumberSets.lean
-- Conjuntos numéricos notables: primos, divisores, coprimos, múltiplos.
-- Combina los predicados de Arith con la infraestructura de FSet.
--
-- § 1. Predicados (conjuntos como proposiciones)
-- § 2. Tests booleanos decidibles
-- § 3. Conjuntos finitos (ℕ₀FSet)

namespace Peano
  open Peano
  open Peano.Axioms
  open Peano.StrictOrder
  open Peano.Order
  open Peano.Arith
  open Peano.List
  open Peano.FSet

  namespace NumberSets

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Predicados (conjuntos como proposiciones)
    -- ══════════════════════════════════════════════════════════════════

    /-- Un natural ≥ 2 es primo si su valor subyacente satisface `Prime`. -/
    def IsPrime (p : ℕ₂) : Prop := Prime p.val.val

    /-- Conjunto (predicado) de naturales coprimos con `n`.
        `CoprimesOf n m` ↔ `gcd(n, m) = 1`. -/
    def CoprimesOf (n : ℕ₂) : ℕ₀ → Prop :=
      fun m => Coprime n.val.val m

    /-- Conjunto (predicado) de divisores de `n`.
        Alias de `Divisors` definido en Arith. -/
    abbrev DivisorsOf (n : ℕ₀) := Divisors n

    /-- Conjunto (predicado) de múltiplos de `n`.
        Alias de `Multiples` definido en Arith. -/
    abbrev MultiplesOf (n : ℕ₀) := Multiples n

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. Tests booleanos decidibles
    -- ══════════════════════════════════════════════════════════════════

    /-- Test booleano de primalidad: `n > 1` y sus únicos divisores
        en `{1, …, n}` son exactamente dos (`1` y `n`). -/
    def isPrimeb (n : ℕ₀) : Bool :=
      blt₀ 𝟙 n &&
      ((range_from_one n).filter (fun d => dividesb d n)).length == 2

    /-- Test booleano de coprimalidad: `gcd(a, b) = 1`. -/
    def coprimeb (a b : ℕ₀) : Bool := gcd a b == 𝟙

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Conjuntos finitos (ℕ₀FSet)
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de divisores de `n` (como ℕ₀FSet).
        Usa `factorsOf` que enumera los divisores en `{1, …, n}`. -/
    def divisorsFSet (n : ℕ₁) : ℕ₀FSet :=
      ℕ₀FSet.ofList (factorsOf n)

    /-- Conjunto finito de primos menores o iguales que `n`.
        Filtra `{1, …, n}` con `isPrimeb`. -/
    def primesFSet (n : ℕ₀) : ℕ₀FSet :=
      ℕ₀FSet.ofList ((range_from_one n).filter (fun p => isPrimeb p))

    /-- Conjunto finito de coprimos de `n` en `{1, …, n}`.
        Nota: `n` queda excluido automáticamente (gcd(n,n) = n ≠ 1
        para `n ≥ 2`). El cardinal coincide con φ(n) (función de Euler). -/
    def coprimesFSet (n : ℕ₂) : ℕ₀FSet :=
      ℕ₀FSet.ofList
        ((range_from_one n.val.val).filter (fun d => coprimeb d n.val.val))

    /-- Conjunto finito de múltiplos de `d` en `{1, …, bound}`.
        Filtra `{1, …, bound}` por divisibilidad de `d`. -/
    def multiplesFSet (d : ℕ₁) (bound : ℕ₀) : ℕ₀FSet :=
      ℕ₀FSet.ofList
        ((range_from_one bound).filter (fun k => dividesb d.val k))

  end NumberSets

end Peano

export Peano.NumberSets (
  IsPrime
  CoprimesOf
  DivisorsOf
  MultiplesOf
  isPrimeb
  coprimeb
  divisorsFSet
  primesFSet
  coprimesFSet
  multiplesFSet
)
