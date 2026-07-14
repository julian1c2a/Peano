/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/ConstructiveCheck.lean
-- Guarda de compilación: verifica que los teoremas clave NO dependen
-- de Classical.choice.  Cada `lake build` ejecuta estas comprobaciones;
-- si alguien introduce lógica clásica por accidente, la compilación falla.

import Lean.Elab.Command
import Lean.Util.CollectAxioms

-- ─────────────────────────────────────────────────────────────────
-- Módulos CONSTRUCTIVOS bajo vigilancia
-- (ninguno importa FSet ni Classical directamente)
-- ─────────────────────────────────────────────────────────────────

-- Aritmética base
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Primes

-- Combinatoria pura
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Combinatorics.Factorial
import Peano.PeanoNat.Combinatorics.Fibonacci
import Peano.PeanoNat.Combinatorics.Summation
import Peano.PeanoNat.Combinatorics.Binom
import Peano.PeanoNat.Combinatorics.NewtonBinom

-- Teoría de números (sin FSet en la cadena de importación)
import Peano.PeanoNat.NumberTheory.ModEq
import Peano.PeanoNat.NumberTheory.ChineseRemainder
-- (Wilson/Fermat/Totient importan FSet → no constructivos)

-- Fundamentos
import Peano.PeanoNat.Foundation.CantorPairing
import Peano.PeanoNat.Foundation.GodelBeta

-- Orden y comparación
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Lattice

-- Aritmética extendida
import Peano.PeanoNat.Sqrt
import Peano.PeanoNat.Log

-- Estructuras de datos
import Peano.PeanoNat.Digits
import Peano.PeanoNat.Tuple
import Peano.PeanoNat.Pairing

-- ─────────────────────────────────────────────────────────────────
-- Módulos EXPLÍCITAMENTE NO CONSTRUCTIVOS — no se comprueban aquí:
--
-- Estado (2026-07-14, ADR-017 Fase C cerrada): tras C.1-C.9, el único uso real
-- de `Classical.*` que queda en todo el proyecto es un rincón metateórico
-- aislado sin ningún consumidor fuera de sí mismo (verificado por grep: nada
-- importa `Foundation/Foundation.lean`, y nada fuera de `Initiality.lean`/
-- `PureAxioms.lean` usa `morph_fn`/`peano_unique`/`ψ`/`φ_ψ`/`ℕ₀_pa`):
--
--   Prelim/Classical.lean         — expone Classical.indefiniteDescription
--                                   (define choose/choose_unique — el único
--                                   punto de entrada de Classical.choice)
--   Foundation/Initiality.lean    — `morph_fn`/`morph_as_morph`/`peano_unique`:
--                                   el morfismo canónico y la unicidad de
--                                   isomorfismo entre dos `PeanoSystem`
--                                   ABSTRACTOS cualesquiera (no `ℕ₀` concreto).
--                                   Inherentemente no constructivo: no hay
--                                   nada que enumerar/acotar cuando se
--                                   cuantifica sobre un tipo arbitrario.
--   Foundation/PureAxioms.lean    — `ψ` (inversa de `φ : ℕ₀ → ℕ₀_pa`, elegida
--                                   por `Peano.choose` sobre `φ_surj`), usada
--                                   para `pa_parity` (ℕ₀ ≅ cualquier modelo
--                                   axiomático puro de Peano, incl. ω de ZFC
--                                   por el mismo mecanismo). Misma naturaleza
--                                   que `Initiality.lean`: es la prueba de que
--                                   el tipo inductivo `ℕ₀` que usa el resto del
--                                   proyecto "es" el objeto axiomático abstracto,
--                                   no al revés — la aritmética/Sylow/etc. NO
--                                   dependen de este módulo.
--
-- Todo el resto del árbol (aritmética, teoría de números, combinatoria, teoría
-- de grupos, los 3 teoremas de Sylow, `Group.order`) es constructivo — ver
-- PLANNING.md Fase C.9 para el historial completo de los 5 hallazgos
-- (2 de ellos invisibles a grep de `Classical\.`: `by_cases`/`omega`/`simp`
-- cayendo a `Classical.propDecidable`/`Classical.choice` sin mencionar la
-- palabra "Classical" en el código fuente).
-- ─────────────────────────────────────────────────────────────────

set_option autoImplicit false

-- ─────────────────────────────────────────────────────────────────
-- Comando  #assert_constructive
-- ─────────────────────────────────────────────────────────────────

section AssertConstructiveCmd
open Lean Elab Command

/-- Falla en tiempo de compilación si la declaración usa `Classical.choice`. -/
elab "#assert_constructive " id:ident : command => do
  let name ← resolveGlobalConstNoOverload id
  -- API pública estable (Lean 4.30.0): `collectAxioms` devuelve `Array Name`.
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``Classical.choice then
    throwError "'{name}' depende de Classical.choice — reescribir constructivamente"

end AssertConstructiveCmd

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Primes.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Primes.prime_coprime_or_dvd
#assert_constructive Peano.Primes.coprime_dvd_of_dvd_mul
#assert_constructive Peano.Primes.irreducible_imp_prime
#assert_constructive Peano.Primes.prime_iff_irreducible
#assert_constructive Peano.Primes.exists_prime_divisor
#assert_constructive Peano.Primes.exists_prime_factorization
#assert_constructive Peano.Primes.unique_prime_factorization

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Div.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Div.div
#assert_constructive Peano.Div.mod
#assert_constructive Peano.Div.divMod_spec

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: WellFounded.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.WellFounded.well_founded_lt
#assert_constructive Peano.WellFounded.strongRecOn

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Pow.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Pow.pow

-- TEST: descomentar para verificar que la guarda detecta Classical:
-- #assert_constructive Peano.choose_spec

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Add.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Add.add_zero
#assert_constructive Peano.Add.add_succ
#assert_constructive Peano.Add.add_comm
#assert_constructive Peano.Add.add_assoc

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Sub.lean  (namespace Peano.Sub)
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Sub.sub_zero
#assert_constructive Peano.Sub.add_k_sub_k

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Mul.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Mul.mul_zero
#assert_constructive Peano.Mul.mul_comm
#assert_constructive Peano.Mul.mul_assoc
#assert_constructive Peano.Mul.mul_add

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Factorial.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Factorial.factorial_zero
#assert_constructive Peano.Factorial.factorial_succ
#assert_constructive Peano.Factorial.factorial_pos
#assert_constructive Peano.Factorial.factorial_ne_zero
#assert_constructive Peano.Factorial.factorial_ge_one

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Fibonacci.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Fibonacci.fib_zero
#assert_constructive Peano.Fibonacci.fib_one
#assert_constructive Peano.Fibonacci.fib_succ_succ

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Summation.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Summation.finSum_zero
#assert_constructive Peano.Summation.finSum_succ
#assert_constructive Peano.Summation.finSum_add_fn

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Binom.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Binom.binom_pascal
#assert_constructive Peano.Binom.binom_self
#assert_constructive Peano.Binom.binom_pos
#assert_constructive Peano.Binom.binom_mul_factorials

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: NewtonBinom.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.NewtonBinom.sum_binom_eq_pow_two
#assert_constructive Peano.NewtonBinom.newton_binom

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: ModEq.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.ModEq.modEq_refl
#assert_constructive Peano.ModEq.modEq_symm
#assert_constructive Peano.ModEq.modEq_trans
#assert_constructive Peano.ModEq.modEq_add
#assert_constructive Peano.ModEq.modEq_mul
#assert_constructive Peano.ModEq.modEq_pow
#assert_constructive Peano.ModEq.mod_eq_zero_iff_dvd
#assert_constructive Peano.ModEq.modEq_zero_iff_dvd

-- ─────────────────────────────────────────────────────────────────
-- Wilson.lean — sin comprobación #assert_constructive todavía.
-- Nota (2026-07-13): la razón original documentada aquí (Wilson → Fermat →
-- Totient → FSet → Classical.byContradiction) era incorrecta — FSet.lean usa
-- `Decidable.byContradiction`, constructivo. Pendiente: añadir
-- #assert_constructive Peano.Wilson.wilson una vez confirmado que su cadena de
-- dependencias no toca ninguno de los puntos reales listados arriba.
-- ─────────────────────────────────────────────────────────────────

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: ChineseRemainder.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.CRT.chinese_remainder

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: CantorPairing.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.CantorPairing.triag
#assert_constructive Peano.CantorPairing.triag_zero
#assert_constructive Peano.CantorPairing.triag_succ
#assert_constructive Peano.CantorPairing.triag_strict_mono
#assert_constructive Peano.CantorPairing.triag_le_of_le
#assert_constructive Peano.CantorPairing.pair
#assert_constructive Peano.CantorPairing.triag_le_pair
#assert_constructive Peano.CantorPairing.pair_lt_triag_succ
#assert_constructive Peano.CantorPairing.antidiag_exists
#assert_constructive Peano.CantorPairing.antidiag_unique
#assert_constructive Peano.CantorPairing.antidiag
#assert_constructive Peano.CantorPairing.antidiag_spec
#assert_constructive Peano.CantorPairing.antidiag_pair
#assert_constructive Peano.CantorPairing.fst
#assert_constructive Peano.CantorPairing.snd
#assert_constructive Peano.CantorPairing.pair_fst
#assert_constructive Peano.CantorPairing.pair_snd
#assert_constructive Peano.CantorPairing.pair_surj

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: GodelBeta.lean
-- (encodeList/encode_decode ya no usan Classical.choose desde C.4, 2026-07-13
-- — búsqueda acotada vía godelC/godelC_spec; ver PLANNING.md Fase C.4)
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.GodelBeta.beta
#assert_constructive Peano.GodelBeta.beta_lt
#assert_constructive Peano.GodelBeta.beta_of_lt
#assert_constructive Peano.GodelBeta.godel_beta_seq
#assert_constructive Peano.GodelBeta.decodeList
#assert_constructive Peano.GodelBeta.list_decode_length
#assert_constructive Peano.GodelBeta.encodeList
#assert_constructive Peano.GodelBeta.encode_decode

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: StrictOrder.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.StrictOrder.lt₀
#assert_constructive Peano.StrictOrder.lt_trans
#assert_constructive Peano.StrictOrder.lt_irrefl
#assert_constructive Peano.StrictOrder.trichotomy
#assert_constructive Peano.StrictOrder.lt_then_lt_succ

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Order.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Order.le₀
#assert_constructive Peano.Order.le_refl
#assert_constructive Peano.Order.le_trans
#assert_constructive Peano.Order.le_antisymm
#assert_constructive Peano.Order.le_total

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Lattice.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Lattice.max
#assert_constructive Peano.Lattice.min
#assert_constructive Peano.Lattice.max_comm
#assert_constructive Peano.Lattice.min_comm
#assert_constructive Peano.Lattice.le_max_left
#assert_constructive Peano.Lattice.min_le_left

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Sqrt.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Sqrt.sqrtMod
#assert_constructive Peano.Sqrt.sqrt
#assert_constructive Peano.Sqrt.sqrtRem
#assert_constructive Peano.Sqrt.sqrtMod_spec
#assert_constructive Peano.Sqrt.sqrt_upper_bound

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Log.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Log.logMod
#assert_constructive Peano.Log.log
#assert_constructive Peano.Log.logRem
#assert_constructive Peano.Log.logMod_spec
#assert_constructive Peano.Log.log_upper_bound

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Digits.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Digits.digits
#assert_constructive Peano.Digits.ofDigits
#assert_constructive Peano.Digits.numDigits
#assert_constructive Peano.Digits.ofDigitsFin_digits
#assert_constructive Peano.Digits.digits_singleton_of_lt

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Tuple.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Tuple
#assert_constructive Peano.emptyTuple
#assert_constructive Peano.consTuple
#assert_constructive Peano.headTuple
#assert_constructive Peano.lexLt_trans

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: Pairing.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Pairing.tri
#assert_constructive Peano.Pairing.cantorPair
#assert_constructive Peano.Pairing.cantorUnpair
#assert_constructive Peano.Pairing.cantorPair_cantorUnpair
#assert_constructive Peano.Pairing.cantorUnpair_cantorPair
