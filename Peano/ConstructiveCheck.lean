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
--   Prelim/Classical.lean        — expone Classical.indefiniteDescription
--   Foundation/GodelBeta.lean    — encodeList y encode_decode usan Classical.choose;
--                                  beta, decodeList, godel_beta_seq SÍ son constructivos
--   ListsAndSets/FSet.lean       — usa Classical.byContradiction
--   ListsAndSets/FSetFunction.lean — usa Classical.byContradiction
--   NumberTheory/Totient.lean    — importa FSet → Classical.byContradiction
--   NumberTheory/Fermat.lean     — importa Totient → FSet
--   NumberTheory/Wilson.lean     — importa Fermat → Totient → FSet
--   Combinatorics/Counting.lean  — importa FSet → Classical.byContradiction
--   Combinatorics/Perm.lean      — importa FSet → Classical.byContradiction
--   Combinatorics/Sign.lean      — importa FSet + Perm → Classical.byContradiction
--   Combinatorics/Orbit.lean     — importa FSet + Group → Classical.em
--   Combinatorics/Product.lean   — importa FSet → Classical.byContradiction
--   Combinatorics/GroupTheory/*  — usa Classical.em (teoría de grupos)
--   Sylow/*                      — usa Classical.em y byContradiction
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
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect name).run env).run {}
  if s.axioms.contains ``Classical.choice then
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
-- Wilson.lean — NO constructivo:
--   Wilson.lean → Fermat.lean → Totient.lean → FSet.lean
--   → Classical.byContradiction → Classical.choice
-- ─────────────────────────────────────────────────────────────────
-- (sin comprobaciones para Wilson)

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: ChineseRemainder.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.CRT.chinese_remainder

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: CantorPairing.lean
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Foundation.triag
#assert_constructive Peano.Foundation.triag_zero
#assert_constructive Peano.Foundation.triag_succ
#assert_constructive Peano.Foundation.triag_strict_mono
#assert_constructive Peano.Foundation.triag_le_of_le
#assert_constructive Peano.Foundation.pair
#assert_constructive Peano.Foundation.triag_le_pair
#assert_constructive Peano.Foundation.pair_lt_triag_succ
#assert_constructive Peano.Foundation.antidiag_exists
#assert_constructive Peano.Foundation.antidiag_unique
#assert_constructive Peano.Foundation.antidiag
#assert_constructive Peano.Foundation.antidiag_spec
#assert_constructive Peano.Foundation.antidiag_pair
#assert_constructive Peano.Foundation.fst
#assert_constructive Peano.Foundation.snd
#assert_constructive Peano.Foundation.pair_fst
#assert_constructive Peano.Foundation.pair_snd
#assert_constructive Peano.Foundation.pair_surj

-- ─────────────────────────────────────────────────────────────────
-- Comprobaciones: GodelBeta.lean (parte constructiva)
-- (encodeList y encode_decode usan Classical.choose — no se comprueban)
-- ─────────────────────────────────────────────────────────────────

#assert_constructive Peano.Foundation.beta
#assert_constructive Peano.Foundation.beta_lt
#assert_constructive Peano.Foundation.beta_of_lt
#assert_constructive Peano.Foundation.godel_beta_seq
#assert_constructive Peano.Foundation.decodeList
#assert_constructive Peano.Foundation.list_decode_length

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
