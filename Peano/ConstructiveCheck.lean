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
-- Módulos adicionales (ADR-017 Fase C.6, 2026-07-14): el resto del árbol,
-- ahora que TODO el proyecto salvo la única excepción documentada (abajo)
-- está verificado libre de Classical.choice. Incluye la cadena de teoría
-- de grupos completa (Group → GroupTheory/* → Sylow/*), FSet/FSetFunction,
-- EquivRel, List, NumberSets, y los módulos de teoría de números que antes
-- se excluían por importar FSet (Totient/Wilson/Fermat).
-- ─────────────────────────────────────────────────────────────────

import Peano.PeanoNat.Axioms
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Fractions
import Peano.PeanoNat.Decidable

-- Combinatoria (resto)
import Peano.PeanoNat.Combinatorics.Product
import Peano.PeanoNat.Combinatorics.Perm

-- Teoría de números (dependen de FSet — ya verificadas Classical.choice-free)
import Peano.PeanoNat.NumberTheory.Totient
import Peano.PeanoNat.NumberTheory.Wilson
import Peano.PeanoNat.NumberTheory.Fermat

-- Conjuntos de números
import Peano.PeanoNat.NumberSets

-- Fundamentos (resto)
import Peano.PeanoNat.Foundation.PeanoSystem
import Peano.PeanoNat.Foundation.Initiality

-- Listas y conjuntos
import Peano.PeanoNat.ListsAndSets.List
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.ListsAndSets.EquivRel

-- Teoría de grupos (cadena completa hasta Sylow)
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Action
import Peano.PeanoNat.Combinatorics.GroupTheory.CorrespondenceTheorem
import Peano.PeanoNat.Combinatorics.GroupTheory.FirstIsomorphism
import Peano.PeanoNat.Combinatorics.GroupTheory.NormalSubgroup
import Peano.PeanoNat.Combinatorics.GroupTheory.QuotientGroup
import Peano.PeanoNat.Combinatorics.GroupTheory.SecondIsomorphism
import Peano.PeanoNat.Combinatorics.GroupTheory.ThirdIsomorphism
import Peano.PeanoNat.Combinatorics.GroupTheory.Zassenhaus
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.CosetAction
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Sylow

-- Re-exports agregadores
import Peano.PeanoNat.Isomorph
import Peano.Prelim
import Peano.Prelim.ExistsUnique

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
-- HALLAZGO (Fase C.6, 2026-07-14) — ✅ RESUELTO. `well_ordering_principle`
-- (Order.lean) hacía `by_cases` sobre `∃ k', le₀ k' n' ∧ P k'` para un `P`
-- arbitrario sin `[DecidablePred P]`, cayendo en `Classical.propDecidable`;
-- se propagaba a `WellFounded.well_ordering_principle` y de ahí a
-- `Mul.exists_unique_mul_le_and_lt_succ_mul`/`exists_factor_of_mul_le`.
-- `Order.lean`/`WellFounded.lean`/`Mul.lean` estaban FROZEN — se hizo
-- `thaw --confirm` puntual (autorizado por el usuario), se añadió
-- `[DecidablePred P]` a la firma de ambos `well_ordering_principle` y una
-- instancia real `decidableExistsLe` (Order.lean, envolviendo el `def`
-- preexistente `decidableBExLe_of_bool` — que por sí solo NO lo recogía la
-- búsqueda de instancias, de ahí el fallback clásico pese a que `P` fuera
-- decidible en la práctica en todos los usos reales), y se volvió a congelar.
-- Ver PLANNING.md Fase C.6 para el detalle completo.
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


-- ═════════════════════════════════════════════════════════════════
-- FASE C.6 (2026-07-14): comprobaciones para el resto del proyecto.
-- Cobertura completa de todo simbolo exportado (export X.Y (...)) en
-- cada modulo .lean bajo Peano/, salvo la unica excepcion documentada
-- arriba (Initiality.morph_fn*/peano_unique, PureAxioms, Prelim choose*).
-- Ver PLANNING.md Fase C.6 para el detalle de la generacion y el conteo.
-- ═════════════════════════════════════════════════════════════════

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: PeanoNat.lean (raiz: Nat0, Λ, Ψ, τ, ρ, ...)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.ℕ₀
#assert_constructive Peano.ℕ₁
#assert_constructive Peano.ℕ₂
#assert_constructive Peano.Nats
#assert_constructive Peano.Nats.toType
#assert_constructive Peano.idℕ₀
#assert_constructive Peano.idNat
#assert_constructive Peano.eqFnGen
#assert_constructive Peano.comp
#assert_constructive Peano.eqFn
#assert_constructive Peano.eqFn2
#assert_constructive Peano.eqFnNat
#assert_constructive Peano.Λ
#assert_constructive Peano.Ψ
#assert_constructive Peano.τ
#assert_constructive Peano.ρ

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Axioms.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Axioms.Λ_inj
#assert_constructive Peano.Axioms.Λ_surj
#assert_constructive Peano.Axioms.Λ_bij
#assert_constructive Peano.Axioms.Ψ_inj
#assert_constructive Peano.Axioms.Ψ_surj
#assert_constructive Peano.Axioms.Ψ_bij
#assert_constructive Peano.Axioms.isZero
#assert_constructive Peano.Axioms.isSucc
#assert_constructive Peano.Axioms.returnBranch
#assert_constructive Peano.Axioms.isNat_zero
#assert_constructive Peano.Axioms.isNat_succ
#assert_constructive Peano.Axioms.zero_ne_succ
#assert_constructive Peano.Axioms.succ_isNat
#assert_constructive Peano.Axioms.succ_congr
#assert_constructive Peano.Axioms.succ_injective
#assert_constructive Peano.Axioms.succ_inj_neg
#assert_constructive Peano.Axioms.AXIOM_zero_notin_ima_succ
#assert_constructive Peano.Axioms.induction_principle
#assert_constructive Peano.Axioms.BIs_zero
#assert_constructive Peano.Axioms.BIs_succ
#assert_constructive Peano.Axioms.category_by_constructor
#assert_constructive Peano.Axioms.neq_succ
#assert_constructive Peano.Axioms.isZero_or_isSucc
#assert_constructive Peano.Axioms.isZero_xor_isSucc
#assert_constructive Peano.Axioms.eqFn_refl
#assert_constructive Peano.Axioms.eqFn_symm
#assert_constructive Peano.Axioms.eqFn_trans
#assert_constructive Peano.Axioms.eqFn_induction
#assert_constructive Peano.Axioms.comp_Λ_eq_Ψ
#assert_constructive Peano.Axioms.comp_Ψ_eq_Λ
#assert_constructive Peano.Axioms.id_eq_id_lambda
#assert_constructive Peano.Axioms.τ_σ_eq_self
#assert_constructive Peano.Axioms.σ_ρ_eq_self
#assert_constructive Peano.Axioms.σ_τ_eq_id_pos
#assert_constructive Peano.Axioms.σ_ρ_eq_id_pos_elem
#assert_constructive Peano.Axioms.ΨΛ
#assert_constructive Peano.Axioms.ΛΨ
#assert_constructive Peano.Axioms.Ψ_σ_eq_σ_Λ
#assert_constructive Peano.Axioms.Λ_σ_eq_σ_Ψ
#assert_constructive Peano.Axioms.Ψ_τ_eq_τ_Λ
#assert_constructive Peano.Axioms.Λ_τ_eq_τ_Ψ
#assert_constructive Peano.Axioms.isomorph_0_Λ
#assert_constructive Peano.Axioms.isomorph_0_Ψ
#assert_constructive Peano.Axioms.isomorph_σ_Λ
#assert_constructive Peano.Axioms.isomorph_σ_Ψ
#assert_constructive Peano.Axioms.isomorph_τ_Λ
#assert_constructive Peano.Axioms.isomorph_τ_Ψ
#assert_constructive Peano.Axioms.isomorph_ρ_Ψ
#assert_constructive Peano.Axioms.isomorph_Λ_ρ
#assert_constructive Peano.Axioms.tau_eq_rho_if_ne_zero
#assert_constructive Peano.Axioms.succ_inj_wp
#assert_constructive Peano.Axioms.succ_inj_pos_wp

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Add.lean (resto de simbolos no cubiertos aun)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Add.add
#assert_constructive Peano.Add.add_l
#assert_constructive Peano.Add.add_zero_l
#assert_constructive Peano.Add.zero_add
#assert_constructive Peano.Add.zero_add_l
#assert_constructive Peano.Add.add_zero_eq_add_l_zero
#assert_constructive Peano.Add.add_one
#assert_constructive Peano.Add.add_one_l
#assert_constructive Peano.Add.one_add
#assert_constructive Peano.Add.one_add_l
#assert_constructive Peano.Add.add_one_eq_add_l_one
#assert_constructive Peano.Add.add_succ_l
#assert_constructive Peano.Add.succ_add
#assert_constructive Peano.Add.succ_add_l
#assert_constructive Peano.Add.add_succ_eq_add_l_succ
#assert_constructive Peano.Add.add_eq_add_l
#assert_constructive Peano.Add.eq_fn_add_add_l
#assert_constructive Peano.Add.add_le
#assert_constructive Peano.Add.add_le_r
#assert_constructive Peano.Add.add_lt
#assert_constructive Peano.Add.add_cancel
#assert_constructive Peano.Add.cancelation_add
#assert_constructive Peano.Add.add_lt_cancelation
#assert_constructive Peano.Add.add_le_cancelation
#assert_constructive Peano.Add.add_eq_zero_iff
#assert_constructive Peano.Add.le_then_le_add
#assert_constructive Peano.Add.le_add_then_le
#assert_constructive Peano.Add.le_iff_le_add
#assert_constructive Peano.Add.le_iff_le_add_forall
#assert_constructive Peano.Add.le_self_add
#assert_constructive Peano.Add.lt_add_succ
#assert_constructive Peano.Add.lt_then_exists_add_succ
#assert_constructive Peano.Add.le_iff_exists_add
#assert_constructive Peano.Add.lt_iff_exists_add_succ
#assert_constructive Peano.Add.lt_iff_add_cancel
#assert_constructive Peano.Add.isomorph_Ψ_add
#assert_constructive Peano.Add.isomorph_Λ_add
#assert_constructive Peano.Add.le_then_exists_zero_add
#assert_constructive Peano.Add.le_self_add_forall
#assert_constructive Peano.Add.le_add_cancel
#assert_constructive Peano.Add.le_then_le_add_zero
#assert_constructive Peano.Add.le_then_le_add_one
#assert_constructive Peano.Add.add_lt_add_left_iff
#assert_constructive Peano.Add.lt_iff_add_lt
#assert_constructive Peano.Add.le_add_r_add_r_then_le
#assert_constructive Peano.Add.le_add_l_add_l_then_le
#assert_constructive Peano.Add.le_then_le_add_r_add_r_then_le
#assert_constructive Peano.Add.le_then_le_add_l_add_l_then_le
#assert_constructive Peano.Add.le_iff_le_add_r_add_r_forall
#assert_constructive Peano.Add.le_iff_le_add_l_add_l_forall
#assert_constructive Peano.Add.add_σn_m_eq_add_n_σm
#assert_constructive Peano.Add.add_σn_m_eq_σadd_n_m
#assert_constructive Peano.Add.σadd_n_m_eq_add_n_σm
#assert_constructive Peano.Add.τadd_n_m_eq_add_τn_m
#assert_constructive Peano.Add.τadd_n_m_eq_add_n_τm
#assert_constructive Peano.Add.add_τn_m_eq_add_n_τm
#assert_constructive Peano.Add.τadd_n_σm_eq_add_n_m
#assert_constructive Peano.Add.τadd_σn_m_eq_add_n_m
#assert_constructive Peano.Add.lt_n_add_n_σm
#assert_constructive Peano.Add.lt_add_of_pos_right
#assert_constructive Peano.Add.le_add_compat
#assert_constructive Peano.Add.le_add_compat_wp
#assert_constructive Peano.Add.lt_le_then_lt_add_compat
#assert_constructive Peano.Add.lt_le_then_add_add_compat_wp
#assert_constructive Peano.Add.le_lt_then_lt_add_compat
#assert_constructive Peano.Add.le_lt_then_lt_add_compat_wp
#assert_constructive Peano.Add.lt_lt_then_lt_add_compat
#assert_constructive Peano.Add.lt_lt_then_lt_add_compat_wp
#assert_constructive Peano.Add.le_a_b_then_le_2a_2b
#assert_constructive Peano.Add.le_a_b_then_le_2a_2b_wp
#assert_constructive Peano.Add.lt_a_b_then_lt_2a_2b
#assert_constructive Peano.Add.lt_a_b_then_lt_2a_2b_wp
#assert_constructive Peano.Add.le_then_exists_add
#assert_constructive Peano.Add.le_then_exists_add_wp
#assert_constructive Peano.Add.linear_equation_right
#assert_constructive Peano.Add.linear_inequation_left
#assert_constructive Peano.Add.linear_equation_left
#assert_constructive Peano.Add.linear_inequation_right
#assert_constructive Peano.Add.lt_then_exists_add_succ_wp
#assert_constructive Peano.Add.lt_add_pos
#assert_constructive Peano.Add.lt_0_then_le_1
#assert_constructive Peano.Add.le_self_add_r
#assert_constructive Peano.Add.le_self_add_r_forall
#assert_constructive Peano.Add.le_self_add_l
#assert_constructive Peano.Add.le_self_add_l_forall
#assert_constructive Peano.Add.lt_self_add_r
#assert_constructive Peano.Add.lt_self_add_r_forall
#assert_constructive Peano.Add.lt_self_add_l
#assert_constructive Peano.Add.lt_self_add_l_forall

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Sub.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Sub.subₕₖ
#assert_constructive Peano.Sub.subₕₖ_zero
#assert_constructive Peano.Sub.subₕₖ_succ
#assert_constructive Peano.Sub.subₕₖ_k_add_k
#assert_constructive Peano.Sub.subₕₖ_k_add_k_forall
#assert_constructive Peano.Sub.sub_k_add_k
#assert_constructive Peano.Sub.sub_k_add_k_forall
#assert_constructive Peano.Sub.add_k_sub_k_forall
#assert_constructive Peano.Sub.aux_ge_1
#assert_constructive Peano.Sub.aux_neq_0
#assert_constructive Peano.Sub.succ_subₕₖ
#assert_constructive Peano.Sub.succ_sub
#assert_constructive Peano.Sub.sub_succ_succ_eq
#assert_constructive Peano.Sub.isomorph_Λ_sub
#assert_constructive Peano.Sub.isomorph_Ψ_sub
#assert_constructive Peano.Sub.subₕₖ_self
#assert_constructive Peano.Sub.sub_self
#assert_constructive Peano.Sub.subₕₖ_le_self
#assert_constructive Peano.Sub.sub_le_self
#assert_constructive Peano.Sub.subₕₖ_eq_iff_eq_add_of_le
#assert_constructive Peano.Sub.subₕₖ_le_subₕₖ_right
#assert_constructive Peano.Sub.subₕₖ_le_subₕₖ_left
#assert_constructive Peano.Sub.add_sub_assoc
#assert_constructive Peano.Sub.add_le_add_left
#assert_constructive Peano.Sub.sub_eq_of_le
#assert_constructive Peano.Sub.le_sub_iff_add_le_of_le
#assert_constructive Peano.Sub.sub_sub
#assert_constructive Peano.Sub.sub_lt_iff_lt_add_of_le
#assert_constructive Peano.Sub.sub_pos_iff_lt
#assert_constructive Peano.Sub.subₕₖ_lt_self
#assert_constructive Peano.Sub.sub_lt_self
#assert_constructive Peano.Sub.lt_b_a_then_sub_a_b_neq_0
#assert_constructive Peano.Sub.sub_pos_of_lt
#assert_constructive Peano.Sub.sub_lt_self_wp
#assert_constructive Peano.Sub.sub_gt_factor_of_gt_one_and_sufficient_gap

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Mul.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Mul.mul
#assert_constructive Peano.Mul.zero_mul
#assert_constructive Peano.Mul.succ_mul
#assert_constructive Peano.Mul.mul_succ
#assert_constructive Peano.Mul.mul_one
#assert_constructive Peano.Mul.one_mul
#assert_constructive Peano.Mul.mul_two
#assert_constructive Peano.Mul.two_mul
#assert_constructive Peano.Mul.mul_three
#assert_constructive Peano.Mul.three_mul
#assert_constructive Peano.Mul.add_mul
#assert_constructive Peano.Mul.mul_cancelation_left
#assert_constructive Peano.Mul.mul_cancelation_right
#assert_constructive Peano.Mul.mul_eq_zero
#assert_constructive Peano.Mul.eq_zero_of_mul_eq_zero
#assert_constructive Peano.Mul.mul_le_right
#assert_constructive Peano.Mul.mul_le_left
#assert_constructive Peano.Mul.mul_le_full_right
#assert_constructive Peano.Mul.mul_le_full_left
#assert_constructive Peano.Mul.mul_n_τm
#assert_constructive Peano.Mul.mul_τn_m
#assert_constructive Peano.Mul.le_n_mul_n_σn
#assert_constructive Peano.Mul.lt_σn_mul_σn_σσm
#assert_constructive Peano.Mul.archimedean_property
#assert_constructive Peano.Mul.exists_unique_mul_le_and_lt_succ_mul
#assert_constructive Peano.Mul.exists_factor_of_mul_le
#assert_constructive Peano.Mul.mul_le_mono_right
#assert_constructive Peano.Mul.le_le_mul_le_compat
#assert_constructive Peano.Mul.lt_lt_mul_lt_compat
#assert_constructive Peano.Mul.mul_pos
#assert_constructive Peano.Mul.le_lt_mul_lt_compat
#assert_constructive Peano.Mul.mul_sub
#assert_constructive Peano.Mul.lt_of_lt_of_le
#assert_constructive Peano.Mul.isomorph_Ψ_mul
#assert_constructive Peano.Mul.isomorph_Λ_mul

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Div.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Div.divMod
#assert_constructive Peano.Div.div_def
#assert_constructive Peano.Div.mod_def
#assert_constructive Peano.Div.mod_lt
#assert_constructive Peano.Div.div_le_self
#assert_constructive Peano.Div.div_lt_self
#assert_constructive Peano.Div.mod_of_lt
#assert_constructive Peano.Div.div_of_lt
#assert_constructive Peano.Div.mod_of_lt_fst_interval
#assert_constructive Peano.Div.div_eq_two
#assert_constructive Peano.Div.mod_of_lt_snd_interval
#assert_constructive Peano.Div.div_of_lt_nth_interval
#assert_constructive Peano.Div.mod_of_lt_nth_interval
#assert_constructive Peano.Div.div_mod_unique
#assert_constructive Peano.Div.div_eq_of_mul_eq
#assert_constructive Peano.Div.isomorph_Ψ_div
#assert_constructive Peano.Div.isomorph_Ψ_mod
#assert_constructive Peano.Div.isomorph_Λ_div
#assert_constructive Peano.Div.isomorph_Λ_mod

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Arith.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Arith.Divides
#assert_constructive Peano.Arith.MultipleOf
#assert_constructive Peano.Arith.DivisorOf
#assert_constructive Peano.Arith.Divisors
#assert_constructive Peano.Arith.Multiples
#assert_constructive Peano.Arith.multiples_to_divides
#assert_constructive Peano.Arith.divides_to_multiples
#assert_constructive Peano.Arith.multiples_iff_divides
#assert_constructive Peano.Arith.DivisorsList
#assert_constructive Peano.Arith.mem_cons
#assert_constructive Peano.Arith.mem_append
#assert_constructive Peano.Arith.range_from_one
#assert_constructive Peano.Arith.dividesb
#assert_constructive Peano.Arith.factorsOf
#assert_constructive Peano.Arith.one_divides
#assert_constructive Peano.Arith.divisorslist_one_mem
#assert_constructive Peano.Arith.divisorslist_self_mem
#assert_constructive Peano.Arith.IsGCD
#assert_constructive Peano.Arith.IsLCM
#assert_constructive Peano.Arith.Coprime
#assert_constructive Peano.Arith.Prime
#assert_constructive Peano.Arith.gcd
#assert_constructive Peano.Arith.lcm
#assert_constructive Peano.Arith.divides_refl
#assert_constructive Peano.Arith.divides_zero
#assert_constructive Peano.Arith.zero_divides_iff
#assert_constructive Peano.Arith.divides_trans
#assert_constructive Peano.Arith.divides_mul_right
#assert_constructive Peano.Arith.divides_mul_left
#assert_constructive Peano.Arith.divides_add
#assert_constructive Peano.Arith.divides_le
#assert_constructive Peano.Arith.antisymm_divides
#assert_constructive Peano.Arith.divides_sub
#assert_constructive Peano.Arith.divides_mod
#assert_constructive Peano.Arith.gcd_greatest
#assert_constructive Peano.Arith.gcd_step
#assert_constructive Peano.Arith.gcd_divides_linear_combo
#assert_constructive Peano.Arith.bezout_natform
#assert_constructive Peano.Arith.gcd_divides_max
#assert_constructive Peano.Arith.gcd_divides_min
#assert_constructive Peano.Arith.gcd_comm
#assert_constructive Peano.Arith.gcd_divides_left
#assert_constructive Peano.Arith.gcd_divides_right
#assert_constructive Peano.Arith.gcd_dvd_left
#assert_constructive Peano.Arith.gcd_dvd_right
#assert_constructive Peano.Arith.dvd_gcd
#assert_constructive Peano.Arith.gcd_zero_right
#assert_constructive Peano.Arith.gcd_zero_left
#assert_constructive Peano.Arith.gcd_one_right
#assert_constructive Peano.Arith.gcd_one_left
#assert_constructive Peano.Arith.gcd_self
#assert_constructive Peano.Arith.gcd_eq_zero_iff
#assert_constructive Peano.Arith.gcd_ne_zero_left
#assert_constructive Peano.Arith.divides_of_add_eq
#assert_constructive Peano.Arith.euclid_lemma
#assert_constructive Peano.Arith.gcd_ne_zero_right
#assert_constructive Peano.Arith.dvd_gcd_iff
#assert_constructive Peano.Arith.gcd_assoc
#assert_constructive Peano.Arith.IsGCD_gcd
#assert_constructive Peano.Arith.div_mul_cancel
#assert_constructive Peano.Arith.mul_div_of_dvd_left
#assert_constructive Peano.Arith.gcd_mul_lcm
#assert_constructive Peano.Arith.lcm_comm
#assert_constructive Peano.Arith.lcm_zero_left
#assert_constructive Peano.Arith.lcm_zero_right
#assert_constructive Peano.Arith.dvd_lcm_left
#assert_constructive Peano.Arith.dvd_lcm_right
#assert_constructive Peano.Arith.lcm_self
#assert_constructive Peano.Arith.coprime_comm
#assert_constructive Peano.Arith.coprime_one_right
#assert_constructive Peano.Arith.coprime_one_left
#assert_constructive Peano.Arith.Divides₁
#assert_constructive Peano.Arith.IsGCD₁
#assert_constructive Peano.Arith.gcd₁
#assert_constructive Peano.Arith.Coprime₁
#assert_constructive Peano.Arith.divides₁_refl
#assert_constructive Peano.Arith.divides₁_trans
#assert_constructive Peano.Arith.divides₁_antisymm
#assert_constructive Peano.Arith.mod_eq_zero_iff_divides
#assert_constructive Peano.Arith.gcd₁_val_eq
#assert_constructive Peano.Arith.gcd₁_comm
#assert_constructive Peano.Arith.gcd₁_divides_left
#assert_constructive Peano.Arith.gcd₁_divides_right
#assert_constructive Peano.Arith.gcd₁_divides_both
#assert_constructive Peano.Arith.isomorph_Ψ_gcd
#assert_constructive Peano.Arith.isomorph_Λ_gcd
#assert_constructive Peano.Arith.isomorph_Ψ_lcm
#assert_constructive Peano.Arith.isomorph_Λ_lcm
#assert_constructive Peano.Arith.IsEven
#assert_constructive Peano.Arith.IsOdd
#assert_constructive Peano.Arith.decidableIsEven
#assert_constructive Peano.Arith.decidableIsOdd
#assert_constructive Peano.Arith.even_zero
#assert_constructive Peano.Arith.odd_one
#assert_constructive Peano.Arith.even_or_odd
#assert_constructive Peano.Arith.not_even_and_odd
#assert_constructive Peano.Arith.not_even_iff_odd
#assert_constructive Peano.Arith.not_odd_iff_even

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Fractions.lean (extiende namespace Peano.Arith)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Arith.dvd_of_mul_dvd
#assert_constructive Peano.Arith.gcd_div_self
#assert_constructive Peano.Arith.cross_mul_eq_imp_reduced_eq

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Primes.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Primes.Prime
#assert_constructive Peano.Primes.ℙ
#assert_constructive Peano.Primes.Irreducible
#assert_constructive Peano.Primes.HasExactlyTwoDivisors
#assert_constructive Peano.Primes.prime_ne_zero
#assert_constructive Peano.Primes.prime_ge_two
#assert_constructive Peano.Primes.prime_divisors
#assert_constructive Peano.Primes.prime_ne_one
#assert_constructive Peano.Primes.not_has_two_divisors_one
#assert_constructive Peano.Primes.not_has_two_divisors_zero
#assert_constructive Peano.Primes.prime_iff_has_exactly_two_divisors
#assert_constructive Peano.Primes.PrimeList
#assert_constructive Peano.Primes.product_list_pos
#assert_constructive Peano.Primes.prime_dvd_product_list
#assert_constructive Peano.Primes.prime_dvd_mul
#assert_constructive Peano.Primes.smallestDivisorAux_spec
#assert_constructive Peano.Primes.smallestDivisor
#assert_constructive Peano.Primes.smallestDivisor_not_dvd_of_lt
#assert_constructive Peano.Primes.smallestDivisor_le_of_prime_dvd
#assert_constructive Peano.Primes.smallestDivisor_prime
#assert_constructive Peano.Primes.factorize
#assert_constructive Peano.Primes.isPrimeb
#assert_constructive Peano.Primes.isPrimeb_iff
#assert_constructive Peano.Primes.decidablePrime
#assert_constructive Peano.Primes.dividesb_true_imp_dvd
#assert_constructive Peano.Primes.dvd_imp_dividesb_true
#assert_constructive Peano.Primes.dividesb_iff_dvd
#assert_constructive Peano.Primes.decidableDvd

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: WellFounded.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.WellFounded.well_ordering_principle
#assert_constructive Peano.WellFounded.strongInductionOn

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: StrictOrder.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.StrictOrder.blt₀
#assert_constructive Peano.StrictOrder.gt₀
#assert_constructive Peano.StrictOrder.bgt₀
#assert_constructive Peano.StrictOrder.lt_iff_lt_σ_σ
#assert_constructive Peano.StrictOrder.nlt_self
#assert_constructive Peano.StrictOrder.not_lt_zero
#assert_constructive Peano.StrictOrder.nlt_n_0
#assert_constructive Peano.StrictOrder.pos_of_ne_zero
#assert_constructive Peano.StrictOrder.ne_of_lt
#assert_constructive Peano.StrictOrder.neq_then_lt_or_gt
#assert_constructive Peano.StrictOrder.lt_nor_gt_then_eq
#assert_constructive Peano.StrictOrder.lt_asymm
#assert_constructive Peano.StrictOrder.strong_trichotomy
#assert_constructive Peano.StrictOrder.lt_equiv_exists_σ
#assert_constructive Peano.StrictOrder.lt_self_σ_self
#assert_constructive Peano.StrictOrder.lt_iff_lt_τ_τ
#assert_constructive Peano.StrictOrder.blt_iff_Lt
#assert_constructive Peano.StrictOrder.bgt_iff_Gt
#assert_constructive Peano.StrictOrder.nblt_iff_nLt
#assert_constructive Peano.StrictOrder.nbgt_iff_nGt
#assert_constructive Peano.StrictOrder.isomorph_Λ_lt
#assert_constructive Peano.StrictOrder.isomorph_Ψ_lt
#assert_constructive Peano.StrictOrder.zero_lt_succ
#assert_constructive Peano.StrictOrder.zero_is_the_minor
#assert_constructive Peano.StrictOrder.lt_zero_succ
#assert_constructive Peano.StrictOrder.lt_succ_iff_lt_or_eq
#assert_constructive Peano.StrictOrder.lt_succ_self
#assert_constructive Peano.StrictOrder.lt_succ
#assert_constructive Peano.StrictOrder.lt_of_succ_lt_succ
#assert_constructive Peano.StrictOrder.succ_lt_succ_iff
#assert_constructive Peano.StrictOrder.decidableLt
#assert_constructive Peano.StrictOrder.decidableGt
#assert_constructive Peano.StrictOrder.neq_01_then_gt_1
#assert_constructive Peano.StrictOrder.nlt_then_ltc_or_eq
#assert_constructive Peano.StrictOrder.lt_or_eq_then_nltc
#assert_constructive Peano.StrictOrder.lt_or_eq_iff_nltc
#assert_constructive Peano.StrictOrder.succ_lt_succ_iff_forall
#assert_constructive Peano.StrictOrder.lt_then_lt_succ_forall
#assert_constructive Peano.StrictOrder.lt_succ_then_lt_forall
#assert_constructive Peano.StrictOrder.nlt_n_0_false
#assert_constructive Peano.StrictOrder.blt_then_Lt_wp
#assert_constructive Peano.StrictOrder.succ_lt_succ_then
#assert_constructive Peano.StrictOrder.lt_then_lt_succ_wp
#assert_constructive Peano.StrictOrder.lt_then_lt_succs
#assert_constructive Peano.StrictOrder.lt_n_sm_then_lt_n_m_or_eq
#assert_constructive Peano.StrictOrder.lt_n_sm_then_lt_n_m_or_eq_wp
#assert_constructive Peano.StrictOrder.lt_sn_m_then_lt_n_m
#assert_constructive Peano.StrictOrder.lt_sn_m_then_lt_n_m_wp
#assert_constructive Peano.StrictOrder.lt_0_succ
#assert_constructive Peano.StrictOrder.lt_1_succ_succ
#assert_constructive Peano.StrictOrder.lt_1_b_then_b_neq_1
#assert_constructive Peano.StrictOrder.lt_1_b_then_b_neq_0
#assert_constructive Peano.StrictOrder.lt_0_1
#assert_constructive Peano.StrictOrder.lt_trans_wp
#assert_constructive Peano.StrictOrder.lt_asymm_wp
#assert_constructive Peano.StrictOrder.StrictLinearOrder
#assert_constructive Peano.StrictOrder.instStrictLinearOrderNat0
#assert_constructive Peano.StrictOrder.instDecidableRelLtOfSLO
#assert_constructive Peano.StrictOrder.instIrreflLTOfSLO
#assert_constructive Peano.StrictOrder.lt_b_1_then_b_eq_0
#assert_constructive Peano.StrictOrder.neq_0_then_lt_0
#assert_constructive Peano.StrictOrder.lt_0_then_neq_0
#assert_constructive Peano.StrictOrder.lt_then_lt_σ_σ_wp
#assert_constructive Peano.StrictOrder.lt_σ_σ_then_lt_wp
#assert_constructive Peano.StrictOrder.lt_succ_then_lt
#assert_constructive Peano.StrictOrder.lt_succ_then_lt_wp

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Order.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Order.ge₀
#assert_constructive Peano.Order.le'
#assert_constructive Peano.Order.ble₀
#assert_constructive Peano.Order.bge₀
#assert_constructive Peano.Order.zero_le
#assert_constructive Peano.Order.succ_le_succ_iff
#assert_constructive Peano.Order.succ_le_succ_then
#assert_constructive Peano.Order.Le_iff_le'
#assert_constructive Peano.Order.bge_iff_Ge
#assert_constructive Peano.Order.le_of_eq
#assert_constructive Peano.Order.decidableLe
#assert_constructive Peano.Order.decidableGe
#assert_constructive Peano.Order.lt_imp_le
#assert_constructive Peano.Order.le_iff_lt_succ
#assert_constructive Peano.Order.not_succ_le_zero
#assert_constructive Peano.Order.lt_of_le_neq
#assert_constructive Peano.Order.lt_of_le_neq_wp
#assert_constructive Peano.Order.le_zero_eq
#assert_constructive Peano.Order.isomorph_Ψ_le
#assert_constructive Peano.Order.isomorph_Λ_le
#assert_constructive Peano.Order.lt_of_le_of_ne
#assert_constructive Peano.Order.le_succ_iff_le_or_eq
#assert_constructive Peano.Order.lt_iff_le_not_le
#assert_constructive Peano.Order.le_succ_iff_le_or_eq_alt
#assert_constructive Peano.Order.le_of_succ_le_succ
#assert_constructive Peano.Order.lt_succ_iff_lt_or_eq_alt
#assert_constructive Peano.Order.nle_iff_gt
#assert_constructive Peano.Order.nle_then_gt
#assert_constructive Peano.Order.le_not_lt
#assert_constructive Peano.Order.gt_then_nle
#assert_constructive Peano.Order.gt_then_nle_wp
#assert_constructive Peano.Order.le_1_m_then_m_neq_0
#assert_constructive Peano.Order.le_n_m_then_m_neq_0
#assert_constructive Peano.Order.le_n_m_n_neq_0_then_m_neq_0
#assert_constructive Peano.Order.m_neq_0_proved_lt_1_m_wp
#assert_constructive Peano.Order.m_neq_0_proved_lt_1_m
#assert_constructive Peano.Order.nle_then_gt_wp
#assert_constructive Peano.Order.le_then_le_succ
#assert_constructive Peano.Order.le_0_succ_then_lt_0_succ_wp
#assert_constructive Peano.Order.lt_0_succ_then_le_0_succ_wp
#assert_constructive Peano.Order.le_0_succ_iff_lt_0_succ
#assert_constructive Peano.Order.lt_0_succ_then_le_0_succ
#assert_constructive Peano.Order.le_0_succ_then_lt_0_succ
#assert_constructive Peano.Order.le_self_of_eq_self
#assert_constructive Peano.Order.le_0_of_eq_0
#assert_constructive Peano.Order.le_then_lt_succ
#assert_constructive Peano.Order.le_then_lt_succ_wp
#assert_constructive Peano.Order.succ_le_succ_iff_wp
#assert_constructive Peano.Order.le_succ_then_le_or_eq
#assert_constructive Peano.Order.le_or_eq_then_le_succ
#assert_constructive Peano.Order.le_succ_then_le_or_eq_wp
#assert_constructive Peano.Order.le_or_eq_then_le_succ_wp
#assert_constructive Peano.Order.le_succ_k_n_then_le_k_n
#assert_constructive Peano.Order.lt_k_succ_n_then_le_k_n
#assert_constructive Peano.Order.lt_k_succ_n_then_le_k_n_wp
#assert_constructive Peano.Order.le_k_n_then_le_k_sn_wp
#assert_constructive Peano.Order.succ_le_succ_then_wp
#assert_constructive Peano.Order.succ_le_succ'_then_wp
#assert_constructive Peano.Order.le_n_m_then_le_n_sm
#assert_constructive Peano.Order.le_n_m_then_le_n_sm_wp
#assert_constructive Peano.Order.le_sn_m_then_le_n_m_or_succ
#assert_constructive Peano.Order.le_sn_m_then_le_n_m_or_succ_wp
#assert_constructive Peano.Order.le_then_lt_or_eq
#assert_constructive Peano.Order.le_zero_eq_zero
#assert_constructive Peano.Order.le_succ_zero_zero
#assert_constructive Peano.Order.le_succ_0_then_false
#assert_constructive Peano.Order.le_1_0_then_false
#assert_constructive Peano.Order.le_1_succ
#assert_constructive Peano.Order.le_of_eq_wp
#assert_constructive Peano.Order.le_zero_eq_wp
#assert_constructive Peano.Order.nle_σn_n
#assert_constructive Peano.Order.le_σn_n_then_false
#assert_constructive Peano.Order.succ_le_succ_if
#assert_constructive Peano.Order.succ_le_succ_if_wp
#assert_constructive Peano.Order.le_succ_k_n_then_lt_k_n
#assert_constructive Peano.Order.le_succ_k_n_then_lt_k_n_wp
#assert_constructive Peano.Order.lt_imp_le_wp
#assert_constructive Peano.Order.le_succ_then_le
#assert_constructive Peano.Order.le_succ_then_le_wp
#assert_constructive Peano.Order.lt_0n_then_le_1n
#assert_constructive Peano.Order.lt_0n_then_le_1n_wp
#assert_constructive Peano.Order.lt_nm_then_le_nm
#assert_constructive Peano.Order.lt_nm_then_le_nm_wp
#assert_constructive Peano.Order.le_then_ngt
#assert_constructive Peano.Order.le_then_ngt_wp
#assert_constructive Peano.Order.ngt_then_le
#assert_constructive Peano.Order.ngt_then_le_wp
#assert_constructive Peano.Order.le_succ_then_lt
#assert_constructive Peano.Order.le_succ_then_lt_wp
#assert_constructive Peano.Order.lt_then_le_succ
#assert_constructive Peano.Order.lt_then_le_succ_wp
#assert_constructive Peano.Order.well_ordering_principle
#assert_constructive Peano.Order.ngt_iff_le
#assert_constructive Peano.Order.ngt_iff_le_wp
#assert_constructive Peano.Order.le_succ_trans
#assert_constructive Peano.Order.le_1_m_then_m_neq_0_wp
#assert_constructive Peano.Order.le_iff_lt_or_eq
#assert_constructive Peano.Order.lt_pred_of_lt_succ
#assert_constructive Peano.Order.lt_succ_iff_le
#assert_constructive Peano.Order.nlt_of_le
#assert_constructive Peano.Order.not_lt_and_not_eq_implies_gt
#assert_constructive Peano.Order.bexLe
#assert_constructive Peano.Order.decidableBExLe_of_bool
#assert_constructive Peano.Order.lt_or_ge
#assert_constructive Peano.Order.le_or_lt

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Lattice.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Lattice.min_max
#assert_constructive Peano.Lattice.max_min
#assert_constructive Peano.Lattice.max_idem
#assert_constructive Peano.Lattice.min_idem
#assert_constructive Peano.Lattice.min_abs_0
#assert_constructive Peano.Lattice.min_0_abs
#assert_constructive Peano.Lattice.max_not_0
#assert_constructive Peano.Lattice.max_0_not
#assert_constructive Peano.Lattice.eq_of_max_eq_min
#assert_constructive Peano.Lattice.eq_then_eq_max_min
#assert_constructive Peano.Lattice.eq_iff_eq_max_min
#assert_constructive Peano.Lattice.min_of_min_max
#assert_constructive Peano.Lattice.max_of_min_max
#assert_constructive Peano.Lattice.max_is_any
#assert_constructive Peano.Lattice.min_is_any
#assert_constructive Peano.Lattice.lt_then_min
#assert_constructive Peano.Lattice.min_then_le
#assert_constructive Peano.Lattice.min_eq_of_gt
#assert_constructive Peano.Lattice.max_eq_of_lt
#assert_constructive Peano.Lattice.max_ne_min_of_ne
#assert_constructive Peano.Lattice.if_neq_then_min_xor
#assert_constructive Peano.Lattice.lt_max_of_ne
#assert_constructive Peano.Lattice.le_then_max_eq_right
#assert_constructive Peano.Lattice.le_then_max_eq_left
#assert_constructive Peano.Lattice.le_max_right
#assert_constructive Peano.Lattice.max_le
#assert_constructive Peano.Lattice.max_assoc
#assert_constructive Peano.Lattice.le_then_min_eq_left
#assert_constructive Peano.Lattice.le_then_min_eq_right
#assert_constructive Peano.Lattice.min_le_right
#assert_constructive Peano.Lattice.le_min
#assert_constructive Peano.Lattice.min_assoc
#assert_constructive Peano.Lattice.not_exists_max
#assert_constructive Peano.Lattice.max_distrib_min
#assert_constructive Peano.Lattice.min_distrib_max
#assert_constructive Peano.Lattice.isomorph_Λ_max
#assert_constructive Peano.Lattice.isomorph_Λ_min
#assert_constructive Peano.Lattice.isomorph_Ψ_max
#assert_constructive Peano.Lattice.isomorph_Ψ_min
#assert_constructive Peano.Lattice.max_eq_left
#assert_constructive Peano.Lattice.max_eq_right
#assert_constructive Peano.Lattice.min_eq_left
#assert_constructive Peano.Lattice.min_eq_right
#assert_constructive Peano.Lattice.le_a_le_b_then_le_min_a_b_left
#assert_constructive Peano.Lattice.le_min_a_b_then_le_a_le_b_left
#assert_constructive Peano.Lattice.le_a_le_b_then_le_min_a_b_right
#assert_constructive Peano.Lattice.le_a_le_b_then_le_max_a_b_right
#assert_constructive Peano.Lattice.le_max_a_b_then_le_a_le_b_right
#assert_constructive Peano.Lattice.le_a_le_b_then_le_max_a_b_left
#assert_constructive Peano.Lattice.max_min_self
#assert_constructive Peano.Lattice.min_max_self
#assert_constructive Peano.Lattice.min_le_max
#assert_constructive Peano.Lattice.max_eq_left_iff
#assert_constructive Peano.Lattice.max_eq_right_iff
#assert_constructive Peano.Lattice.min_eq_left_iff
#assert_constructive Peano.Lattice.min_eq_right_iff
#assert_constructive Peano.Lattice.max_le_iff
#assert_constructive Peano.Lattice.le_min_iff
#assert_constructive Peano.Lattice.max_le_max
#assert_constructive Peano.Lattice.min_le_min
#assert_constructive Peano.Lattice.max_left_comm
#assert_constructive Peano.Lattice.min_left_comm
#assert_constructive Peano.Lattice.max_right_comm
#assert_constructive Peano.Lattice.min_right_comm
#assert_constructive Peano.Lattice.max_succ_succ
#assert_constructive Peano.Lattice.min_succ_succ

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Decidable.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Order.ble_iff_Le

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Sqrt.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Sqrt.sqrt_zero
#assert_constructive Peano.Sqrt.sqrtRem_zero
#assert_constructive Peano.Sqrt.sqrt_one
#assert_constructive Peano.Sqrt.sqrtRem_one
#assert_constructive Peano.Sqrt.sqrtRem_lt
#assert_constructive Peano.Sqrt.csqrt
#assert_constructive Peano.Sqrt.csqrt_zero
#assert_constructive Peano.Sqrt.csqrt_one
#assert_constructive Peano.Sqrt.le_csqrt_sq
#assert_constructive Peano.Sqrt.csqrt_lower

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Log.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Log.log_zero
#assert_constructive Peano.Log.logRem_zero
#assert_constructive Peano.Log.log_of_lt
#assert_constructive Peano.Log.logRem_of_lt
#assert_constructive Peano.Log.log_one
#assert_constructive Peano.Log.logRem_one
#assert_constructive Peano.Log.clog
#assert_constructive Peano.Log.clog_zero
#assert_constructive Peano.Log.clog_one
#assert_constructive Peano.Log.le_clog_pow
#assert_constructive Peano.Log.clog_lower

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Digits.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Digits.toValues
#assert_constructive Peano.Digits.ofDigitsFin
#assert_constructive Peano.Digits.digits_zero
#assert_constructive Peano.Digits.ofDigits_nil
#assert_constructive Peano.Digits.ofDigits_cons
#assert_constructive Peano.Digits.toValues_nil
#assert_constructive Peano.Digits.toValues_cons
#assert_constructive Peano.Digits.numDigits_zero

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Tuple.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.NatsTuple
#assert_constructive Peano.HTuple
#assert_constructive Peano.tailTuple
#assert_constructive Peano.mkTuple
#assert_constructive Peano.tupleDecEq
#assert_constructive Peano.tupleRepr
#assert_constructive Peano.emptyNatsTuple
#assert_constructive Peano.consNatsTuple
#assert_constructive Peano.headNatsTuple
#assert_constructive Peano.tailNatsTuple
#assert_constructive Peano.mkNatsTuple
#assert_constructive Peano.instDecidableEqNatsType
#assert_constructive Peano.instReprNatsType
#assert_constructive Peano.natsTupleDecEq
#assert_constructive Peano.natsTupleRepr
#assert_constructive Peano.emptyHTuple
#assert_constructive Peano.consHTuple
#assert_constructive Peano.headHTuple
#assert_constructive Peano.tailHTuple
#assert_constructive Peano.mkHTuple
#assert_constructive Peano.HTupleRepr
#assert_constructive Peano.instHTupleReprNil
#assert_constructive Peano.instHTupleReprCons
#assert_constructive Peano.htupleRepr
#assert_constructive Peano.lexLt
#assert_constructive Peano.lexLe
#assert_constructive Peano.instLTTuple
#assert_constructive Peano.instLETuple
#assert_constructive Peano.instDecidableRelLtTuple
#assert_constructive Peano.instDecidableRelLeTuple
#assert_constructive Peano.instDecidableRelLeTuple'
#assert_constructive Peano.instDecidableEqTuple
#assert_constructive Peano.lexLt_irrefl
#assert_constructive Peano.lexLt_trich
#assert_constructive Peano.instStrictLinearOrderTuple
#assert_constructive Peano.instIrreflTuple
#assert_constructive Peano.instAsymmTuple
#assert_constructive Peano.instTransTuple
#assert_constructive Peano.instTrichotomousTuple
#assert_constructive Peano.instIrreflLTTuple
#assert_constructive Peano.natsVal
#assert_constructive Peano.natsLexLt
#assert_constructive Peano.natsLexLe
#assert_constructive Peano.instLTNatsTuple
#assert_constructive Peano.instLENatsTuple
#assert_constructive Peano.instDecidableRelLtNatsTuple
#assert_constructive Peano.instDecidableRelLeNatsTuple
#assert_constructive Peano.HTupleDecidableEq
#assert_constructive Peano.instHTupleDecEqNil
#assert_constructive Peano.instHTupleDecEqCons
#assert_constructive Peano.htupleDecEq
#assert_constructive Peano.HTupleLT
#assert_constructive Peano.instHTupleLTNil
#assert_constructive Peano.instHTupleLTCons
#assert_constructive Peano.instLTHTuple
#assert_constructive Peano.HTupleLE
#assert_constructive Peano.instHTupleLENil
#assert_constructive Peano.instHTupleLECons
#assert_constructive Peano.instLEHTuple
#assert_constructive Peano.hlexLt
#assert_constructive Peano.hlexLe
#assert_constructive Peano.HTupleDecidableLT
#assert_constructive Peano.instHTupleDecLTNil
#assert_constructive Peano.instHTupleDecLTCons
#assert_constructive Peano.instDecidableRelLtHTuple
#assert_constructive Peano.HTupleDecidableLE
#assert_constructive Peano.instHTupleDecLENil
#assert_constructive Peano.instHTupleDecLECons
#assert_constructive Peano.instDecidableRelLeHTuple

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Pairing.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Pairing.pairAux
#assert_constructive Peano.Pairing.tri_zero
#assert_constructive Peano.Pairing.tri_succ
#assert_constructive Peano.Pairing.cantorPair_zero_zero
#assert_constructive Peano.Pairing.cantorUnpair_zero
#assert_constructive Peano.Pairing.pairAux_spec
#assert_constructive Peano.Pairing.pairAux_bound
#assert_constructive Peano.Pairing.cantorPair_injective

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Pow.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Pow.pow_zero
#assert_constructive Peano.Pow.zero_pow
#assert_constructive Peano.Pow.one_pow
#assert_constructive Peano.Pow.pow_one
#assert_constructive Peano.Pow.pow_succ
#assert_constructive Peano.Pow.pow_gt
#assert_constructive Peano.Pow.pow_ge_one
#assert_constructive Peano.Pow.pow_lt_succ_base
#assert_constructive Peano.Pow.pow_lt_succ_base_strong
#assert_constructive Peano.Pow.pow_lt_succ_exp
#assert_constructive Peano.Pow.pow_add_eq_mul_pow
#assert_constructive Peano.Pow.mul_pow_n_m_pow_k_m_eq_pow_nk_m
#assert_constructive Peano.Pow.pow_pow_eq_pow_mul
#assert_constructive Peano.Pow.pow_ne_zero
#assert_constructive Peano.Pow.pow_two
#assert_constructive Peano.Pow.pow_eq_zero_iff
#assert_constructive Peano.Pow.one_lt_pow
#assert_constructive Peano.Pow.pow_eq_one_iff
#assert_constructive Peano.Pow.pow_lt_mono_exp
#assert_constructive Peano.Pow.pow_le_pow_right
#assert_constructive Peano.Pow.pow_lt_mono_base
#assert_constructive Peano.Pow.pow_le_pow_left
#assert_constructive Peano.Pow.pow_mul_comm
#assert_constructive Peano.Pow.isomorph_Ψ_pow
#assert_constructive Peano.Pow.isomorph_Λ_pow
#assert_constructive Peano.Pow.n_le_two_pow_n

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Factorial.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Factorial.factorial
#assert_constructive Peano.Factorial.factorial_one
#assert_constructive Peano.Factorial.factorial_two
#assert_constructive Peano.Factorial.factorial_le_succ
#assert_constructive Peano.Factorial.factorial_le_mono

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Fibonacci.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Fibonacci.fibPair
#assert_constructive Peano.Fibonacci.fib
#assert_constructive Peano.Fibonacci.fibList
#assert_constructive Peano.Fibonacci.fib_two
#assert_constructive Peano.Fibonacci.fibList_zero
#assert_constructive Peano.Fibonacci.fibList_succ

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Summation.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Summation.finSum
#assert_constructive Peano.Summation.finSum_zero_fn
#assert_constructive Peano.Summation.finSum_mul_const
#assert_constructive Peano.Summation.finSum_mul_const_right
#assert_constructive Peano.Summation.finSum_le_of_le
#assert_constructive Peano.Summation.finSum_pos
#assert_constructive Peano.Summation.finSum_const
#assert_constructive Peano.Summation.finSum_succ_left
#assert_constructive Peano.Summation.finSum_reverse
#assert_constructive Peano.Summation.sum_list
#assert_constructive Peano.Summation.sum_list_nil
#assert_constructive Peano.Summation.sum_list_cons
#assert_constructive Peano.Summation.sum_list_append
#assert_constructive Peano.Summation.sum_list_singleton

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Binom.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Binom.binom
#assert_constructive Peano.Binom.binom_zero_zero
#assert_constructive Peano.Binom.binom_zero_succ
#assert_constructive Peano.Binom.binom_succ_zero
#assert_constructive Peano.Binom.binom_n_zero
#assert_constructive Peano.Binom.binom_n_one
#assert_constructive Peano.Binom.binom_eq_zero_of_gt
#assert_constructive Peano.Binom.binom_one
#assert_constructive Peano.Binom.binom_succ_n_by_n
#assert_constructive Peano.Binom.prime_dvd_binom_prime
#assert_constructive Peano.Binom.binom_prime_row
#assert_constructive Peano.Binom.binom_pr_p_mod
#assert_constructive Peano.Binom.binom_pow_p_mod

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: NewtonBinom.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.NewtonBinom.binomTerm
#assert_constructive Peano.NewtonBinom.binomTerm_zero
#assert_constructive Peano.NewtonBinom.binomTerm_self
#assert_constructive Peano.NewtonBinom.pow_add_split
#assert_constructive Peano.NewtonBinom.exists_nm_growth

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Product.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Product.product_list
#assert_constructive Peano.Product.product_nil
#assert_constructive Peano.Product.product_cons
#assert_constructive Peano.Product.product_append
#assert_constructive Peano.Product.product_list_singleton
#assert_constructive Peano.Product.finProd
#assert_constructive Peano.Product.finProd_zero
#assert_constructive Peano.Product.finProd_succ
#assert_constructive Peano.Product.finProd_one_fn
#assert_constructive Peano.Product.finProd_zero_fn
#assert_constructive Peano.Product.finProd_succ_left
#assert_constructive Peano.Factorization.factorValue
#assert_constructive Peano.Factorization.product_factorization
#assert_constructive Peano.Factorization.product_factorization_empty
#assert_constructive Peano.Factorization.product_factorization_singleton

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Perm.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Perm.FunPerm.comp
#assert_constructive Peano.Perm.Sym

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: ModEq.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.ModEq.mod_zero_right
#assert_constructive Peano.ModEq.mod_zero_left
#assert_constructive Peano.ModEq.mod_self
#assert_constructive Peano.ModEq.mod_mod
#assert_constructive Peano.ModEq.add_mod
#assert_constructive Peano.ModEq.mul_mod
#assert_constructive Peano.ModEq.ModEq
#assert_constructive Peano.ModEq.modEq_zero_of_dvd
#assert_constructive Peano.ModEq.modEq_mod
#assert_constructive Peano.ModEq.modEq_one
#assert_constructive Peano.ModEq.modEq_add_right
#assert_constructive Peano.ModEq.instDecidableModEq

-- Comprobaciones: ChineseRemainder.lean (resto) -- (sin simbolos nuevos; todos ya cubiertos/excluidos)

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Totient.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Totient.lengthₚ_append
#assert_constructive Peano.Totient.lengthₚ_singleton
#assert_constructive Peano.Totient.lengthₚ_range_from_one
#assert_constructive Peano.Totient.lengthₚ_filter_le
#assert_constructive Peano.Totient.filter_append_singleton
#assert_constructive Peano.Totient.filter_all_true
#assert_constructive Peano.Totient.mem_range_from_one_pos
#assert_constructive Peano.Totient.mem_range_from_one_le
#assert_constructive Peano.Totient.totient
#assert_constructive Peano.Totient.totient_zero
#assert_constructive Peano.Totient.totient_one
#assert_constructive Peano.Totient.totient_two
#assert_constructive Peano.Totient.totient_le
#assert_constructive Peano.Totient.totient_pos
#assert_constructive Peano.Totient.totient_prime
#assert_constructive Peano.Totient.instDecidableEqTotient

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Wilson.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Wilson.modInv
#assert_constructive Peano.Wilson.modInv_lt
#assert_constructive Peano.Wilson.modInv_mul
#assert_constructive Peano.Wilson.modInv_pos

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Fermat.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Fermat.fermat_little_theorem

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: NumberSets.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.NumberSets.IsPrime
#assert_constructive Peano.NumberSets.CoprimesOf
#assert_constructive Peano.NumberSets.DivisorsOf
#assert_constructive Peano.NumberSets.MultiplesOf
#assert_constructive Peano.NumberSets.isPrimeb
#assert_constructive Peano.NumberSets.coprimeb
#assert_constructive Peano.NumberSets.divisorsFSet
#assert_constructive Peano.NumberSets.primesFSet
#assert_constructive Peano.NumberSets.coprimesFSet
#assert_constructive Peano.NumberSets.multiplesFSet

-- Comprobaciones: CantorPairing.lean (resto) -- (sin simbolos nuevos; todos ya cubiertos/excluidos)

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GodelBeta.lean (resto)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.GodelBeta.godelB
#assert_constructive Peano.GodelBeta.godelC
#assert_constructive Peano.GodelBeta.godelC_spec

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: PeanoSystem.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.PeanoSystem.PeanoSystem
#assert_constructive Peano.PeanoSystem.PeanoMorphism
#assert_constructive Peano.PeanoSystem.isPeanoIso
#assert_constructive Peano.PeanoSystem.compMorph
#assert_constructive Peano.PeanoSystem.idMorph

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Initiality.lean (solo simbolos CONSTRUCTIVOS sobre N0 concreto; ver exclusiones)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Initiality.ℕ₀_prim_rec
#assert_constructive Peano.Initiality.ℕ₀_PeanoSystem
#assert_constructive Peano.Initiality.ℕ₀_to
#assert_constructive Peano.Initiality.ℕ₀_to_zero
#assert_constructive Peano.Initiality.ℕ₀_to_succ
#assert_constructive Peano.Initiality.ℕ₀_to_morph
#assert_constructive Peano.Initiality.ℕ₀_initial
#assert_constructive Peano.Initiality.ℕ₀_morph_unique
#assert_constructive Peano.Initiality.ℕ₀_rec_principle

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: List.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.List.instDecidableEqN1
#assert_constructive Peano.List.instDecidableEqN2
#assert_constructive Peano.List.instLTN1
#assert_constructive Peano.List.instLEN1
#assert_constructive Peano.List.instLTN2
#assert_constructive Peano.List.instLEN2
#assert_constructive Peano.List.decidableLtN1
#assert_constructive Peano.List.decidableLeN1
#assert_constructive Peano.List.decidableLtN2
#assert_constructive Peano.List.decidableLeN2
#assert_constructive Peano.List.instStrictLinearOrderNat1
#assert_constructive Peano.List.instStrictLinearOrderNat2
#assert_constructive Peano.List.lexLt
#assert_constructive Peano.List.instLTProdN2N1
#assert_constructive Peano.List.decidableLexLt
#assert_constructive Peano.List.lengthₚ
#assert_constructive Peano.List.lengthₚ_nil
#assert_constructive Peano.List.lengthₚ_cons
#assert_constructive Peano.List.Sorted
#assert_constructive Peano.List.sorted_nil
#assert_constructive Peano.List.sorted_singleton
#assert_constructive Peano.List.decidableMemList
#assert_constructive Peano.List.Nat0List
#assert_constructive Peano.List.Nat1List
#assert_constructive Peano.List.Nat2List
#assert_constructive Peano.List.FactList
#assert_constructive Peano.List.Fin₀
#assert_constructive Peano.List.instDecidableEqFin0
#assert_constructive Peano.List.DigitList
#assert_constructive Peano.List.TupleList
#assert_constructive Peano.List.NatsTupleList
#assert_constructive Peano.List.GTupleList
#assert_constructive Peano.List.HTupleList
#assert_constructive Peano.List.PeanoVal
#assert_constructive Peano.List.instDecidableEqPeanoVal
#assert_constructive Peano.List.PeanoValList
#assert_constructive Peano.List.getDₚ
#assert_constructive Peano.List.getDₚ_cons_zero
#assert_constructive Peano.List.getDₚ_cons_succ
#assert_constructive Peano.List.getDₚ_mem
#assert_constructive Peano.List.List.indexOfₚ
#assert_constructive Peano.List.List.indexOfₚ_nil
#assert_constructive Peano.List.List.indexOfₚ_cons_eq
#assert_constructive Peano.List.List.indexOfₚ_cons_ne
#assert_constructive Peano.List.getDₚ_indexOfₚ
#assert_constructive Peano.List.List.indexOfₚ_lt_length
#assert_constructive Peano.List.natsKindLt
#assert_constructive Peano.List.instLTNats
#assert_constructive Peano.List.instLENats
#assert_constructive Peano.List.instDecidableRelLtNats
#assert_constructive Peano.List.instDecidableRelLeNats
#assert_constructive Peano.List.peanoValEncode
#assert_constructive Peano.List.instLTPeanoVal
#assert_constructive Peano.List.instLEPeanoVal
#assert_constructive Peano.List.instDecidableRelLtPeanoVal
#assert_constructive Peano.List.instDecidableRelLePeanoVal
#assert_constructive Peano.List.instReprPeanoVal
#assert_constructive Peano.List.instIrreflListLt
#assert_constructive Peano.List.instAsymmListLt
#assert_constructive Peano.List.instTrichotomousListLt
#assert_constructive Peano.List.instLEList
#assert_constructive Peano.List.instDecidableLeList

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: FSet.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.FSet.FSet
#assert_constructive Peano.FSet.FSet.ext
#assert_constructive Peano.FSet.FSet.eq_of_mem_iff
#assert_constructive Peano.FSet.FSet.eq_of_mem_iff'
#assert_constructive Peano.FSet.ℕ₀FSet
#assert_constructive Peano.FSet.ℕ₁FSet
#assert_constructive Peano.FSet.ℕ₂FSet
#assert_constructive Peano.FSet.NatsFSet
#assert_constructive Peano.FSet.FactFSet
#assert_constructive Peano.FSet.UniqueKeys
#assert_constructive Peano.FSet.SortedByKey
#assert_constructive Peano.FSet.sortedByKey_imp_uniqueKeys
#assert_constructive Peano.FSet.sortedInsert
#assert_constructive Peano.FSet.mem_sortedInsert_iff
#assert_constructive Peano.FSet.sorted_sortedInsert
#assert_constructive Peano.FSet.sortedByKey_factListAddFactor
#assert_constructive Peano.FSet.uniqueKeys_factListAddFactor
#assert_constructive Peano.FSet.TupleFSet
#assert_constructive Peano.FSet.NatsTupleFSet
#assert_constructive Peano.FSet.GTupleFSet
#assert_constructive Peano.FSet.HTupleFSet
#assert_constructive Peano.FSet.ℕ₀FSet.Fin₀Set
#assert_constructive Peano.FSet.ℕ₀FSet.mem_Fin₀Set_iff
#assert_constructive Peano.FSet.ℕ₀FSet.Fin₀Set_card
#assert_constructive Peano.FSet.Nat0ListFSet
#assert_constructive Peano.FSet.Nat1ListFSet
#assert_constructive Peano.FSet.Nat2ListFSet
#assert_constructive Peano.FSet.NatsListFSet
#assert_constructive Peano.FSet.TupleListFSet
#assert_constructive Peano.FSet.NatsTupleListFSet
#assert_constructive Peano.FSet.GTupleListFSet
#assert_constructive Peano.FSet.HTupleListFSet
#assert_constructive Peano.FSet.PeanoValFSet
#assert_constructive Peano.FSet.Nat0FSetFSet
#assert_constructive Peano.FSet.sortedInsertFSet
#assert_constructive Peano.FSet.sortFSetList
#assert_constructive Peano.FSet.mem_sortedInsertFSet_iff
#assert_constructive Peano.FSet.sorted_sortedInsertFSet
#assert_constructive Peano.FSet.sorted_sortFSetList
#assert_constructive Peano.FSet.mem_sortFSetList_iff
#assert_constructive Peano.FSet.sortedInsert'
#assert_constructive Peano.FSet.sortList'
#assert_constructive Peano.FSet.mem_sortedInsert'_iff
#assert_constructive Peano.FSet.sorted_sortedInsert'
#assert_constructive Peano.FSet.sorted_sortList'
#assert_constructive Peano.FSet.mem_sortList'_iff
#assert_constructive Peano.FSet.FSet.ofList
#assert_constructive Peano.FSet.FSet.mem_ofList_iff
#assert_constructive Peano.FSet.FSet.insert
#assert_constructive Peano.FSet.mem_insert_iff
#assert_constructive Peano.FSet.FSet.union
#assert_constructive Peano.FSet.mem_union_iff
#assert_constructive Peano.FSet.FSet.inter
#assert_constructive Peano.FSet.mem_inter_iff
#assert_constructive Peano.FSet.FSet.image
#assert_constructive Peano.FSet.mem_image_iff
#assert_constructive Peano.FSet.FSet.quotient
#assert_constructive Peano.FSet.mem_quotient_classes

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: FSetFunction.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.FSetFunction.card_eq_mul_of_uniform_fibers
#assert_constructive Peano.FSetFunction.MapOn
#assert_constructive Peano.FSetFunction.MapOn.comp
#assert_constructive Peano.FSetFunction.InjectiveOn
#assert_constructive Peano.FSetFunction.SurjectiveOn
#assert_constructive Peano.FSetFunction.MapOn.Injective
#assert_constructive Peano.FSetFunction.MapOn.Surjective
#assert_constructive Peano.FSetFunction.MapOn.Bijective
#assert_constructive Peano.FSetFunction.MapOn.comp_injective
#assert_constructive Peano.FSetFunction.MapOn.comp_surjective
#assert_constructive Peano.FSetFunction.MapOn.comp_bijective
#assert_constructive Peano.FSetFunction.MapOn.comp_assoc
#assert_constructive Peano.FSetFunction.MapOn.id
#assert_constructive Peano.FSetFunction.MapOn.id_injective
#assert_constructive Peano.FSetFunction.MapOn.id_surjective
#assert_constructive Peano.FSetFunction.MapOn.id_bijective
#assert_constructive Peano.FSetFunction.MapOn.comp_id
#assert_constructive Peano.FSetFunction.MapOn.id_comp
#assert_constructive Peano.FSetFunction.MapOn.injective_of_comp_injective
#assert_constructive Peano.FSetFunction.MapOn.surjective_of_comp_surjective
#assert_constructive Peano.FSetFunction.MapOn.Im
#assert_constructive Peano.FSetFunction.MapOn.rightInverse
#assert_constructive Peano.FSetFunction.MapOn.rightInverse_prop
#assert_constructive Peano.FSetFunction.MapOn.rightInverse_injective
#assert_constructive Peano.FSetFunction.MapOn.leftInverse
#assert_constructive Peano.FSetFunction.MapOn.leftInverse_prop
#assert_constructive Peano.FSetFunction.MapOn.leftInverse_surjective
#assert_constructive Peano.FSetFunction.MapOn.injective_of_has_leftInverse
#assert_constructive Peano.FSetFunction.MapOn.injective_iff_has_leftInverse
#assert_constructive Peano.FSetFunction.MapOn.surjective_of_has_rightInverse
#assert_constructive Peano.FSetFunction.MapOn.surjective_iff_has_rightInverse
#assert_constructive Peano.FSetFunction.MapOn.bijective_of_injective_leftInverse_injective
#assert_constructive Peano.FSetFunction.MapOn.bijective_of_surjective_rightInverse_surjective
#assert_constructive Peano.FSetFunction.MapOn.inverse
#assert_constructive Peano.FSetFunction.MapOn.inverse_left_prop
#assert_constructive Peano.FSetFunction.MapOn.inverse_right_prop
#assert_constructive Peano.FSetFunction.MapOn.inverse_injective
#assert_constructive Peano.FSetFunction.MapOn.inverse_surjective
#assert_constructive Peano.FSetFunction.MapOn.inverse_bijective
#assert_constructive Peano.FSetFunction.MapOn.inverse_inverse
#assert_constructive Peano.FSetFunction.MapOn.comp_inverse_left
#assert_constructive Peano.FSetFunction.MapOn.comp_inverse_right
#assert_constructive Peano.FSetFunction.card_image_of_injective
#assert_constructive Peano.FSetFunction.injective_of_card_image
#assert_constructive Peano.FSetFunction.card_image_of_surjective
#assert_constructive Peano.FSetFunction.surjective_of_card_image
#assert_constructive Peano.FSetFunction.MapOn.injective_iff_surjective_of_card_eq
#assert_constructive Peano.FSetFunction.MapOn.injective_iff_bijective_of_card_eq
#assert_constructive Peano.FSetFunction.MapOn.surjective_iff_bijective_of_card_eq
#assert_constructive Peano.FSetFunction.MapOn.leftInverse_eq_inverse_of_card_eq
#assert_constructive Peano.FSetFunction.MapOn.leftInverse_right_prop_of_card_eq
#assert_constructive Peano.FSetFunction.MapOn.rightInverse_eq_inverse_of_card_eq
#assert_constructive Peano.FSetFunction.MapOn.rightInverse_left_prop_of_card_eq
#assert_constructive Peano.FSetFunction.card_le_of_injective
#assert_constructive Peano.FSetFunction.card_le_of_surjective
#assert_constructive Peano.FSetFunction.not_injective_of_card_lt
#assert_constructive Peano.FSetFunction.collision_of_card_lt
#assert_constructive Peano.FSetFunction.card_eq_of_injections
#assert_constructive Peano.FSetFunction.card_eq_of_surjections
#assert_constructive Peano.FSetFunction.MapOn.Bijective.card_eq
#assert_constructive Peano.FSetFunction.MapOn.endo_injective_iff_surjective
#assert_constructive Peano.FSetFunction.MapOn.endo_injective_iff_bijective
#assert_constructive Peano.FSetFunction.MapOn.endo_surjective_iff_bijective
#assert_constructive Peano.FSetFunction.MapOn.endo_bijective_of_injective
#assert_constructive Peano.FSetFunction.MapOn.endo_bijective_of_surjective
#assert_constructive Peano.FSetFunction.MapOn.endo_leftInverse_eq_inverse
#assert_constructive Peano.FSetFunction.MapOn.endo_leftInverse_right_prop
#assert_constructive Peano.FSetFunction.MapOn.endo_rightInverse_eq_inverse
#assert_constructive Peano.FSetFunction.MapOn.endo_rightInverse_left_prop
#assert_constructive Peano.FSetFunction.Perm
#assert_constructive Peano.FSetFunction.Perm.injective
#assert_constructive Peano.FSetFunction.Perm.surjective
#assert_constructive Peano.FSetFunction.Perm.id
#assert_constructive Peano.FSetFunction.Perm.comp
#assert_constructive Peano.FSetFunction.Perm.comp_id_fn
#assert_constructive Peano.FSetFunction.Perm.id_comp_fn
#assert_constructive Peano.FSetFunction.Perm.inv
#assert_constructive Peano.FSetFunction.Perm.inv_left
#assert_constructive Peano.FSetFunction.Perm.inv_right
#assert_constructive Peano.FSetFunction.Perm.inv_inv
#assert_constructive Peano.FSetFunction.Perm.comp_inv_left
#assert_constructive Peano.FSetFunction.Perm.comp_inv_right
#assert_constructive Peano.FSetFunction.Perm.comp_assoc
#assert_constructive Peano.FSetFunction.MapOn.PreIm
#assert_constructive Peano.FSetFunction.MapOn.mem_PreIm_iff
#assert_constructive Peano.FSetFunction.MapOn.PreIm_full
#assert_constructive Peano.FSetFunction.MapOn.card_PreIm_le
#assert_constructive Peano.FSetFunction.MapOn.fiber
#assert_constructive Peano.FSetFunction.MapOn.mem_fiber_iff
#assert_constructive Peano.FSetFunction.MapOn.card_fiber_le_one_of_injective
#assert_constructive Peano.FSetFunction.MapOn.restrict
#assert_constructive Peano.FSetFunction.MapOn.restrict_injective
#assert_constructive Peano.FSetFunction.MapOn.mem_Im_restrict
#assert_constructive Peano.FSetFunction.BinOpOn
#assert_constructive Peano.FSetFunction.FunTable
#assert_constructive Peano.FSetFunction.FunTable.apply
#assert_constructive Peano.FSetFunction.FunTable.applyElem
#assert_constructive Peano.FSetFunction.FunTable.applyElem_mem
#assert_constructive Peano.FSetFunction.FunTable.id
#assert_constructive Peano.FSetFunction.FunTable.comp
#assert_constructive Peano.FSetFunction.FunPerm
#assert_constructive Peano.FSetFunction.FunPerm.id
#assert_constructive Peano.FSetFunction.FunPerm.applyElem_injective
#assert_constructive Peano.FSetFunction.sorted_nodup
#assert_constructive Peano.FSetFunction.nodup_map_of_inj_on
#assert_constructive Peano.FSetFunction.nodup_subset_length_le
#assert_constructive Peano.FSetFunction.perm_of_nodup_subset_same_length
#assert_constructive Peano.FSetFunction.perm_map_of_injective_on_nodup

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: EquivRel.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.EquivRel.EquivRelOn
#assert_constructive Peano.EquivRel.EquivRelOn.classOf
#assert_constructive Peano.EquivRel.EquivRelOn.mem_classOf_iff
#assert_constructive Peano.EquivRel.EquivRelOn.classOf_nonempty_of_mem
#assert_constructive Peano.EquivRel.EquivRelOn.classOf_subset_domain
#assert_constructive Peano.EquivRel.EquivRelOn.rel_of_mem_classOf
#assert_constructive Peano.EquivRel.EquivRelOn.mem_classOf_of_rel
#assert_constructive Peano.EquivRel.EquivRelOn.classOf_eq_of_mem_classOf
#assert_constructive Peano.EquivRel.EquivRelOn.mem_classOf_iff_of_rel
#assert_constructive Peano.EquivRel.EquivRelOn.classOf_eq_or_disjoint
#assert_constructive Peano.EquivRel.EquivRelOn.ClassFamily
#assert_constructive Peano.EquivRel.EquivRelOn.canonicalClassFamily
#assert_constructive Peano.EquivRel.EquivRelOn.classes
#assert_constructive Peano.EquivRel.EquivRelOn.mem_classes_iff
#assert_constructive Peano.EquivRel.EquivRelOn.classOf_mem_classes_of_mem
#assert_constructive Peano.EquivRel.EquivRelOn.mem_classes_elim
#assert_constructive Peano.EquivRel.EquivRelOn.classes_cover

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Group.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Group.FinGroup
#assert_constructive Peano.Group.ℕ₀FinGroup
#assert_constructive Peano.Group.id_unique
#assert_constructive Peano.Group.inv_mem
#assert_constructive Peano.Group.op_mem
#assert_constructive Peano.Group.op_cancel_left
#assert_constructive Peano.Group.op_cancel_right
#assert_constructive Peano.Group.inv_inv_eq
#assert_constructive Peano.Group.inv_id_eq
#assert_constructive Peano.Group.inv_op_eq
#assert_constructive Peano.Group.inv_unique
#assert_constructive Peano.Group.gpow
#assert_constructive Peano.Group.gpow_zero
#assert_constructive Peano.Group.gpow_succ
#assert_constructive Peano.Group.gpow_one
#assert_constructive Peano.Group.gpow_mem
#assert_constructive Peano.Group.gpow_add
#assert_constructive Peano.Group.gpow_comm_single
#assert_constructive Peano.Group.gpow_inv
#assert_constructive Peano.Group.order
#assert_constructive Peano.Group.order_pos
#assert_constructive Peano.Group.gpow_order_eq_id
#assert_constructive Peano.Group.order_ne_zero
#assert_constructive Peano.Group.order_minimal
#assert_constructive Peano.Group.order_le_card
#assert_constructive Peano.Group.gpow_mul_order_eq_id
#assert_constructive Peano.Group.gpow_mod_order
#assert_constructive Peano.Group.Subgroup
#assert_constructive Peano.Group.Subgroup.op_inv_closed
#assert_constructive Peano.Group.subgroup_of_op_inv_closed
#assert_constructive Peano.Group.trivialSubgroup
#assert_constructive Peano.Group.improperSubgroup
#assert_constructive Peano.Group.Subgroup.IsTrivial
#assert_constructive Peano.Group.Subgroup.IsProper
#assert_constructive Peano.Group.cyclicCarrier
#assert_constructive Peano.Group.cyclicCarrier_id_in
#assert_constructive Peano.Group.cyclicCarrier_mem_iff
#assert_constructive Peano.Group.cyclicSubgroup
#assert_constructive Peano.Group.cyclicSubgroup'
#assert_constructive Peano.Group.Subgroup.IsNormal
#assert_constructive Peano.Group.trivialSubgroup_normal
#assert_constructive Peano.Group.improperSubgroup_normal
#assert_constructive Peano.Group.Subgroup.inter
#assert_constructive Peano.Group.Subgroup.inter_subset_left
#assert_constructive Peano.Group.Subgroup.inter_subset_right
#assert_constructive Peano.Group.Subgroup.inter_normal_of_normal
#assert_constructive Peano.Group.GroupHom
#assert_constructive Peano.Group.Subgroup.ext_carrier
#assert_constructive Peano.Group.Subgroup.carrier_inj
#assert_constructive Peano.Group.instDecidableEqSubgroup
#assert_constructive Peano.Group.instLTSubgroup
#assert_constructive Peano.Group.instStrictLinearOrderSubgroup

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/Action.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Action.GroupAction
#assert_constructive Peano.Action.GroupAction.orb
#assert_constructive Peano.Action.mem_orb_iff
#assert_constructive Peano.Action.GroupAction.stab
#assert_constructive Peano.Action.orbit_stabilizer
#assert_constructive Peano.Action.orbits_partition
#assert_constructive Peano.Action.conjugAction
#assert_constructive Peano.Action.class_equation_split
#assert_constructive Peano.Action.class_equation

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/CorrespondenceTheorem.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.CorrespondenceTheorem.preimageSubgroup
#assert_constructive Peano.CorrespondenceTheorem.mem_preimageSubgroup_iff
#assert_constructive Peano.CorrespondenceTheorem.N_le_preimageSubgroup
#assert_constructive Peano.CorrespondenceTheorem.imageSubgroup_preimage
#assert_constructive Peano.CorrespondenceTheorem.preimageSubgroup_image
#assert_constructive Peano.CorrespondenceTheorem.SubgroupAbove
#assert_constructive Peano.CorrespondenceTheorem.correspondencePhi
#assert_constructive Peano.CorrespondenceTheorem.correspondencePsi
#assert_constructive Peano.CorrespondenceTheorem.correspondencePhi_psi
#assert_constructive Peano.CorrespondenceTheorem.correspondencePsi_phi
#assert_constructive Peano.CorrespondenceTheorem.correspondenceInjective
#assert_constructive Peano.CorrespondenceTheorem.correspondenceSurjective
#assert_constructive Peano.CorrespondenceTheorem.preimage_subgroup_card

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/FirstIsomorphism.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.FirstIsomorphism.Subgroup.toFinGroup
#assert_constructive Peano.FirstIsomorphism.homKer
#assert_constructive Peano.FirstIsomorphism.mem_homKer_iff
#assert_constructive Peano.FirstIsomorphism.homImg
#assert_constructive Peano.FirstIsomorphism.mem_homImg_iff
#assert_constructive Peano.FirstIsomorphism.homKer_isNormal
#assert_constructive Peano.FirstIsomorphism.quotientHomomorphism_surjective
#assert_constructive Peano.FirstIsomorphism.homImgInclusion
#assert_constructive Peano.FirstIsomorphism.homImgInclusion_injective
#assert_constructive Peano.FirstIsomorphism.firstIsoMap
#assert_constructive Peano.FirstIsomorphism.firstIsoMap_welldefined
#assert_constructive Peano.FirstIsomorphism.firstIsoMap_op
#assert_constructive Peano.FirstIsomorphism.firstIsoMap_injective
#assert_constructive Peano.FirstIsomorphism.firstIsoMap_surjective
#assert_constructive Peano.FirstIsomorphism.firstIsoMap_bijective

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/NormalSubgroup.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.NormalSubgroup.centralizer
#assert_constructive Peano.NormalSubgroup.mem_centralizer_iff
#assert_constructive Peano.NormalSubgroup.center
#assert_constructive Peano.NormalSubgroup.mem_center_iff
#assert_constructive Peano.NormalSubgroup.center_isNormal
#assert_constructive Peano.NormalSubgroup.central_subgroup_isNormal
#assert_constructive Peano.NormalSubgroup.normalizer
#assert_constructive Peano.NormalSubgroup.mem_normalizer_iff
#assert_constructive Peano.NormalSubgroup.H_subset_normalizer
#assert_constructive Peano.NormalSubgroup.isNormal_iff_normalizer_eq_G
#assert_constructive Peano.NormalSubgroup.rightCoset
#assert_constructive Peano.NormalSubgroup.mem_rightCoset_iff
#assert_constructive Peano.NormalSubgroup.isNormal_iff_leftCoset_eq_rightCoset

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/QuotientGroup.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.QuotientGroup.quotientCarrier
#assert_constructive Peano.QuotientGroup.mem_quotientCarrier_iff
#assert_constructive Peano.QuotientGroup.mem_quotientCarrier_is_leftCoset
#assert_constructive Peano.QuotientGroup.coset_nonempty_of_mem_quotientCarrier
#assert_constructive Peano.QuotientGroup.leftCoset_mem_cosetClasses
#assert_constructive Peano.QuotientGroup.leftCoset_mem_quotientCarrier
#assert_constructive Peano.QuotientGroup.leftCoset_id_mem_quotientCarrier
#assert_constructive Peano.QuotientGroup.cosetRel_of_leftCoset_eq
#assert_constructive Peano.QuotientGroup.leftCoset_eq_iff_cosetRel
#assert_constructive Peano.QuotientGroup.cosetRepOf
#assert_constructive Peano.QuotientGroup.cosetRepOf_eq_head
#assert_constructive Peano.QuotientGroup.cosetRepOf_mem_C
#assert_constructive Peano.QuotientGroup.cosetRepOf_mem_G
#assert_constructive Peano.QuotientGroup.cosetRepOf_leftCoset_eq
#assert_constructive Peano.QuotientGroup.quotientOp_welldefined
#assert_constructive Peano.QuotientGroup.quotientOp
#assert_constructive Peano.QuotientGroup.quotientInv
#assert_constructive Peano.QuotientGroup.quotientId
#assert_constructive Peano.QuotientGroup.quotientId_mem
#assert_constructive Peano.QuotientGroup.quotientOp_assoc
#assert_constructive Peano.QuotientGroup.quotientOp_id
#assert_constructive Peano.QuotientGroup.quotientOp_inv
#assert_constructive Peano.QuotientGroup.quotientGroup
#assert_constructive Peano.QuotientGroup.quotient_card
#assert_constructive Peano.QuotientGroup.quotientHomomorphism
#assert_constructive Peano.QuotientGroup.quotientHomomorphism_op
#assert_constructive Peano.QuotientGroup.quotientHomomorphism_kernel
#assert_constructive Peano.QuotientGroup.imageSubgroup

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/SecondIsomorphism.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.SecondIsomorphism.subgroupHN
#assert_constructive Peano.SecondIsomorphism.mem_subgroupHN_iff
#assert_constructive Peano.SecondIsomorphism.H_le_subgroupHN
#assert_constructive Peano.SecondIsomorphism.N_le_subgroupHN
#assert_constructive Peano.SecondIsomorphism.N_in_subgroupHN
#assert_constructive Peano.SecondIsomorphism.N_normal_in_subgroupHN
#assert_constructive Peano.SecondIsomorphism.interHN_as_subgroup_H
#assert_constructive Peano.SecondIsomorphism.interHN_as_subgroup_H_isNormal
#assert_constructive Peano.SecondIsomorphism.secondIsoMap
#assert_constructive Peano.SecondIsomorphism.secondIsoMap_welldefined
#assert_constructive Peano.SecondIsomorphism.secondIsoMap_injective
#assert_constructive Peano.SecondIsomorphism.secondIsoMap_surjective
#assert_constructive Peano.SecondIsomorphism.secondIsoMap_bijective

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/ThirdIsomorphism.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.ThirdIsomorphism.cosetRel_N_imp_K
#assert_constructive Peano.ThirdIsomorphism.KmodN_normal
#assert_constructive Peano.ThirdIsomorphism.thirdIsoMap
#assert_constructive Peano.ThirdIsomorphism.thirdIsoMap_welldefined
#assert_constructive Peano.ThirdIsomorphism.thirdIsoMap_op
#assert_constructive Peano.ThirdIsomorphism.thirdIsoMap_id
#assert_constructive Peano.ThirdIsomorphism.thirdIsoMap_inv
#assert_constructive Peano.ThirdIsomorphism.thirdIsoGroupHom
#assert_constructive Peano.ThirdIsomorphism.thirdIsoMap_surjective
#assert_constructive Peano.ThirdIsomorphism.thirdIsoMap_kernel

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/Zassenhaus.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Zassenhaus.prodSubgroup
#assert_constructive Peano.Zassenhaus.mem_prodSubgroup_iff
#assert_constructive Peano.Zassenhaus.N_le_prodSubgroup
#assert_constructive Peano.Zassenhaus.S_le_prodSubgroup
#assert_constructive Peano.Zassenhaus.inter_N_K_normal_in_inter_H_K
#assert_constructive Peano.Zassenhaus.inter_H_M_normal_in_inter_H_K
#assert_constructive Peano.Zassenhaus.prodNKHM
#assert_constructive Peano.Zassenhaus.prodNKHM_normal
#assert_constructive Peano.Zassenhaus.prodN_HK
#assert_constructive Peano.Zassenhaus.prodN_HM
#assert_constructive Peano.Zassenhaus.prodN_HM_le_prodN_HK
#assert_constructive Peano.Zassenhaus.prodN_HM_normal_in_prodN_HK
#assert_constructive Peano.Zassenhaus.zassenhaus_bijection
#assert_constructive Peano.Zassenhaus.zassenhaus_bijection_symm
#assert_constructive Peano.Zassenhaus.zassenhaus_bijection_extremes

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/Sylow/Cosets.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Cosets.leftCoset
#assert_constructive Peano.Cosets.mem_leftCoset_iff
#assert_constructive Peano.Cosets.coset_card_eq_subgroup_card
#assert_constructive Peano.Cosets.cosetRel
#assert_constructive Peano.Cosets.cosetRel_refl
#assert_constructive Peano.Cosets.cosetRel_symm
#assert_constructive Peano.Cosets.cosetRel_trans
#assert_constructive Peano.Cosets.cosetEquivRel
#assert_constructive Peano.Cosets.mem_classOf_cosetEquivRel_iff_leftCoset
#assert_constructive Peano.Cosets.classOf_cosetEquivRel_eq_leftCoset
#assert_constructive Peano.Cosets.classOf_cosetEquivRel_card_eq_subgroup_card
#assert_constructive Peano.Cosets.cosetClassFamily
#assert_constructive Peano.Cosets.mem_some_cosetClassFamily_class
#assert_constructive Peano.Cosets.cosetClasses
#assert_constructive Peano.Cosets.card_eq_subgroup_card_of_mem_cosetClasses
#assert_constructive Peano.Cosets.mem_some_cosetClasses
#assert_constructive Peano.Cosets.cosetClass_eq_classOf_of_mem
#assert_constructive Peano.Cosets.leftCoset_subset_of_rel
#assert_constructive Peano.Cosets.leftCoset_eq_of_rel
#assert_constructive Peano.Cosets.lagrange

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/Sylow/CosetAction.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.CosetAction.coset_conjugate_exists

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: GroupTheory/Sylow/Sylow.lean
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.Sylow.cauchy_minimal
#assert_constructive Peano.Sylow.sylow_lift_from_cauchy
#assert_constructive Peano.Sylow.sylow_first
#assert_constructive Peano.Sylow.sylow_second
#assert_constructive Peano.Sylow.sylow_third

-- Comprobaciones: Isomorph.lean (re-exporta simbolos ya cubiertos arriba; dedup) -- (sin simbolos nuevos; todos ya cubiertos/excluidos)

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Prelim.lean (solo ExistsUnique; choose* excluidos, ver arriba)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.ExistsUnique

-- ───────────────────────────────────────────────────────────────────
-- Comprobaciones: Prelim/ExistsUnique.lean (dedup con Prelim.lean)
-- ───────────────────────────────────────────────────────────────────

#assert_constructive Peano.ExistsUnique.exists

