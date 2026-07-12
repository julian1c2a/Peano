# Referencia Técnica — Proyecto Peano

**Última actualización:** 2026-05-07
**Autor**: Julián Calderón Almendros

> Documentación técnica de referencia para IA y desarrolladores Lean 4. **No** es documentación de usuario final.
> Contiene únicamente lo que está demostrado o construido en los archivos `.lean` (requisito 8).
> **Proyectar** un `.lean` en este archivo = actualizar las secciones correspondientes con todo lo exportable (no privado).

---

## 0. Estructura del Proyecto (requisitos 1–3)

### 0.1. Módulos `.lean`

> 66 build jobs · 0 sorry · 0 errores · Lean 4 v4.29.0 · *Actualizado: 2026-07-12*

| Módulo (ruta) | Namespace | Depende de | Dependido por |
|---|---|---|---|
| `Peano.lean` | — | todos los módulos de `Peano/` | — |
| **Prelim** | | | |
| `Peano/Prelim.lean` | `Peano` | `Prelim/ExistsUnique`, `Prelim/Classical` | `PeanoNat` y todos los siguientes |
| `Peano/Prelim/ExistsUnique.lean` | `Peano` | — | `Prelim`, `Classical` |
| `Peano/Prelim/Classical.lean` | `Peano` | `ExistsUnique`, `Init.Classical` | `Prelim` |
| **Core aritmético** | | | |
| `Peano/PeanoNat.lean` | `Peano` | `Prelim` | todos los de `PeanoNat/` |
| `Peano/PeanoNat/Axioms.lean` | `Peano.Axioms` | `PeanoNat` | `StrictOrder` y descendientes |
| `Peano/PeanoNat/StrictOrder.lean` | `Peano.StrictOrder` | `PeanoNat`, `Axioms` | `Order` y descendientes |
| `Peano/PeanoNat/Order.lean` | `Peano.Order` | `…StrictOrder` | `Lattice` y descendientes |
| `Peano/PeanoNat/Tuple.lean` | `Peano` | `PeanoNat`, `StrictOrder` | — |
| `Peano/PeanoNat/Lattice.lean` | `Peano.Lattice` | `…Order` | `WellFounded` y descendientes |
| `Peano/PeanoNat/WellFounded.lean` | `Peano.WellFounded` | `…Lattice` | `Add` y descendientes |
| `Peano/PeanoNat/Add.lean` | `Peano.Add` | `…WellFounded` | `Sub` y descendientes |
| `Peano/PeanoNat/Sub.lean` | `Peano.Sub` | `…Add` | `Mul` y descendientes |
| `Peano/PeanoNat/Mul.lean` | `Peano.Mul` | `…Sub` | `Div` y descendientes |
| `Peano/PeanoNat/Div.lean` | `Peano.Div` | `…Mul` | `Arith`, `Pow` y descendientes |
| `Peano/PeanoNat/Arith.lean` | `Peano.Arith` | todos los anteriores | `Primes`, `NumberTheory/*` |
| `Peano/PeanoNat/Fractions.lean` | `Peano.Arith` | `Arith`, `Lattice` | — |
| `Peano/PeanoNat/Primes.lean` | `Peano.Primes` | `Arith` | `NumberTheory/*` |
| `Peano/PeanoNat/NumberSets.lean` | `Peano` | `PeanoNat` | — |
| `Peano/PeanoNat/Decidable.lean` | — (reexport) | `Order` | — |
| `Peano/PeanoNat/Isomorph.lean` | — (reexport) | `Arith` | — |
| **Representaciones** | | | |
| `Peano/PeanoNat/Digits.lean` | `Peano.Digits` | `Div`, `Pow`, `Log` | — |
| `Peano/PeanoNat/Log.lean` | `Peano.Log` | `Div`, `Pow` | `Digits` |
| `Peano/PeanoNat/Sqrt.lean` | `Peano.Sqrt` | `Mul`, `Sub`, `Pow` | — |
| `Peano/PeanoNat/Pairing.lean` | `Peano.Pairing` | `Div`, `Sqrt` | — |
| **Foundation** | | | |
| `Peano/PeanoNat/Foundation/CantorPairing.lean` | `Peano.Foundation` | `Add`, `Sub`, `Mul`, `Div`, `Arith`, `Prelim.Classical` | `GodelBeta` |
| `Peano/PeanoNat/Foundation/GodelBeta.lean` | `Peano.Foundation` | `CantorPairing`, `ChineseRemainder`, `Factorial`, `Arith` | — |
| `Peano/PeanoNat/Foundation/Foundation.lean` | `Peano.Foundation` | `PeanoSystem`, `Initiality`, `CantorPairing`, `GodelBeta` | `Peano.lean` |
| **Combinatoria** | | | |
| `Peano/PeanoNat/Combinatorics/Pow.lean` | `Peano.Pow` | `Mul`, `Div` | `NewtonBinom`, `Log`, `Sqrt`, `Digits` |
| `Peano/PeanoNat/Combinatorics/Factorial.lean` | `Peano.Factorial` | `Add`, `Mul` | `Binom`, `NewtonBinom` |
| `Peano/PeanoNat/Combinatorics/Binom.lean` | `Peano.Binom` | `Mul`, `Sub`, `Factorial`, `Primes` | `NewtonBinom` |
| `Peano/PeanoNat/Combinatorics/NewtonBinom.lean` | `Peano.NewtonBinom` | `Pow`, `Factorial`, `Binom`, `Summation` | — |
| `Peano/PeanoNat/Combinatorics/Summation.lean` | `Peano.Summation` | `Add`, `Mul` | `NewtonBinom`, `Product` |
| `Peano/PeanoNat/Combinatorics/Product.lean` | `Peano.Product` | `Mul`, `Summation` | `Totient` |
| `Peano/PeanoNat/Combinatorics/Fibonacci.lean` | `Peano.Fibonacci` | `Add` | — |
| `Peano/PeanoNat/Combinatorics/Counting.lean` | `— (stub)` | `FSet`, `Primes` | — |
| **Listas y conjuntos finitos** | | | |
| `Peano/PeanoNat/ListsAndSets/List.lean` | `Peano.List` | `PeanoNat` | `FSet` |
| `Peano/PeanoNat/ListsAndSets/FSet.lean` | `Peano.FSet` | `List`, `Add` | `FSetFunction`, `EquivRel`, `Counting`, `Group` |
| `Peano/PeanoNat/ListsAndSets/FSetFunction.lean` | `Peano.FSetFunction` | `FSet`, `List`, `Mul` | `Perm`, `Group` |
| `Peano/PeanoNat/ListsAndSets/EquivRel.lean` | `Peano.EquivRel` | `FSet` | `Cosets` |
| **Teoría de números** | | | |
| `Peano/PeanoNat/NumberTheory/ModEq.lean` | `Peano.ModEq` | `Arith`, `Primes` | `Totient`, `CRT`, `Fermat` |
| `Peano/PeanoNat/NumberTheory/Totient.lean` | `Peano.Totient` | `ModEq`, `Product`, `FSet` | `Fermat` |
| `Peano/PeanoNat/NumberTheory/ChineseRemainder.lean` | `Peano.CRT` | `ModEq`, `Arith` | — |
| `Peano/PeanoNat/NumberTheory/Fermat.lean` | `Peano.Fermat` | `ModEq`, `Totient`, `Primes` | — |
| `Peano/PeanoNat/NumberTheory/Wilson.lean` | `Peano.Wilson` | `ModEq`, `Fermat`, `Factorial`, `Pow`, `Primes` | — |
| **Teoría de grupos finitos** | | | |
| `Peano/PeanoNat/Combinatorics/Perm.lean` | `Peano.Perm` | `FSetFunction` | `Group`, `Sign` |
| `Peano/PeanoNat/Combinatorics/Group.lean` | `Peano.Group` | `FSet`, `Perm` | `Orbit`, `Action` |
| `Peano/PeanoNat/Combinatorics/Sign.lean` | `— (stub)` | `Perm` | — |
| `Peano/PeanoNat/Combinatorics/Orbit.lean` | `— (stub)` | `Group`, `FSet` | `Action` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean` | `Peano.GroupTheory` | `Group`, `Orbit` | `Cosets`, `Sylow` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean` | `Peano.GroupTheory` | `Cosets`, `Group` | `QuotientGroup` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean` | `Peano.GroupTheory` | `NormalSubgroup`, `Cosets` | `FirstIsomorphism`, `SecondIsomorphism`, `CorrespondenceTheorem` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean` | `Peano.GroupTheory` | `QuotientGroup` | — |
| `Peano/PeanoNat/Combinatorics/GroupTheory/SecondIsomorphism.lean` | `Peano.GroupTheory` | `QuotientGroup` | `Zassenhaus` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/ThirdIsomorphism.lean` | `Peano.GroupTheory` | `QuotientGroup` | — |
| `Peano/PeanoNat/Combinatorics/GroupTheory/CorrespondenceTheorem.lean` | `Peano.GroupTheory` | `QuotientGroup` | — |
| `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean` | `Peano.GroupTheory` | `SecondIsomorphism` | — |
| `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean` | `Peano.GroupTheory` | `Action`, `Group` | `CosetAction`, `Sylow` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/CosetAction.lean` | `Peano.GroupTheory` | `Cosets`, `Action`, `Group` | `Sylow` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean` | `Peano.GroupTheory` | `Cosets`, `CosetAction`, `Action` | — |
| **Verificación** | | | |
| `Peano/ConstructiveCheck.lean` | — | `Prelim` | — |

### 0.2. Espacios de nombres y relaciones (requisito 3)

| Namespace | Módulo | Sub-namespace de |
|---|---|---|
| `Peano` | `Prelim.lean`, `PeanoNat.lean`, `Tuple`, `NumberSets` | — (raíz) |
| `Peano.Axioms` | `Axioms.lean` | `Peano` |
| `Peano.StrictOrder` | `StrictOrder.lean` | `Peano` |
| `Peano.Order` | `Order.lean` | `Peano` |
| `Peano.Lattice` | `Lattice.lean` | `Peano` |
| `Peano.WellFounded` | `WellFounded.lean` | `Peano` |
| `Peano.Add` | `Add.lean` | `Peano` |
| `Peano.Sub` | `Sub.lean` | `Peano` |
| `Peano.Mul` | `Mul.lean` | `Peano` |
| `Peano.Div` | `Div.lean` | `Peano` |
| `Peano.Arith` | `Arith.lean` | `Peano` |
| `Peano.Primes` | `Primes.lean` | `Peano` |
| `Peano.Digits` | `Digits.lean` | `Peano` |
| `Peano.Log` | `Log.lean` | `Peano` |
| `Peano.Sqrt` | `Sqrt.lean` | `Peano` |
| `Peano.Pairing` | `Pairing.lean` | `Peano` |
| `Peano.Pow` | `Combinatorics/Pow.lean` | `Peano` |
| `Peano.Factorial` | `Combinatorics/Factorial.lean` | `Peano` |
| `Peano.Binom` | `Combinatorics/Binom.lean` | `Peano` |
| `Peano.NewtonBinom` | `Combinatorics/NewtonBinom.lean` | `Peano` |
| `Peano.Summation` | `Combinatorics/Summation.lean` | `Peano` |
| `Peano.Product` | `Combinatorics/Product.lean` | `Peano` |
| `Peano.Fibonacci` | `Combinatorics/Fibonacci.lean` | `Peano` |
| `Peano.Counting` | `Combinatorics/Counting.lean` (stub, sin API) | `Peano` |
| `Peano.List` | `ListsAndSets/List.lean` | `Peano` |
| `Peano.FSet` | `ListsAndSets/FSet.lean` | `Peano` |
| `Peano.FSetFunction` | `ListsAndSets/FSetFunction.lean` | `Peano` |
| `Peano.EquivRel` | `ListsAndSets/EquivRel.lean` | `Peano` |
| `Peano.ModEq` | `NumberTheory/ModEq.lean` | `Peano` |
| `Peano.Totient` | `NumberTheory/Totient.lean` | `Peano` |
| `Peano.CRT` | `NumberTheory/ChineseRemainder.lean` | `Peano` |
| `Peano.Fermat` | `NumberTheory/Fermat.lean` | `Peano` |
| `Peano.Wilson` | `NumberTheory/Wilson.lean` | `Peano` |
| `Peano.Foundation` | `PeanoNat/Foundation/CantorPairing.lean` | `Peano` |
| `Peano.Perm` | `Combinatorics/Perm.lean` | `Peano` |
| `Peano.Group` | `Combinatorics/Group.lean` | `Peano` |
| `Peano.Sign` | `Combinatorics/Sign.lean` (stub, sin API) | `Peano` |
| `Peano.Orbit` | `Combinatorics/Orbit.lean` (stub, sin API) | `Peano` |
| `Peano.GroupTheory` | `GroupTheory/Action.lean`, `NormalSubgroup.lean`, `QuotientGroup.lean`, `FirstIsomorphism.lean`, `SecondIsomorphism.lean`, `ThirdIsomorphism.lean`, `CorrespondenceTheorem.lean`, `Zassenhaus.lean`, `Sylow/Cosets.lean`, `Sylow/CosetAction.lean`, `Sylow/Sylow.lean` | `Peano` |

### 0.3. Notaciones registradas (requisito 4.4)

| Símbolo | Tipo | Prioridad | Namespace | Módulo |
|---|---|---|---|---|
| `σ n` | prefijo | `max` | `Peano` | `PeanoNat.lean` |
| `𝟘` | constante | — | `Peano` | `PeanoNat.lean` |
| `𝟙` | constante | — | `Peano` | `PeanoNat.lean` |
| `𝟚` | constante | — | `Peano` | `PeanoNat.lean` |
| `𝟛` | constante | — | `Peano` | `PeanoNat.lean` |
| `∃¹ x, p x` | macro cuantificador (4 variantes) | — | `Peano` | `Prelim.lean` |
| `⟨⟩` | tupla vacía | — | `Peano` | `PeanoNat.lean` |
| `⟨x⟩` | tupla singleton | — | `Peano` | `PeanoNat.lean` |
| `n + m` | infijo, instancia `Add ℕ₀` | ~65 | `Peano.Add` | `Add.lean` |
| `a +l b` | infijo | — | `Peano.Add` | `Add.lean` |
| `n - m` | infijo | 65 | `Peano.Sub` | `Sub.lean` |
| `n -( h ) m` | notación con prueba | 65 | `Peano.Sub` | `Sub.lean` |
| `n * m` | infijo | 70 | `Peano.Mul` | `Mul.lean` |
| `a / b` | instancia `Div ℕ₀` | — | `Peano.Div` | `Div.lean` |
| `a % b` | instancia `Mod ℕ₀` | — | `Peano.Div` | `Div.lean` |
| `n < m` | instancia `LT ℕ₀` | — | `Peano.StrictOrder` | `StrictOrder.lean` |
| `n ≤ m` | instancia `LE ℕ₀` | — | `Peano.Order` | `Order.lean` |
| `a ∣ b` | infijo | 50 | `Peano.Arith` | `Arith.lean` |
| `a ∤ b` | notación negación | 50 | `Peano.Arith` | `Arith.lean` |
| `a ∣₁ b` | infijo | 50 | `Peano.Arith` | `Arith.lean` |
| `n ^ m` | infijo | 80 | `Peano.Pow` | `Combinatorics/Pow.lean` |
| `C(n, k)` | notación combinatoria | — | `Peano.Binom` | `Combinatorics/Binom.lean` |
| `∑ k ≤ n, f` | macro sumatorio | — | `Peano.Summation` | `Combinatorics/Summation.lean` |
| `a ≡ b [MOD n]` | notación congruencia | 50 | `Peano.ModEq` | `NumberTheory/ModEq.lean` |
| `{[a, b, c]}` | macro FSet literal | — | `Peano.FSet` | `ListsAndSets/FSet.lean` |
| `{[x \| p]}` | macro FSet comprensión | — | `Peano.FSet` | `ListsAndSets/FSet.lean` |

### 0.4. Nodos temáticos (`doc/REFERENCE-*.md`)

Documentación detallada de exports por área temática. Cada archivo contiene firmas exactas Lean 4, importancia, computabilidad, notación matemática y dependencias.

| Nodo temático | Módulos cubiertos | Símbolos | Actualizado |
|---|---|---|---|
| [doc/REFERENCE-Prelim.md](doc/REFERENCE-Prelim.md) | `Prelim/ExistsUnique.lean`, `Prelim/Classical.lean` | ~15 | 2026-05-10 |
| [doc/REFERENCE-Arithmetic.md](doc/REFERENCE-Arithmetic.md) | `PeanoNat.lean`, `Tuple.lean`, `Axioms.lean`, `StrictOrder.lean`, `Order.lean`, `Lattice.lean`, `WellFounded.lean`, `Add.lean`, `Sub.lean`, `Mul.lean`, `Div.lean`, `Arith.lean`, `Primes.lean`, `Isomorph.lean`, `Decidable.lean`, `Log.lean`, `Sqrt.lean` | ~450 | 2026-05-10 |
| [doc/REFERENCE-NumberTheory.md](doc/REFERENCE-NumberTheory.md) | `NumberTheory/ModEq.lean`, `Totient.lean`, `ChineseRemainder.lean`, `Fermat.lean`, `Wilson.lean` | ~80 | 2026-05-10 |
| [doc/REFERENCE-Foundation.md](doc/REFERENCE-Foundation.md) | `Foundation/PureAxioms.lean`, `PeanoSystem.lean`, `Initiality.lean`, `CantorPairing.lean`, `GodelBeta.lean` | ~50 | 2026-05-10 |
| [doc/REFERENCE-ListsAndSets.md](doc/REFERENCE-ListsAndSets.md) | `ListsAndSets/List.lean`, `FSet.lean`, `FSetFunction.lean`, `EquivRel.lean` | ~120 | 2026-05-10 |
| [doc/REFERENCE-Combinatorics.md](doc/REFERENCE-Combinatorics.md) | `Combinatorics/Pow.lean`, `Factorial.lean`, `Binom.lean`, `NewtonBinom.lean`, `Summation.lean`, `Product.lean`, `Fibonacci.lean`, `Counting.lean`, `Perm.lean`, `Sign.lean`, `Group.lean`, `Orbit.lean` | ~200 | 2026-05-10 |
| [doc/REFERENCE-GroupTheory.md](doc/REFERENCE-GroupTheory.md) | `GroupTheory/NormalSubgroup.lean`, `QuotientGroup.lean`, `FirstIsomorphism.lean`, `SecondIsomorphism.lean`, `ThirdIsomorphism.lean`, `CorrespondenceTheorem.lean`, `Zassenhaus.lean`, `Action.lean`, `Sylow/Cosets.lean`, `Sylow/CosetAction.lean`, `Sylow/Sylow.lean` | ~138 | 2026-05-10 |

---

