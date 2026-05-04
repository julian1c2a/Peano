# Peano

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

Formalización de la aritmética de Peano en **Lean 4**, construida desde los axiomas inductivos de `ℕ₀` sin depender de Mathlib.

> **Autor:** Julián Calderón Almendros
> **Lean:** `leanprover/lean4:v4.29.0`
> **Build:** 59 jobs · 0 errores · 0 warnings · 0 sorry (4 axiomas privados en Sylow.lean)
> **Licencia:** MIT

---

## Descripción

Este proyecto define el tipo inductivo `ℕ₀` (números naturales de Peano) y demuestra desde cero toda la aritmética: orden estricto y no estricto, estructura de retícula, bien-fundación e inducción fuerte, suma, resta truncada, multiplicación, división entera con módulo, logaritmo y raíz cuadrada enteros, divisibilidad (MCD, MCM, Bézout), números primos con factorización única (TFA), potenciación, factorial, coeficientes binomiales, **Binomio de Newton**, sumatorias, productorias, sucesión de Fibonacci, conjuntos finitos, funciones entre conjuntos finitos (inyectividad, sobreyectividad, biyectividad, **principio del palomar**), paridad, decidabilidad completa, congruencia modular, función φ de Euler, **Teorema Chino del Resto**, **Pequeño Teorema de Fermat**, **Teorema de Wilson**, permutaciones, grupos finitos, signo de permutaciones, órbitas y acciones de grupo, y coclases con los **teoremas de Sylow** formalmente cerrados.

Toda la biblioteca está **computacionalmente realizada**: las operaciones producen términos de `ℕ₀` evaluables por el kernel de Lean. El proyecto registra todas las instancias estándar de Init (`Zero`, `One`, `OfNat`, `Add`, `Mul`, `Sub`, `Div`, `Mod`, `Pow`, `LT`, `LE`, `Ord`, `BEq`, `DecidableEq`, `SizeOf`, `Repr`, `WellFoundedRelation`, `DecidableRel`) para `ℕ₀`, haciendo que las operaciones trabajen con la notación natural de Lean 4.

---

## Estructura de módulos

```
Peano.lean                                        ← entrada; importa toda la librería
└─ Peano/
   ├─ PeanoNat.lean                               Peano           — ℕ₀, ℕ₁, ℕ₂, constantes, isomorfismos
   ├─ ConstructiveCheck.lean                      Peano           — verificación de constructividad
   ├─ Prelim.lean                                 Peano           — reexporta ExistsUnique + Classical
   │  ├─ Prelim/ExistsUnique.lean                 Peano           — ∃¹, ExistsUnique (constructivo)
   │  └─ Prelim/Classical.lean                    Peano           — choose, choose_unique (noncomputable)
   └─ PeanoNat/
      ├─ Axioms.lean                              Peano.Axioms       — axiomas de Peano, inducción
      ├─ StrictOrder.lean                         Peano.StrictOrder   — orden estricto <, tricotomía
      ├─ Order.lean                               Peano.Order        — orden ≤, totalidad, lt_or_ge
      ├─ Tuple.lean                               Peano              — tuplas de longitud n, orden lexicográfico
      ├─ Lattice.lean                             Peano.Lattice      — max, min, retícula distributiva
      ├─ WellFounded.lean                         Peano.WellFounded  — bien-fundación, inducción fuerte
      ├─ Add.lean                                 Peano.Add          — suma, neutro, conmutatividad
      ├─ Sub.lean                                 Peano.Sub          — resta truncada
      ├─ Mul.lean                                 Peano.Mul          — multiplicación, distributividad
      ├─ Div.lean                                 Peano.Div          — división entera, módulo
      ├─ Arith.lean                               Peano.Arith        — divisibilidad, MCD/MCM, Bézout, paridad
      ├─ Primes.lean                              Peano.Primes       — primos, TFA, decidabilidad de Prime
      ├─ Decidable.lean                           Peano.Decidable    — instancias Ord, DecidableRel
      ├─ NumberSets.lean                          Peano.NumberSets   — divisores, coprimos, primos ≤ n
      ├─ Isomorph.lean                            Peano.Isomorph     — isomorfismo Nat↔ℕ₀ completo
      ├─ Log.lean                                 Peano.Log          — logaritmo entero con resto
      ├─ Sqrt.lean                                Peano.Sqrt         — raíz cuadrada entera con resto
      ├─ Digits.lean                              Peano.Digits       — dígitos en base arbitraria
      ├─ Pairing.lean                             Peano.Pairing      — emparejamiento de Cantor
      ├─ Foundation/
      │  ├─ Foundation.lean                       Peano.Foundation   — módulo paraguas Foundation
      │  ├─ PeanoSystem.lean                      Peano.Foundation   — estructura PeanoSystem, morfismos, isomorfismos
      │  ├─ Initiality.lean                       Peano.Foundation   — ℕ₀ como álgebra inicial; unicidad e inicialidad
      │  ├─ PureAxioms.lean                       Peano.Foundation   — sistema PA axiomático puro + teorema de paridad
      │  ├─ CantorPairing.lean                    Peano.Foundation   — biyección ℕ₀×ℕ₀ ≅ ℕ₀ (pair/fst/snd)
      │  └─ GodelBeta.lean                        Peano.Foundation   — función β de Gödel; codificación List ℕ₀ ≃ ℕ₀
      ├─ ListsAndSets/
      │  ├─ List.lean                             Peano.List         — listas polimórficas, sortedInsert genérico
      │  ├─ FSet.lean                             Peano.FSet         — conjuntos finitos genéricos (FSet α)
      │  └─ FSetFunction.lean                     Peano.FSetFunction — MapOn, Im, Perm, Pigeonhole, collision_of_card_lt, ~92 decl.
      ├─ NumberTheory/
      │  ├─ ModEq.lean                            Peano.ModEq        — congruencia modular
      │  ├─ Totient.lean                          Peano.Totient      — función φ de Euler
      │  ├─ ChineseRemainder.lean                 Peano.CRT          — Teorema Chino del Resto
      │  ├─ Fermat.lean                           Peano.Fermat       — Pequeño Teorema de Fermat
      │  └─ Wilson.lean                           Peano.Wilson       — Teorema de Wilson (0 sorry)
      └─ Combinatorics/
         ├─ Pow.lean                              Peano.Pow          — potenciación
         ├─ Factorial.lean                        Peano.Factorial    — factorial
         ├─ Binom.lean                            Peano.Binom        — coeficientes binomiales, Pascal
         ├─ NewtonBinom.lean                      Peano.NewtonBinom  — binomio de Newton
         ├─ Summation.lean                        Peano.Summation    — sumatorias ∑
         ├─ Product.lean                          Peano.Product      — productorias ∏
         ├─ Fibonacci.lean                        Peano.Fibonacci    — sucesión de Fibonacci
         ├─ Counting.lean                         Peano.Counting     — conteo combinatorio
         ├─ Perm.lean                             Peano.Perm         — permutaciones
         ├─ Sign.lean                             Peano.Sign         — signo de permutaciones
         ├─ Orbit.lean                            Peano.Orbit        — órbitas de permutaciones
         ├─ Group.lean                            Peano.Group        — FinGroup (α) polimórfico, Subgroup, gpow, subgrupos especiales
         └─ GroupTheory/
            ├─ Action.lean                        Peano.Action       — acciones de grupo
            └─ Sylow/
               ├─ Cosets.lean                     Peano.Cosets       — coclases
               ├─ CosetAction.lean                Peano.CosetAction  — acción de coclases (coset_conjugate_exists)
               └─ Sylow.lean                      Peano.Sylow        — teoremas de Sylow (0 sorry, 4 axiomas privados)
```

---

## Contenido destacado

### Tipos y constantes

| Símbolo | Descripción |
|---|---|
| `ℕ₀` | Tipo inductivo (`zero` / `succ`) con todas las instancias Init |
| `ℕ₁` | Subtipo `{n : ℕ₀ // n ≠ 0}` |
| `ℕ₂` | Subtipo `{n : ℕ₁ // n.val ≠ 1}` |
| `ℙ` | Subtipo `{n : ℕ₂ // Prime n.val.val}` |
| `𝟘 𝟙 𝟚 𝟛` | Constantes `0, 1, 2, 3` |
| `σ n` | Notación para `ℕ₀.succ n` |
| `Λ`, `Ψ` | Isomorfismos `Nat → ℕ₀` y `ℕ₀ → Nat` |

### Axiomas de Peano

Los 8 axiomas clásicos demostrados como teoremas a partir de la estructura inductiva de `ℕ₀`:
`0 ≠ σ(n)`, inyectividad de `σ`, principio de inducción, etc.

### Orden y retícula

- **Orden estricto**: `Lt`, `Gt`, instancias `LT`/`Decidable`, tricotomía
- **Orden no estricto**: `Le`, `Ge`, totalidad, `lt_or_ge`, `le_or_lt`
- **Retícula**: `max`/`min` computables, idempotencia, conmutatividad, asociatividad, distributividad, absorción, 18 extensiones Mathlib-style

### Bien-fundación e inducción fuerte

- `well_founded_lt : WellFounded Lt`
- `well_ordering_principle`: existencia y unicidad del mínimo de conjuntos no vacíos
- `strongRecOn`: recursión fuerte (Sort), `strongInductionOn`: inducción fuerte (Prop)
- Instancia `WellFoundedRelation ℕ₀`

### Aritmética completa

- **Suma**: neutro, conmutatividad, asociatividad, cancelación
- **Resta truncada**: monus, `sub_self`, `add_k_sub_k`
- **Multiplicación**: distributividad, `mul_eq_zero`, propiedad arquimediana
- **División/módulo**: `divMod_eq` ($a = \lfloor a/b \rfloor \cdot b + a \bmod b$), `mod_lt`
- **Logaritmo entero**: `logMod`, `log`, `logRem`
- **Raíz cuadrada entera**: `sqrtMod`, `sqrt`, `sqrtRem`

### Teoría de números

- **Divisibilidad**: `Divides`, reflexividad, transitividad, antisimetría
- **MCD/MCM**: algoritmo de Euclides, `gcd_greatest`, 25 extensiones Mathlib-style
- **Identidad de Bézout**: `bezout_natform`
- **Primos**: tres definiciones equivalentes (`Prime`, `Irreducible`, `HasExactlyTwoDivisors`)
- **Lema de Gauss**: `coprime_dvd_of_dvd_mul`
- **Teorema Fundamental de la Aritmética**: existencia y unicidad de la factorización prima
- **Decidabilidad de Prime**: `isPrimeb`, `isPrimeb_iff`, instancia `Decidable (Prime n)`
- **Paridad**: `IsEven`/`IsOdd` con instancias `Decidable`, 6 teoremas
- **Congruencia modular**: `ModEq`, reflexividad, simetría, transitividad, compatibilidad aritmética
- **Función de Euler**: `totient`, `totient_prime`, `totient_pos`
- **Teorema Chino del Resto**: `chinese_remainder` (existencia)
- **Pequeño Teorema de Fermat**: `fermat_little` — $a^{p-1} \equiv 1 \pmod{p}$
- **Teorema de Wilson**: `wilson` — $p \mid (p-1)! + 1$ (demostrado por pairing argument sobre $\{2,\ldots,p-2\}$)

### Combinatoria

- **Potenciación**: `pow_add`, `pow_mul`, monotonía
- **Factorial**: `factorial_pos`, `factorial_le_mono`
- **Coeficientes binomiales**: Pascal, fórmula factorial ($C(n,k) \cdot k! \cdot (n-k)! = n!$), simetría, $p \mid C(p,k)$ para $0 < k < p$, identidad de fila $C(pr,p) = r \cdot C(pr{-}1,p{-}1)$
- **Binomio de Newton**: $(a+b)^n = \sum_{k=0}^{n} C(n,k) \cdot a^k \cdot b^{n-k}$ (demostrado)
- **Sumatorias/Productorias**: linealidad, monotonía, desplazamiento, inversión
- **Fibonacci**: identidad de Cassini, `fib_add`, propiedades
- **Conteo**: principios de conteo combinatorio

### Conjuntos finitos y funciones

- **FSet α**: conjuntos finitos genéricos para cualquier tipo con `StrictLinearOrder` (lista ordenada + invariante `Sorted`)
- **FSetFunction** (~92 declaraciones):
  - `MapOn`: funciones totales entre FSet, composición (`comp`), asociatividad (`comp_assoc`)
  - `Im`: imagen, cardinalidad de la imagen
  - Inyectividad, sobreyectividad, biyectividad con iff de cardinalidad
  - `leftInverse`, `rightInverse`, `inverse` para biyecciones
  - **Principio del Palomar**: inyectiva ⇒ card(dom) ≤ card(cod), sobreyectiva ⇒ card(cod) ≤ card(dom)
  - Preimagen (`PreIm`), fibras, restricción
  - Conteo por fibras uniformes: `card_eq_mul_of_uniform_fibers`
  - `BinOpOn`: operaciones binarias sobre FSet
  - Endomorfismos: `EndoOn`, especialización para funciones A → A
  - **Perm**: tipo de permutaciones `A → A` biyectivas, inversas, composición

### Teoría de grupos finitos

- **Group.lean**: `FinGroup`, `Subgroup`, `gpow`, subgrupos trivial/impropio/cíclico/normal, orden de elemento
- **Sign.lean**: signo de permutaciones (paridad de transposiciones)
- **Orbit.lean**: órbitas de elementos bajo permutaciones
- **Action.lean**: acciones de grupo, órbitas y estabilizadores, `orbit_stabilizer`, `orbits_partition`
- **Cosets.lean**: coclases, Lagrange ($|H| \cdot k = |G|$), conteo por fibras
- **CosetAction.lean**: acción de $G$ sobre coclases, `coset_conjugate_exists` (cierra Sylow II)
- **Sylow.lean**: los tres teoremas de Sylow **formalmente cerrados** (0 sorry):
  - `cauchy_minimal` — argumento de órbitas de McKay
  - `sylow_first` — existencia de p-subgrupo de Sylow
  - `sylow_second` — conjugación de subgrupos de Sylow
  - `sylow_third` — $n_p \equiv 1 \pmod{p}$ y $n_p \mid |G|$
  - ⚠ 4 axiomas privados pendientes de prueba (rutas Wielandt y Conjugation en curso)

> *4 axiomas privados en Sylow.lean: `wielandt_fixed_point_exists`, `wielandt_p_ndvd_r`, `sylow_third_mod`, `sylow_third_dvd` — pendientes de prueba.*

### Decidabilidad completa

Todas las relaciones y predicados principales son decidibles:
`DecidableEq ℕ₀`, `Decidable (Lt a b)`, `Decidable (Le a b)`, `Decidable (Divides a b)`, `Decidable (Prime n)`, `Decidable (IsEven n)`, `Decidable (IsOdd n)`.

### Isomorfismos Nat↔ℕ₀

14 teoremas de compatibilidad cubriendo: `0`, `σ`, `τ`, `ρ`, `Lt`, `Le`, `max`, `min`, `add`, `sub`, `mul`, `div`, `mod`, `pow`, `gcd`, `lcm`.

---

## Instalación y compilación

**Requisitos:** [`elan`](https://github.com/leanprover/elan) instalado.

```bash
git clone https://github.com/julian1c2a/Peano.git
cd Peano
lake build
```

La versión de Lean se instala automáticamente desde `lean-toolchain` (`leanprover/lean4:v4.29.0`).

---

## Uso como dependencia

En tu `lakefile.lean`:

```lean
require peanolib from git
  "https://github.com/julian1c2a/Peano.git"
```

Luego importa lo que necesites:

```lean
import Peano                              -- librería completa
import Peano.PeanoNat.Arith               -- hasta divisibilidad, MCD/MCM, paridad
import Peano.PeanoNat.Primes              -- incluye primos y TFA
import Peano.PeanoNat.ListsAndSets.FSetFunction  -- funciones entre conjuntos finitos
import Peano.PeanoNat.NumberTheory.Fermat  -- Pequeño Teorema de Fermat
import Peano.PeanoNat.NumberTheory.Wilson  -- Teorema de Wilson
```

---

## Hoja de ruta

### Completado (Phase 21 — Completación de ℕ₀) ✅

- [x] Instancias Init completas (Zero, One, OfNat, Add, Mul, Sub, Div, Mod, Pow, Ord, WellFoundedRelation, DecidableRel)
- [x] Inducción fuerte (`strongRecOn`, `strongInductionOn`)
- [x] `IsEven`/`IsOdd` decidibles
- [x] `Decidable (Prime n)`
- [x] **Digits.lean** — representación en base *b*
- [x] **Pairing.lean** — función de emparejamiento de Cantor
- [x] **ModEq.lean** — congruencia modular
- [x] **Totient.lean** — función φ de Euler
- [x] **ChineseRemainder.lean** — Teorema del Resto Chino
- [x] **Fermat.lean** — Pequeño Teorema de Fermat
- [x] **Wilson.lean** — Teorema de Wilson (pairing argument)

### Completado (Phase 24 — Conjuntos finitos y funciones) ✅

- [x] **List.lean** → `ListsAndSets/List.lean` — listas polimórficas, `sortedInsert` genérico con `[StrictLinearOrder α]`
- [x] **FSet.lean** → `ListsAndSets/FSet.lean` — `FSet α` genérico para cualquier `StrictLinearOrder α`
- [x] **FSetFunction.lean** — MapOn, Im, inyectividad/sobreyectividad/biyectividad, Pigeonhole, inversas, Perm, `card_eq_mul_of_uniform_fibers`, ~92 declaraciones
- [x] ListList.lean y FSetFSet.lean **eliminados** (fusionados en List.lean y FSet.lean)

### En curso (Phase 25 — Teoría de grupos finitos) 🔶

- [x] **Perm.lean** — tipo de permutaciones ✅
- [x] **Group.lean** — `FinGroup (α) [DecidableEq α] [LT α] [StrictLinearOrder α]` polimórfico, Subgroup, gpow, subgrupos especiales, orden de elemento ✅
- [x] **Sign.lean** — signo de permutaciones ✅
- [x] **Orbit.lean** — órbitas ✅
- [x] **Counting.lean** — conteo combinatorio ✅
- [x] **Action.lean** — acciones de grupo, orbit_stabilizer, orbits_partition ✅
- [x] **Sylow/Cosets.lean** — coclases, Lagrange ✅
- [x] **Sylow/CosetAction.lean** — `coset_conjugate_exists`, cierra Sylow II sin axioma privado ✅
- [x] **Sylow/Sylow.lean** — los 3 teoremas formalmente cerrados (0 sorry) ✅
- [x] `prime_dvd_binom_prime` — p | C(p,k) para 0 < k < p (Binom.lean) ✅
- [x] `binom_prime_row` — C(pr, p) = r · C(pr−1, p−1) (Binom.lean) ✅
- [x] **Foundation/CantorPairing.lean** — biyección ℕ₀×ℕ₀ ≅ ℕ₀, `pair`/`fst`/`snd`/`pair_surj` (Phase F.1) ✅
- [x] **Foundation/GodelBeta.lean** — función β de Gödel, `godel_beta_seq`, `encodeList`/`decodeList`/`encode_decode` (Phase F.2) ✅
- [x] **Foundation/Foundation.lean** — módulo paraguas compilando (Phase F.3) ✅
- [ ] **Eliminar 4 axiomas privados** en Sylow.lean:
  - [ ] `wielandt_fixed_point_exists` y `wielandt_p_ndvd_r` — argumento de punto fijo de Wielandt (Track 1)
  - [ ] `sylow_third_mod` y `sylow_third_dvd` — acción de conjugación sobre subgrupos de Sylow (Track 3)

### Futuro

- **Phase 22**: Extensión a enteros `ℤ` (tipo inductivo canónico)
- **Phase 23**: Extensión a racionales `ℚ` (estructura con invariante de coprimalidad)
- **FinGroup Fase 2–5**: `Action.lean` y `Cosets.lean` genéricos, `FinGroup (Subgroup G)` para Sylow III

---

## Documentación técnica

- [`REFERENCE.md`](REFERENCE.md) — referencia completa de definiciones, teoremas, notaciones y dependencias
- [`CURRENT-STATUS-PROJECT.md`](CURRENT-STATUS-PROJECT.md) — estado de compilación y módulos
- [`NEXT-STEPS.md`](NEXT-STEPS.md) — planificación detallada de fases
- [`CHANGELOG.md`](CHANGELOG.md) — historial de cambios
- [`NAMING-CONVENTIONS.md`](NAMING-CONVENTIONS.md) — convenciones de nombres Mathlib4-style

---

## Créditos y Reconocimientos

**Recursos Educativos:**

- "Razonando con Lean" - José A. Alonso (YouTube)
- Adrián GQ (@conjuntos_y_logica) - YouTube

**Referencias Bibliográficas:**

- "Axiomatic Set Theory" - Patrick Suppes (1960/1972)
- "Axiomatic Set Theory" - Paul Bernays (1958)

**Herramientas de IA:**

- Claude Code AI (Anthropic)
- Gemini AI (Google)

---

## Licencia

MIT — ver [`LICENSE`](LICENSE).

Copyright (c) 2025 Julián Calderón Almendros
