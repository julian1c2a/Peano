# Peano

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

Formalización de la aritmética de Peano en **Lean 4**, construida desde los axiomas inductivos de `ℕ₀` sin depender de Mathlib.

> **Autor:** Julián Calderón Almendros
> **Lean:** `leanprover/lean4:v4.29.0`
> **Build:** 33 jobs · 0 sorry · 0 warnings
> **Licencia:** MIT

---

## Descripción

Este proyecto define el tipo inductivo `ℕ₀` (números naturales de Peano) y demuestra desde cero toda la aritmética: orden estricto y no estricto, estructura de retícula, bien-fundación e inducción fuerte, suma, resta truncada, multiplicación, división entera con módulo, logaritmo y raíz cuadrada enteros, divisibilidad (MCD, MCM, Bézout), números primos con factorización única (TFA), potenciación, factorial, coeficientes binomiales, **Binomio de Newton**, sumatorias, productorias, sucesión de Fibonacci, conjuntos finitos, paridad y decidabilidad completa.

Toda la biblioteca está **computacionalmente realizada**: las operaciones producen términos de `ℕ₀` evaluables por el kernel de Lean. El proyecto registra todas las instancias estándar de Init (`Zero`, `One`, `OfNat`, `Add`, `Mul`, `Sub`, `Div`, `Mod`, `Pow`, `LT`, `LE`, `Ord`, `BEq`, `DecidableEq`, `SizeOf`, `Repr`, `WellFoundedRelation`, `DecidableRel`) para `ℕ₀`, haciendo que las operaciones trabajen con la notación natural de Lean 4.

---

## Estructura de módulos

```
Peano.lean                                  ← entrada; importa toda la librería
└─ Peano/
   ├─ PeanoNat.lean                         Peano           — ℕ₀, ℕ₁, ℕ₂, constantes, isomorfismos
   ├─ Prelim.lean                           Peano.Prelim    — infraestructura compartida (DList→List)
   └─ PeanoNat/
      ├─ Axioms.lean                        Peano.Axioms       — axiomas de Peano, inducción
      ├─ StrictOrder.lean                   Peano.StrictOrder   — orden estricto <, tricotomía
      ├─ Order.lean                         Peano.Order        — orden ≤, totalidad, lt_or_ge
      ├─ Tuple.lean                         Peano              — tuplas de longitud n, orden lexicográfico
      ├─ Lattice.lean                       Peano.Lattice      — max, min, retícula distributiva
      ├─ MaxMin.lean                        Peano.MaxMin       — (legacy, migrado a Lattice)
      ├─ WellFounded.lean                   Peano.WellFounded  — bien-fundación, inducción fuerte
      ├─ Add.lean                           Peano.Add          — suma, neutro, conmutatividad
      ├─ Sub.lean                           Peano.Sub          — resta truncada
      ├─ Mul.lean                           Peano.Mul          — multiplicación, distributividad
      ├─ Div.lean                           Peano.Div          — división entera, módulo
      ├─ Arith.lean                         Peano.Arith        — divisibilidad, MCD/MCM, Bézout, paridad
      ├─ Primes.lean                        Peano.Primes       — primos, TFA, decidabilidad de Prime
      ├─ Decidable.lean                     Peano.Decidable    — instancias Ord, DecidableRel
      ├─ List.lean                         Peano.List        — listas de ℕ₀
      ├─ FSet.lean                          Peano.FSet         — conjuntos finitos ordenados
      ├─ NumberSets.lean                    Peano.NumberSets   — divisores, coprimos, primos ≤ n
      ├─ Isomorph.lean                      Peano.Isomorph     — isomorfismo Nat↔ℕ₀ completo
      ├─ Log.lean                           Peano.Log          — logaritmo entero con resto
      ├─ Sqrt.lean                          Peano.Sqrt         — raíz cuadrada entera con resto
      └─ Combinatorics/
         ├─ Pow.lean                        Peano.Pow          — potenciación
         ├─ Factorial.lean                  Peano.Factorial    — factorial
         ├─ Binom.lean                      Peano.Binom        — coeficientes binomiales, Pascal
         ├─ NewtonBinom.lean                Peano.NewtonBinom  — binomio de Newton
         ├─ Summation.lean                  Peano.Summation    — sumatorias ∑
         ├─ Product.lean                    Peano.Product      — productorias ∏
         └─ Fibonacci.lean                  Peano.Fibonacci    — sucesión de Fibonacci
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

### Combinatoria

- **Potenciación**: `pow_add`, `pow_mul`, monotonía
- **Factorial**: `factorial_pos`, `factorial_le_mono`
- **Coeficientes binomiales**: Pascal, fórmula factorial ($C(n,k) \cdot k! \cdot (n-k)! = n!$), simetría
- **Binomio de Newton**: $(a+b)^n = \sum_{k=0}^{n} C(n,k) \cdot a^k \cdot b^{n-k}$ (demostrado)
- **Sumatorias/Productorias**: linealidad, monotonía, desplazamiento, inversión
- **Fibonacci**: identidad de Cassini, `fib_add`, propiedades

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
import Peano                  -- librería completa
import Peano.PeanoNat.Arith   -- hasta divisibilidad, MCD/MCM, paridad
import Peano.PeanoNat.Primes  -- incluye primos y TFA
```

---

## Hoja de ruta

### En curso (Phase 21 — Completación de ℕ₀)

- [x] Instancias Init completas (Zero, One, OfNat, Add, Mul, Sub, Div, Mod, Pow, Ord, WellFoundedRelation, DecidableRel)
- [x] Inducción fuerte (`strongRecOn`, `strongInductionOn`)
- [x] `IsEven`/`IsOdd` decidibles
- [x] `Decidable (Prime n)`
- [ ] **Digits.lean** — representación en base *b*
- [ ] **Pairing.lean** — función de emparejamiento de Cantor
- [ ] **ModEq.lean** — congruencia modular
- [ ] **Totient.lean** — función φ de Euler
- [ ] **ChineseRemainder.lean** — Teorema del Resto Chino
- [ ] **Fermat.lean** — Pequeño Teorema de Fermat

### Futuro

- **Phase 22**: Extensión a enteros `ℤ` (pares de equivalencia sobre `ℕ₀ × ℕ₀`)
- **Phase 23**: Extensión a racionales `ℚ`

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
