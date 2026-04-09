# Thoughts — Peano

**Last updated:** 2026-04-08 21:00
**Author**: Julián Calderón Almendros

> This is an informal design journal. Record ideas, alternatives considered,
> open questions, and future directions here. Not normative — purely exploratory.
> Useful for AI context on "why" decisions were made.

---

## Design Philosophy

This project formalizes Peano arithmetic from scratch in Lean 4, deriving all
8 Peano axioms as theorems from the inductive type `ℕ₀`. No external dependencies
(not even Mathlib). The goal is a complete, self-contained arithmetic library
covering: order, arithmetic operations (add, sub, mul, div, mod, pow), primes,
factorial, binomial coefficients, and the Newton binomial theorem.

---

## Ideas and Alternatives

### 2026-04-08 — Infrastructure modernization

Migrated from the old `.bat`-based freeze system to the template-standard
`git-lock.bash` system with two levels (lock + freeze), pre-commit hook, and
Makefile integration. The old system only had freeze/unfreeze with no
session-based locking.

---

## Open Questions

- [ ] Should export blocks in Peano.lean be migrated to individual leaf modules per §30?
- [ ] Is the Peano/ vs Peano namespace mismatch worth resolving?

---

## Lessons Learned

### Inductive Type Approach

- Defining `ℕ₀` as an inductive type gives all Peano axioms for free as proven theorems
- The recursion principle is the most powerful tool — all arithmetic flows from it
- Well-foundedness proofs are needed for termination of recursive definitions

### Module Organization

- The linear dependency chain (Axioms → Order → Arithmetic → Advanced) works well
- Each module builds strictly on previous ones — no circular dependencies
- 16 modules is manageable without subdirectories

### Documentation

- REFERENCE.md must be self-sufficient for AI assistants
- The "project" protocol (AI-GUIDE.md §12) prevents documentation drift

---

## 2026-04-09 — Comparación Peano vs Mathlib: Líneas de expansión

Tras comparar la cobertura de Peano con `Data.Nat` + `NumberTheory` de Mathlib,
se identifican las siguientes líneas de trabajo. Cada punto corresponde a una
propuesta concreta del autor.

### [1] Branch `makingdecidable` — Eliminar `noncomputable` progresivamente

**Situación actual:** Solo hay 2 definiciones `noncomputable` en todo el proyecto:
`choose` y `choose_unique` en `Prelim.lean`. Ambas usan `Classical.indefiniteDescription`.
_No_ hay definiciones no-computables en los módulos aritméticos.

**Usos de `Classical`** (que no son lo mismo que `noncomputable`):

- `Classical.em` en `Arith.lean` (1 uso)
- `Classical.byContradiction` en `WellFounded.lean` (1 uso)
- `Classical.not_forall`, `Classical.not_not`, `Classical.not_imp` en `Primes.lean` (6 usos)

**Comentario:** El impacto real de `noncomputable` es mínimo (solo `choose`/`choose_unique`).
El trabajo verdadero sería reemplazar los usos de `Classical.em`/`Classical.byContradiction`
por versiones `Decidable`, que es más sutil. Se puede hacer en un branch `makingdecidable`
sin riesgo.

**Plan propuesto:**

1. Crear branch `makingdecidable` desde `updating`.
2. En `WellFounded.lean`: reemplazar `Classical.byContradiction` por la versión
   decidable usando `decidableLt` (ya existe).
3. En `Arith.lean`: el `Classical.em (a = 𝟘)` se puede reemplazar por `DecidableEq ℕ₀`
   (ya existe como `deriving DecidableEq` en `ℕ₀`).
4. En `Primes.lean`: los 6 usos de `Classical.not_forall` etc. son más difíciles porque
   operan sobre proposiciones no-decidables (∀ sobre ℕ₀). Habría que proporcionar
   instancias `Decidable` para los predicados relevantes (ej. `Decidable (Prime p)`),
   o aceptar que ciertas pruebas existenciales sobre ℕ₀ son intrínsecamente clásicas.
5. `choose`/`choose_unique` en `Prelim.lean` son inherentemente no-computables
   (elección sobre tipos arbitrarios). No pueden eliminarse, pero tampoco se usan
   en las definiciones computacionales.

### [2] ~~Renombrar `MaxMin.lean` → `Lattice.lean`~~ (DONE) y ampliar hacia estructura de retículo

**Situación actual:** Renombrado completado. `Lattice.lean` (antes `MaxMin.lean`) define `max`, `min`, `min_max` y teoremas de
idempotencia, conmutatividad, asociatividad, distributividad, y relación con `≤`/`<`.

**Lo que hace Mathlib:** En `Mathlib/Data/Nat/Lattice.lean` instancia `ℕ` como
`ConditionallyCompleteLinearOrderBot` — un orden lineal con:

- `sSup`/`sInf` sobre conjuntos (`Set ℕ`)
- `iSup`/`iInf` indexados
- `⊥ = 0` como elemento mínimo
- Propiedad de completitud condicional (todo conjunto no-vacío acotado tiene sup/inf)

**Ruta de ampliación:**

1. ~~Renombrar `MaxMin.lean` → `Lattice.lean` (fase 1: solo rename).~~ DONE
2. Demostrar que `(ℕ₀, max, min)` es un retículo (`Lattice`):
   - `max` = `⊔` (sup), `min` = `⊓` (inf)
   - Leyes de absorción: `a ⊔ (a ⊓ b) = a`, `a ⊓ (a ⊔ b) = a`
   - (Ya tenemos asociatividad, conmutatividad, idempotencia)
3. Demostrar que es un retículo distributivo (ya tenemos distributividad).
4. Demostrar que es un retículo linealmente ordenado (tricotomía).
5. Agregar `⊥ = 𝟘` como bottom element.
6. Fase avanzada: definir `sSup`/`sInf` sobre subconjuntos decidables de ℕ₀
   (usando el principio del mínimo de `WellFounded.lean`).

**Nota:** No podemos emular completamente `ConditionallyCompleteLinearOrderBot`
sin una teoría de conjuntos (o `Finset`). Pero el retículo distributivo acotado
inferiormente es alcanzable con lo que tenemos.

### [3] Ampliar `DecidableEq` y `DecidablePred` — ¿Decidabilidad del orden?

**Situación actual:** `Decidable.lean` ya reexporta:

- `decidableLt`, `decidableGt` (de `StrictOrder.lean`)
- `decidableLe`, `decidableGe` (de `Order.lean`)
- `blt`, `bgt`, `ble`, `bge` con sus `iff`

Además, `ℕ₀` tiene `deriving DecidableEq` y `Tuple` tiene `tupleDecEq`.

**Comentario:** ¡Ya tenemos decidabilidad del orden! Las cuatro instancias
`Decidable (Lt a b)`, `Decidable (a ≤ b)`, etc. están definidas. Lo que falta
es registrarlas como instancias formales de `DecidableRel`:

```
instance : DecidableRel (@Lt.lt ℕ₀ _)    -- envolviendo decidableLt
instance : DecidableRel (@LE.le ℕ₀ _)    -- envolviendo decidableLe
```

Esto permitiría que tácticas como `decide` funcionen automáticamente con `<`/`≤`.

**Faltantes por añadir:**

- `DecidablePred` para predicados comunes: `Prime`, `Coprime`, `Divides`
- `Decidable (a ∣ b)` — factible vía `a % b = 𝟘` (ya tenemos `mod` y `DecidableEq`)
- `Decidable (Prime p)` — factible vía comprobación de divisores hasta `p`
- `Decidable (Coprime a b)` — vía `gcd a b = 𝟙`

### [4] Nuevos módulos: `ModEq.lean`, `ChineseRemainder.lean`, `PowModTotient.lean`, `Totient.lean`

**Viabilidad:** Cada uno es factible con la infraestructura actual:

- **`ModEq.lean`**: Definir `a ≡ b [MOD n] ↔ n ∣ (a - b)` (o la versión truncada:
  `a % n = b % n`). Ya tenemos `mod`, `sub`, `divides`. Demostrar: reflexividad,
  simetría, transitividad, compatibilidad con `+`, `*`, `^`.

- **`Totient.lean`**: Definir `φ(n)` = número de `k < n` con `gcd(k, n) = 1`.
  Requiere contar elementos — necesitaríamos `count` o usar `DList.length` con
  `DList.filter`. Ya tenemos `gcd`, `DList`, `filter`, `length`, `range_from_one`.
  Es construible.

- **`ChineseRemainder.lean`**: El CRT: si `gcd(m, n) = 1` entonces `∀ a b, ∃ x,
  x ≡ a [MOD m] ∧ x ≡ b [MOD n]`. Necesita `ModEq` + `Coprime` + identidad de
  Bézout (`bezout_natform` ya existe en `Arith.lean`).

- **`PowModTotient.lean`**: Teorema de Euler: `gcd(a, n) = 1 → a^φ(n) ≡ 1 [MOD n]`.
  Necesita `Totient` + `ModEq` + `Pow` + propiedades multiplicativas de `φ`.

**Orden de dependencias:** `ModEq` → `Totient` → `ChineseRemainder` → `PowModTotient`.

### [5] `NumberTheory/` — Roadmap de expansión

Crear un subdirectorio `Peano/PeanoNat/NumberTheory/` (análogo a `Combinatorics/`)
para albergar los nuevos módulos. Hoja de ruta priorizada:

**Tier 1 (alcanzable con infraestructura actual):**

- `ModEq.lean` — congruencias
- `Totient.lean` — función de Euler φ
- `ChineseRemainder.lean` — CRT
- `Fermat.lean` — pequeño teorema de Fermat (corolario de Euler)
- `Wilson.lean` — teorema de Wilson

**Tier 2 (requiere extensiones moderadas):**

- `GCD.lean` — API extendida de gcd/lcm (mover/ampliar desde `Arith.lean`)
- `Fibonacci.lean` — definición recursiva + propiedades
- `Digits.lean` — representación en base b
- `PrimeCounting.lean` — π(x), cotas elementales

**Tier 3 (requiere nueva infraestructura):**

- `ArithmeticFunctions.lean` — Möbius μ, von Mangoldt Λ, σ_k (requiere sumatorios
  generalizados sobre divisores)
- `Squarefree.lean` — libre de cuadrados
- `SmoothNumbers.lean` — B-smooth

**Tier 4 (largo plazo, requiere ℤ y ℚ):**

- Ecuaciones diofánticas, Pell, reciprocidad cuadrática, sumas de cuadrados

### [6] GCD y LCM — ¡Sí existen

**Corrección sobre la comparación anterior:** GCD y LCM **sí están definidos** en
el proyecto, en `Arith.lean`:

- `def gcd (a b : ℕ₀) : ℕ₀` — algoritmo de Euclides con terminación demostrada
- `def lcm (a b : ℕ₀) : ℕ₀ := (mul a b) / (gcd a b)`
- `def IsGCD (a b d : ℕ₀) : Prop`
- `def IsLCM (a b m : ℕ₀) : Prop`
- `def Coprime (a b : ℕ₀) : Prop := IsGCD a b 𝟙`

Además, hay versiones para `ℕ₁`:

- `def gcd₁`, `def IsGCD₁`, `def Coprime₁`

Teoremas exportados (`Peano.lean`):

- `gcd_greatest`, `gcd_divides_linear_combo`, `bezout_natform`
- `gcd_divides_max`, `gcd_divides_min`
- `gcd₁_comm`, `gcd₁_divides_left`, `gcd₁_divides_right`, `gcd₁_divides_both`

En `Primes.lean` (privados, re-derivados):

- `gcd_dvd_left`, `gcd_dvd_right`, `gcd_comm'`
- `gcd_eq_one_iff_coprime`, `prime_not_dvd_imp_coprime`

**Conclusión:** La cobertura de GCD/LCM es sólida. Lo que faltaría respecto a
Mathlib es: `gcd_assoc`, `gcd_comm` (público), `lcm_comm`, `lcm_assoc`,
`gcd_mul_lcm`, `gcd_one_left/right`, `Coprime` API extendida.
El error en la comparación anterior fue que busqué en las secciones equivocadas.

### [7] Secciones 3.4–3.7 de la comparación: líneas de ampliación

**3.4 — Representaciones numéricas:**

- **Digits:** Definir `digits b n` que devuelve `DList ℕ₀` con los dígitos de `n`
  en base `b`. Requiere div/mod (ya los tenemos). Factible.
- **Log:** `log b n` = entero tal que `b^k ≤ n < b^(k+1)`. Tenemos `pow` y orden.
- **Sqrt:** `sqrt n` = entero tal que `k² ≤ n < (k+1)²`. Factible con búsqueda acotada.
- **Pairing:** Función de emparejamiento de Cantor: `pair(a,b) = (a+b)(a+b+1)/2 + a`.
  Tenemos todas las operaciones necesarias.

**3.5 — Fibonacci y sucesiones:**

- Fibonacci se define por recursión directa, trivial con nuestra infraestructura.
- Hyperoperation (generalización +, ×, ^) por doble recursión.

**3.6 — Estructura algebraica:**

- Actualmente instanciamos: `Add`, `LT`, `LE`, `Mul`, `BEq`, `DecidableEq`, `Repr`.
- **Podemos añadir** (sin dependencias externas):
  - `Sub` (ya tenemos la operación, falta la instancia `HSub`)
  - `Div`/`Mod` (instancias)
  - `HPow` (instancia)
  - Clases propias: `CommMonoid ℕ₀` (con `*`), `OrderedCommSemiring ℕ₀`
  - O definir nuestras propias typeclasses equivalentes si no queremos depender de Mathlib.

**3.7 — Factorización prima como `Finsupp`:**

- Mathlib usa `Nat.factorization : ℕ →₀ ℕ` (función con soporte finito: primo → exponente).
- Nosotros tenemos `factorsOf : ℕ₀ → DList ℕ₀` (lista de factores primos con repetición).
- Para emular: definir un tipo `PrimeFactorization` como lista de pares `(primo, exponente)`
  usando `DList (ℕ₀ × ℕ₀)` o `Tuple`-based. Demostrar correspondencia con `factorsOf`.

### [8] Par ordenado como `Tuple 𝟚`

**Sí es posible.** `Tuple 𝟚 = Tuple (σ (σ 𝟘)) = ℕ₀ × (ℕ₀ × Unit)`.

Se puede definir:

```
def OrderedPair := Tuple 𝟚
def mkPair (a b : ℕ₀) : OrderedPair := consTuple a (consTuple b emptyTuple)
def fst (p : OrderedPair) : ℕ₀ := headTuple p
def snd (p : OrderedPair) : ℕ₀ := headTuple (tailTuple p)
```

**Ventaja:** Unifica la noción de par con el sistema de tuplas. Un par es un caso
particular de tupla, como debe ser.

**Desventaja menor:** `Tuple 𝟚` se reduce a `ℕ₀ × (ℕ₀ × Unit)` en vez de `ℕ₀ × ℕ₀`.
El `Unit` extra no molesta computacionalmente pero puede complicar algunas pruebas
(necesitaría un isomorfismo `ℕ₀ × (ℕ₀ × Unit) ≃ ℕ₀ × ℕ₀` o trabajar siempre con
la interfaz `mkPair`/`fst`/`snd`).

**Recomendación:** Definirlo como alias de tipo y encapsular con la API. El `Unit`
queda oculto detrás de las proyecciones.

### [9] Implementación de tácticas — Guía para un proyecto sin Mathlib

**¿Cómo se implementan tácticas en Lean 4?**

En Lean 4, las tácticas se implementan como funciones de tipo `TacticM Unit` usando
la API de metaprogramación (`Lean.Elab.Tactic`). Hay tres niveles:

1. **Macros de tácticas** (`macro_rules`): La forma más simple. Reescriben sintaxis
   a combinaciones de tácticas existentes. Ejemplo: definir `trivial` como
   combinación de `assumption`, `rfl`, `decide`.

2. **`elab_rules`**: Nivel intermedio. Acceso al goal y al contexto local. Se puede
   inspeccionar el tipo del goal, aplicar lemas, crear subgoals.

3. **Elaboradores completos** (`@[tactic ...]`): Control total sobre metas, unificación,
   y producción de términos. Es como escribir en la API de `MetaM`/`TacticM` directamente.

**Tácticas de Mathlib que podríamos emular sin Mathlib:**

| Táctica | Dificultad | Cómo |
|---------|-----------|------|
| `omega` | 🔴 MUY ALTA | Requiere solver aritmético completo. Impracticable sin importar. Lean 4.x la incluye en `Init` — ya está disponible para `Nat`, pero habría que construir un bridge `ℕ₀ ↔ Nat` automático. |
| `decide` | 🟢 GRATIS | Ya funciona si las instancias `Decidable` existen. |
| `norm_num` | 🔴 ALTA | Plugin de normalización numérica. Requiere un evaluador de expresiones aritméticas. |
| `ring` | 🟡 MEDIA | Normalización de expresiones de semianillo. Se puede hacer un mini-`ring` para `ℕ₀` con macro_rules reescribiendo a forma normal (suma de productos). |
| `linarith` | 🔴 ALTA | Solver de aritmética lineal. Impracticable from scratch. |
| `simp` / `simp only` | 🟢 GRATIS | Ya está en Lean 4 core. Solo hay que marcar lemas con `@[simp]`. |
| `positivity` | 🟡 MEDIA | Para ℕ₀ es simple: todo es ≥ 0 trivialmente. |

**Enfoque práctico recomendado:**

1. **Aprovechar `omega` nativa** de Lean 4 via el isomorfismo `Λ`/`Ψ`: definir una
   tactic macro `omega₀` que traduzca el goal de `ℕ₀` a `Nat`, aplique `omega`, y
   traduzca de vuelta.
2. **Registrar `@[simp]` lemas**: Marcar todos nuestros lemas de simplificación
   (`add_zero`, `mul_one`, `σ_τ`, etc.) con `@[simp]` para potenciar `simp`.
3. **Mini-`ring₀`**: Una macro que normalice expresiones de `ℕ₀` reescribiendo a
   forma canónica usando nuestros lemas de conmutatividad/asociatividad/distributividad.
4. **`peano_decide`**: Táctica que, dado un goal decidable sobre `ℕ₀`, aplique
   `decide` tras instanciar las `Decidable` relevantes.

### [10] Resumen de prioridades

Este punto recoge la visión global del autor sobre el orden de las expansiones:

1. **`makingdecidable` branch**: Eliminar usos de `Classical` donde sea posible,
   añadir instancias `DecidableRel`/`DecidablePred` para orden y divisibilidad.
2. **~~Rename `MaxMin` → `Lattice`~~** (DONE) y ampliar la estructura de retículo.
3. **`NumberTheory/` tier 1**: `ModEq` → `Totient` → `ChineseRemainder` → `PowModTotient`.
4. **API de GCD/LCM extendida** (ya existe la base; falta completar).
5. **Representaciones**: `Digits`, `Log`, `Sqrt`, `Fibonacci`, `Pairing`.
6. **Instancias algebraicas**: `HSub`, `HDiv`, `HMod`, `HPow`; typeclasses propias.
7. **Tácticas**: `omega₀` bridge, `@[simp]` labels, mini-`ring₀`.
8. **`OrderedPair` como `Tuple 𝟚`** — refinar API.
9. **Infraestructura de listas y conjuntos finitos** (ver §11 abajo).
10. **Largo plazo**: ℤ, ℚ, ecuaciones diofánticas, teoría analítica elemental.

### [11] Reemplazar `DList` por `List` y construir infraestructura de conjuntos finitos

#### 11.1. `DList` es redundante — usar `List` del core

`DList` (definida en `Arith.lean`) es **exactamente isomorfa** al `List` de
`Init.Prelude` de Lean 4: mismos constructores (`nil`/`cons`), misma semántica.
La diferencia es que `List` viene con ~200+ lemmas en `Init.Data.List`:
`map`, `filter`, `foldl`, `foldr`, `length`, `append`, `reverse`, `zip`, `enum`,
`Membership`, `DecidableEq`, `BEq`, `Repr`, `ToString`, notación `[a, b, c]`, etc.

**Decisión:** Reemplazar `DList α` por `List α` en todo el proyecto. Esto elimina
~40 líneas de definiciones redundantes y hereda toda la API de Init gratis.

**Nota sobre `length`:** `List.length` devuelve `Nat`, no `ℕ₀`. No es problema:
la longitud es metadato, los elementos son `ℕ₀`. Si se necesita, se define:
`def lengthₚ (l : List ℕ₀) : ℕ₀ := Λ l.length`.

#### 11.2. Jerarquía de tipos de lista

Se definen cuatro tipos concretos de lista basados en `List`, parametrizados por
el tipo de sus elementos:

| Tipo | Elementos | Definición |
|------|-----------|-----------|
| `Nat0List` | `ℕ₀` | `List ℕ₀` con `Sorted (· < ·)` y `Nodup` |
| `Nat1List` | `ℕ₁` | `List ℕ₁` con `Sorted (· < ·)` y `Nodup` |
| `Nat2List` | `ℕ₂` | `List ℕ₂` con `Sorted (· < ·)` y `Nodup` |
| `FactList` | `ℕ₂ × ℕ₁` | `List (ℕ₂ × ℕ₁)` con `Sorted lexLt` y `Nodup` en la primera componente |

Donde:

- `ℕ₁ = {n : ℕ₀ // n ≠ 𝟘}` (positivos, ya existe)
- `ℕ₂ = {n : ℕ₁ // n.val ≠ 𝟙}` (≥ 2, ya existe)
- En `FactList`: cada par `(p, e)` tiene `p : ℕ₂` (primo ≥ 2) y `e : ℕ₁` (exponente ≥ 1)
- Orden lexicográfico: `(p₁, e₁) < (p₂, e₂)` ↔ `p₁ < p₂ ∨ (p₁ = p₂ ∧ e₁ < e₂)`
- La condición `Sorted (· < ·)` con orden estricto **implica `Nodup`** automáticamente
  (no hay repeticiones en una lista estrictamente creciente)

**Nota sobre `FactList`:** La condición `Nodup` en la primera componente (primos
distintos) junto con `Sorted` garantiza que cada primo aparece exactamente una vez.
Los exponentes son `ℕ₁` (≥ 1), por lo que no hay factores triviales `p⁰ = 1`.
Esto da **unicidad de representación** de la factorización por el tipo.

#### 11.3. Relación de equivalencia y forma canónica

Para cada tipo `XList` se define:

1. **Relación de equivalencia entre `List`s:** Dos listas son equivalentes si
   contienen los mismos elementos (misma "bolsa" para listas con repetición, o
   mismo conjunto para listas sin repetición). Formalmente:

   ```
   def ListEquiv (l₁ l₂ : List α) : Prop :=
     ∀ x, x ∈ l₁ ↔ x ∈ l₂
   ```

   Para `FactList`, la equivalencia es sobre los pares `(primo, exponente)`.

2. **Forma canónica:** La lista ordenada sin repetición es el representante canónico
   de cada clase de equivalencia. Esto se demuestra con:
   - `sort_equiv`: ordenar una lista produce una lista equivalente
   - `dedup_equiv`: eliminar duplicados produce una lista equivalente
   - `canonical_unique`: dos listas equivalentes tienen la misma forma canónica
   - `canonical_sorted`: la forma canónica está ordenada
   - `canonical_nodup`: la forma canónica no tiene duplicados

3. **Representabilidad:** Toda `List α` tiene una forma canónica, y la forma
   canónica de una `XList` es ella misma (ya está ordenada y sin repetición).

#### 11.4. Setoides: `ℕ₀FSet`, `ℕ₁FSet`, `ℕ₂FSet`, `ℕ₂×ℕ₁FSet`

Se construyen como setoides (tipos + relación de equivalencia) y luego se definen
los conjuntos finitos como el tipo cociente o, pragmáticamente, como la forma
canónica (lista ordenada sin repetición):

| Setoide | Tipo subyacente | Relación | Representante canónico |
|---------|----------------|----------|----------------------|
| `ℕ₀FSet` | `Nat0List` | `ListEquiv` | Lista ordenada creciente de `ℕ₀` |
| `ℕ₁FSet` | `Nat1List` | `ListEquiv` | Lista ordenada creciente de `ℕ₁` |
| `ℕ₂FSet` | `Nat2List` | `ListEquiv` | Lista ordenada creciente de `ℕ₂` |
| `ℕ₂×ℕ₁FSet` | `FactList` | `ListEquiv` | Lista lex-ordenada de `(ℕ₂, ℕ₁)` |

**Implementación concreta (opción preferida):** En lugar de quotient types
(que introducirían `noncomputable`), usar directamente la forma canónica como
**tipo opaco** con smart constructors:

```
structure ℕ₀FSet where
  elems : List ℕ₀
  sorted : List.Sorted (· < ·) elems
```

Donde `List.Sorted (· < ·)` implica `Nodup` (estrictamente creciente = sin repetición).

#### 11.5. Operaciones de conjunto — decidibles y computables

Todas las operaciones siguientes son **computables** (no `noncomputable`) y
**decidibles** (devuelven `Bool` o tienen instancias `Decidable`):

**Operaciones básicas para `ℕ₀FSet` (y análogas para los otros):**

| Operación | Tipo | Notas |
|-----------|------|-------|
| `empty` | `ℕ₀FSet` | `⟨[], trivial⟩` |
| `singleton x` | `ℕ₀FSet` | `⟨[x], trivial⟩` |
| `insert x S` | `ℕ₀FSet` | Inserción ordenada preservando invariante |
| `remove x S` | `ℕ₀FSet` | Filtrado preservando orden |
| `mem x S` | `Bool` (`Decidable`) | Búsqueda binaria o lineal en lista ordenada |
| `union S T` | `ℕ₀FSet` | Merge de listas ordenadas |
| `inter S T` | `ℕ₀FSet` | Intersección de listas ordenadas |
| `diff S T` | `ℕ₀FSet` | Diferencia de listas ordenadas |
| `subset S T` | `Bool` (`Decidable`) | Recorrido simultáneo |
| `eq S T` | `Bool` (`DecidableEq`) | Comparación de listas (canónicas = iguales) |
| `card S` | `ℕ₀` | Longitud (vía `Λ ∘ List.length`) |
| `filter p S` | `ℕ₀FSet` | Filtro preservando orden |
| `map f S` | `ℕ₀FSet` | Aplicar `f` y re-canonicalizar |
| `fold f init S` | `α` | Fold sobre lista subyacente |
| `toList S` | `List ℕ₀` | Extracción de la lista ordenada |
| `fromList l` | `ℕ₀FSet` | Ordenar + deduplicar |

**Propiedades a demostrar:**

- `mem_union`: `x ∈ union S T ↔ x ∈ S ∨ x ∈ T`
- `mem_inter`: `x ∈ inter S T ↔ x ∈ S ∧ x ∈ T`
- `mem_diff`: `x ∈ diff S T ↔ x ∈ S ∧ x ∉ T`
- `subset_iff`: `subset S T ↔ ∀ x, x ∈ S → x ∈ T`
- `eq_iff_subset_both`: `S = T ↔ subset S T ∧ subset T S`
- `union_comm`, `union_assoc`, `inter_comm`, `inter_assoc`
- `union_inter_distrib`, `inter_union_distrib`
- `card_union_inter`: `card(S ∪ T) + card(S ∩ T) = card S + card T`

**Instancias a registrar:**

- `DecidableEq ℕ₀FSet` (comparación de listas canónicas)
- `Membership ℕ₀ ℕ₀FSet` (`.mem`)
- `Union ℕ₀FSet`, `Inter ℕ₀FSet` (notación `∪`, `∩`)
- `HasSubset ℕ₀FSet` (notación `⊆`)
- `EmptyCollection ℕ₀FSet` (notación `∅`)
- `Repr ℕ₀FSet`, `BEq ℕ₀FSet`

#### 11.6. Módulos de infraestructura propuestos

| Módulo | Namespace | Contenido |
|--------|-----------|-----------|
| `Peano/PeanoNat/Lists.lean` | `Peano.Lists` | Definiciones base: `Nat0List`, `Nat1List`, `Nat2List`, `FactList`. Órdenes inducidos sobre `ℕ₁`, `ℕ₂`, `ℕ₂ × ℕ₁`. Relación de equivalencia `ListEquiv`. Forma canónica `canonicalize`. Teoremas de equivalencia y unicidad. |
| `Peano/PeanoNat/FSet.lean` | `Peano.FSet` | Setoides. Structures `ℕ₀FSet`, `ℕ₁FSet`, `ℕ₂FSet`, `ℕ₂×ℕ₁FSet`. Smart constructors (`empty`, `singleton`, `insert`, `fromList`). Operaciones de conjunto (`union`, `inter`, `diff`, `subset`, `mem`). Instancias `Decidable`, `DecidableEq`, `Membership`, `Union`, `Inter`. Propiedades algebraicas. |

**Dependencias:**

```
PeanoNat.lean (ℕ₀, ℕ₁, ℕ₂)
    ↓
Axioms.lean
    ↓
StrictOrder.lean + Order.lean (órdenes para ℕ₀)
    ↓
Lists.lean (listas tipadas, equivalencia, forma canónica)
    ↓
FSet.lean (conjuntos finitos, operaciones)
    ↓
Arith.lean (usa FSet para factorsOf, DivisorsList, etc.)
```

#### 11.7. Migración de `DList` — plan de transición

1. Crear `Lists.lean` y `FSet.lean` con la nueva infraestructura.
2. En `Arith.lean`: reemplazar `DList ℕ₀` por `List ℕ₀` (o por `ℕ₀FSet` donde
   corresponda). Eliminar las 40 líneas de definición de `DList` y sus operaciones.
3. `DivisorsList` pasa a ser un `ℕ₁FSet` (divisores son positivos).
4. `factorsOf` devuelve un `ℕ₂FSet` (factores son ≥ 2) o un `List ℕ₂`.
5. En `Primes.lean`: `PrimeList` se redefine como `List ℕ₂` con predicado
   `∀ p ∈ l, Prime p.val.val`. La factorización como `FactList` o `ℕ₂×ℕ₁FSet`.
6. `product_list` opera sobre `List ℕ₀` directamente (vía `List.foldl mul 𝟙`).

#### 11.8. Relación con `Tuple`

- `Tuple n` es un tipo **de longitud fija** indexado por `ℕ₀`.
- `List α` / `ℕ₀FSet` son tipos **de longitud variable**.
- Son complementarios, no competidores:
  - `Tuple` para aridad fija (argumentos de funciones, pares ordenados vía `Tuple 𝟚`).
  - `List`/`FSet` para colecciones dinámicas (divisores, factores, rangos).
- `OrderedPair := Tuple 𝟚` sigue siendo válido como abstracción de par.

---

## Future Directions

- Integer extension (ℤ from ℕ₀)
- Rational numbers (ℚ from ℤ)
- Connection to Lean 4's native `Nat` type
