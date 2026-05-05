# Thoughts — Peano

**Last updated:** 2026-05-02
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

### 2026-05-05 — Segundo y tercer teoremas de isomorfismos entre grupos

#### Segundo teorema de isomorfismos

Sea ⟨G, *⟩ grupo, H ≤ G, subgrupo, y N ⊴ G, subgrupo normal. Entonces:

- H ∩ N ⊴ H

- HN = {h * n | h ∈ H, n ∈ N} ≤ G

- N ⊴ HN

- (HN)/N ≃ H/(H ∩ N)

Vamos a ver el primer punto: H ∩ N ⊴ H. Para ello, tomamos h ∈ H y k ∈ H ∩ N. Entonces, como N es normal en G, tenemos que h *k* h⁻¹ ∈ N. Además, como H es un subgrupo de G, tenemos que h *k* h⁻¹ ∈ H. Por lo tanto, h *k* h⁻¹ ∈ H ∩ N, lo que demuestra que H ∩ N es normal en H.

Vamos a ver el sugndo punto: HN = {h *n | h ∈ H, n ∈ N} ≤ G. Para ello, tomamos h₁* n₁, h₂ *n₂ ∈ HN. Entonces, (h₁* n₁) *(h₂* n₂) = h₁ *(n₁* h₂) *n₂. Como N es normal en G, tenemos que n₁* h₂ = h₂' *n₁' para algún h₂' ∈ H y n₁' ∈ N. Por lo tanto, (h₁* n₁) *(h₂* n₂) = h₁ *h₂'* (n₁' *n₂), lo que demuestra que HN es cerrado bajo la operación de grupo. Además, el elemento identidad e ∈ HN ya que e = e* e con e ∈ H y e ∈ N. Finalmente, para cada h *n ∈ HN, su inverso es (h* n)⁻¹ = n⁻¹ * h⁻¹, que también pertenece a HN ya que n⁻¹ ∈ N y h⁻¹ ∈ H. Por lo tanto, HN es un subgrupo de G.

El tercer punto: N ⊴ HN. Para ello, tomamos h *n ∈ HN y k ∈ N. Entonces, (h* n) *k* (h *n)⁻¹ = h* (n *k* n⁻¹) *h⁻¹. Como N es normal en G, tenemos que n* k *n⁻¹ ∈ N. Además, como H es un subgrupo de G, tenemos que h* (n *k* n⁻¹) *h⁻¹ ∈ N. Por lo tanto, (h* n) *k* (h * n)⁻¹ ∈ N, lo que demuestra que N es normal en HN.

Vamos a finiquitar el cuarto punto: (HN)/N ≃ H/(H ∩ N). Para ello, toma h ∈ H. Entonces, el coset hN ∈ (HN)/N. Definamos la función φ : H/(H ∩ N) → (HN)/N por φ(h(H ∩ N)) = hN. Para mostrar que φ es un isomorfismo, primero debemos verificar que está bien definida. Si h₁(H ∩ N) = h₂(H ∩ N), entonces h₁⁻¹ * h₂ ∈ H ∩ N ⊆ N, lo que implica que h₁N = h₂N. Por lo tanto, φ está bien definida. Ahora, veamos que φ es un homomorfismo de grupos.

#### Tercer teorema de isomorfismos

Sea ⟨G, *⟩ grupo, y N₁, N₂ ⊴ G, subgrupos normales, N₁ ⊂ N₂. Entonces:

- N₂/N₁ ⊴ G/N₁

- (G/N₁)/(N₂/N₁) ≃ G/N₂

- Si G/N₂ es cíclico, entonces (G/N₁)/(N₂/N₁) es cíclico.

#### Cuarto teorema de isomorfismos

Sea $G$ un grupo y $N$ un subgrupo normal de $G$. Existe una correspondencia biunívoca entre:

- El conjunto de subgrupos de $G$ que contienen a $N$

- El conjunto de todos los subgrupos del grupo cociente $G/N$.

#### Lema de Zassenhaus (o de la Mariposa)

Sea $G$ un grupo y $A$, $B$ dos subgrupos de $G$. Entonces existe un isomorfismo entre los grupos cocientes $(A \cap B) \backslash A$ y $(A \cap B) \backslash B$.

Sean $U$ y $V$ subgrupos de un grupo finito $G$, y sean $u \trianglelefteq U$ y $v \trianglelefteq V$ sus respectivos subgrupos normales. El lema establece el siguiente isomorfismo:

$$\frac{u(U \cap V)}{u(U \cap v)} \cong \frac{v(V \cap U)}{v(V \cap u)}$$

¿Cómo se construye este isomorfismo?El isomorfismo no se define directamente entre los dos extremos, sino que ambos se demuestran isomorfos a un término central común basado en las intersecciones.

La construcción sigue estos pasos:

1. Identificar el "núcleo" común. Se define un grupo central que combina las intersecciones:

   - Denominador común: $(U \cap v)(V \cap u)$

   - Numerador común: $(U \cap V)$

2. Aplicar el Segundo Teorema. Se utiliza el segundo teorema de isomorfismo (el del diamante) para demostrar que:

   - El lado izquierdo es isomorfo a: $\frac{U \cap V}{(U \cap v)(U \cap v \cap u)}$ que se simplifica a $\frac{U \cap V}{(U \cap v)(V \cap u)}$.

   - El lado derecho es isomorfo exactamente a la misma expresión.

### 2026-04-08 — Infrastructure modernization

Migrated from the old `.bat`-based freeze system to the template-standard
`git-lock.bash` system with two levels (lock + freeze), pre-commit hook, and
Makefile integration. The old system only had freeze/unfreeze with no
session-based locking.

---

## Open Questions

- [ ] Should export blocks in Peano.lean be migrated to individual leaf modules per §30?
- [ ] Is the Peano/ vs Peano namespace mismatch worth resolving?
- [ ] Should FSetFunction.lean (~1550 lines, ~92 declarations) be split into smaller modules?
- [ ] How to approach `sylow_third_mod` and `sylow_third_dvd`? (requires normalizer N_G(K) — not yet in library)

**Resolved questions (no longer open):**

- ~~How to approach the remaining sorry in group theory modules~~ → All 3 Sylow theorems closed; 5 private axioms remain (Wielandt route).
- ~~FSet design: Quotient vs sorted list~~ → Sorted list (ADR-007).
- ~~FinGroup polymorphism approach~~ → Opción A implemented (ADR-010, 2026-04-27).
- ~~Phase F Foundation (CantorPairing + GodelBeta)~~ → Phase F completamente terminada (2026-05-02): F.1 CantorPairing ✅, F.2 GodelBeta ✅, F.3 paraguas Foundation.lean ✅.

---

## Nuevas cuestiones (15:30/27-04-2026)

- Una vez cubierto el problema fundacional en el proyecto AczelSetTheory, que consigue fundamentar desde Peano sin axiomas adicionales las listas de Lean 4, ¿es posible que en AczelSetTheory se defina un tipo natural como `def Nat := List Unit` o similar, o incluso mejor, a partir del solo tipo HFSet?. Esto daría mucha libertad de acción en AczelSetTheory, de hecho, una vez el embedding Peano -> Aczel es lógicamente completo, debería dejar de desarrollar Peano, en el sentido que todo sería mucho más expresivo en AczelSetTheory. ¿Estoy en lo cierto?

- Si la respuesta a la pregunta anterior es afirmativa, creo que además todo lo que es computable en Peano, va ser perfectamente computable en AczelSetTheory, y por lo tanto, el proyecto AczelSetTheory va a ser un proyecto de desarrollo de una biblioteca de teoría de conjuntos, con un embedding completo de Peano, pero sin necesidad de desarrollar Peano. ¿Estoy en lo cierto?

- Si la respuesta a la pregunta anterior es afirmativa, en este proyecto solo quedaría terminar los coletazos que aún nos quedan abiertos, que son muy pocos, y la labor principipal pasaría a ser estar básicamente en modo mantenimiento, corrigiendo bugs y añadiendo pequeñas cosas, pero sin necesidad de desarrollar nada nuevo. La labor pasaría básicamente a AczelSetTheory, que sería tan computable como este proyecto. ¿Estoy en lo cierto?

- El paso natural sería en AczelSetTheory definir la infraestructura y as importaciones desde Peano, y casi vaciar el actual proyecto Peano más que para la parte puramente fundacional.

- El otro problema a abordar es la migración de REFERENCE.md monolítico actual a un sistema de REFERENCE-{Temática Matemática}.md en árbol con el mismo formato (idéntico) solo que cada nodo de documentación tiene que ofrecer enlaces a los siguientes y anteriores nodos de documentación, incluyendo README.md, y escondiendo del directorio raíz el complejo de documentación, pasandoe stea  el directorio /raíz/doc/. Esto es importante para evitar la deriva de la documentación, y para que los AIs asistentes puedan navegar por la documentación sin perder el contexto.

---

## Lessons Learned

### Inductive Type Approach

- Defining `ℕ₀` as an inductive type gives all Peano axioms for free as proven theorems
- The recursion principle is the most powerful tool — all arithmetic flows from it
- Well-foundedness proofs are needed for termination of recursive definitions

### Module Organization

- The linear dependency chain (Axioms → Order → Arithmetic → Advanced) works well
- Each module builds strictly on previous ones — no circular dependencies
- 51 modules with 4 subdirectories: ListsAndSets/, NumberTheory/, Combinatorics/, GroupTheory/
- FSetFunction.lean is the largest module (~1500 lines, ~92 exported declarations)

### Documentation

- REFERENCE.md must be self-sufficient for AI assistants
- The "project" protocol (AI-GUIDE.md §12) prevents documentation drift

### Isomorfismos Nat↔ℕ₀ — Lecciones (2026-04-09)

- **`Coe Nat ℕ₀` causa ambigüedad de operadores**: `(Ψ x + 1) * Ψ y` es ambiguo entre
  ops de Peano y ops de Nat. Solución: evitar `show` con aritmética infix; usar rewrites
  explícitos (`Nat.add_mul`, `Nat.one_mul`) o calificadores (`Nat.div`).
- **Patrón `congrArg Ψ` + rewrite en hipótesis**: Cuando `rw [isomorph_Ψ_add]` en el
  objetivo reescribe al revés (por la coerción), transportar la hipótesis con
  `congrArg Ψ h_eq` y luego `rw [...] at h_transported`.
- **`isomorph_Ψ_mod` requiere `m ≠ 𝟘`**: Peano define `mod n 𝟘 = 𝟘` pero
  Lean core define `Nat.mod n 0 = n`. No hay isomorfismo incondicionado.
- **`Nat.mod` vs `%`**: Son definicionalmente iguales pero `rw` exige coincidencia
  sintáctica. Bridge con `have : ... % ... := by rw [...]; exact this`.
- **`omega` no resuelve div/mod no-lineales**: Hay que usar `Nat.div_eq_of_lt_le` explícitamente.

### Foundation/GodelBeta.lean — Lecciones (2026-05-02)

- **`List.map_congr` no existe en Lean 4 core**: el nombre correcto es `List.map_congr_left`.
- **`isomorph_Λ_le i m : le₀ (Λ i) (Λ m) ↔ i ≤ m`**: la dirección `.mp` va de `i ≤ m` a
  `le₀ (Λ i) (Λ m)`, no al revés. Confundir la dirección bloquea la prueba silenciosamente.
- **`set` tactic no disponible**: en Lean 4 core sin Mathlib, usar `let`/`have` en su lugar.
- **`List.range_succ_eq_map`**: existe en Lean 4 core; permite demostrar `list_map_getD_range`
  por inducción con `simp [List.range_succ_eq_map]` (cierra automáticamente).
- **`List.length_pos.mpr` no existe en este contexto**: usar `Nat.succ_pos xs.length` para
  probar `0 < (x :: xs).length`.
- **`noncomputable def` + `Classical.choice`**: la no-computabilidad de `encodeList` es
  inevitable; el `decodeList` sí es computable (puro `map` sobre `List.range`).

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

**Situación actual:** Renombrado completado. `Lattice.lean` (antes `MaxMin.lean`) define `max`, `min`, `min_max` y teoremas de idempotencia, conmutatividad, asociatividad, distributividad, y relación con `≤`/`<`.

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

Subdirectorio `Peano/PeanoNat/NumberTheory/` creado y operativo.

**Tier 1 — ✅ Completado:**

- ~~`ModEq.lean`~~ ✅ — congruencias modulares
- ~~`Totient.lean`~~ ✅ — función de Euler φ
- ~~`ChineseRemainder.lean`~~ ✅ — CRT
- ~~`Fermat.lean`~~ ✅ — pequeño teorema de Fermat (corolario de Euler)
- `Wilson.lean` — teorema de Wilson (pendiente)

**Tier 2 (requiere extensiones moderadas):**

- ~~`GCD.lean`~~ ✅ Implementado en `Arith.lean` § 8 (25 teoremas Mathlib-style)
- ~~`Fibonacci.lean`~~ ✅ en `Combinatorics/Fibonacci.lean`
- ~~`Digits.lean`~~ ✅ en `PeanoNat/Digits.lean`
- `PrimeCounting.lean` — π(x), cotas elementales (pendiente)

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

**✅ Actualización (paso [3]):** Se han añadido 25 teoremas Mathlib-style en
`Arith.lean` § 8, incluyendo: `gcd_comm` (público), `gcd_assoc`, `gcd_mul_lcm`,
`lcm_comm`, `gcd_one_left/right`, `gcd_zero_left/right`, `gcd_self`,
`gcd_eq_zero_iff`, `div_mul_cancel`, `dvd_gcd_iff`, `dvd_lcm_left/right`,
`lcm_self`, `coprime_comm`, `coprime_one_left/right`. Pendientes para Primes.lean:
`lcm_dvd`, `IsLCM_lcm` (requieren `coprime_dvd_of_dvd_mul`).

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

**3.6 — Estructura algebraica:** ✅ Completado

- Instancias implementadas: `Add`, `LT`, `LE`, `Mul`, `BEq`, `DecidableEq`, `Repr`,
  `HSub`, `HDiv`, `HMod`, `HPow`, `Zero`, `One`, `OfNat`, `Ord`,
  `WellFoundedRelation`, `DecidableRel` (para LT, LE, Divides, Prime, IsEven, IsOdd).
- Clases propias decididas en ADR-006: no definir typeclasses algebraicas propias (CommMonoid, etc.)
  por el momento; mantener lemas sueltos que verifican las propiedades.

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

### [10] Resumen de prioridades (actualizado 2026-04-16)

Este punto recoge la visión global del autor sobre el orden de las expansiones:

1. ~~**`makingdecidable` branch**~~: ✅ Decidabilidad completa implementada (LT, LE, Prime, IsEven, IsOdd, Divides).
2. ~~**Rename `MaxMin` → `Lattice`**~~: ✅ Completado + 18 extensiones Mathlib-style.
3. ~~**`NumberTheory/` tier 1**~~: ✅ `ModEq` → `Totient` → `ChineseRemainder` → `Fermat` — todos completados.
4. ~~**API de GCD/LCM extendida**~~: ✅ 25 teoremas Mathlib-style en Arith.lean § 8.
5. ~~**Representaciones**~~: ✅ `Digits`, `Log`, `Sqrt`, `Fibonacci`, `Pairing` — todos completados.
6. ~~**Instancias algebraicas**~~: ✅ `HSub`, `HDiv`, `HMod`, `HPow`, Zero, One, OfNat, Ord, WellFoundedRelation, DecidableRel.
7. ~~**Infraestructura de conjuntos finitos**~~: ✅ List, FSet, FSetFSet, FSetFunction (~90 decl.), MapOn, Im, Pigeonhole, Perm.
8. **Eliminar 5 axiomas privados en Sylow.lean** — ruta Wielandt en curso (2/5 pasos completados: `prime_dvd_binom_prime`, `binom_prime_row`).
9. **Tácticas**: `omega₀` bridge, `@[simp]` labels, mini-`ring₀`.
10. **Phase 22**: ℤ — tipo inductivo canónico, operaciones, orden, aritmética.
11. **Phase 23**: ℚ — estructura con invariante de coprimalidad, operaciones, campo.
12. **Largo plazo**: ecuaciones diofánticas, polinomios Q[x], teoría analítica elemental.

### [11] Reemplazar `DList` por `List` y construir infraestructura de conjuntos finitos

> **Estado (2026-04-15):** ✅ Implementado. La migración DList → List se completó.
> La jerarquía real difiere del plan original: `List` → `FSet` (tipo cociente
> por permutación, sin invariante de orden) → `FSetFSet` → `FSetFunction` (~90 decl.).
> Las listas ordenadas sin duplicados (§11.2) no se adoptaron; en cambio, `FSet`
> usa `Quotient (Perm.setoid α)` — más elegante pero introduce `noncomputable`
> para `DecidableEq`. Ver `LISTS_FSETS_N_FSETFUNCTIONS.md` para detalles.

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
| `Peano/PeanoNat/List.lean` | `Peano.List` | Definiciones base: `Nat0List`, `Nat1List`, `Nat2List`, `FactList`. Órdenes inducidos sobre `ℕ₁`, `ℕ₂`, `ℕ₂ × ℕ₁`. Relación de equivalencia `ListEquiv`. Forma canónica `canonicalize`. Teoremas de equivalencia y unicidad. |
| `Peano/PeanoNat/FSet.lean` | `Peano.FSet` | Setoides. Structures `ℕ₀FSet`, `ℕ₁FSet`, `ℕ₂FSet`, `ℕ₂×ℕ₁FSet`. Smart constructors (`empty`, `singleton`, `insert`, `fromList`). Operaciones de conjunto (`union`, `inter`, `diff`, `subset`, `mem`). Instancias `Decidable`, `DecidableEq`, `Membership`, `Union`, `Inter`. Propiedades algebraicas. |

**Dependencias:**

```
PeanoNat.lean (ℕ₀, ℕ₁, ℕ₂)
    ↓
Axioms.lean
    ↓
StrictOrder.lean + Order.lean (órdenes para ℕ₀)
    ↓
List.lean (listas tipadas, equivalencia, forma canónica)
    ↓
FSet.lean (conjuntos finitos, operaciones)
    ↓
Arith.lean (usa FSet para factorsOf, DivisorsList, etc.)
```

#### 11.7. Migración de `DList` — plan de transición

1. Crear `List.lean` y `FSet.lean` con la nueva infraestructura.
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

## 12. Posibilidades para la extensión entera (ℤ) y racional (ℚ)

- La primera idea es definir $\mathbb(Z)$ como un tipo inductivo del tipo:

```lean
inductive ℤ where
  | pos : ℕ₀ → ℤ
  | neg : ℕ₁ → ℤ
```

y dado el par de ℕ₀ × ℕ₀, definimos la función de equivalencia:

```lean
def int_equiv : ℕ₀ × ℕ₀ → ℤ
  | (a, b) => if a ≥ b then ℤ.pos (a - b) else ℤ.neg (b - a)
```

y también la dada el número entero z, definimos la representación como un par de naturales:

```lean
def int_repr : ℤ → ℕ₀ × ℕ₀
  | ℤ.pos n => (n, 0)
  | ℤ.neg n => (0, n.val)
```

las operaciones se realizan sobre los pares ordenados, y luego se canonizan a través de `int_equiv`. Creo que no habría por qué introducir `Quotient` ni `Setoid` con este mecanismo.

Las definiciones para el orden son sencillas: `ℤ.pos a < ℤ.pos b` si `a < b`, `ℤ.neg a < ℤ.neg b` si `a > b`, y `ℤ.neg _ < ℤ.pos _` siempre. La suma se define como `(a₁, b₁) + (a₂, b₂) = (a₁ + a₂, b₁ + b₂)` y la multiplicación como `(a₁, b₁) * (a₂, b₂) = (a₁ * a₂ + b₁ * b₂, a₁ * b₂ + a₂ * b₁)`. La resta se puede definir como `a - b = a + (-b)`, donde `-b` se obtiene intercambiando las componentes del par.

Necesitaríamos las funciones de canonización (canon) para asegurar que cada entero tiene una representación única, y demostrar que las operaciones son compatibles con la relación de equivalencia dada por `int_equiv`.

También necesitamos las funciones `abs` y `sign` para definir el valor absoluto y el signo de un entero, lo que facilitará la definición de la función de orden y otras propiedades.

También pondremos las funciones de comparación (`<`, `≤`, `>`, `≥`) y las instancias de `Decidable` para estas relaciones, lo que permitirá usar tácticas como `decide` para resolver metas que involucren comparaciones entre enteros. Las instancias de Decidable para la igualdad también serán necesarias para trabajar con enteros. También pondremos los predicados `IsEven` y `IsOdd` (que habría que pasar también a ℕ₀).

- La idea para definir el tipo $\mathbb{Q}$ como un tipo inductivo va ser mucho más difícil. En principio se puede hacer algo parecido a lo anterior:

```lean
inductive ℚ where
  | rat : ℤ × ℕ₁ → ℚ
```

donde el par `(z, n)` representa la fracción `z / n`. La relación de equivalencia sería algo como:

```lean
def rat_equiv : (ℤ × ℕ₁) → (ℤ × ℕ₁) → Prop
  | (z₁, n₁), (z₂, n₂) => z₁ * n₂ = z₂ * n₁
```

Obtenemos el representante canónico del par como `rat_equiv`-equivalente a `(z, n)` con `gcd(z.val, n.val) = 1` y `n.val > 0`. Las operaciones de suma, resta, multiplicación y división se definen sobre los pares ordenados y luego se canonizan usando `rat_equiv`.

La comparación dadas dos fracciones `z₁ / n₁` y `z₂ / n₂` se puede definir como `z₁ * n₂ < z₂ * n₁`, lo que es compatible con la relación de equivalencia. También se pueden definir las instancias de `Decidable` para la igualdad y las comparaciones, lo que permitirá usar tácticas como `decide` para resolver metas que involucren racionales.

---

## Future Directions

- Integer extension (ℤ from ℕ₀)
- Rational numbers (ℚ from ℤ)
- Connection to Lean 4's native `Nat` type

---

## 2026-04-09 — Typeclasses de orden y álgebra: ¿LinearOrder, CommSemiring, ring?

### Contexto

Se plantean dos líneas de trabajo:

**Línea A (orden):** Instanciar `LinearOrder ℕ₀`, derivar `le_total`, `lt_or_ge`,
`le_or_lt`, `sup_eq_max`, `inf_eq_min`, `WellFoundedRelation ℕ₀`,
`ℕ₀.strongRecOn`, `ℕ₀.strongInductionOn`.

**Línea B (álgebra):** Instanciar `CommSemiring ℕ₀`, `OrderedSemiring ℕ₀`,
`CanonicallyOrderedCommSemiring ℕ₀`, y alguna forma de `Ring` (commutativa, sin
divisores de cero) para habilitar la táctica `ring`.

### Inventario de disponibilidad en Lean 4.29.0 Init (sin Mathlib)

Se verificó experimentalmente qué typeclasses existen en `Init`:

| Typeclass | ¿En Init? | Notas |
|-----------|-----------|-------|
| `WellFoundedRelation` | ✅ Sí | `rel : α → α → Prop`, `wf : WellFounded rel` |
| `Add`, `Mul`, `Sub`, `Div`, `Mod` | ✅ Sí | Clases básicas de operaciones |
| `HPow`, `HSub`, `HDiv`, `HMod` | ✅ Sí | Versiones heterogéneas |
| `Zero`, `One`, `OfNat` | ✅ Sí | Literales numéricos |
| `LT`, `LE` | ✅ Sí | Orden (ya instanciados) |
| `Ord` | ✅ Sí | `compare : α → α → Ordering` |
| `LinearOrder` | ❌ **Mathlib** | `Preorder` + `PartialOrder` + `le_total` + `decidable_le` |
| `Preorder` | ❌ **Mathlib** | `le_refl`, `le_trans` |
| `PartialOrder` | ❌ **Mathlib** | `Preorder` + `le_antisymm` |
| `Monoid`, `CommMonoid` | ❌ **Mathlib** | Estructuras multiplicativas |
| `AddMonoid`, `AddCommMonoid` | ❌ **Mathlib** | Estructuras aditivas |
| `Semiring`, `CommSemiring` | ❌ **Mathlib** | Anillo sin resta |
| `Ring` | ❌ **Mathlib** | Anillo con grupo aditivo |
| `OrderedSemiring` | ❌ **Mathlib** | Semianillo + orden compatible |
| `WellFoundedLT` | ❌ **Mathlib** | `WellFounded (· < ·)` |

**Conclusión clave:** `LinearOrder`, `CommSemiring`, `OrderedSemiring`,
`CanonicallyOrderedCommSemiring` y **toda la jerarquía algebraica son de Mathlib**.
Sin Mathlib, **no existen** esas typeclasses.

### Línea A: Orden — Análisis

#### A.1. Lo que ya tenemos (sin typeclasses formales)

| Propiedad | Teorema existente | Archivo |
|-----------|------------------|---------|
| `le_refl` | `le_refl` | Order.lean |
| `le_trans` | `le_trans` | Order.lean |
| `le_antisymm` | `le_antisymm` | Order.lean |
| `le_total` | `le_total` | Order.lean (línea 445) |
| `lt_iff_le_not_le` | Derivable de `lt_imp_le` + `lt_then_neq` | — |
| `decidable_le` | `decidableLe` (instancia) | Order.lean |
| `decidable_lt` | `decidableLt` (instancia) | StrictOrder.lean |
| `well_founded_lt` | `well_founded_lt` | WellFounded.lean |
| `max`/`min` | `max`, `min` con 18+ teoremas | Lattice.lean |

#### A.2. Lo que falta para la semántica de LinearOrder

Aunque no podemos instanciar `LinearOrder` (no existe sin Mathlib), podemos
**implementar todos los teoremas equivalentes** con nombres Mathlib-compatibles:

| Teorema | Estado | Cómo implementar |
|---------|--------|-------------------|
| `le_total` | ✅ Ya existe | Order.lean |
| `lt_or_ge (a b : ℕ₀) : Lt a b ∨ Le b a` | ❌ Falta | Directo de `le_total` + `le_iff_lt_or_eq` |
| `le_or_lt (a b : ℕ₀) : Le a b ∨ Lt b a` | ❌ Falta | Simétrico de `lt_or_ge` |
| `sup_eq_max` / `inf_eq_min` | ❌ Falta | Definir `Sup`/`Inf` como alias de `max`/`min` |
| `strongRecOn` | ❌ Falta | Via `WellFounded.recursion well_founded_lt` |
| `strongInductionOn` | ❌ Falta | Variante proposicional de `strongRecOn` |

#### A.3. WellFoundedRelation ℕ₀

**Sí es factible.** `WellFoundedRelation` está en Init:

```lean
instance : WellFoundedRelation ℕ₀ where
  rel := Lt
  wf  := well_founded_lt
```

Esto habilita recursión con `termination_by` sobre `ℕ₀` usando `Lt`.

#### A.4. Recomendación Línea A

**Implementar** — es autocontenido, de complejidad baja-media, y desbloquea:

- `termination_by` nativo sobre `ℕ₀` (vía `WellFoundedRelation`)
- `strongRecOn`/`strongInductionOn` (herramientas de demostración potentes)
- Nombres Mathlib-compatibles para teoremas de orden existentes

**Ubicación:** Nuevos teoremas en `Order.lean` y `WellFounded.lean`.
Instancia `WellFoundedRelation` en `WellFounded.lean`.

### Línea B: Álgebra — Análisis

#### B.1. El problema fundamental

Sin Mathlib no existen las typeclasses `CommSemiring`, `OrderedSemiring`, etc.
Hay **tres opciones**:

**Opción B1: Importar Mathlib.**

- Pro: Acceso inmediato a toda la jerarquía + tácticas `ring`, `linarith`, `field_simp`.
- Contra: **Rompe la filosofía del proyecto** ("self-contained, no Mathlib").
  Compila ~2000 archivos. El tiempo de build pasa de ~15s a ~15min.

**Opción B2: Definir nuestras propias typeclasses (mini-álgebra Peano).**

- Pro: Autocontenido. Podemos adaptarlas a nuestras necesidades.
- Contra: Duplicación enorme. La jerarquía Mathlib tiene ~40 clases interrelacionadas.
  Incluso un subset mínimo (`AddCommMonoid` → `CommMonoidWithZero` → `Semiring` →
  `CommSemiring` → `OrderedCommSemiring`) son ~8 clases con ~30 axiomas totales.
  Y la táctica `ring` **no funciona con clases custom** — es un plugin de Lean/Mathlib
  que despacha específicamente sobre la jerarquía de Mathlib.

**Opción B3: No instanciar typeclasses algebraicas, pero implementar un mini-ring₀.**

- Pro: Pragmático. Los teoremas ya existen (`add_comm`, `mul_assoc`, `mul_add`, etc.).
  Una macro de táctica `ring₀` puede normalizar expresiones reescribiendo con esos lemas.
- Contra: La táctica sería rudimentaria (no un decision procedure completo).

#### B.2. La táctica `ring` — qué necesita realmente

La táctica `ring` de Lean 4 / Mathlib:

1. Refleja la expresión del goal en un tipo de datos `RingExpr`.
2. Normaliza a una forma canónica (polinomio en variables ordenadas).
3. Compara ambos lados normalizados.
4. Produce un proof term usando lemas de `CommSemiring`/`CommRing`.

**Puntos clave:**

- Requiere **exactamente** las typeclasses de Mathlib (despacha por nombre).
- No se puede "engañar" con clases propias a menos que se reimplemente el plugin.
- Reimplementar `ring` desde cero es un proyecto de ~1000 líneas de metaprogramación.

#### B.3. Alternativa práctica: `ring₀` como macro rewriter

En lugar de `ring`, podemos crear una táctica `ring₀` que:

1. Intente `simp only [add_comm, add_assoc, mul_comm, mul_assoc, mul_add, add_mul,
   mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul]`
2. Si no resuelve, aplique `omega` via el bridge `Λ`/`Ψ`.
3. Como fallback, use `decide` para instancias concretas.

Esto cubriría ~80% de los usos reales de `ring` en nuestro contexto.

#### B.4. Recomendación Línea B

**Posponer la instanciación de typeclasses algebraicas.** No merece la pena sin
Mathlib — el esfuerzo de definir la jerarquía es grande y la táctica `ring` no
funcionaría con clases propias.

**Sí implementar:** instancias de `Init` que faltan (`Mul`, `Sub`, `HPow`, `Zero`,
`One`, `OfNat`, `Ord`) + una macro `ring₀` pragmática. Esto **es** el contenido
del punto 21.7 de NEXT-STEPS.md.

### Relación con la fase 21.7 de NEXT-STEPS.md

**Sí, hay relación directa.** La fase 21.7 planifica exactamente:

> `instance : HSub ℕ₀ ℕ₀ ℕ₀`, `HDiv`, `HMod`, `HPow`,
> `DecidableRel (@LT.lt ℕ₀ _)`, `DecidableRel (@LE.le ℕ₀ _)`

La Línea A extiende 21.7 con:

- `WellFoundedRelation ℕ₀` (nueva)
- `strongRecOn` / `strongInductionOn` (nueva)
- `lt_or_ge`, `le_or_lt` (nuevos)
- `Ord ℕ₀` (nueva, con `compare`)

La Línea B (en su versión pragmática) extiende 21.7 con:

- `Zero ℕ₀`, `One ℕ₀`, `OfNat ℕ₀ n` (nuevas, permiten escribir `(0 : ℕ₀)`, `(1 : ℕ₀)`)
- Instancias `Mul`, `Sub` (actualmente solo hay `Add`)
- Macro `ring₀` (futura, no es una instancia)

**Propuesta:** Fusionar Línea A + la versión pragmática de Línea B en una
**fase 21.7 ampliada**, con dos sub-fases:

```
21.7a — Instancias Init:  Mul, Sub, HDiv, HMod, HPow, Zero, One, OfNat, Ord
21.7b — Orden avanzado:   WellFoundedRelation, lt_or_ge, le_or_lt,
                           strongRecOn, strongInductionOn, sup_eq_max, inf_eq_min
```

La macro `ring₀` queda para una fase separada (requiere metaprogramación).

----------------------------------------------------------------------------------------

**PROPUESTA INFORMAL**
Este es un enfoque brillante para un proyecto pedagógico o de fundamentación en Lean 4. Estás diseñando una "escalera lógica" donde cada peldaño requiere una renuncia a una propiedad computacional a cambio de una ganancia en potencia matemática.

Para mostrar esos "momentos intermedios" y las necesidades lógicas que los disparan, te sugiero estructurar tu progresión en estos cuatro estadios:

---

### 1. El Estadio de la Aproximación (Computabilidad Pura)

Aquí es donde vives ahora. Todo es `decidable`. Un número no es un "punto", sino una **interfaz** que responde con un racional ante una petición de precisión.

- **Herramienta lógica:** Funciones de precisión fija $f : \mathbb{N} \to \mathbb{Q}$ con un módulo de convergencia $g : \mathbb{Q} \to \mathbb{N}$.
- **Decidibilidad:** Puedes decidir si $approx(x, \epsilon) < approx(y, \epsilon)$, pero **no** puedes decidir si $x < y$.
- **Limitación:** No puedes demostrar que $\sqrt{2} \cdot \sqrt{2} = 2$ de forma exacta; solo puedes demostrar que la diferencia es menor que cualquier $\epsilon$ que elijas.

### 2. El Estadio de la Relación de Equivalencia (Salto a la No-Decidibilidad)

Para que los Reales sean un "cuerpo" en el sentido algebraico, necesitas que $x - x = 0$. Pero con tus funciones, $f_x(n) - f_x(n)$ es una función que tiende a cero, no el cero racional.

- **Necesidad Lógica:** El **Cociente de Tipos** (`Quotient`).
- **Consecuencia:** En el momento en que defines $\mathbb{R} := \text{Cauchy} / \sim$, pierdes la capacidad de usar `if x = y`. Lean no tiene un algoritmo para colapsar todas las funciones que tienden al mismo límite en un solo punto booleano.
- **Momento de transición:** Aquí los reales dejan de ser "programas" y pasan a ser "clases de equivalencia".

### 3. El Estadio de la Completitud (Salto a la No-Computabilidad)

Hasta aquí, solo tienes los reales computables (como $\pi, e, \sqrt{2}$). Pero si quieres el **Axioma del Supremo** para _cualquier_ conjunto acotado, entras en terreno no computable.

- **El Problema:** Imagina un conjunto de reales definido por una propiedad que depende de si una máquina de Turing se detiene. El supremo de ese conjunto existe matemáticamente, pero no hay forma de construir su función de aproximación $f(n)$.
- **Necesidad Lógica:** El **Axioma de Elección (`Classical.choice`)**. Lo necesitas para "extraer" una sucesión de Cauchy de un conjunto de reales del cual solo sabes que tiene una cota superior, sin tener una receta para calcular los elementos de esa sucesión.

### 4. El Estadio de la Lógica Clásica (El Real Matemático)

Este es el último peldaño. Aquí ya no te importa la computación; tratas a $\mathbb{R}$ como una estructura completa y perfecta.

- **Necesidad Lógica:** **Tercero Excluido (`em`)**. Lo necesitas para demostrar, por ejemplo, que para cualquier par de reales, $x < y \lor x = y \lor x > y$ (Tricotomía). Aunque parezca obvio, en el Estadio 1 esto es falso porque podrías estar comparando dos números tan cercanos que tu precisión actual no permite distinguir.

---

### Resumen de la "Escalera de Peano" en Lean 4

| Estadio | Objeto Lógico | Propiedad que se gana | Propiedad que se pierde |
| :--- | :--- | :--- | :--- |
| **I. Aproximación** | `Structure` (f, g) | Computabilidad total | Igualdad verdadera ($x - x \neq 0$ como objeto) |
| **II. Cociente** | `Quotient` | Estructura de Cuerpo ($\mathbb{R}$ es grupo) | Decidibilidad de la igualdad |
| **III. Supremo** | `Nonempty` + `Choice` | Completitud (Análisis Real) | Constructibilidad (Números "fantasma") |
| **IV. Clásico** | `Classical.em` | Tricotomía y Topología | Intuicionismo |

### Propuesta de implementación en tu código

Para mostrar estos "momentos", podrías definir un namespace para cada uno:

1. `Peano.ApproxReal`: Solo estructuras y funciones.
2. `Peano.ExactReal`: El cociente del anterior (aquí dejas de usar `decidable`).
3. `Peano.ClassicalReal`: Donde abres `Classical` y defines el Supremo.

<!-- AUTO-UPDATE-2026-04-17-START -->
## Actualizacion de estado - 2026-04-17

- Estado del build: compila en el estado actual de la rama makingdecidable.
- Lagrange: cerrado en Sylow/Cosets con conteo por fibras y clases de cosets.
- GroupAction: sorries cerrados en orbit_stabilizer y orbits_partition.
- Sylow I: caso base n=0 cerrado; estructura separada en paso de Cauchy y paso de elevacion.
- Nota temporal: cauchy_minimal se apoya en un axioma explicito cauchy_minimal_axiom para continuar el desarrollo.
- Pendientes activos en Sylow: sylow_lift_from_cauchy, sylow_second, sylow_third.
- Objetivo proximo: reemplazar cauchy_minimal_axiom por demostracion interna y completar Sylow I.

<!-- AUTO-UPDATE-2026-04-17-END -->

---

## Respuestas formales a las Nuevas cuestiones (2026-05-02)

_Las preguntas del 2026-04-27 se adoptan como decisiones de diseño formales.
AczelSetTheory ya existe como repositorio en GitHub y tiene una copia local en
`E:\dropbox\github\lean4\AczelSetTheory\`. Lo que sigue es el análisis formal
que determina exactamente qué resta hacer en Peano antes de la transición._

---

### Respuesta 1 — AczelSetTheory puede redefinir los naturales desde HFSet

**Decisión: Sí, y es la arquitectura correcta.**

Una vez que `GodelBeta.lean` esté completo, AczelSetTheory dispone de todo lo
necesario para definir sus propios naturales internamente a HFSet. La estructura
actual de AczelSetTheory ya tiene `HFSets.lean` con el tipo `HFSet`; la extensión
natural es:

```lean
-- En AczelSetTheory/Foundation/VonNeumannNat.lean
def nat_to_hfset : ℕ₀ → HFSet
  | .zero   => .mk []
  | .succ n => .mk [nat_to_hfset n]

-- Predicado interno: naturales de von Neumann en HFSet
inductive IsVNNatural : HFSet → Prop
  | zero : IsVNNatural (.mk [])
  | succ : ∀ n, IsVNNatural n → IsVNNatural (.mk [n])
```

El isomorfismo `{ s : HFSet // IsVNNatural s } ≅ ℕ₀` es una instancia de
`peano_unique` (de `Peano.PeanoNat.Foundation.Initiality`) aplicada al sistema
de Peano definido sobre `IsVNNatural`.

**Implicación para el proyecto**: Una vez completada la cadena F.1→F.2→F.3,
AczelSetTheory tiene aritmética completa internamente. Peano deja de ser
necesario como entorno de desarrollo activo — se convierte en una **biblioteca
de dependencia estable** que AczelSetTheory referencia en su `lake-manifest.json`.

---

### Respuesta 2 — Computabilidad preservada con matiz preciso

**Decisión: Sí. La computabilidad se preserva íntegramente.**

| Función | Computable en Peano | Computable en AczelSetTheory | Razón |
|---------|--------------------|-----------------------------|-------|
| `pair`, `triag` | ✅ | ✅ | Aritmética pura |
| `encodeList`, `decodeList` | ✅ | ✅ | Aritmética pura |
| `antidiag`, `fst`, `snd` | ❌ | ❌ | `Classical.choice` intrínseco |
| Predicados decidables (LT, LE, Prime, Coprime…) | ✅ | ✅ vía isomorfismo | — |

La no-computabilidad de `antidiag`/`fst`/`snd` no es un artefacto de Peano
sino una propiedad de la elección clásica usada para definirlos. AczelSetTheory
no puede evitarla — ni necesita hacerlo, pues los usa como herramientas de
existencia, no de cómputo efectivo.

**Conclusión**: AczelSetTheory es tan computable como Peano. La ganancia no es
en computabilidad sino en **expresividad** (tipos de conjuntos, pertenencia,
extensionalidad).

---

### Respuesta 3 — Peano entra en modo mantenimiento: criterio exacto

**Decisión: Sí. El criterio de feature-freeze es las siguientes 4 condiciones.**

**CONDICIONES NECESARIAS Y SUFICIENTES para declarar Peano feature-frozen:**

| # | Ítem | Estado | Observación |
|---|------|--------|-------------|
| F.1 | `CantorPairing.lean` | ✅ (2026-05-02) | Biyección ℕ₀×ℕ₀≅ℕ₀ |
| F.2 | `GodelBeta.lean` | ❌ | Codificación de listas en ℕ₀ |
| F.3 | `Foundation.lean` paraguas | ❌ | Módulo de importación unificado |
| G.1 | Migración de doc. a `/doc/` | ❌ | Navegación AI sin pérdida de contexto |

**Condición opcional (cosmética, no bloqueante):**

| Opt | 5 axiomas privados en `Sylow.lean` | ❌ | Los 3 teoremas de Sylow están lógicamente cerrados; los axiomas son deuda técnica |

Una vez cumplidas las 4 condiciones necesarias, Peano entra en
**"feature-frozen maintenance mode"**: solo acepta corrección de errores,
actualizaciones de `lean-toolchain`, mejoras de build, y lemas menores
solicitados por AczelSetTheory.

---

### Respuesta 4 — AczelSetTheory importa desde Peano: arquitectura de paquetes

**Decisión: Sí. La arquitectura de dependencias es la definitiva.**

```
Peano  (dependencia git, feature-frozen tras F.3+G.1)
  └── importado por → AczelSetTheory  (E:\dropbox\github\lean4\AczelSetTheory\)
       └── importado por → ZfcSetTheory  (proyecto futuro)
```

El `lakefile.lean` actual de AczelSetTheory es:

```lean
import Lake
open Lake DSL

package "aczelsettheory"
lean_lib "AczelSetTheory"

@[default_target]
lean_exe "aczelsettheory" where
  root := `Main
```

Tras el feature-freeze de Peano, hay que añadir la dependencia:

```lean
require Peano from git
  "https://github.com/julian1c2a/Peano" @ "<sha-de-F.3>"
```

y en `lake-manifest.json` de AczelSetTheory referenciar el commit exacto donde
`Foundation` compila sin `sorry`.

El contrato mínimo que Peano exporta a AczelSetTheory:

```lean
Peano.Foundation.pair         : ℕ₀ → ℕ₀ → ℕ₀
Peano.Foundation.pair_fst     : fst (pair m n) = m
Peano.Foundation.pair_snd     : snd (pair m n) = n
Peano.Foundation.pair_surj    : pair (fst z) (snd z) = z
Peano.Foundation.encodeList   : List ℕ₀ → ℕ₀
Peano.Foundation.decodeList   : ℕ₀ → ℕ₀ → List ℕ₀
Peano.Foundation.encode_decode : ∀ l, decodeList (encodeList l) l.length = l
Peano.Foundation.peano_unique  : unicidad del sistema de Peano inicial
```

---

### Respuesta 5 — Migración de documentación a `/doc/` tree (Phase G)

**Decisión: Sí, necesario y planificado como Phase G.**

El `REFERENCE.md` actual (~2000 líneas monolítico) es inmanejable para
asistentes de IA que tienen ventanas de contexto limitadas. La estructura
objetivo es:

```
Peano/
├── doc/
│   ├── INDEX.md                      ← índice maestro, sustituye al REFERENCE.md raíz
│   ├── REFERENCE-Foundations.md      ← §1–§5:  Axioms, Order, StrictOrder, WellFounded, Sub
│   ├── REFERENCE-Arithmetic.md       ← §6–§15: Add, Mul, Div, Mod, Arith, Isomorph
│   ├── REFERENCE-NumberSets.md       ← §16:    NumberSets (ℕ₁, ℕ₂, cocientes)
│   ├── REFERENCE-NumberTheory.md     ← §17–§25: ModEq, Totient, CRT, Fermat, Primes
│   ├── REFERENCE-Combinatorics.md    ← §26–§38: List, FSet, Binom, Factorial, Perm…
│   ├── REFERENCE-GroupTheory.md      ← §39–§44: Action, Cosets, Sylow
│   └── REFERENCE-Foundation.md       ← §45+:   CantorPairing, GodelBeta, PeanoSystem
├── REFERENCE.md                      ← queda como redirect/índice de una sola página
└── (resto del proyecto)
```

Cada archivo tendrá un header de navegación:

```markdown
**Navegación:** [← Índice](doc/INDEX.md) · [← Anterior](REFERENCE-X.md) · [Siguiente →](REFERENCE-Y.md)
```

**Beneficios concretos**:

- Los asistentes de IA navegan sin perder contexto (cada archivo ≤ 400 líneas).
- La documentación no deriva: cada sección tiene exactamente un archivo responsable.
- La migración puede hacerse en paralelo con F.2 (no hay dependencia).

---

### Largo plazo — ℤ, ℚ, ℝ (Phase H, post-AczelSetTheory)

La escalera lógica del 2026-04-27 es el plan para una eventual **Phase H**,
que puede desarrollarse en AczelSetTheory o en un tercer proyecto:

| Fase | Tipo | Herramienta lógica | Ganancia | Pérdida |
|------|------|--------------------|----------|---------|
| H.1 | `ℤ` | Tipo inductivo `pos/neg/zero` | Resta total | — |
| H.2 | `ℚ` | Par `(ℤ × ℕ₁)` con canonización | División exacta | — |
| H.3 | `ℝ_approx` | Estructura `(f, g)` (sucesión Cauchy) | Computabilidad real | Igualdad exacta |
| H.4 | `ℝ_exact` | `Quotient` | Cuerpo ordenado | Decidibilidad de `=` |
| H.5 | `ℝ_complete` | `Classical.choice` | Axioma del supremo | Constructibilidad |

Esta fase es **post-AczelSetTheory** y **no bloquea** el cierre de Peano.
