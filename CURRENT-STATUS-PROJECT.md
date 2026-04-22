# Estado Actual del Proyecto: Peano

**Última actualización:** 2026-04-22
**Autor**: Julián Calderón Almendros

---

## Resumen

Biblioteca de aritmética de Peano pura en Lean 4, sin Mathlib, construida íntegramente desde los axiomas de Peano. Incluye aritmética completa de ℕ₀, teoría de números (Fermat, Euler, CRT), conjuntos finitos con funciones y principio del palomar, y teoría de grupos finitos (permutaciones, orden de elemento, subgrupo cíclico, acciones, coclases, Sylow).

---

## Estado de compilación

```
lean-toolchain  →  leanprover/lean4:v4.29.0
lake build      →  Build completed successfully (52 jobs)   [2026-04-22]
sorry count     →  4 (todos en Sylow.lean)
check-sorry     →  8 total (4 Sylow + 2 Perm.lean comentarios + 2 Primes.lean comentarios)
warnings        →  4 (4 sorry warnings)
errors          →  0
```

### Desglose de sorry

| Archivo | Líneas | Cantidad | Bloqueado por |
|---|---|---|---|
| `Combinatorics/GroupTheory/Sylow/Sylow.lean` | ~1190 | 1 | `mckay_p_dvd_powEqId` (conteo de órbitas McKay sobre G^p) |
| `Combinatorics/GroupTheory/Sylow/Sylow.lean` | ~1273 | 1 | `sylow_lift_from_cauchy` (inducción + normalizer) |
| `Combinatorics/GroupTheory/Sylow/Sylow.lean` | ~1307 | 1 | `sylow_second` (conjugación de p-subgrupos) |
| `Combinatorics/GroupTheory/Sylow/Sylow.lean` | ~1324 | 1 | `sylow_third` (n_p ≡ 1 mod p) |

> `Cosets.lean` (`lagrange`), `Action.lean` (`orbit_stabilizer`, `orbits_partition`), `Perm.lean`, `Group.lean` — **todos cerrados en sesiones 2026-04-15–19**.
> Lemas privados de `cauchy_minimal` (5 lemas, biyección `Fin₀Set(p) → ⟨g⟩`) — **cerrados en sesión 2026-04-19**.
> Infraestructura McKay (`Vector`, `allVectorsList`, `mckayShiftList`, `mckayShiftList_mem`, `mckayShiftList_inj`) — **completada en sesión 2026-04-20**.
> `mckay_orbit_remove` y `mckay_orbit_count` (lemas privados del argumento de McKay sobre `Vector ℕ₀ p`) — **cerrados en sesión 2026-04-22**.
> `cauchy_minimal` formalizado condicionalmente: depende de `mckay_p_dvd_powEqId` (único sorry de Cauchy).

---

## Módulos

| Archivo | Namespace | Contenido principal | Estado |
|---|---|---|---|
| `Peano/PeanoNat.lean` | `Peano` | `ℕ₀`, `ℕ₁`, `ℕ₂`, constantes, isomorfismos Λ/Ψ | ✅ |
| `Peano/Prelim.lean` | `Peano` | Reexporta ExistsUnique + Classical | ✅ |
| `Peano/Prelim/ExistsUnique.lean` | `Peano` | `ExistsUnique`, `∃¹` (constructivo) | ✅ |
| `Peano/Prelim/Classical.lean` | `Peano` | `choose`, `choose_unique` (noncomputable) | ✅ |
| `Peano/ConstructiveCheck.lean` | `Peano` | Verificación de constructividad | ✅ |
| `Peano/PeanoNat/Axioms.lean` | `Peano.Axioms` | Axiomas, `𝟘`, `succ`, `𝟙`, inducción | ✅ |
| `Peano/PeanoNat/StrictOrder.lean` | `Peano.StrictOrder` | Orden estricto `<`, tricotomía | ✅ |
| `Peano/PeanoNat/Order.lean` | `Peano.Order` | Orden `≤`, `le_antisymm`, `lt_or_ge`, `le_or_lt` | ✅ |
| `Peano/PeanoNat/Tuple.lean` | `Peano` | Tuplas de longitud `n`, orden lexicográfico | ✅ |
| `Peano/PeanoNat/Lattice.lean` | `Peano.Lattice` | `max`/`min`, retícula distributiva, 18 ext. Mathlib | ✅ |
| `Peano/PeanoNat/WellFounded.lean` | `Peano.WellFounded` | `well_founded_lt`, `strongRecOn`, `strongInductionOn` | ✅ |
| `Peano/PeanoNat/Add.lean` | `Peano.Add` | Suma, neutro, conmutatividad, asociatividad | ✅ |
| `Peano/PeanoNat/Sub.lean` | `Peano.Sub` | Resta truncada, `sub_self`, `add_k_sub_k` | ✅ |
| `Peano/PeanoNat/Mul.lean` | `Peano.Mul` | Multiplicación, `mul_sub`, `mul_le_mono_right` | ✅ |
| `Peano/PeanoNat/Div.lean` | `Peano.Div` | División entera, módulo, `divMod_spec`, `mod_lt` | ✅ |
| `Peano/PeanoNat/Arith.lean` | `Peano.Arith` | Divisibilidad, MCD/MCM, Bézout, Coprime, IsEven/IsOdd | ✅ |
| `Peano/PeanoNat/Decidable.lean` | `Peano.Decidable` | `DecidableRel` LT/LE, `Ord`, booleanos | ✅ |
| `Peano/PeanoNat/Isomorph.lean` | `Peano.Isomorph` | 14 isomorfismos Nat↔ℕ₀ (add, sub, mul, div, mod, pow, gcd, lcm) | ✅ |
| `Peano/PeanoNat/Primes.lean` | `Peano.Primes` | Primos, TFA, Gauss, `Decidable (Prime n)` | ✅ |
| `Peano/PeanoNat/NumberSets.lean` | `Peano.NumberSets` | `DivisorsOf`, `CoprimesOf`, `PrimesUpTo` | ✅ |
| `Peano/PeanoNat/Log.lean` | `Peano.Log` | Logaritmo entero con resto | ✅ |
| `Peano/PeanoNat/Sqrt.lean` | `Peano.Sqrt` | Raíz cuadrada entera con resto | ✅ |
| `Peano/PeanoNat/Digits.lean` | `Peano.Digits` | Dígitos en base arbitraria | ✅ |
| `Peano/PeanoNat/Pairing.lean` | `Peano.Pairing` | Emparejamiento de Cantor y su inversa | ✅ |
| **ListsAndSets/** | | | |
| `ListsAndSets/List.lean` | `Peano.List` | Listas de ℕ₀, operaciones, sorted, nodup | ✅ |
| `ListsAndSets/ListList.lean` | `Peano.ListList` | Listas de listas | ✅ |
| `ListsAndSets/FSet.lean` | `Peano.FSet` | Conjuntos finitos con UniqueKeys + SortedByKey | ✅ |
| `ListsAndSets/FSetFSet.lean` | `Peano.FSetFSet` | Conjuntos de conjuntos finitos | ✅ |
| `ListsAndSets/FSetFunction.lean` | `Peano.FSetFunction` | MapOn, Im, Pigeonhole, `collision_of_card_lt`, inversas, Perm, ~92 decl. | ✅ |
| **NumberTheory/** | | | |
| `NumberTheory/ModEq.lean` | `Peano.ModEq` | Congruencia modular, compatibilidad aritmética | ✅ |
| `NumberTheory/Totient.lean` | `Peano.Totient` | Función de Euler φ, `totient_prime`, `totient_pos` | ✅ |
| `NumberTheory/ChineseRemainder.lean` | `Peano.CRT` | Teorema Chino del Resto | ✅ |
| `NumberTheory/Fermat.lean` | `Peano.Fermat` | Pequeño Teorema de Fermat | ✅ |
| **Combinatorics/** | | | |
| `Combinatorics/Pow.lean` | `Peano.Pow` | Potenciación, `pow_add`, `pow_mul` | ✅ |
| `Combinatorics/Factorial.lean` | `Peano.Factorial` | Factorial, `factorial_pos`, `factorial_succ` | ✅ |
| `Combinatorics/Binom.lean` | `Peano.Binom` | Coeficientes binomiales, Pascal, simetría | ✅ |
| `Combinatorics/NewtonBinom.lean` | `Peano.NewtonBinom` | Binomio de Newton | ✅ |
| `Combinatorics/Summation.lean` | `Peano.Summation` | Sumatorias `∑`, propiedades algebraicas | ✅ |
| `Combinatorics/Product.lean` | `Peano.Product` | Productorias `∏` | ✅ |
| `Combinatorics/Fibonacci.lean` | `Peano.Fibonacci` | Fibonacci, Cassini, fib_add | ✅ |
| `Combinatorics/Counting.lean` | `Peano.Counting` | Conteo combinatorio | ✅ |
| `Combinatorics/Perm.lean` | `Peano.Perm` | Permutaciones, `FunPerm`, composición | ✅ |
| `Combinatorics/Sign.lean` | `Peano.Sign` | Signo de permutaciones | ✅ |
| `Combinatorics/Orbit.lean` | `Peano.Orbit` | Órbitas | ✅ |
| `Combinatorics/Group.lean` | `Peano.Group` | FinGroup, Subgroup, gpow, `order`, subgrupos trivial/impropio/cíclico, IsNormal, inter | ✅ |
| **GroupTheory/** | | | |
| `GroupTheory/Action.lean` | `Peano.Action` | Acciones de grupo, `orb`, `stab`, `fix`, `orbit_stabilizer`, `orbits_partition` | ✅ |
| `GroupTheory/Sylow/Cosets.lean` | `Peano.Cosets` | Coclases, `cosetRel`, `coset_card_eq_subgroup_card`, `lagrange` | ✅ |
| `GroupTheory/Sylow/Sylow.lean` | `Peano.Sylow` | Teoremas de Sylow I/II/III | ⚠ 4 sorry |

---

## Hitos completados

### Fase 1–4: Aritmética completa de ℕ₀ y ℕ₁ (2026-03-03)

- **Divisibilidad completa**: `divides_refl`, `divides_trans`, `antisymm_divides`.
- **MCD y conmutatividad**: `gcd_step`, `gcd_greatest`, `gcd_comm`.
- **Identidad de Bézout**: `bezout_additive` y `bezout_natform`.
- **ℕ₁**: `Divides₁`, `IsGCD₁`, `gcd₁`, `Coprime₁`.

### Fase 5–6: Infraestructura y exports (2026-03-15)

- Potenciación, factorial, coeficientes binomiales, binomio de Newton.
- Primos: `unique_prime_factorization`, `coprime_dvd_of_dvd_mul` (Gauss), `prime_iff_irreducible`.

### Fase 7–17: Reestructuración y modernización (2026-04-08)

- Directorio `PeanoNatLib/` → `Peano/`, `PeanoNatLib.lean` → `PeanoNat.lean`.
- Subdirectorio `Combinatorics/` extraído. `Prelim.lean`, `Isomorph.lean`, `Decidable.lean` factorizados.
- Copyright headers, migración de identificadores a convenciones Mathlib4.

### Phase 21: Completación de ℕ₀ (2026-04-09 — 2026-06)

- **21.7a**: Todas las instancias Init (Mul, Sub, Div, Mod, Pow, Zero, One, OfNat, Ord).
- **21.7b**: `WellFoundedRelation ℕ₀`, `lt_or_ge`, `le_or_lt`, `strongRecOn`, `strongInductionOn`, `DecidableRel`.
- **21.8**: `IsEven`/`IsOdd` con instancias `Decidable` + 6 teoremas.
- **21.9**: `Decidable (Prime n)` vía `isPrimeb` + `isPrimeb_iff`.
- **21.1**: Digits.lean — representación en base *b*.
- **21.2**: Pairing.lean — función de emparejamiento de Cantor.
- **21.3**: ModEq.lean — congruencia modular.
- **21.4**: Totient.lean — función φ de Euler, `totient_prime`.
- **21.5**: ChineseRemainder.lean — Teorema del Resto Chino.
- **21.6**: Fermat.lean — Pequeño Teorema de Fermat.

### Phase 24: Conjuntos finitos y funciones (2026-04)

- **FSet.lean**: Conjuntos finitos con invariantes `UniqueKeys` + `SortedByKey`.
- **FSetFSet.lean**: Conjuntos de conjuntos finitos.
- **FSetFunction.lean** (~92 declaraciones):
  - § 1: `MapOn`, `comp`, `comp_assoc`, `id`
  - § 2: `Im`, `rightInverse`, `leftInverse`, `inverse`, involution
  - § 3: Pigeonhole, card inequalities/equalities, iff characterizations
  - § 3b: **`not_injective_of_card_lt`**, **`collision_of_card_lt`** (2026-04-16) — necesarios para B2.3 `order`
  - § 3e: **`card_eq_mul_of_uniform_fibers`** (2026-04-17) — conteo por fibras uniformes
  - `FSet.eq_of_mem_iff` añadido en `FSet.lean` y usado como extensionalidad de trabajo
  - § 3d: `PreIm`, fibras, restricción
  - § 3e: Endomorfismos (`EndoOn`)
  - § 3f: Permutaciones (`Perm` structure)
  - § 4–8: `BinOpOn`, `CoeFun`, `FunTable`, `FunPerm`, Export

### Phase 25: Teoría de grupos finitos (2026-04 — en curso)

- **Perm.lean**: Tipo de permutaciones, `FunPerm.comp is_perm` — **✅ sin sorry** (commit `9a17a8e`).
- **Group.lean**: `FinGroup`, `Subgroup`, `gpow` + lemas, `order`/`order_pos`/`gpow_order_eq_id`/`gpow_mod_order`, subgrupos trivial/impropio/cíclico, `IsNormal`, `Subgroup.inter` — **✅ sin sorry** (commit `413c6e3`).
- **Sign.lean**: Signo de permutaciones (paridad). ✅
- **Orbit.lean**: Órbitas de permutaciones. ✅
- **Counting.lean**: Conteo combinatorio. ✅
- **Action.lean**: Acciones de grupo, órbita, estabilizador, subgrupo fijo — **✅ sin sorry** (`orbit_stabilizer`, `orbits_partition` cerrados en sesión 2026-04-17).
- **Sylow/Cosets.lean**: Coclases, índice, `cosetRel`, `lagrange` — **✅ sin sorry** (cerrado en sesión 2026-04-17).
- **Sylow/Sylow.lean**: Teoremas de Sylow I/II/III (⚠ 4 sorry: `mckay_p_dvd_powEqId`, `sylow_lift_from_cauchy`, `sylow_second`, `sylow_third`).

---

## Próximos objetivos

- **B6 `lagrange`** (Cosets.lean:128): partición de G en cosetos de H + conteo por fibras (|G| = |H|·[G:H]).
- **B7 `orbit_stabilizer`** (Action.lean:119): biyección G/Stab(x) ≅ Orb(x) — necesita Lagrange.
- **B8 `orbits_partition`** (Action.lean:153): extensionalidad de FSet (sorted list equality).
- **B9 Sylow I** (sylow_first): Cauchy → p-subgrupo de orden p^k.
- **B10 Sylow II/III**: acción por conjugación + conteo mod p.
- **Phase 22**: Extensión a enteros ℤ (tipo inductivo canónico).
- **Phase 23**: Extensión a racionales ℚ (estructura con invariante de coprimalidad).

---

**Licencia**: MIT License

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

<!-- AUTO-UPDATE-2026-04-20-START -->
## Actualizacion de estado - 2026-04-20

- Estado del build: 52 jobs, 0 errores, 4 sorry warnings (todos en Sylow.lean).
- Infraestructura McKay completada: Vector, allVectorsList, mckayShiftList, mckayShift, mckayShiftList_mem, mckayShiftList_inj, append_singleton_inj.
- cauchy_minimal formalizado condicionalmente: todos los lemas auxiliares cerrados; unico sorry es mckay_p_dvd_powEqId (conteo de orbitas mod p).
- Sorries vigentes: mckay_p_dvd_powEqId (~498), sylow_lift_from_cauchy (~577), sylow_second (~610), sylow_third (~627).
- Objetivo proximo: formalizar mckay_p_dvd_powEqId usando Action.lean (ecuacion de clases).

<!-- AUTO-UPDATE-2026-04-20-END -->
