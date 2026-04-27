# Estado Actual del Proyecto: Peano

**Última actualización:** 2026-04-27
**Autor**: Julián Calderón Almendros

---

## Resumen

Biblioteca de aritmética de Peano pura en Lean 4, sin Mathlib, construida íntegramente desde los axiomas de Peano. Incluye aritmética completa de ℕ₀, teoría de números (Fermat, Euler, CRT), conjuntos finitos con funciones y principio del palomar, y teoría de grupos finitos (permutaciones, orden de elemento, subgrupo cíclico, acciones, coclases, Sylow). Desde 2026-04-27 incluye también polimorfismo completo de `FinGroup` sobre tipo arbitrario con `StrictLinearOrder`.

---

## Estado de compilación

```
lean-toolchain  →  leanprover/lean4:v4.29.0
lake build      →  Build completed successfully (51 jobs)   [2026-04-27]
sorry count     →  0 (5 axiomas privados en Sylow.lean, pendientes de prueba)
warnings        →  0
errors          →  0
```

### Desglose de axiomas privados (Sylow.lean)

| Axioma | Usado por | Dificultad | Ruta |
|---|---|---|---|
| `sylow_center_step` | `sylow_lift_from_cauchy` | Difícil | Wielandt (2/5 pasos completos) |
| `sylow_card_eq` | `sylow_second` | Medio | `pow_dvd_pow` en Pow.lean |
| `sylow_second_incl` | `sylow_second` | Difícil | H-acción sobre G/K |
| `sylow_third_mod` | `sylow_third` | Muy difícil | Normalizador + conteo mod p |
| `sylow_third_dvd` | `sylow_third` | Muy difícil | G-acción + orbit-stabilizer |

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
| `Peano/PeanoNat/StrictOrder.lean` | `Peano.StrictOrder` | Orden estricto `<`, tricotomía, `StrictLinearOrder α`, `instIrreflLTOfSLO` | ✅ |
| `Peano/PeanoNat/Order.lean` | `Peano.Order` | Orden `≤`, `le_antisymm`, `lt_or_ge`, `le_or_lt` | ✅ |
| `Peano/PeanoNat/Tuple.lean` | `Peano` | Tuplas de longitud `n`, orden lexicográfico, `instStrictLinearOrderTuple` | ✅ |
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
| `ListsAndSets/List.lean` | `Peano.List` | Listas polimórficas `List α`, sorted, nodup, `sortedInsert` genérico | ✅ |
| `ListsAndSets/FSet.lean` | `Peano.FSet` | `FSet α` — conjuntos finitos genéricos (lista ordenada + invariante `Sorted`) | ✅ |
| `ListsAndSets/FSetFunction.lean` | `Peano.FSetFunction` | MapOn, Im, Pigeonhole, `collision_of_card_lt`, inversas, Perm, ~92 decl. | ✅ |
| **NumberTheory/** | | | |
| `NumberTheory/ModEq.lean` | `Peano.ModEq` | Congruencia modular, compatibilidad aritmética | ✅ |
| `NumberTheory/Totient.lean` | `Peano.Totient` | Función de Euler φ, `totient_prime`, `totient_pos` | ✅ |
| `NumberTheory/ChineseRemainder.lean` | `Peano.CRT` | Teorema Chino del Resto | ✅ |
| `NumberTheory/Fermat.lean` | `Peano.Fermat` | Pequeño Teorema de Fermat | ✅ |
| **Combinatorics/** | | | |
| `Combinatorics/Pow.lean` | `Peano.Pow` | Potenciación, `pow_add`, `pow_mul` | ✅ |
| `Combinatorics/Factorial.lean` | `Peano.Factorial` | Factorial, `factorial_pos`, `factorial_succ` | ✅ |
| `Combinatorics/Binom.lean` | `Peano.Binom` | Coef. binomiales, Pascal, `prime_dvd_binom_prime`, `binom_prime_row` | ✅ |
| `Combinatorics/NewtonBinom.lean` | `Peano.NewtonBinom` | Binomio de Newton | ✅ |
| `Combinatorics/Summation.lean` | `Peano.Summation` | Sumatorias `∑`, propiedades algebraicas | ✅ |
| `Combinatorics/Product.lean` | `Peano.Product` | Productorias `∏` | ✅ |
| `Combinatorics/Fibonacci.lean` | `Peano.Fibonacci` | Fibonacci, Cassini, fib_add | ✅ |
| `Combinatorics/Counting.lean` | `Peano.Counting` | Conteo combinatorio | ✅ |
| `Combinatorics/Perm.lean` | `Peano.Perm` | Permutaciones, `FunPerm`, composición | ✅ |
| `Combinatorics/Sign.lean` | `Peano.Sign` | Signo de permutaciones | ✅ |
| `Combinatorics/Orbit.lean` | `Peano.Orbit` | Órbitas | ✅ |
| `Combinatorics/Group.lean` | `Peano.Group` | `FinGroup (α) [DecidableEq α] [LT α] [StrictLinearOrder α]`, `Subgroup`, `gpow`, `order`, subgrupos, `IsNormal`, inter | ✅ |
| **GroupTheory/** | | | |
| `GroupTheory/Action.lean` | `Peano.Action` | Acciones de grupo, `orb`, `stab`, `fix`, `orbit_stabilizer`, `orbits_partition` | ✅ |
| `GroupTheory/Sylow/Cosets.lean` | `Peano.Cosets` | Coclases, `cosetRel`, `coset_card_eq_subgroup_card`, `lagrange` | ✅ |
| `GroupTheory/Sylow/Sylow.lean` | `Peano.Sylow` | Teoremas de Sylow I/II/III — formalmente cerrados (0 sorry, 5 axiomas privados) | ⚠ 5 axiomas |

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

### Phase 21: Completación de ℕ₀ (2026-04-09)

- Instancias Init completas, `DecidableRel`, inducción fuerte, `IsEven`/`IsOdd`, `Decidable (Prime n)`.
- Digits, Pairing, ModEq, Totient, CRT, Fermat.

### Phase 24: Conjuntos finitos y funciones (2026-04)

- **FSet α**: conjuntos finitos genéricos (estructura con lista ordenada + invariante `Sorted`).
- **FSetFunction.lean** (~92 declaraciones): MapOn, Im, Pigeonhole, inversas, Perm, `card_eq_mul_of_uniform_fibers`.
- **Nota**: ListList.lean y FSetFSet.lean eliminados en 2026-04-27 (fusionados en List.lean y FSet.lean).

### Phase 25: Teoría de grupos finitos (2026-04)

- **Perm.lean**: ✅ sin sorry (commit `9a17a8e`).
- **Group.lean**: `FinGroup (α : Type) [DecidableEq α] [LT α] [StrictLinearOrder α]` — polimórfico sobre tipo arbitrario. `Subgroup`, `gpow`, `order`, `order_pos`, `gpow_order_eq_id`, `gpow_mod_order`, subgrupos trivial/impropio/cíclico, `IsNormal`, `Subgroup.inter` — ✅ sin sorry.
- **Action.lean**: `orbit_stabilizer`, `orbits_partition` — ✅ sin sorry.
- **Cosets.lean**: coclases, `lagrange` — ✅ sin sorry.
- **Sylow.lean**: todos los teoremas de Sylow I/II/III formalmente cerrados (0 sorry):
  - `cauchy_minimal` — argumento de órbitas de McKay.
  - `sylow_first`, `sylow_second`, `sylow_third` — todos cerrados.
  - 5 axiomas privados pendientes de prueba.

### Refactoring: StrictLinearOrder y FSet genérico (2026-04-27)

- **StrictOrder.lean**: `StrictLinearOrder α` typeclass; instancia bridge `instIrreflLTOfSLO`.
- **Tuple.lean**: `instStrictLinearOrderTuple` — `FSet (Tuple ℕ₀ n)` funciona automáticamente.
- **List.lean**: `sortedInsert` generalizado a `[StrictLinearOrder α]`.
- **FSet.lean**: `FSet α` genérico para cualquier tipo con `StrictLinearOrder α`.
- **Group.lean**: `FinGroup (α) [DecidableEq α] [LT α] [StrictLinearOrder α]` con `carrier : FSet α`, `id : α`. Alias `abbrev ℕ₀FinGroup := FinGroup ℕ₀`.
- Build: 52 → 51 jobs (eliminados ListList.lean y FSetFSet.lean).

### Wielandt — pasos completados (2026-04-23/24)

- `prime_dvd_binom_prime` — p primo, 0 < k < p → p | C(p,k) ✅
- `binom_prime_row` — C(p·r, p) = r · C(p·r−1, p−1) ✅

---

## Próximos objetivos

### Ruta Wielandt (eliminar `sylow_center_step`)

1. **`binom_pr_p_mod`** — C(p·r, p) ≡ r (mod p) por inducción sobre r, usando `binom_prime_row` + `prime_dvd_binom_prime`. Requiere: `p | C(pr,p) - r` o argumentar directamente con divisibilidad.
2. **Lucas' theorem** — C(p^n·r, p^n) ≡ r (mod p).
3. **Wielandt fixed-point** — argumento de punto fijo sobre conjunto Ω de p^n-subsets de G.
4. → Reemplaza `sylow_center_step`.

### Otros axiomas privados

5. **`sylow_card_eq`** — añadir `pow_dvd_pow` a Pow.lean, luego unicidad del exponente de Sylow.
6. **`sylow_second_incl`** — H-acción sobre G/K (coclases ya en librería), fixed point = r⁻¹Hr ⊆ K.
7. **`sylow_third_mod`** y **`sylow_third_dvd`** — requieren normalizador y acción por conjugación sobre subgrupos.

---

**Licencia**: MIT License
