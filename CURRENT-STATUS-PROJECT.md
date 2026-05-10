# Estado Actual del Proyecto: Peano

**Última actualización:** 2026-05-10
**Autor**: Julián Calderón Almendros

---

## Resumen

Biblioteca de aritmética de Peano pura en Lean 4, sin Mathlib, construida íntegramente desde los axiomas de Peano. Incluye aritmética completa de ℕ₀, teoría de números (Fermat, Euler, CRT, Wilson), conjuntos finitos con funciones y principio del palomar, relaciones de equivalencia sobre dominios finitos, y teoría de grupos finitos (permutaciones, orden de elemento, subgrupo cíclico, acciones, coclases, Sylow). Toda la infraestructura de grupos (`FinGroup`, `GroupAction`, `leftCoset`, `cosetRel`, `EquivRelOn`) es completamente polimórfica sobre `{α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]`.

---

## Estado de compilación

```
lean-toolchain  →  leanprover/lean4:v4.29.0
lake build      →  Build completed successfully (66 jobs)   [2026-05-10]
sorry count     →  0
warnings        →  2 (htrans sin usar en wielandt_fixed_point_exists; hg_ne sin usar en wielandt_orbit_stab)
errors          →  0
```

### Axiomas privados — estado final (2026-05-10)

Los únicos `private axiom` son los **6 axiomas intencionales de Peano** en `PureAxioms.lean`.
No hay ningún `private axiom` ni `sorry` en `Sylow.lean` ni en ningún otro módulo.

| Símbolo | Módulo | Tipo | Notas |
|---|---|---|---|
| `wielandt_p_ndvd_r` | `Sylow.lean` | `private theorem` ✅ | demostrado (línea ~3755) |
| `sylow_third_mod` | `Sylow.lean` | `private theorem` ✅ | demostrado (línea ~4955) |
| `sylow_third_dvd` | `Sylow.lean` | `private theorem` ✅ | demostrado (línea ~5434) |
| `wielandt_fixed_point_exists` | `Sylow.lean` | `private theorem` ✅ | demostrado (2026-05-07) |

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
| **Foundation/** | | | |
| `PeanoNat/Foundation/CantorPairing.lean` | `Peano.Foundation` | `triag`, `pair`, `antidiag`, `fst`, `snd`, `pair_surj` — biyección ℕ₀×ℕ₀≅ℕ₀ | ✅ |
| `PeanoNat/Foundation/GodelBeta.lean` | `Peano.Foundation` | Función β de Gödel, `encodeList`/`decodeList`/`encode_decode` | ✅ |
| `PeanoNat/Foundation/PeanoSystem.lean` | `Peano.Foundation` | Estructura PeanoSystem, morfismos, isomorfismos | ✅ |
| `PeanoNat/Foundation/Initiality.lean` | `Peano.Foundation` | ℕ₀ como álgebra inicial; unicidad e inicialidad | ✅ |
| `PeanoNat/Foundation/PureAxioms.lean` | `Peano.Foundation` | Sistema PA axiomático puro + teorema de paridad | ✅ |
| `PeanoNat/Foundation/Foundation.lean` | `Peano.Foundation` | Módulo paraguas Foundation | ✅ |
| **ListsAndSets/** | | | |
| `ListsAndSets/List.lean` | `Peano.List` | Listas polimórficas `List α`, sorted, nodup, `sortedInsert` genérico | ✅ |
| `ListsAndSets/FSet.lean` | `Peano.FSet` | `FSet α` — conjuntos finitos genéricos (lista ordenada + invariante `Sorted`); `eq_of_mem_iff'`, `sortList'`, `ofList` | ✅ |
| `ListsAndSets/FSetFunction.lean` | `Peano.FSetFunction` | MapOn, Im, Pigeonhole, `collision_of_card_lt`, inversas, Perm, ~92 decl. | ✅ |
| `ListsAndSets/EquivRel.lean` | `Peano.EquivRel` | `EquivRelOn`, `classOf`, `classes`, `ClassFamily`, `canonicalClassFamily` — 17 símbolos exportados | ✅ |
| **NumberTheory/** | | | |
| `NumberTheory/ModEq.lean` | `Peano.ModEq` | Congruencia modular, compatibilidad aritmética | ✅ |
| `NumberTheory/Totient.lean` | `Peano.Totient` | Función de Euler φ, `totient_prime`, `totient_pos` | ✅ |
| `NumberTheory/ChineseRemainder.lean` | `Peano.CRT` | Teorema Chino del Resto | ✅ |
| `NumberTheory/Fermat.lean` | `Peano.Fermat` | Pequeño Teorema de Fermat | ✅ |
| `NumberTheory/Wilson.lean` | `Peano.Wilson` | Teorema de Wilson — `p ∣ (p−1)! + 1`, pairing argument | ✅ |
| **Combinatorics/** | | | |
| `Combinatorics/Pow.lean` | `Peano.Pow` | Potenciación, `pow_add`, `pow_mul` | ✅ |
| `Combinatorics/Factorial.lean` | `Peano.Factorial` | Factorial, `factorial_pos`, `factorial_succ` | ✅ |
| `Combinatorics/Binom.lean` | `Peano.Binom` | Coef. binomiales, Pascal, `prime_dvd_binom_prime`, `binom_pow_p_mod` | ✅ |
| `Combinatorics/NewtonBinom.lean` | `Peano.NewtonBinom` | Binomio de Newton | ✅ |
| `Combinatorics/Summation.lean` | `Peano.Summation` | Sumatorias `∑`, propiedades algebraicas | ✅ |
| `Combinatorics/Product.lean` | `Peano.Product` | Productorias `∏` | ✅ |
| `Combinatorics/Fibonacci.lean` | `Peano.Fibonacci` | Fibonacci, Cassini, fib_add | ✅ |
| `Combinatorics/Counting.lean` | `Peano.Counting` | Conteo combinatorio | ✅ |
| `Combinatorics/Perm.lean` | `Peano.Perm` | Permutaciones, `FunPerm`, composición | ✅ |
| `Combinatorics/Sign.lean` | `Peano.Sign` | Signo de permutaciones | ✅ |
| `Combinatorics/Orbit.lean` | `Peano.Orbit` | Órbitas | ✅ |
| `Combinatorics/Group.lean` | `Peano.Group` | `FinGroup (α) [DecidableEq α] [LT α] [StrictLinearOrder α]`, `Subgroup`, `gpow`, `order`, subgrupos, `IsNormal`, inter; instancias `instDecidableEqSubgroup`, `instLTSubgroup`, `instStrictLinearOrderSubgroup` | ✅ |
| **GroupTheory/** | | | |
| `GroupTheory/NormalSubgroup.lean` | `Peano.GroupTheory` | `centralizer`, `normalizer`, `rightCoset`, criterios de normalidad | ✅ |
| `GroupTheory/QuotientGroup.lean` | `Peano.GroupTheory` | `quotientGroup`, `quotientHomomorphism`, `imageSubgroup` (29 exports) | ✅ |
| `GroupTheory/FirstIsomorphism.lean` | `Peano.GroupTheory` | `homKer`, `homImg`, `firstIsoMap` — G/ker≅Im | ✅ |
| `GroupTheory/SecondIsomorphism.lean` | `Peano.GroupTheory` | `subgroupHN`, `interHN`, `secondIsoMap` — H/(H∩N)≅HN/N | ✅ |
| `GroupTheory/CorrespondenceTheorem.lean` | `Peano.GroupTheory` | `preimageSubgroup`, `SubgroupAbove`, `correspondencePhi`/`Psi` (12 exports) | ✅ |
| `GroupTheory/Zassenhaus.lean` | `Peano.GroupTheory` | `prodSubgroup`, `prodNKHM`, `prodN_HK`, `prodN_HM`, normalidad (12 exports) | ✅ |
| `GroupTheory/Action.lean` | `Peano.Action` | `GroupAction` polimórfico, `orb`, `stab`, `orbit_stabilizer`, `orbits_partition` | ✅ |
| `GroupTheory/Sylow/Cosets.lean` | `Peano.Cosets` | `leftCoset`, `cosetRel`, `cosetEquivRel`, `lagrange`, `cosetClasses` — polimórfico | ✅ |
| `GroupTheory/Sylow/CosetAction.lean` | `Peano.CosetAction` | Acción de G sobre coclases, `coset_conjugate_exists` (cierra Sylow II) | ✅ |
| `GroupTheory/Sylow/Sylow.lean` | `Peano.Sylow` | Teoremas de Sylow I/II/III — completamente demostrados (0 sorry, 0 axiomas privados) | ✅ |

---

## Hitos completados

### Phase 5 — Polimorfismo completo FinGroup/FSet/EquivRel (2026-05-07)

- `FSet.lean`: añadidos `eq_of_mem_iff'` (genérico), `sortList'`, `FSet.ofList`.
- `EquivRel.lean`: nuevo módulo — `EquivRelOn`, `classOf`, `classes`, `ClassFamily`, `canonicalClassFamily`, 17 símbolos exportados.
- `Group.lean`: instancias `instDecidableEqSubgroup`, `instLTSubgroup`, `instStrictLinearOrderSubgroup` para `FSet (Subgroup G)`.
- `Cosets.lean` y `Action.lean`: completamente refactorizados a polimorfismo pleno sobre `{α β : Type}`.
- **Build**: 64 jobs, 0 sorry.

### wielandt_fixed_point_exists — ✅ axioma eliminado (2026-05-07)

Demostrado como `private theorem` completo (0 sorry): G actúa sobre Ω por traslación;
p∤|Ω| → `wielandt_exists_nondvd_orbit_aux` da punto fijo → estabilizador tiene orden p^(m+1).

### Wilson.lean — ✅ 0 sorry (2026-05-05)

`wilson : p ∣ add (factorial (sub p 𝟙)) 𝟙` — pairing argument sobre {2,…,p−2}.

### CorrespondenceTheorem.lean — ✅ 0 sorry (2026-05-05)

`correspondencePhi`/`correspondencePsi` — biyección entre subgrupos sobre N y subgrupos de G/N.

### Phase 6 — Lema de la Mariposa de Zassenhaus ✅ (2026-05-10)

- `Zassenhaus.lean` — 12 símbolos públicos: `prodSubgroup`, `mem_prodSubgroup_iff`,
  `N_le_prodSubgroup`, `S_le_prodSubgroup`, `inter_N_K_normal_in_inter_H_K`,
  `inter_H_M_normal_in_inter_H_K`, `prodNKHM`, `prodNKHM_normal`,
  `prodN_HK`, `prodN_HM`, `prodN_HM_le_prodN_HK`, `prodN_HM_normal_in_prodN_HK`.
- 0 sorry. `zassenhaus_bijection` incluido con enunciado placeholder `True` (trivial); el isomorfismo real requiere cocientes de FinGroup.
- **Build**: 66 jobs, 0 sorry, 0 axiomas privados no intencionales.
- Documentación proyectada: `doc/REFERENCE-GroupTheory.md`.

### Phase F — Foundation: cadena Peano → Aczel → ZFC ✅ (2026-05-02)

- `CantorPairing.lean` — biyección ℕ₀×ℕ₀ ≅ ℕ₀
- `GodelBeta.lean` — función β de Gödel; codificación List ℕ₀ ≃ ℕ₀

---

## Próximos objetivos

1. **`zassenhaus_bijection`** — Formalizar el isomorfismo `(H∩K)/[(N∩K)(H∩M)] ≅ N(H∩K)/N(H∩M)` como tipo completo. Actualmente el enunciado es `True` (placeholder `trivial`). Requiere cocientes de `FinGroup` formalizados.
2. **`ConstructiveCheck.lean`** — Añadir `#assert_constructive` para aritmética base, NumberTheory y Combinatorics pura.
3. **Feature-freeze + handoff a `AczelSetTheory`** — Precondición: los dos anteriores.

---

**Licencia**: MIT License
