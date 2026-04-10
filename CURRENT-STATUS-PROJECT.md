# Estado Actual del Proyecto: Peano

**Última actualización:** 2026-04-09
**Autor**: Julián Calderón Almendros

---

## Resumen

Biblioteca de aritmética de Peano pura en Lean 4, sin Mathlib, construida íntegramente desde los axiomas de Peano. Todos los módulos compilan sin ningún `sorry`.

---

## Estado de compilación

```
lean-toolchain  →  leanprover/lean4:v4.29.0
lake build      →  Build completed successfully (37 jobs)
sorry count     →  0
warnings        →  0
```

---

## Módulos

| Archivo | Namespace | Contenido principal | Estado |
|---|---|---|---|
| `Peano/PeanoNat.lean` | `Peano` | `ℕ₀`, `ExistsUnique`, `choose`, constantes, isomorfismos | ✅ Completo |
| `Peano/Prelim.lean` | `Peano.Prelim` | Infraestructura compartida (DList→List) | ✅ Completo |
| `Peano/PeanoNat/Axioms.lean` | `Peano.Axioms` | Axiomas, `𝟘`, `succ`, `𝟙`, inducción | ✅ Completo |
| `Peano/PeanoNat/StrictOrder.lean` | `Peano.StrictOrder` | Orden estricto `<`, `lt_of_lt_of_le` | ✅ Completo |
| `Peano/PeanoNat/Order.lean` | `Peano.Order` | Orden `≤`, `le_antisymm`, `le_trans`, `lt_or_ge`, `le_or_lt` | ✅ Completo |
| `Peano/PeanoNat/Lattice.lean` | `Peano.Lattice` | `max`, `min`, retícula distributiva, 18 extensiones Mathlib-style | ✅ Completo |
| `Peano/PeanoNat/WellFounded.lean` | `Peano.WellFounded` | Inducción bien fundada, `well_founded_lt`, `WellFoundedRelation`, `strongRecOn`, `strongInductionOn` | ✅ Completo |
| `Peano/PeanoNat/Add.lean` | `Peano.Add` | Suma, neutro, conmutatividad, asociatividad | ✅ Completo |
| `Peano/PeanoNat/Sub.lean` | `Peano.Sub` | Resta truncada, `sub_self`, `add_k_sub_k` | ✅ Completo |
| `Peano/PeanoNat/Mul.lean` | `Peano.Mul` | Multiplicación, `mul_sub`, `mul_le_mono_right` | ✅ Completo |
| `Peano/PeanoNat/Div.lean` | `Peano.Div` | División entera, módulo, `divMod_eq`, `mod_lt` | ✅ Completo |
| `Peano/PeanoNat/Arith.lean` | `Peano.Arith` | Divisibilidad, MCD/MCM, Bézout, `ℕ₁`, 25 extensiones GCD/LCM/Coprime Mathlib-style, `IsEven`/`IsOdd` decidibles | ✅ Completo |
| `Peano/PeanoNat/Decidable.lean` | `Peano.Decidable` | Decidabilidad de `=`, `<`, `≤`, `∣`; instancias `Ord`, `DecidableRel` LT/LE | ✅ Completo |
| `Peano/PeanoNat/MaxMin.lean` | `Peano.MaxMin` | (Legacy) `max`, `min` — migrado a Lattice.lean | ✅ Completo |
| `Peano/PeanoNat/Isomorph.lean` | `Peano.Isomorph` | Isomorfismo Nat↔ℕ₀ completo (0, σ, τ, ρ, Lt, Le, max, min, add, sub, mul, div, mod, pow, gcd, lcm) | ✅ Completo |
| `Peano/PeanoNat/Primes.lean` | `Peano.Primes` | Primos, irreducibles, factorización única, `Decidable (Prime n)` | ✅ Completo |
| `Peano/PeanoNat/Lists.lean` | `Peano.Lists` | Listas de ℕ₀, FSet, operaciones | ✅ Completo |
| `Peano/PeanoNat/FSet.lean` | `Peano.FSet` | Conjuntos finitos con UniqueKeys+SortedByKey | ✅ Completo |
| `Peano/PeanoNat/NumberSets.lean` | `Peano.NumberSets` | Divisores, coprimos, primos ≤ n | ✅ Completo |
| `Peano/PeanoNat/Combinatorics/Pow.lean` | `Peano.Pow` | Potenciación, `pow_add`, `pow_mul` | ✅ Completo |
| `Peano/PeanoNat/Combinatorics/Factorial.lean` | `Peano.Factorial` | Factorial, `factorial_pos`, `factorial_succ` | ✅ Completo |
| `Peano/PeanoNat/Combinatorics/Binom.lean` | `Peano.Binom` | Coeficientes binomiales, Pascal, simetría | ✅ Completo |
| `Peano/PeanoNat/Combinatorics/NewtonBinom.lean` | `Peano.NewtonBinom` | Binomio de Newton, `sum_binom_eq_pow_two` | ✅ Completo |
| `Peano/PeanoNat/Combinatorics/Summation.lean` | `Peano.Summation` | Sumatorias `∑`, propiedades algebraicas | ✅ Completo |
| `Peano/PeanoNat/Combinatorics/Product.lean` | `Peano.Product` | Productorias `∏`, propiedades algebraicas | ✅ Completo |
| `Peano/PeanoNat/Combinatorics/Fibonacci.lean` | `Peano.Fibonacci` | Sucesión de Fibonacci, propiedades | ✅ Completo |
| `Peano/PeanoNat/Log.lean` | `Peano.Log` | Logaritmo entero con resto: `logMod`, `log`, `logRem` | ✅ Completo |
| `Peano/PeanoNat/Sqrt.lean` | `Peano.Sqrt` | Raíz cuadrada entera con resto: `sqrtMod`, `sqrt`, `sqrtRem` | ✅ Completo |
| `Peano/PeanoNat/Digits.lean` | `Peano.Digits` | Dígitos en base arbitraria, representación posicional | ✅ Completo |
| `Peano/PeanoNat/Pairing.lean` | `Peano.Pairing` | Función de emparejamiento de Cantor y su inversa | ✅ Completo |
| `Peano/PeanoNat/NumberTheory/ModEq.lean` | `Peano.ModEq` | Congruencia modular `ModEq`, propiedades algebraicas | ✅ Completo |
| `Peano/PeanoNat/NumberTheory/Totient.lean` | `Peano.Totient` | Función de Euler φ, `totient_prime`, `totient_pos` | ✅ Completo |

---

## Hitos completados

### Fase 1–4: Aritmética completa de ℕ₀ y ℕ₁ (2026-03-03)

- **Divisibilidad completa**: `divides_refl`, `divides_trans`, `divides_add`, `divides_sub`, `divides_mod`, `one_divides`, `divides_zero`, `divides_le`, `antisymm_divides`.
- **MCD y conmutatividad**: `gcd_step`, `gcd_divides_left/right`, `gcd_greatest`, `gcd_comm`.
- **Identidad de Bézout**: `bezout_additive` y `bezout_natform`.
- **ℕ₁**: `Divides₁`, `IsGCD₁`, `gcd₁`, `Coprime₁`, `gcd₁_comm`, `gcd₁_divides_both`.

### Fase 5–6: Infraestructura y exports (2026-03-15)

- Toolchain v4.29.0, scripts de gestión, export blocks en los 16 módulos.
- Potenciación, factorial, coeficientes binomiales, binomio de Newton.
- Primos: `unique_prime_factorization`, `coprime_dvd_of_dvd_mul` (Gauss), `prime_iff_irreducible`.

### Fase 7–17: Reestructuración y modernización (2026-04-08)

- Directorio `PeanoNatLib/` → `Peano/`, `PeanoNatLib.lean` → `PeanoNat.lean`.
- Subdirectorio `Combinatorics/` extraído. `Prelim.lean`, `Isomorph.lean`, `Decidable.lean` factorizados.
- Copyright headers, migración de identificadores a convenciones Mathlib4.

### Extensiones recientes (2026-06)

- **Lattice.lean**: Módulo de retícula con `max`/`min` + 18 teoremas Mathlib-style (distributividad, `max_comm_assoc`, `min_max_distrib`, etc.).
- **Arith.lean § 8**: 25 teoremas GCD/LCM/Coprime Mathlib-style (`gcd_assoc`, `gcd_mul_lcm`, `lcm_comm`, `div_mul_cancel`, `dvd_gcd_iff`, etc.).
- **FSet.lean**: Conjuntos finitos con invariantes `UniqueKeys` + `SortedByKey`.
- **Fibonacci.lean**: Sucesión de Fibonacci + propiedades (identidad de Cassini, fib_add, etc.).
- **Summation.lean**, **Product.lean**: Sumatorias y productorias con propiedades algebraicas.
- **NumberSets.lean**: `DivisorsOf`, `CoprimesOf`, `PrimesUpTo` como FSet.
- **Isomorph.lean (§ 20.5)**: 14 teoremas de isomorfismo Nat↔ℕ₀ para mul, div, mod, pow, gcd, lcm. Reexporta desde Mul, Div, Pow y Arith.

### Phase 21 — Instancias Init y decidabilidad (2026-04-09)

- **21.7a**: Todas las instancias Init (Mul, Sub, Div, Mod, Pow, Zero, One, OfNat, Ord).
- **21.7b**: `WellFoundedRelation ℕ₀`, `lt_or_ge`, `le_or_lt`, `strongRecOn`, `strongInductionOn`, `DecidableRel` para LT/LE.
- **21.8**: `IsEven`/`IsOdd` con instancias `Decidable` + 6 teoremas.
- **21.9**: `Decidable (Prime n)` vía `isPrimeb` + `isPrimeb_iff`.

---

## Próximos objetivos

- **Phase 21 (en curso)**: Digits ✅, Pairing ✅, ModEq ✅, Totient ✅, ChineseRemainder.lean, Fermat.lean.
- **Phase 22**: Extensión a enteros ℤ (pares de equivalencia).
- **Phase 23**: Extensión a racionales ℚ.

---

**Licencia**: MIT License
