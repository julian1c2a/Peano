# Estado Actual del Proyecto: Peano

**Última actualización:** 2026-04-08
**Autor**: Julián Calderón Almendros

---

## Resumen

Biblioteca de aritmética de Peano pura en Lean 4, sin Mathlib, construida íntegramente desde los axiomas de Peano. Todos los módulos compilan sin ningún `sorry`.

---

## Estado de compilación

```
lean-toolchain  →  leanprover/lean4:v4.29.0
lake build      →  Build completed successfully (19 jobs)
sorry count     →  0
warnings        →  1 (PeanoNatSub.lean:484 — unused simp arg, cosmético)
```

---

## Módulos

| Archivo | Namespace | Contenido principal | Estado |
|---|---|---|---|
| `PeanoNatLib.lean` | `Peano` | `ℕ₀`, `ExistsUnique`, `choose`, constantes, isomorfismos | ✅ Completo |
| `PeanoNatAxioms.lean` | `Peano.Axioms` | Axiomas, `𝟘`, `succ`, `𝟙`, inducción | ✅ Completo |
| `PeanoNatStrictOrder.lean` | `Peano.StrictOrder` | Orden estricto `<`, `lt_of_lt_of_le` | ✅ Completo |
| `PeanoNatOrder.lean` | `Peano.Order` | Orden `≤`, `le_antisymm`, `le_trans` | ✅ Completo |
| `PeanoNatMaxMin.lean` | `Peano.MaxMin` | `max`, `min`, propiedades básicas | ✅ Completo |
| `PeanoNatWellFounded.lean` | `Peano.WellFounded` | Inducción bien fundada, `well_founded_lt` | ✅ Completo |
| `PeanoNatAdd.lean` | `Peano.Add` | Suma, neutro, conmutatividad, asociatividad | ✅ Completo |
| `PeanoNatSub.lean` | `Peano.Sub` | Resta truncada, `sub_self`, `add_k_sub_k` | ✅ Completo |
| `PeanoNatMul.lean` | `Peano.Mul` | Multiplicación, `mul_sub`, `mul_le_mono_right` | ✅ Completo |
| `PeanoNatDiv.lean` | `Peano.Div` | División entera, módulo, `divMod_eq`, `mod_lt_divisor` | ✅ Completo |
| `PeanoNatArith.lean` | `Peano.Arith` | Divisibilidad, MCD, Bézout, `ℕ₁`, `gcd₁` | ✅ Completo |
| `PeanoNatPow.lean` | `Peano.Pow` | Potenciación, `pow_add`, `pow_mul` | ✅ Completo |
| `PeanoNatFactorial.lean` | `Peano.Factorial` | Factorial, `factorial_pos`, `factorial_succ` | ✅ Completo |
| `PeanoNatBinom.lean` | `Peano.Binom` | Coeficientes binomiales, Pascal, simetría | ✅ Completo |
| `PeanoNatNewtonBinom.lean` | `Peano.NewtonBinom` | Binomio de Newton, `sum_binom_eq_pow_two` | ✅ Completo |
| `PeanoNatPrimes.lean` | `Peano.Primes` | Primos, irreducibles, factorización única | ✅ Completo |

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

### Fase 7: Renombrado de directorio (2026-04-08, en curso)

- Directorio `PeanoNatLib/` → `Peano/`, imports y scripts actualizados.
- Copyright headers añadidos a los 16 módulos.
- Build verificado: 19/19 jobs OK, 0 sorry.

---

## Próximos objetivos

- **Fase 8**: Renombrar `PeanoNatLib.lean` → `PeanoNat.lean` (ver NEXT-STEPS.md).
- **Fase 10**: Migración de nombres de identificadores a convenciones Mathlib4.
- **Futuro**: Extensión a enteros ℤ (pares de equivalencia).

---

**Licencia**: MIT License
