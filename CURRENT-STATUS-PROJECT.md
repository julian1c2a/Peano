# Estado Actual del Proyecto: Peano

**Última actualización:** 2026-03-03
**Autor**: Julián Calderón Almendros

---

## Resumen

Biblioteca de aritmética de Peano pura en Lean 4, sin Mathlib, construida íntegramente desde los axiomas de Peano. Todos los módulos compilan sin ningún `sorry`.

---

## Estado de compilación

```
lake build   →   Build completed successfully (13 jobs)
sorry count  →   0
```

---

## Módulos

| Archivo | Contenido principal | Estado |
|---|---|---|
| `PeanoNatAxioms.lean` | Axiomas, `𝟘`, `succ`, `𝟙`, `ℕ₀` | ✅ Completo |
| `PeanoNatAdd.lean` | Suma, neutro, conmutatividad, asociatividad | ✅ Completo |
| `PeanoNatMul.lean` | Multiplicación, `mul_sub`, `mul_le_mono_right` | ✅ Completo |
| `PeanoNatOrder.lean` | Orden `≤`, `Eq`, `le_antisymm`, `le_trans` | ✅ Completo |
| `PeanoNatStrictOrder.lean` | Orden estricto `<`, `lt_of_lt_of_le` | ✅ Completo |
| `PeanoNatSub.lean` | Resta truncada, `sub_self`, `add_k_sub_k` | ✅ Completo |
| `PeanoNatDiv.lean` | División entera, módulo, `divMod_eq`, `mod_lt_divisor` | ✅ Completo |
| `PeanoNatMaxMin.lean` | `max`, `min`, propiedades básicas | ✅ Completo |
| `PeanoNatWellFounded.lean` | Inducción bien fundada, `well_founded_lt` | ✅ Completo |
| `PeanoNatArith.lean` | Teoría de números: divisibilidad, MCD, Bézout, `ℕ₁`, `gcd₁` | ✅ **Completo** |

---

## Hitos completados (2026-03-03)

### ℕ₀ — Aritmética de números naturales

- **Divisibilidad completa**: `divides_refl`, `divides_trans`, `divides_add`, `divides_sub`, `divides_mod`, `one_divides`, `divides_zero`, `divides_le`, `antisymm_divides`.
- **MCD y conmutatividad**: `gcd_step`, `gcd_divides_left/right`, `gcd_greatest`, `gcd_divides_max/min`, `gcd_divides_linear_combo`, `gcd_comm`.
- **Identidad de Bézout**: `bezout_additive` (forma OR con coeficientes ℕ₀) y `bezout_natform` (`gcd a b = n*a - m*b ∨ gcd a b = n*b - m*a`).

### ℕ₁ — Naturales positivos `{n : ℕ₀ // n ≠ 𝟘}`

- **Definiciones**: `Divides₁` (notación `∣₁`), `IsGCD₁`, `gcd₁` (Euclides con terminación well-founded), `Coprime₁`.
- **Divisibilidad**: `divides₁_refl`, `divides₁_trans`, `divides₁_antisymm`.
- **MCD**: `gcd₁_val_eq` (puente ℕ₁↔ℕ₀), `gcd₁_comm`, `gcd₁_divides_left`, `gcd₁_divides_right`, `gcd₁_divides_both`.

---

## Próximos objetivos

- `gcd₁_greatest` — maximalidad del MCD en `ℕ₁`.
- `gcd₁_isGCD` — demostrar que `gcd₁ a b` satisface `IsGCD₁`.
- Teorema de Bézout sobre `ℤ` (requiere implementar enteros o usar subtipo con signo).
- `Prime`, `Coprime` sobre `ℕ₁` y lema de Euclides.

---

**Licencia**: MIT License
