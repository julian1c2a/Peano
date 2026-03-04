# Peano

Formalización de la aritmética de Peano en **Lean 4**, construida desde los axiomas inductivos de `ℕ₀` sin depender de Mathlib.

> **Autor:** Julián Calderón Almendros
> **Lean:** `leanprover/lean4:v4.23.0`
> **Licencia:** MIT

---

## Descripción

Este proyecto define el tipo inductivo `ℕ₀` (números naturales de Peano) y demuestra desde cero toda la aritmética básica: orden, suma, resta, multiplicación, división entera, máximo/mínimo, bien-fundación y aritmética de divisores (MCD, MCM, primos, Bézout).

Toda la biblioteca está **computacionalmente realizada**: las operaciones producen términos de `ℕ₀` evaluables por el kernel de Lean.

---

## Estructura de módulos

```
Peano.lean                        ← entrada; importa toda la librería
└─ PeanoNatLib/
   ├─ PeanoNatLib.lean            namespace Peano
   ├─ PeanoNatAxioms.lean         namespace Peano.Axioms
   ├─ PeanoNatStrictOrder.lean    namespace Peano.StrictOrder
   ├─ PeanoNatOrder.lean          namespace Peano.Order
   ├─ PeanoNatMaxMin.lean         namespace Peano.MaxMin
   ├─ PeanoNatWellFounded.lean    namespace Peano.WellFounded
   ├─ PeanoNatAdd.lean            namespace Peano.Add
   ├─ PeanoNatSub.lean            namespace Peano.Sub
   ├─ PeanoNatMul.lean            namespace Peano.Mul
   ├─ PeanoNatDiv.lean            namespace Peano.Div
   └─ PeanoNatArith.lean          namespace Peano.Arith
```

---

## Contenido por módulo

### `Peano` — Tipos base y utilidades

| Símbolo | Descripción |
|---|---|
| `ℕ₀` | Tipo inductivo (`zero` / `succ`) con `Repr`, `BEq`, `DecidableEq` |
| `ℕ₁` | Subtipo `{n : ℕ₀ // n ≠ 0}` |
| `ℕ₂` | Subtipo `{n : ℕ₁ // n ≠ 1}` |
| `𝟘 𝟙 𝟚 𝟛` | Constantes `0, 1, 2, 3` |
| `σ n` | Notación para `ℕ₀.succ n` |
| `Λ`, `Ψ` | Isomorfismos `Nat ↔ ℕ₀` |
| `ExistsUnique`, `∃¹` | Cuantificador de existencia única |
| `choose`, `choose_unique` | Elección clásica de testigos |

### `Peano.Axioms` — Axiomas de Peano

Los 8 axiomas clásicos demostrados como teoremas a partir de la estructura inductiva:
`0 ≠ σ(n)`, inyectividad de `σ`, principio de inducción, etc.

### `Peano.StrictOrder` — Orden estricto `<`

- `Lt` (Prop), `BLt` (Bool), `Gt`, `BGt`
- Instancias `LT ℕ₀`, `Decidable (Lt n m)`, `Decidable (Gt n m)`
- Teoremas: irreflexividad, asimetría, transitividad, **tricotomía**

### `Peano.Order` — Orden no estricto `≤`

- `Le` (`Lt n m ∨ n = m`), `Ge`, `Le'` (def. recursiva equivalente)
- Instancias `LE ℕ₀`, decisión para `Le` y `Ge`
- Teoremas: reflexividad, antisimetría, transitividad, totalidad, `lt_succ_iff_le`, `le_iff_exists_add`

### `Peano.MaxMin` — Máximo y mínimo

- `max`, `min`: computable, usa `BLt`
- `min_max`, `max_min`: pares ordenados
- Retícula distributiva completa: idempotencia, conmutatividad, asociatividad, distributividad

### `Peano.WellFounded` — Bien-fundación

- `instance : SizeOf ℕ₀` vía `Ψ`
- `well_founded_lt : WellFounded Lt`
- `well_ordering_principle`: existencia y unicidad del mínimo de todo conjunto no vacío
- `isomorph_Ψ_lt`: conexión `n < m ↔ Ψ n < Ψ m` (puente con terminación de Lean)

### `Peano.Add` — Suma `+`

- `add` (recursión sobre `m`), `add_l` (recursión sobre `n`)
- Notaciones `n + m`, `n +l m`
- Teoremas: neutro, conmutatividad, asociatividad, cancelación, `le_iff_exists_add`

### `Peano.Sub` — Resta truncada `∸`

- `subₕₖ n m h` (resta exacta con prueba `Le m n`), notación `n -( h ) m`
- `sub n m` (monus: `n - m = 0` si `m > n`), notación `n - m`
- `termination_by n` con `decreasing_by` via `sub_lt_self`

### `Peano.Mul` — Multiplicación `*`

- `mul` (recursión sobre `m`, prioridad 70)
- Teoremas: neutro, conmutatividad, asociatividad, distributividad, `mul_eq_zero`, propiedad arquimediana, existencia y unicidad del cociente entero

### `Peano.Div` — División entera `/` y módulo `%`

- `divMod` (par `(⌊a/b⌋, a mod b)`), terminado por `termination_by a`
- `div a b`, `mod a b`
- Teoremas: `divMod_eq` (`a = (a/b)·b + a%b`), `mod_lt_divisor`

### `Peano.Arith` — Divisibilidad, MCD, MCM y primos

| Definición | Descripción |
|---|---|
| `Divides a b` / `a ∣ b` | ∃k, b = a·k |
| `IsGCD`, `gcd` | MCD (algoritmo de Euclides) |
| `IsLCM`, `lcm` | MCM |
| `Coprime` | gcd(a,b) = 1 |
| `Prime` | Definición euclídea (Lema de Euclides) |
| `Divides₁`, `gcd₁`, `Coprime₁` | Variantes en `ℕ₁` |
| `DList`, `Factors_of`, `DivisorsList` | Listas computables de divisores |
| `Multiples` | Inductivo de múltiplos |

Teoremas destacados: `bezout_natform`, `gcd_greatest`, `divides_trans`, `multiples_iff_divides`, `gcd_divides_linear_combo`.

---

## Instalación y compilación

**Requisitos:** [`elan`](https://github.com/leanprover/elan) instalado.

```bash
git clone https://github.com/julian1c2a/Peano.git
cd Peano
lake build
```

La versión de Lean se instala automáticamente desde `lean-toolchain` (`leanprover/lean4:v4.23.0`).

---

## Uso como dependencia

En tu `lakefile.lean`:

```lean
require peanolib from git
  "https://github.com/julian1c2a/Peano.git"
```

Luego importa lo que necesites:

```lean
import PeanoNatLib.PeanoNatArith   -- incluye todo lo anterior
```

---

## Documentación técnica

Ver [`REFERENCE.md`](REFERENCE.md) para la referencia completa de definiciones, teoremas, notaciones y dependencias entre módulos.

---

## Licencia

MIT — ver [`LICENSE`](LICENSE).
