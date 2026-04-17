# Naming Conventions — Mathlib Style

> Permanent reference document for this project.
> All rules are based on the
> [Mathlib Naming Conventions](https://leanprover-community.github.io/contribute/naming.html),
> adapted to the project's specific domain.

**Last updated:** 2026-04-17
**Author**: Julián Calderón Almendros

---

## 1. Capitalization Rules

| Declaration type | Convention | Example |
|------------------|------------|---------|
| Theorems, lemmas (Prop terms) | `snake_case` | `add_comm`, `succ_inj` |
| Types, Props, Structures, Classes | `UpperCamelCase` | `ExistsUnique`, `IsNat` |
| Functions returning `Type` | by return type | `succ` (→ ℕ₀ → `snake`), `RecursiveFn` (→ Type → `Upper`) |
| Other `Type` terms | `lowerCamelCase` | `cero`, `one`, `idℕ₀` |
| Acronyms | as group upper/lower | `Peano` (namespace), `peano` (in snake_case) |

---

## 2. Symbol-to-Word Dictionary

| Symbol | In names | Notes |
|--------|----------|-------|
| σ | `succ` | successor |
| 0 / cero | `zero` | first natural |
| 1 | `one` | |
| + | `add` | |
| \* / · | `mul` | |
| − | `sub` (binary) / `neg` (unary) | |
| ^ | `pow` | |
| / | `div` | |
| % | `mod` | modulo |
| ∣ | `dvd` | divides |
| ≤ | `le` | |
| < | `lt` | |
| ≥ | `ge` | only for argument swap |
| > | `gt` | only for argument swap |
| = | `eq` | often omitted |
| ≠ | `ne` | |
| → | `of` / implicit | conclusion goes first |
| ↔ | `iff` | suffix |
| ¬ | `not` | |
| ∃ | `exists` | |
| ∀ | `forall` | |
| ∘ | `comp` | composition |
| ⁻¹ | `inv` | inverse |
| ! | `factorial` | |
| C(n,k) | `binom` | binomial coefficient |

---

## 3. Name Formation Rules (12 rules)

### RULE 1 — Conclusion first, hypotheses with `_of_`

The name describes **what is proved**, not how. Hypotheses are added with `_of_`:

```
-- Pattern: A → B → C
-- Name:    c_of_a_of_b
-- Order:   conclusion_of_hypothesis1_of_hypothesis2

-- Example:
-- Theorem: isNat n → isNat (σ n)
-- Name:    isNat_succ_of_isNat
```

### RULE 2 — Biconditionals carry suffix `_iff`

```
-- Theorem: a ≤ b ↔ a < b ∨ a = b
-- Name:    le_iff_lt_or_eq
```

### RULE 3 — Eliminate `_wc` — Use `.mp` / `.mpr` or `_of_`

```
-- For forward direction of an iff:
--    le_iff_lt_or_eq.mp
-- For backward direction:
--    le_iff_lt_or_eq.mpr
-- As standalone theorem:
--    lt_of_le_of_ne    (conclusion_of_hypothesis)
```

### RULE 4 — Algebraic properties → short axiomatic name

```
-- commutativity:   add_comm, mul_comm
-- associativity:   add_assoc, mul_assoc
-- distributivity:  mul_add_distrib_left
```

**Standard axiomatic suffixes (Mathlib):**

| Suffix | Meaning | Example |
|--------|---------|---------|
| `_comm` | commutativity | `add_comm` |
| `_assoc` | associativity | `mul_assoc` |
| `_refl` | reflexivity | `le_refl` |
| `_irrefl` | irreflexivity | `lt_irrefl` |
| `_symm` | symmetry | `eq_symm` |
| `_trans` | transitivity | `le_trans` |
| `_antisymm` | antisymmetry | `le_antisymm` |
| `_asymm` | asymmetry | `lt_asymm` |
| `_inj` | injectivity (iff) | `succ_inj` (σ a = σ b ↔ a = b) |
| `_injective` | injectivity (pred) | `succ_injective` |
| `_self` | operation with itself | `add_zero` |
| `_left` / `_right` | lateral variant | `add_left_cancel` |
| `_cancel` | cancellation | `add_left_cancel` |
| `_mono` | monotonicity | `add_mono` |

### RULE 5 — Predicates as prefix, operations in infix order

```
-- Predicate as prefix:   isNat_zero (not zero_is_nat)
-- Exception:             succ_injective (_injective, _surjective are always suffix)
```

### RULE 6 — Standard abbreviations for frequent conditions

| Instead of | Use | Meaning |
|-----------|-----|---------|
| `zero_lt_x` | `pos` | x > 0 |
| `x_lt_zero` | `neg` | x < 0 |
| `x_le_zero` | `nonpos` | x ≤ 0 |
| `zero_le_x` | `nonneg` | x ≥ 0 |

### RULE 7 — Definitions with `Is` for Prop predicates

```
-- Definition (Prop): def IsNat (n : U) : Prop := ...     (UpperCamelCase)
-- In theorem names:  isNat_zero, isNat_succ, isNat_of_mem (lowerCamelCase in snake_case)
```

### RULE 8 — Functions/constructors non-Prop: `lowerCamelCase`

```
-- succ (not Succ)            — lowerCamelCase
-- cero (not Cero)            — lowerCamelCase
-- idℕ₀ (not IdFunction)     — abbreviation
-- divModFn (not DivModPair) — lowerCamelCase
```

### RULE 9 — Specifications: `_iff` and `mem_X_iff`

```
-- succ_inj          (σ a = σ b ↔ a = b)
-- le_iff_lt_or_eq   (a ≤ b ↔ a < b ∨ a = b)
-- lt_iff_le_and_ne  (a < b ↔ a ≤ b ∧ a ≠ b)
```

### RULE 10 — Uniqueness and existence

```
-- div_exists_unique    — existence and uniqueness of quotient
-- mod_lt               — modulo is less than divisor
```

### RULE 11 — Names with `_left` / `_right`

```
-- add_left_cancel    — a + b = a + c → b = c (cancel left arg)
-- mul_right_cancel   — b * a = c * a → b = c (cancel right arg)
```

### RULE 12 — Named theorems (proper names)

```
-- euclid_division         — proper name + description (OK in Mathlib)
-- newton_binom            — Newton's binomial theorem
```

> **NOTE:** Mathematical proper names are kept as-is in Mathlib.
> Only operational words are normalized (`add`, `mul`, etc.).

---

## 4. Quick Reference Tables

### 4.1 Definitions — common renamings

| Before | After | Rationale |
|--------|-------|-----------|
| `successor` | `succ` | standard abbreviation |
| `zero` | `cero` | project convention for ℕ₀ zero |
| `FunctionComposition` | `comp` | standard abbreviation |
| `IdFunction` | `id` | standard abbreviation |

### 4.2 Theorems — algebraic properties

| Before | After | Breakdown |
|--------|-------|-----------|
| `add_commutative` | `add_comm` | + + commutativity |
| `mul_commutative` | `mul_comm` | · + commutativity |
| `add_associative` | `add_assoc` | + + associativity |
| `le_reflexive` | `le_refl` | ≤ + reflexivity |
| `le_transitive` | `le_trans` | ≤ + transitivity |
| `le_antisymmetric` | `le_antisymm` | ≤ + antisymmetry |

---

## 5. Migration Note

During development, names are renamed progressively following these conventions.
Priority order for migration:

1. Base modules (axioms): `Peano`, `PeanoNatAxioms`
2. Order: `PeanoNatStrictOrder`, `PeanoNatOrder`, `Lattice`, `PeanoNatWellFounded`
3. Arithmetic: `PeanoNatAdd`, `PeanoNatSub`, `PeanoNatMul`, `PeanoNatDiv`, `PeanoNatArith`
4. Advanced: `PeanoNatPrimes`, `PeanoNatPow`, `PeanoNatFactorial`, `PeanoNatBinom`, `PeanoNatNewtonBinom`

Each rename is verified with full compilation before proceeding.

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

