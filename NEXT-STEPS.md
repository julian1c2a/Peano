# Next Steps — Peano

**Last updated:** 2026-04-15
**Author**: Julián Calderón Almendros

> This file tracks planned development phases. Each phase includes
> objectives, modules to create, dependencies, and estimated complexity.

---

## Phase Status Summary

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Peano Foundations | ✅ Complete |
| 2 | Order Theory | ✅ Complete |
| 3 | Arithmetic Operations | ✅ Complete |
| 4 | Advanced Number Theory | ✅ Complete |
| 5 | Infrastructure Modernization | ✅ Complete |
| 6 | Export/Glob Architecture | ✅ Complete |
| 7 | Directory rename PeanoNatLib → Peano | ✅ Complete |
| 8 | File rename PeanoNatLib.lean → PeanoNat.lean | ✅ Complete |
| 9 | Namespace Migration | ✅ Complete (no-op) |
| 10 | Identifier Naming Migration | ✅ Complete |
| 11 | Warning Cleanup | ✅ Complete |
| 12 | Update REFERENCE.md with new names | ✅ Complete |
| 13 | Subdirectory restructure PeanoNat/ | ✅ Complete |
| 14 | Extract Prelim.lean (shared infrastructure) | ✅ Complete |
| 15 | Create Isomorph.lean (Nat↔ℕ₀ reexport) | ✅ Complete |
| 16 | Factor Decidable module | ✅ Complete |
| 17 | Factor Combinatorics subdirectory | ✅ Complete |
| 18 | Lattice.lean Mathlib-style extensions | ✅ Complete |
| 19 | GCD/LCM/Coprime Mathlib-style extensions | ✅ Complete |
| 20 | Log.lean + Sqrt.lean (floor + remainder) | ✅ Complete |
| 20.5 | Isomorfismos Nat↔ℕ₀ completos (mul/div/mod/pow/gcd/lcm) | ✅ Complete |
| 21 | Naturals completion (ℕ₀) | 🔶 In progress |
| 22 | Integer extension (ℤ) | ❌ Pending |
| 23 | Rational extension (ℚ) | ❌ Pending |
| 24 | FSet Generalization | 🔶 In progress |

---

## Phase 5: Infrastructure Modernization

**Objective**: Bring project infrastructure to template standard.
**Status**: ✅ Complete

**Steps**:

- [x] Add git-lock.bash, check-sorry.bash, gen-root.bash, new-module.bash, update-toolchain.bash
- [x] Add Makefile
- [x] Add AI-GUIDE.md, NAMING-CONVENTIONS.md, WORKFLOW.md, DECISIONS.md, THOUGHTS.md
- [x] Add _template.lean, frozen_files.txt, locked_files.txt
- [x] Fix .gitignore
- [x] Remove obsolete files (AIDER-AI-GUIDE.md, .bat scripts, etc.)
- [x] Update toolchain to v4.29.0

---

## Phase 6: Export/Glob Architecture

**Objective**: Add export blocks to all 16 leaf modules per AI-GUIDE.md §30–31.
**Status**: ✅ Complete — all 16 modules have export blocks.

---

## Phase 7: Directory Rename PeanoNatLib → Peano

**Objective**: Complete the directory rename and update all references.
**Status**: ✅ Complete

**Steps**:

- [x] Rename directory `PeanoNatLib/` → `Peano/`
- [x] Update `lakefile.lean` globs
- [x] Update all `import` statements in `.lean` files
- [x] Update 12 documentation `.md` files
- [x] Update scripts: `gen-root.bash`, `new-module.bash`, `git-lock.bash`, `copiar_txt.bash`
- [x] Update comments in `lakefile.lean`, `Peano.lean`, `.lean` module headers
- [x] Add copyright headers to 9 missing modules (AI-GUIDE §19)
- [x] Add `LSP_*.log` to `.gitignore`
- [x] Fix README.md Lean version (v4.23.0 → v4.29.0)
- [x] Update CURRENT-STATUS-PROJECT.md (add Pow, Factorial, Binom, NewtonBinom, Primes)
- [x] Update timestamps in all docs
- [x] `lake clean && lake build` — verify compilation
- [x] Commit

---

## Phase 8: File Rename PeanoNatLib.lean → PeanoNat.lean

**Objective**: Rename the base definitions file to match the module naming pattern.
**Status**: ✅ Complete
**Dependencies**: Phase 7 complete

The file `Peano/PeanoNatLib.lean` is the foundational module containing `ℕ₀`,
`ExistsUnique`, `choose`, constants, and isomorphisms. Its name is a relic of
the old directory name and should be `PeanoNat.lean` for consistency.

**Steps**:

1. Rename file: `Peano/PeanoNatLib.lean` → `Peano/PeanoNat.lean`
2. Update all `import Peano.PeanoNatLib` → `import Peano.PeanoNat` in 15 modules
3. Update `Peano.lean` root: `import Peano.PeanoNatLib` → `import Peano.PeanoNat`
4. Update `export Peano (...)` block in `Peano.lean`
5. Update `frozen_files.txt`: `Peano/PeanoNatLib.lean` → `Peano/PeanoNat.lean`
6. Update `locked_files.txt`: `Peano/PeanoNatLib.lean` → `Peano/PeanoNat.lean`
7. Update `new-module.bash` template substitution line
8. Update REFERENCE.md module table
9. `lake clean && lake build`
10. Commit

**Complexity**: Simple (mechanical, no code changes)

---

## Phase 9: Namespace Migration

**Objective**: Align namespace names with Mathlib conventions and remove redundant `PeanoNat` prefix.
**Status**: ❌ Pending
**Dependencies**: Phase 8 complete
**Reference**: [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) §NC-2

### Current → Target namespace mapping

| File | Current namespace | Target namespace | Rationale |
|------|------------------|-----------------|-----------|
| `PeanoNat.lean` | `Peano` | `Peano` | ✅ No change (root) |
| `PeanoNatAxioms.lean` | `Peano.Axioms` | `Peano.Axioms` | ✅ No change |
| `PeanoNatStrictOrder.lean` | `Peano.StrictOrder` | `Peano.StrictOrder` | ✅ No change |
| `PeanoNatOrder.lean` | `Peano.Order` | `Peano.Order` | ✅ No change |
| `Lattice.lean` | `Peano.Lattice` | `Peano.Lattice` | ✅ Renamed from MaxMin |
| `PeanoNatWellFounded.lean` | `Peano.WellFounded` | `Peano.WellFounded` | ✅ No change |
| `PeanoNatAdd.lean` | `Peano.Add` | `Peano.Add` | ✅ No change |
| `PeanoNatSub.lean` | `Peano.Sub` | `Peano.Sub` | ✅ No change |
| `PeanoNatMul.lean` | `Peano.Mul` | `Peano.Mul` | ✅ No change |
| `PeanoNatDiv.lean` | `Peano.Div` | `Peano.Div` | ✅ No change |
| `PeanoNatArith.lean` | `Peano.Arith` | `Peano.Arith` | ✅ No change |
| `PeanoNatPrimes.lean` | `Peano.Primes` | `Peano.Primes` | ✅ No change |
| `PeanoNatPow.lean` | `Peano.Pow` | `Peano.Pow` | ✅ No change |
| `PeanoNatFactorial.lean` | `Peano.Factorial` | `Peano.Factorial` | ✅ No change |
| `PeanoNatBinom.lean` | `Peano.Binom` | `Peano.Binom` | ✅ No change |
| `PeanoNatNewtonBinom.lean` | `Peano.NewtonBinom` | `Peano.NewtonBinom` | ✅ No change |

**Conclusion**: All namespaces already follow the `Peano.Topic` pattern per NC-2. **No namespace renames needed.** The only remaining issue is that the `export` blocks in leaf modules use the full `Peano.Namespace (...)` form correctly.

**Complexity**: None — namespaces are already correct.

---

## Phase 10: Identifier Naming Migration

**Objective**: Ensure all public identifiers follow Mathlib4 naming conventions.
**Status**: ✅ Complete
**Dependencies**: Phase 8 complete (Phase 9 is a no-op)
**Reference**: [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) — all 12 rules

### 10.1. Migration strategy

Each module is migrated independently. For each module:

1. **Thaw** the frozen module: `bash git-lock.bash thaw Peano/Module.lean --confirm`
2. **Rename** identifiers (both declaration + all usage sites within the module)
3. **Update** the module's `export` block
4. **Update** dependent modules' usage of renamed identifiers
5. **Verify**: `lake build` — must compile
6. **Update** `Peano.lean` export blocks
7. **Update** REFERENCE.md
8. **Re-freeze**: `bash git-lock.bash freeze Peano/Module.lean`
9. **Commit** the module migration

Migration order follows the dependency chain (bottom-up):

```
PeanoNat.lean          (1st — no dependencies)
PeanoNatAxioms.lean    (2nd — depends on PeanoNat)
PeanoNatStrictOrder.lean (3rd)
PeanoNatOrder.lean     (4th)
Lattice.lean           (5th — renamed from MaxMin, MOST renames here)
PeanoNatWellFounded.lean (6th)
PeanoNatAdd.lean       (7th)
PeanoNatSub.lean       (8th)
PeanoNatMul.lean       (9th)
PeanoNatDiv.lean       (10th)
PeanoNatArith.lean     (11th)
PeanoNatPrimes.lean    (12th)
PeanoNatPow.lean       (13th)
PeanoNatFactorial.lean (14th)
PeanoNatBinom.lean     (15th)
PeanoNatNewtonBinom.lean (16th)
```

### 10.2. Audit results — renames needed per module

#### PeanoNat.lean (namespace Peano)

| Current | Target | Rule |
|---------|--------|------|
| `EqFnGen` | `eqFnGen` | NC-4: functions → lowerCamelCase |
| `Comp` | `comp` | NC-4: functions → lowerCamelCase |
| `EqFn` | `eqFn` | NC-4: functions → lowerCamelCase |
| `EqFn2` | `eqFn2` | NC-4: functions → lowerCamelCase |
| `EqFnNat` | `eqFnNat` | NC-4: functions → lowerCamelCase |
| `Tuple` | `Tuple` | ✅ NC-3: Type → UpperCamelCase |
| `ExistsUnique` | `ExistsUnique` | ✅ NC-3: Prop → UpperCamelCase |

> Note: `Λ`, `Ψ`, `τ`, `ρ` are single-letter Greek — acceptable as-is.

#### PeanoNatAxioms.lean (namespace Peano.Axioms)

| Current | Target | Rule |
|---------|--------|------|
| `AXIOM_zero_is_an_PeanoNat` | `isNat_zero` | Rule 5: predicate prefix |
| `AXIOM_succ_is_an_PeanoNat` | `isNat_succ` | Rule 5 |
| `AXIOM_cero_neq_succ` | `zero_ne_succ` | Rule 1: conclusion first |
| `AXIOM_succ_is_funct_forall_n_in_PeanoNat` | `succ_isNat` | Rule 5 |
| `AXIOM_uniqueness_on_image` | `succ_inj` | Rule 4: standard _inj suffix |
| `AXIOM_succ_inj` | `succ_injective` | Rule 4: _injective for predicate |
| `AXIOM_induction_principle` | `induction_principle` | OK (named theorem, Rule 12) |
| `return_branch` | `returnBranch` | NC-4: lowerCamelCase for functions |
| `is_zero` | `isZero` | NC-7: Prop predicate → `Is` prefix, lowerCamelCase in names |
| `is_succ` | `isSucc` | NC-7 |

#### PeanoNatStrictOrder.lean (namespace Peano.StrictOrder)

| Current | Target | Rule |
|---------|--------|------|
| `BLt` | `blt` | NC-4: Bool function → lowerCamelCase |
| `BGt` | `bgt` | NC-4 |
| `nlt_0_0` | `not_lt_zero` | Rule 1 + Symbol dict: ¬ → `not` |
| `lt_0_n` | `zero_lt_succ` | Rule 1 (conclusion first) |
| `lt_then_neq` | `ne_of_lt` | Rule 1 + Rule 3 |
| `ble_to_le` | `le_of_ble` | Rule 1 |
| Various `_wc` suffixed theorems | `.mp`/`.mpr` or `_of_` | Rule 3 |

#### PeanoNatOrder.lean (namespace Peano.Order)

| Current | Target | Rule |
|---------|--------|------|
| `BLe` | `ble` | NC-4 |
| `BGe` | `bge` | NC-4 |
| `Le'` | `le'` | NC-4 (recursive def) |
| Various verbose names | Mathlib-style | Rules 1-3 |

#### Lattice.lean (namespace Peano.Lattice) — MOST RENAMES (formerly MaxMin)

| Current | Target | Rule |
|---------|--------|------|
| `Lt_of_not_le` | `lt_of_not_le` | Lowercase (theorem naming) |
| `eq_max_min_then_eq` | `eq_of_max_eq_min` | Rule 1 |
| `if_neq_then_max_xor` | `max_ne_min_of_ne` | Rule 1 |
| `neq_args_then_lt_min_max` | `lt_max_of_ne` | Rule 1 |
| `nexists_max_abs` | `not_exists_max` | Symbol dict: ¬ → `not` |

#### PeanoNatAdd.lean (namespace Peano.Add)

| Current | Target | Rule |
|---------|--------|------|
| `add_cancelation` | `add_cancel` | Rule 4: standard `_cancel` suffix |
| Other names | ✅ Already Mathlib-compliant | — |

#### PeanoNatMul.lean (namespace Peano.Mul)

| Current | Target | Rule |
|---------|--------|------|
| `mul_ldistr` | `mul_add_left` or `left_distrib` | Mathlib convention |
| `mul_rdistr` | `mul_add_right` or `right_distrib` | Mathlib convention |
| `mul_eq_zero_wp` | `eq_zero_of_mul_eq_zero` | Rule 1 |
| `mul_le_then_exists_max_factor` | `exists_factor_of_mul_le` | Rule 1 |

#### PeanoNatDiv.lean (namespace Peano.Div)

| Current | Target | Rule |
|---------|--------|------|
| `divMod_eq` | `divMod_spec` | Clarify purpose |
| `mod_lt_divisor` | `mod_lt` | Mathlib standard |
| `div_of_lt_snd_interval` | `div_of_lt` | Simplify |

#### PeanoNatArith.lean (namespace Peano.Arith)

| Current | Target | Rule |
|---------|--------|------|
| `Divides` | `Divides` | ✅ NC-3: Prop |
| `MultipleOf` | `MultipleOf` | ✅ NC-3 |
| `DivisorOf` | `DivisorOf` | ✅ NC-3 |
| `DList` | `DList` | ✅ NC-3: Type |
| `Coprime` | `Coprime` | ✅ NC-3 |
| `Prime` | `Prime` | ✅ NC-3 |
| `divides_le` | ✅ | — |
| `gcd_greatest` | ✅ | — |
| `bezout_natform` | ✅ (named theorem, Rule 12) | — |

#### PeanoNatPrimes.lean (namespace Peano.Primes)

| Current | Target | Rule |
|---------|--------|------|
| `Factors_of` | `factorsOf` | NC-4: lowerCamelCase |
| `unique_prime_factorization` | ✅ (Rule 12, named theorem) | — |
| Other names | ✅ Already compliant | — |

#### PeanoNatPow / Factorial / Binom / NewtonBinom

**✅ These 4 modules are already fully Mathlib-compliant.** No renames needed.

### 10.3. Execution protocol per module

For each module in dependency order:

```bash
# 1. Thaw (emergency unfreeze for migration)
bash git-lock.bash thaw Peano/Module.lean --confirm

# 2. Apply renames (using find-and-replace with exact match)
#    - Rename in the module file
#    - Rename in all downstream modules that use the old name
#    - Rename in the module's export block
#    - Rename in Peano.lean's export block

# 3. Build
lake build

# 4. Re-freeze
bash git-lock.bash freeze Peano/Module.lean

# 5. Update REFERENCE.md

# 6. Commit
git commit -m "naming: migrate Module.lean to Mathlib conventions"
```

### 10.4. Risk mitigation

- **Build after each module** — never batch multiple module renames
- **Downstream breakage**: renaming an identifier in module N requires updating modules N+1…16
- **Dependency chain**: migrate bottom-up to minimize cascading renames
- **Rollback**: each commit is atomic per module — easy `git revert`

### 10.5. Execution deviations (2026-04-09)

| Planned name | Actual name | Reason |
|-------------|-------------|--------|
| `AXIOM_uniqueness_on_image → succ_inj` | `succ_congr` | Theorem is congruence (n=m → σn=σm), not injectivity. `succ_inj` already existed as wrapper for the true injectivity theorem. |
| `lt_0_n → zero_lt_succ` | `pos_of_ne_zero` | `zero_lt_succ` already existed in PeanoNatStrictOrder.lean (line 923) with different signature (Lt 𝟘 (σ n)). `pos_of_ne_zero` follows Mathlib convention for `n ≠ 0 → 0 < n`. |
| `mul_ldistr → mul_add_left` | `mul_add` | Standard Mathlib4 name for left distributivity. |
| `mul_rdistr → mul_add_right` | `add_mul` | Standard Mathlib4 name for right distributivity. |
| `div_of_lt_snd_interval → div_of_lt` | `div_eq_two` | `div_of_lt` already existed. `div_eq_two` describes the conclusion. |

---

## Phase 11: Warning Cleanup

**Objective**: Eliminate all compiler/linter warnings so that `lake build` produces zero warnings.
**Status**: ✅ Complete (2026-04-08)
**Dependencies**: Phase 10 complete

Removed unused `Nat.sub` simp arg from `PeanoNat/Sub.lean:484`. Build: 19/19, 0 warnings.

---

## Phase 12: Update REFERENCE.md with New Names

**Objective**: Regenerate REFERENCE.md to reflect all identifier renames from Phase 10.
**Status**: ✅ Complete (2026-04-09)
**Dependencies**: Phase 10 and 11 complete

Regenerated REFERENCE.md from scratch (~1350 lines, 19 sections) reflecting:

- New file paths from Phase 13 subdirectory restructure
- Renamed identifiers from Phase 10
- 3 new modules from Phases 14-16 (Prelim, Isomorph, Decidable)
- Combinatorics subdirectory from Phase 17

---

## Phase 13: Subdirectory Restructure PeanoNat/

**Objective**: Move all `PeanoNat*.lean` modules into `Peano/PeanoNat/` subdirectory.
**Status**: ✅ Complete (2026-04-08)
**Dependencies**: Phase 11 complete

Moved 15 files: `PeanoNatAxioms.lean → PeanoNat/Axioms.lean`, etc.
Updated all imports: `Peano.PeanoNatXxx` → `Peano.PeanoNat.Xxx`.
`PeanoNat.lean` remains at `Peano/PeanoNat.lean` as barrel/root module.
Build: 19/19 OK, 0 warnings.

---

## Phase 14: Extract Prelim.lean (shared infrastructure)

**Objective**: Extract `ExistsUnique` + choice infrastructure from `PeanoNat.lean` into `Peano/Prelim.lean`.
**Status**: ✅ Complete (2026-04-08)
**Dependencies**: Phase 13 complete

### Content to extract

| Definition | Type |
|-----------|------|
| `ExistsUnique` | Prop |
| `∃¹` syntax macros (4 variants) | notation |
| `choose` | noncomputable def |
| `choose_spec` | theorem |
| `ExistsUnique.exists` | def |
| `choose_unique` | noncomputable def |
| `choose_spec_unique` | theorem |
| `choose_uniq` | theorem |

### Steps

1. Create `Peano/Prelim.lean` with extracted content + export block
2. Update `PeanoNat.lean`: replace inline defs with `import Peano.Prelim`
3. Update `Peano.lean`: add `import Peano.Prelim`
4. `lake clean && lake build`
5. Commit

---

## Phase 15: Create Isomorph.lean (Nat↔ℕ₀ reexport)

**Objective**: Create `Peano/PeanoNat/Isomorph.lean` that re-exports all 26 bridge theorems.
**Status**: ✅ Complete (2026-04-08)
**Dependencies**: Phase 14 complete

Isomorphism theorems remain in their original modules but are re-exported from a single file.
Downstream code can `import Peano.PeanoNat.Isomorph` to get all Nat↔ℕ₀ bridges at once.

---

## Phase 16: Factor Decidable Module

**Objective**: Extract `blt`/`bgt`/`ble`/`bge` and decidability instances into `PeanoNat/Decidable.lean`.
**Status**: ✅ Complete (2026-04-08)
**Dependencies**: Phase 15 complete

Separates computational (boolean) decision procedures from pure mathematical theory.

---

## Phase 17: Factor Combinatorics Subdirectory

**Objective**: Group `Pow`, `Factorial`, `Binom`, `NewtonBinom` under `PeanoNat/Combinatorics/`.
**Status**: ✅ Complete (2026-04-08)
**Dependencies**: Phase 16 complete

Structure:

```
PeanoNat/Combinatorics/
├── Pow.lean
├── Factorial.lean
├── Binom.lean
└── NewtonBinom.lean
```

---

## Phase 18: Lattice.lean Mathlib-style Extensions

**Objective**: Add 18 Mathlib-style theorems to Lattice.lean.
**Status**: ✅ Complete (2026-04-09)

Added: `max_min_self`, `min_max_self`, `min_le_max`, `max_eq_left_iff`, `max_eq_right_iff`,
`min_eq_left_iff`, `min_eq_right_iff`, `max_le_iff`, `le_min_iff`, `max_le_max`,
`min_le_min`, `max_left_comm`, `min_left_comm`, `max_right_comm`, `min_right_comm`,
`max_succ_succ`, `min_succ_succ`. Build: 28 jobs, 0 warnings, 0 sorry.

---

## Phase 19: GCD/LCM/Coprime Mathlib-style Extensions

**Objective**: Add 25 Mathlib-style GCD/LCM/Coprime theorems to Arith.lean.
**Status**: ✅ Complete (2026-04-09)

Added: `gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`, `gcd_zero_right`, `gcd_zero_left`,
`gcd_one_right`, `gcd_one_left`, `gcd_self`, `gcd_eq_zero_iff`, `gcd_ne_zero_left`,
`gcd_ne_zero_right`, `dvd_gcd_iff`, `gcd_assoc`, `IsGCD_gcd`, `div_mul_cancel`,
`gcd_mul_lcm`, `lcm_comm`, `lcm_zero_left`, `lcm_zero_right`, `dvd_lcm_left`,
`dvd_lcm_right`, `lcm_self`, `coprime_comm`, `coprime_one_right`, `coprime_one_left`.
Build: 28 jobs, 0 warnings, 0 sorry.

---

## Phase 20: Log.lean + Sqrt.lean

**Objective**: Floor logarithm and floor square root with remainder.
**Status**: ✅ Complete (2026-04-10)

**Log.lean** (`Peano.Log`): `logMod b n = (k, r)` con $n = b^k + r$ y $n < b^{k+1}$.
11 símbolos: `logMod`, `log`, `logRem`, `log_zero`, `logRem_zero`, `log_of_lt`,
`logRem_of_lt`, `log_one`, `logRem_one`, `logMod_spec`, `log_upper_bound`.

**Sqrt.lean** (`Peano.Sqrt`): `sqrtMod n = (k, r)` con $n = k^2 + r$ y $r < 2k+1$.
10 símbolos: `sqrtMod`, `sqrt`, `sqrtRem`, `sqrt_zero`, `sqrtRem_zero`, `sqrt_one`,
`sqrtRem_one`, `sqrtMod_spec`, `sqrtRem_lt`, `sqrt_upper_bound`.

Build: 30 jobs, 0 warnings, 0 sorry.

---

## Phase 20.5: Isomorfismos Nat↔ℕ₀ completos

**Objective**: Bridge theorems for all remaining operations (mul, div, mod, pow, gcd, lcm).
**Status**: ✅ Complete (2026-04-09)

14 nuevos teoremas de isomorfismo en 4 módulos:

- **Mul.lean**: `isomorph_Ψ_mul`, `isomorph_Λ_mul`
- **Div.lean**: `isomorph_Ψ_div`, `isomorph_Ψ_mod` (req. `m ≠ 𝟘`), `isomorph_Λ_div`, `isomorph_Λ_mod` (req. `m ≠ 0`)
- **Pow.lean**: `isomorph_Ψ_pow`, `isomorph_Λ_pow`
- **Arith.lean**: `isomorph_Ψ_gcd`, `isomorph_Λ_gcd`, `isomorph_Ψ_lcm`, `isomorph_Λ_lcm`

**Isomorph.lean** actualizado con imports de Mul, Div, Pow, Arith + 6 bloques export.
**Peano.lean** exports actualizados.
Build: 30 jobs, 0 warnings, 0 sorry.

---

## Phase 21: Naturals Completion (ℕ₀)

**Objective**: Complete remaining natural number modules before extending to ℤ/ℚ.
**Status**: ✅ Complete (2026-06)

### 21.1. Digits.lean — Representación en base b

**Módulo**: `Peano/PeanoNat/Digits.lean` — `namespace Peano.Digits`
**Dependencias**: `Div`, `Log`, `Pow`

Definiciones:

- `digits (b n : ℕ₀) : List ℕ₀` — dígitos de `n` en base `b` (lista, dígito menos significativo primero)
- `ofDigits (b : ℕ₀) (ds : List ℕ₀) : ℕ₀` — reconstrucción desde dígitos
- `numDigits (b n : ℕ₀) : ℕ₀` — número de dígitos = `σ (log b n)` para `n ≠ 𝟘`, `b > 1`

Teoremas:

- `ofDigits_digits`: round-trip `ofDigits b (digits b n) = n`
- `digits_lt`: cada dígito `d ∈ digits b n → Lt d b`
- `numDigits_eq_succ_log`: enlace con `log`
- `digits_zero`, `digits_one`

**Complejidad**: Media (la recursión usa `div`/`mod`, ya probado en Log.lean)

### 21.2. Pairing.lean — Función de emparejamiento de Cantor

**Módulo**: `Peano/PeanoNat/Pairing.lean` — `namespace Peano.Pairing`
**Dependencias**: `Add`, `Mul`, `Div`, `Sqrt`

Definiciones:

- `cantorPair (a b : ℕ₀) : ℕ₀ := add (div (mul (add a b) (σ (add a b))) 𝟚) a`
  Es decir, $\pi(a,b) = \frac{(a+b)(a+b+1)}{2} + a$
- `cantorUnpair (n : ℕ₀) : ℕ₀ × ℕ₀` — inversa (usa `sqrt` del número triangular)

Teoremas:

- `cantorUnpair_cantorPair`: `cantorUnpair (cantorPair a b) = (a, b)`
- `cantorPair_cantorUnpair`: `cantorPair (cantorUnpair n).1 (cantorUnpair n).2 = n`
- `cantorPair_injective`: inyectividad

**Complejidad**: Media-Alta (la inversa requiere `sqrt` + aritmética cuidadosa)

### 21.3. ModEq.lean — Congruencias modulares

**Módulo**: `Peano/PeanoNat/NumberTheory/ModEq.lean` — `namespace Peano.ModEq`
**Dependencias**: `Div`, `Arith`

Definiciones:

- `ModEq (n a b : ℕ₀) : Prop := mod a n = mod b n`
- Notación: `a ≡ b [MOD n]`

Teoremas:

- `modEq_refl`, `modEq_symm`, `modEq_trans` (relación de equivalencia)
- `modEq_add`, `modEq_mul`, `modEq_pow` (compatibilidad con operaciones)
- `modEq_zero_iff_dvd`: `a ≡ 0 [MOD n] ↔ Divides n a`

**Complejidad**: Media

### 21.4. Totient.lean — Función de Euler φ

**Módulo**: `Peano/PeanoNat/NumberTheory/Totient.lean` — `namespace Peano.Totient`
**Dependencias**: `Arith` (gcd, Coprime), `NumberSets` (o `FSet`)

Definiciones:

- `totient (n : ℕ₀) : ℕ₀` — cuenta los `k` con `1 ≤ k ≤ n` y `gcd(k, n) = 1`

Teoremas:

- `totient_one`: `φ(1) = 1`
- `totient_prime`: `Prime p → φ(p) = p − 1`
- `totient_mul_coprime`: `Coprime m n → φ(m·n) = φ(m)·φ(n)` (multiplicatividad)

**Complejidad**: Alta (requiere contar sobre rangos filtrados)

### 21.5. ChineseRemainder.lean — CRT

**Módulo**: `Peano/PeanoNat/NumberTheory/ChineseRemainder.lean` — `namespace Peano.CRT`
**Dependencias**: `ModEq`, `Arith` (Coprime, bezout_natform)

Teorema principal:

- `chinese_remainder`: `Coprime m n → ∀ a b, ∃ x, ModEq m x a ∧ ModEq n x b`

**Complejidad**: Alta (usa identidad de Bézout)

### 21.6. Fermat.lean — Pequeño teorema de Fermat

**Módulo**: `Peano/PeanoNat/NumberTheory/Fermat.lean` — `namespace Peano.Fermat`
**Dependencias**: `ModEq`, `Totient`, `Pow`, `Primes`

Teoremas:

- `euler_theorem`: `Coprime a n → ModEq n (pow a (totient n)) 𝟙`
- `fermat_little`: `Prime p → ¬Divides p a → ModEq p (pow a (sub p 𝟙)) 𝟙`

**Complejidad**: Muy Alta

### 21.7a. Instancias Init — operaciones y literales

**En módulos existentes (Add, Sub, Mul, Div, Pow) + PeanoNat.lean:**

Instancias de typeclasses que existen en Lean 4 Init (sin Mathlib):

- `instance : Mul ℕ₀` (envolviendo `mul`) — en Mul.lean
- `instance : Sub ℕ₀` (envolviendo `sub`) — en Sub.lean
- `instance : Div ℕ₀` (envolviendo `div`) — en Div.lean
- `instance : Mod ℕ₀` (envolviendo `mod`) — en Div.lean
- `instance : Pow ℕ₀ ℕ₀` (envolviendo `pow`) — en Pow.lean
- `instance : Zero ℕ₀` — en PeanoNat.lean
- `instance : One ℕ₀` — en PeanoNat.lean
- `instance : OfNat ℕ₀ n` — en PeanoNat.lean (permite `(0 : ℕ₀)`, `(1 : ℕ₀)`, `(2 : ℕ₀)`)
- `instance : Ord ℕ₀` (con `compare`) — en Decidable.lean

**Complejidad**: Baja (mecánico, 1-3 líneas cada una)

### 21.7b. Orden avanzado — WellFounded, strong induction, tricotomía

**Status: ✅ Complete (2026-04-09)**

**En Order.lean, WellFounded.lean, Decidable.lean:**

Instancias implementadas:

- ✅ `instance : WellFoundedRelation ℕ₀` (vía `well_founded_lt`) — en WellFounded.lean
- ✅ `instance : DecidableRel (@LT.lt ℕ₀ _)` — en Decidable.lean
- ✅ `instance : DecidableRel (@LE.le ℕ₀ _)` — en Decidable.lean

Teoremas implementados:

- ✅ `lt_or_ge (a b : ℕ₀) : Lt a b ∨ Le b a` — en Order.lean
- ✅ `le_or_lt (a b : ℕ₀) : Le a b ∨ Lt b a` — en Order.lean
- ✅ `strongRecOn {C : ℕ₀ → Sort _} (n : ℕ₀) (h) : C n` — en WellFounded.lean (noncomputable)
- ✅ `strongInductionOn {P : ℕ₀ → Prop} (n : ℕ₀) (h) : P n` — en WellFounded.lean
- `sup_eq_max` / `inf_eq_min` — pospuestos (Sup/Inf son Mathlib-only)

**Complejidad**: Baja-Media

### 21.8. IsEven/IsOdd

**En Arith.lean o módulo dedicado:**

- `def IsEven (n : ℕ₀) : Prop := mod n 𝟚 = 𝟘`
- `def IsOdd (n : ℕ₀) : Prop := mod n 𝟚 = 𝟙`
- `instance : Decidable (IsEven n)` (vía `DecidableEq`)
- Teoremas: `even_or_odd`, `not_even_iff_odd`, `even_add`, `odd_succ_even`, etc.

**Complejidad**: Baja

### Orden de ejecución dentro de Phase 21

```
21.7a Instancias Init (Mul, Sub, Div, Mod, Pow, Zero, One, OfNat, Ord) ✅
21.7b Orden avanzado (WellFoundedRelation, lt_or_ge, le_or_lt, strongRecOn, strongInductionOn, DecidableRel) ✅
21.8 IsEven/IsOdd ✅
21.9 Decidable Prime ✅
21.1 Digits.lean ✅
21.2 Pairing.lean ✅
21.3 ModEq.lean ✅
21.4 Totient.lean ✅
21.5 ChineseRemainder.lean ✅
21.6 Fermat.lean ✅
```

---

## Phase 22: Integer Extension (ℤ)

**Objective**: Construct the integers from ℕ₀, with full arithmetic and order.
**Status**: ❌ Pending
**Dependencies**: Phase 21 (al menos 21.7 instancias + 21.8 IsEven/IsOdd)

### 22.0. Filosofía de diseño

- ℤ se define como tipo inductivo con representación canónica (sin quotients).
- Todas las operaciones se definen por pattern matching directo sobre los constructores.
- No se usa `Quotient` ni `Setoid`, aunque se deja la relación de equivalencia
  sobre pares `ℕ₀ × ℕ₀` como herramienta conceptual y puente de demostración.
- La canonización es inherente al tipo: cada entero tiene exactamente una representación.
- El `gcd` para ℚ se calcula exclusivamente con naturales (`abs` + `gcd` de ℕ₀).

### 22.1. Basic.lean — Definición de ℤ y operaciones fundamentales

**Módulo**: `Peano/Integer/Basic.lean` — `namespace Peano.Int`
**Dependencias**: `PeanoNat`, `Axioms`, `StrictOrder`, `Order`, `Add`, `Sub`, `Mul`

#### Tipo inductivo

```lean
inductive ℤ where
  | pos : ℕ₀ → ℤ      -- 0, 1, 2, ...  (pos 𝟘 = 0)
  | neg : ℕ₁ → ℤ      -- -1, -2, -3, ... (neg ⟨n, h⟩ = -(n))
```

- `pos 𝟘` = 0, `pos (σ n)` = n+1
- `neg ⟨σ n, _⟩` = -(n+1)
- Representación canónica por construcción: no hay `pos n` = `neg m` posible.

#### Funciones fundamentales

| Función | Signatura | Descripción |
|---------|-----------|-------------|
| `abs` | `ℤ → ℕ₀` | `abs (pos n) = n`, `abs (neg n) = n.val` |
| `sign` | `ℤ → ℤ` | `sign (pos 𝟘) = pos 𝟘`, `sign (pos (σ _)) = pos 𝟙`, `sign (neg _) = neg ⟨𝟙, ..⟩` |
| `negZ` | `ℤ → ℤ` | Negación: `negZ (pos 𝟘) = pos 𝟘`, `negZ (pos (σ n)) = neg ⟨σ n, ..⟩`, `negZ (neg n) = pos n.val` |
| `ofNat` | `ℕ₀ → ℤ` | Inyección: `ofNat n = pos n` |

#### Puente con pares (conceptual, no canónico)

```lean
def intEquiv : ℕ₀ × ℕ₀ → ℤ
  | (a, b) => if Le b a then pos (sub a b) else neg ⟨sub b a, ...⟩

def intRepr : ℤ → ℕ₀ × ℕ₀
  | pos n => (n, 𝟘)
  | neg n => (𝟘, n.val)
```

Teoremas puente:

- `intEquiv_intRepr`: `intEquiv (intRepr z) = z`
- `intRepr_equiv`: `intEquiv (a, b) = intEquiv (add a k, add b k)`

#### Instancias a registrar

- `DecidableEq ℤ` (derivable)
- `Repr ℤ`, `BEq ℤ`, `ToString ℤ`

**Complejidad**: Media

### 22.2. Order.lean — Orden sobre ℤ

**Módulo**: `Peano/Integer/Order.lean` — `namespace Peano.Int`
**Dependencias**: `Integer/Basic.lean`, `StrictOrder`, `Order`

#### Definición del orden

```lean
def ltZ : ℤ → ℤ → Prop
  | neg a, neg b => Lt b.val a.val    -- -3 < -2 porque 2 < 3
  | neg _, pos _ => True               -- todo negativo < todo positivo/cero
  | pos _, neg _ => False
  | pos a, pos b => Lt a b
```

#### Teoremas

- `ltZ_irrefl`, `ltZ_trans`, `ltZ_trichotomy`
- `leZ` definido como `ltZ a b ∨ a = b`
- `leZ_antisymm`, `leZ_total`
- `Decidable (ltZ a b)`, `Decidable (leZ a b)`

**Complejidad**: Media (6 cases por teorema, mecánico pero verboso)

### 22.3. Arithmetic.lean — Suma, resta, multiplicación

**Módulo**: `Peano/Integer/Arithmetic.lean` — `namespace Peano.Int`
**Dependencias**: `Integer/Basic.lean`, `Integer/Order.lean`, `Add`, `Sub`, `Mul`

#### Suma por pattern matching

```lean
def addZ : ℤ → ℤ → ℤ
  | pos a, pos b => pos (add a b)
  | neg a, neg b => neg ⟨add a.val b.val, ...⟩
  | pos a, neg b => if Le b.val a then pos (sub a b.val) else neg ⟨sub b.val a, ...⟩
  | neg a, pos b => if Le a.val b then pos (sub b a.val) else neg ⟨sub a.val b, ...⟩
```

#### Resta

```lean
def subZ (a b : ℤ) : ℤ := addZ a (negZ b)
```

#### Multiplicación por pattern matching

```lean
def mulZ : ℤ → ℤ → ℤ
  | pos a, pos b => pos (mul a b)
  | neg a, neg b => pos (mul a.val b.val)
  | pos 𝟘, neg _ => pos 𝟘            -- 0 * (-n) = 0
  | pos (σ a), neg b => neg ⟨mul (σ a) b.val, ...⟩
  | neg _, pos 𝟘 => pos 𝟘
  | neg a, pos (σ b) => neg ⟨mul a.val (σ b), ...⟩
```

#### Teoremas

- `addZ_comm`, `addZ_assoc`, `addZ_zero`, `zero_addZ`
- `addZ_negZ`: `addZ z (negZ z) = pos 𝟘` (inverso aditivo)
- `mulZ_comm`, `mulZ_assoc`, `mulZ_one`, `one_mulZ`
- `mulZ_zero`, `zero_mulZ`
- `mulZ_addZ_distrib`: distributividad `a * (b + c) = a*b + a*c`
- `negZ_negZ`: `negZ (negZ z) = z`
- `mulZ_neg_one`: `mulZ (neg ⟨𝟙, ..⟩) z = negZ z`
- `abs_mulZ`: `abs (mulZ a b) = mul (abs a) (abs b)`

#### Instancias

- `instance : Add ℤ` (envolviendo `addZ`)
- `instance : Sub ℤ` (envolviendo `subZ`)
- `instance : Mul ℤ` (envolviendo `mulZ`)
- `instance : Neg ℤ` (envolviendo `negZ`)

**Complejidad**: Alta (muchos cases, pruebas de propiedades algebraicas)

### 22.4. DivMod.lean — División entera y módulo sobre ℤ

**Módulo**: `Peano/Integer/DivMod.lean` — `namespace Peano.Int`
**Dependencias**: `Integer/Arithmetic.lean`, `Div`

#### Definición (truncada hacia cero, como en la mayoría de lenguajes)

```lean
def divZ (a b : ℤ) : ℤ :=
  match a, b with
  | _, pos 𝟘 => pos 𝟘                  -- div by zero = 0
  | pos a, pos b => pos (div a b)
  | neg a, neg b => pos (div a.val b.val)
  | pos a, neg b => negZ (pos (div a b.val))
  | neg a, pos b => negZ (pos (div a.val b))

def modZ (a b : ℤ) : ℤ := subZ a (mulZ (divZ a b) b)
```

Teorema: `a = addZ (mulZ (divZ a b) b) (modZ a b)` (euclid para ℤ)

**Complejidad**: Media

### 22.5. IsEvenZ/IsOddZ + propiedades

- `IsEven (z : ℤ) : Prop := ∃ k : ℤ, z = mulZ (pos 𝟚) k`
- `IsOdd (z : ℤ) : Prop := ∃ k : ℤ, z = addZ (mulZ (pos 𝟚) k) (pos 𝟙)`
- Enlace: `IsEven (pos n) ↔ IsEven_nat n`

**Complejidad**: Baja

### Orden de ejecución dentro de Phase 22

```
22.1 Basic.lean (tipo, abs, sign, negZ, ofNat, puentes)
22.2 Order.lean (ltZ, leZ, tricotomía, decidabilidad)
22.3 Arithmetic.lean (addZ, subZ, mulZ, propiedades algebraicas)
22.4 DivMod.lean (divZ, modZ, especificación euclidiana)
22.5 IsEvenZ/IsOddZ
```

**Estructura de directorio**:

```
Peano/Integer/
├── Basic.lean
├── Order.lean
├── Arithmetic.lean
└── DivMod.lean
```

---

## Phase 23: Rational Extension (ℚ)

**Objective**: Construct the rationals from ℤ and ℕ₁, with full arithmetic and order.
**Status**: ❌ Pending
**Dependencies**: Phase 22 completa

### 23.0. Filosofía de diseño

- ℚ se define como structure con invariante de coprimalidad built-in.
- **No se usa `Quotient`**: la forma canónica es forzada por el tipo.
- Todas las operaciones se reducen a **operaciones sobre ℕ₀ + manipulación de signos**.
- El `gcd` se calcula exclusivamente con naturales: dado `z/n`, se computa
  `g = gcd(abs(z), n.val)` y se reduce a `sign(z) * (abs(z)/g) / (n/g)`.
- La comparación `z₁/n₁ vs z₂/n₂` se reduce a comparar signos + comparar
  `abs(z₁) * n₂` vs `abs(z₂) * n₁` (todo natural).
- La suma `z₁/n₁ + z₂/n₂` se reduce a manipulación de signos + operaciones
  naturales sobre `abs(z₁)*n₂ ± abs(z₂)*n₁` y `n₁*n₂`, seguido de canonización.

### 23.1. Basic.lean — Definición de ℚ y canonización

**Módulo**: `Peano/Rational/Basic.lean` — `namespace Peano.Rat`
**Dependencias**: `Integer/Basic.lean`, `Arith` (gcd, Coprime), `Div`

#### Tipo

```lean
structure ℚ where
  num : ℤ              -- numerador
  den : ℕ₁             -- denominador (> 0)
  coprime : gcd (abs num) den.val = 𝟙   -- fracción irreducible
```

#### Funciones de construcción

```lean
/-- Construye ℚ desde ℤ × ℕ₁, canonizando. -/
def mkRat (z : ℤ) (n : ℕ₁) : ℚ :=
  let g := gcd (abs z) n.val
  -- Aquí g ≠ 0 porque n.val ≠ 0
  -- sign(z) * (abs(z) / g) es el numerador canonizado
  -- n.val / g es el denominador canonizado
  { num := mulZ (sign z) (pos (div (abs z) g))
    den := ⟨div n.val g, ...⟩
    coprime := ... }
```

**Funciones auxiliares**:

- `ofInt (z : ℤ) : ℚ := mkRat z ⟨𝟙, succ_neq_zero 𝟘⟩`
- `ofNatQ (n : ℕ₀) : ℚ := ofInt (pos n)`

**Complejidad**: Alta (probar que `gcd(a/g, b/g) = 1` tras dividir por `g`)

### 23.2. Order.lean — Orden sobre ℚ

**Módulo**: `Peano/Rational/Order.lean` — `namespace Peano.Rat`
**Dependencias**: `Rational/Basic.lean`, `Integer/Order.lean`

#### Estrategia: reducir a comparación de signos + naturales

```lean
def ltQ (p q : ℚ) : Prop :=
  ltZ (mulZ p.num (pos q.den.val)) (mulZ q.num (pos p.den.val))
```

Dado que `den > 0`, multiplicar por denominadores preserva el orden.
Internamente, se separan los signos y se comparan naturales.

#### Teoremas

- `ltQ_irrefl`, `ltQ_trans`, `ltQ_trichotomy`
- `leQ`, `leQ_antisymm`, `leQ_total`
- `Decidable (ltQ p q)`, `Decidable (leQ p q)`

**Complejidad**: Media

### 23.3. Arithmetic.lean — Suma, resta, multiplicación, división

**Módulo**: `Peano/Rational/Arithmetic.lean` — `namespace Peano.Rat`
**Dependencias**: `Rational/Basic.lean`, `Rational/Order.lean`, `Integer/Arithmetic.lean`

#### Suma

```lean
def addQ (p q : ℚ) : ℚ :=
  -- p.num/p.den + q.num/q.den = (p.num*q.den + q.num*p.den) / (p.den*q.den)
  mkRat (addZ (mulZ p.num (pos q.den.val)) (mulZ q.num (pos p.den.val)))
        ⟨mul p.den.val q.den.val, ...⟩
```

`mkRat` canoniza automáticamente (divide por gcd).

#### Resta

```lean
def subQ (p q : ℚ) : ℚ := addQ p (negQ q)
def negQ (p : ℚ) : ℚ := { num := negZ p.num, den := p.den, coprime := ... }
```

#### Multiplicación

```lean
def mulQ (p q : ℚ) : ℚ :=
  mkRat (mulZ p.num q.num) ⟨mul p.den.val q.den.val, ...⟩
```

#### División (inversa)

```lean
def invQ (p : ℚ) : ℚ :=
  match p.num with
  | pos 𝟘 => p                   -- inv(0) = 0 (convención)
  | pos (σ n) => mkRat (pos p.den.val) ⟨σ n, succ_neq_zero n⟩
  | neg n => mkRat (negZ (pos p.den.val)) ⟨n.val, n.property⟩

def divQ (p q : ℚ) : ℚ := mulQ p (invQ q)
```

#### Teoremas

- `addQ_comm`, `addQ_assoc`, `addQ_zero`, `addQ_negQ` (inverso)
- `mulQ_comm`, `mulQ_assoc`, `mulQ_one`, `mulQ_invQ` (inverso, para p ≠ 0)
- `mulQ_addQ_distrib`
- `mulQ_zero`, `zero_mulQ`
- Campo: `p ≠ 0 → mulQ p (invQ p) = 1`

#### Instancias

- `instance : Add ℚ`, `instance : Sub ℚ`, `instance : Mul ℚ`
- `instance : Neg ℚ`, `instance : Div ℚ`, `instance : Inv ℚ`

**Complejidad**: Muy Alta (muchas pruebas de canonicidad tras cada operación)

### 23.4. Embedding.lean — Inyecciones ℕ₀ ↪ ℤ ↪ ℚ

**Módulo**: `Peano/Rational/Embedding.lean` — `namespace Peano.Rat`
**Dependencias**: `Rational/Arithmetic.lean`, `Integer/Arithmetic.lean`

Teoremas:

- `ofInt_addZ`: `ofInt (addZ a b) = addQ (ofInt a) (ofInt b)`
- `ofInt_mulZ`: `ofInt (mulZ a b) = mulQ (ofInt a) (ofInt b)`
- `ofNatQ_add`: `ofNatQ (add a b) = addQ (ofNatQ a) (ofNatQ b)`
- `ofNatQ_mul`: `ofNatQ (mul a b) = mulQ (ofNatQ a) (ofNatQ b)`
- `ofInt_injective`, `ofNatQ_injective`
- `ofInt_ltZ_iff`: `ltZ a b ↔ ltQ (ofInt a) (ofInt b)`

**Complejidad**: Media

### Orden de ejecución dentro de Phase 23

```
23.1 Basic.lean (tipo ℚ, mkRat, canonización)
23.2 Order.lean (ltQ, leQ, tricotomía)
23.3 Arithmetic.lean (addQ, subQ, mulQ, divQ, invQ, propiedades de campo)
23.4 Embedding.lean (ℕ₀ ↪ ℤ ↪ ℚ, preservación de operaciones)
```

**Estructura de directorio**:

```
Peano/Integer/
├── Basic.lean
├── Order.lean
├── Arithmetic.lean
└── DivMod.lean

Peano/Rational/
├── Basic.lean
├── Order.lean
├── Arithmetic.lean
└── Embedding.lean
```

---

## Cadena de dependencias global

```
                        ┌─── Digits.lean
                        ├─── Pairing.lean
Phase 21 (ℕ₀) ─────────┤
                        ├─── NumberTheory/ModEq.lean
                        │         ↓
                        ├─── NumberTheory/Totient.lean
                        │         ↓
                        ├─── NumberTheory/ChineseRemainder.lean
                        │         ↓
                        └─── NumberTheory/Fermat.lean

Phase 22 (ℤ) ──────────┬─── Integer/Basic.lean
                        ├─── Integer/Order.lean
                        ├─── Integer/Arithmetic.lean
                        └─── Integer/DivMod.lean

Phase 23 (ℚ) ──────────┬─── Rational/Basic.lean
                        ├─── Rational/Order.lean
                        ├─── Rational/Arithmetic.lean
                        └─── Rational/Embedding.lean
```

---

## Build Issues (2026-06-17)

**Toolchain**: leanprover/lean4:v4.29.0
**Build command**: `lake build`
**Result**: 51/51 modules OK, 0 errors, 14 sorry warnings

### sorry warnings (non-blocking)

| File | Lines | Count | Description |
|------|-------|-------|-------------|
| `Combinatorics/Perm.lean` | 39 | 1 | Perm sorry |
| `Combinatorics/Group.lean` | 98 | 1 | Group sorry |
| `Combinatorics/GroupTheory/Action.lean` | 62, 73, 87, 104 | 4 | Action sorry |
| `Combinatorics/GroupTheory/Sylow/Cosets.lean` | 42, 48, 68, 74, 86 | 5 | Coset sorry |
| `Combinatorics/GroupTheory/Sylow/Sylow.lean` | 71, 93, 113 | 3 | Sylow sorry |

Todos los sorry están en módulos de teoría de grupos avanzada (Phase 25).
La aritmética básica, teoría de números y FSetFunction están completamente demostrados.

---

## Phase 24: FSet Generalization & FSetFunction

**Objective**: Infrastructure for finite sets, finite functions, and the Pigeonhole principle.
**Status**: ✅ Complete (2026-06)

Desarrollo completo:

- **ListsAndSets/List.lean**: Listas de ℕ₀, operaciones, sorted, nodup
- **ListsAndSets/ListList.lean**: Listas de listas
- **ListsAndSets/FSet.lean**: Conjuntos finitos con UniqueKeys + SortedByKey
- **ListsAndSets/FSetFSet.lean**: Conjuntos de conjuntos finitos
- **ListsAndSets/FSetFunction.lean** (~90 declaraciones exportadas):
  - § 1: `MapOn` (funciones totales A → B), `id`, `comp`, `comp_assoc`
  - § 2: `Im` (imagen), `rightInverse`, `leftInverse`, `inverse`, involution
  - § 3: Pigeonhole, desigualdades de cardinalidad, iff characterizations
  - § 3d: `PreIm`, fibras, restricción
  - § 3e: Endomorfismos (`EndoOn`)
  - § 3f: Permutaciones (`Perm` structure)
  - § 4–8: `BinOpOn`, `CoeFun`, `FunTable`, `FunPerm`, Export

---

## Phase 25: Finite Group Theory

**Objective**: Permutation groups, group actions, orbits, and Sylow theorems.
**Status**: 🔶 In progress

### 25.1. Modules completados (sin sorry)

- **Combinatorics/Counting.lean**: Conteo combinatorio
- **Combinatorics/Sign.lean**: Signo de permutaciones (paridad de transposiciones)
- **Combinatorics/Orbit.lean**: Órbitas de elementos bajo permutaciones

### 25.2. Modules con sorry pendientes

- **Combinatorics/Perm.lean**: Permutaciones (1 sorry)
- **Combinatorics/Group.lean**: Grupo simétrico Sym(A) (1 sorry)
- **Combinatorics/GroupTheory/Action.lean**: Acciones de grupo (4 sorry)
- **Combinatorics/GroupTheory/Sylow/Cosets.lean**: Coclases (5 sorry)
- **Combinatorics/GroupTheory/Sylow/Sylow.lean**: Teoremas de Sylow (3 sorry)

### Orden de ejecución

```
25.1 Counting.lean ✅
25.2 Perm.lean ⚠ (1 sorry)
25.3 Sign.lean ✅
25.4 Orbit.lean ✅
25.5 Group.lean ⚠ (1 sorry)
25.6 Action.lean ⚠ (4 sorry)
25.7 Sylow/Cosets.lean ⚠ (1 sorry — lagrange)
25.8 Sylow/Sylow.lean ⚠ (3 sorry)
```

---

## Estado actual de sorry (actualizado 2026-04-16)

Tras la sesión de limpieza de sorry de Phase 25, el proyecto pasó de **14 sorry** a **7 sorry**.

| # | Archivo | Línea | Teorema | Dificultad |
|---|---------|-------|---------|------------|
| 1 | `Perm.lean` | 39 | `FunPerm.comp is_perm` | Media |
| 2 | `Action.lean` | 116 | `orbit_stabilizer` | Alta |
| 3 | `Action.lean` | 132 | `orbits_partition` (rama left) | Media |
| 4 | `Cosets.lean` | 126 | `lagrange` | Alta |
| 5 | `Sylow.lean` | 71 | `sylow_first` | Muy alta |
| 6 | `Sylow.lean` | 88 | `sylow_second` | Muy alta |
| 7 | `Sylow.lean` | 105 | `sylow_third` | Muy alta |

### Sorry ya eliminados en esta sesión (7 de 14)

- `Group.lean`: Sym/Perm duplicado → eliminada definición con sorry (−1)
- `Cosets.lean`: `mem_leftCoset_iff` → demostrado con `List.mem_filter` + `List.any_eq_true` (−1)
- `Cosets.lean`: `cosetRel_symm` → demostrado con `inv_op_eq` + `inv_inv_eq` + `H.inv_closed` (−1)
- `Cosets.lean`: `cosetRel_trans` → demostrado con asociatividad + `H.op_closed` (−1)
- `Cosets.lean`: `coset_card_eq_subgroup_card` → demostrado con biyección `h ↦ g·h` (MapOn.Bijective.card_eq) (−1)
- `Action.lean`: `mem_orb_iff` → demostrado con `List.mem_filter` + `List.any_eq_true` (−1)
- `Action.lean`: `GroupAction.stab` → construido como Subgroup vía `ℕ₀FSet.filter` (−1)

---

## Plan detallado de demostración de los 7 sorry restantes

### Dependencias entre los sorry

```
FunPerm.comp ─────────────────────── (independiente)

orbits_partition ──┐
                   ├──► orbit_stabilizer ──► lagrange
                   │
                   ├──► sylow_first ──┐
                   │                  ├──► sylow_second ──► sylow_third
                   ├──► (center Z(G)) │
                   └──► (Cauchy)  ────┘
```

### Orden recomendado de ejecución

```
Paso 1: FunPerm.comp (Perm.lean)          — independiente
Paso 2: orbits_partition (Action.lean)     — necesita FSet.ext
Paso 3: lagrange (Cosets.lean)             — necesita conteo por fibras
Paso 4: orbit_stabilizer (Action.lean)     — necesita lagrange
Paso 5: Infraestructura Sylow             — Z(G), normal, cocientes, Cauchy
Paso 6: sylow_first (Sylow.lean)           — necesita toda la infraestructura
Paso 7: sylow_second (Sylow.lean)          — necesita sylow_first + conjugación
Paso 8: sylow_third (Sylow.lean)           — necesita sylow_second + conteo mod p
```

---

### Paso 1: `FunPerm.comp is_perm` (Perm.lean:39)

**Enunciado**: Si `f, g : FunPerm A`, entonces la tabla de `g ∘ f` es
`List.Perm` de `A.elems`.

**Cómo**: La tabla de `comp g f dflt` es `f.table.map (fun a => g.applyElem a dflt)`.

**Estrategia en 3 sub-lemas**:

1. **`applyElem_injective_on_elems`** (nuevo, en FSetFunction.lean):

   ```
   Si g : FunPerm A y a₁ a₂ ∈ A.elems, entonces
     g.applyElem a₁ dflt = g.applyElem a₂ dflt → a₁ = a₂
   ```

   *Prueba*: `applyElem a = getDₚ dflt g.table (indexOfₚ a A.elems)`.
   Si `g.is_perm : g.table ~ A.elems`, entonces `g.table` tiene los mismos
   elementos que `A.elems` sin repeticiones (sorted ⟹ nodup).
   Necesita: `getDₚ_indexOfₚ`, `indexOfₚ_injective` (de Sorted ⟹ Nodup ⟹
   distintos índices para distintos elementos), y que `getDₚ` es inyectiva
   sobre un rango válido en una lista sin duplicados.

   *Sub-lema auxiliar*: `sorted_lt_nodup : Sorted (· < ·) l → l.Nodup`.
   Prueba: `Pairwise (· < ·) l → Pairwise (· ≠ ·) l` por transitividad
   de `<` e irreflexividad, luego `Nodup = Pairwise (· ≠ ·)`.

2. **`applyElem_mem_of_perm`** (ya existe como `applyElem_mem`):
   `g.applyElem a dflt ∈ A.elems` si `a ∈ A.elems`.

3. **Prueba final**: `f.table.map (g.applyElem · dflt) ~ A.elems` porque:
   - `f.is_perm : f.table ~ A.elems`
   - `List.Perm.map (g.applyElem · dflt)` da `f.table.map (...) ~ A.elems.map (...)`
   - `A.elems.map (g.applyElem · dflt) ~ A.elems` porque la función es
     inyectiva sobre una lista nodup de mismo tamaño que A.elems, y cada
     imagen está en A.elems.
   - Usar `List.perm_iff_count` (stdlib): basta mostrar que para todo
     `a ∈ A.elems`, `count a (A.elems.map f) = count a A.elems`, lo que
     se sigue de inyectividad + pertenencia + nodup.

**Infraestructura nueva requerida**:

- `sorted_lt_nodup` (~10 líneas, en List.lean o FSet.lean)
- `applyElem_injective_on_elems` (~15 líneas, en FSetFunction.lean)
- `perm_map_of_injective_on_nodup` (~20 líneas, podría ir en List.lean)

**Dificultad**: Media. ~50 líneas de lemas auxiliares.

---

### Paso 2: `orbits_partition` rama left (Action.lean:132)

**Enunciado** (rama pendiente): Si `z ∈ orb(x) ∩ orb(y)`, entonces
`orb(x).elems = orb(y).elems`.

**Estado actual**: La rama `right` (disjuntas) ya está demostrada.
Faltan ~8 líneas en la rama `left`.

**Estrategia**:

1. De `z ∈ orb(x)` obtenemos `g₁` con `α(g₁, x) = z`.
   De `z ∈ orb(y)` obtenemos `g₂` con `α(g₂, y) = z`.

2. **Inclusión orb(x) ⊆ orb(y)**: Si `w ∈ orb(x)`, existe `h` con
   `α(h, x) = w`. Entonces `x = α(g₁⁻¹, z) = α(g₁⁻¹, α(g₂, y)) = α(g₁⁻¹·g₂, y)`.
   Luego `w = α(h, x) = α(h, α(g₁⁻¹·g₂, y)) = α(h·g₁⁻¹·g₂, y) ∈ orb(y)`.

3. **Inclusión orb(y) ⊆ orb(x)**: Simétrica.

4. **Igualdad de listas**: Ambas listas son sublistas sorted de `X.elems`
   (construidas por `FSet.filter`). Dos sublistas sorted con los mismos
   elementos son iguales.
   Usar `List.Perm.eq_of_sorted` de stdlib (renombrado a `eq_of_pairwise`):

   ```
   antireflexive_of_lt + pairwise_sorted₁ + pairwise_sorted₂ + perm → eq
   ```

   Necesita construir `List.Perm` entre `orb(x).elems` y `orb(y).elems`.

**Infraestructura nueva requerida**:

- `FSet.ext : s₁.elems = s₂.elems → s₁ = s₂` (~3 líneas, en FSet.lean —
  basta `cases s₁; cases s₂; simp` o similar con proof irrelevance)
- Aplicar `List.Perm.eq_of_pairwise` con `(· < ·)` y la antisimetría
  `a < b → b < a → False` (ya disponible como `IrreflLT`).

**Dificultad**: Media. ~30 líneas incluyendo el lema `FSet.ext`.

---

### Paso 3: `lagrange` (Cosets.lean:126)

**Enunciado**: `∃ k, mul H.carrier.card k = G.carrier.card`.

**Ingredientes ya disponibles**:

- `cosetRel` es relación de equivalencia (refl, symm, trans demostrados)
- `coset_card_eq_subgroup_card`: cada coseto tiene cardinalidad `|H|`
- `mem_leftCoset_iff`: caracterización de pertenencia a cosetos

**Estrategia de la prueba**:

1. **Construir el conjunto de cosetos**: `cosets G H : List ℕ₀FSet` =
   lista de cosetos distintos `gH` para `g ∈ G.carrier.elems`, eliminando
   duplicados. Definir como:

   ```lean
   def cosetList (G : FinGroup) (H : Subgroup G) : List ℕ₀FSet :=
     (G.carrier.elems.map (leftCoset G H)).dedup
   ```

2. **Los cosetos particionan G**:
   - Todo `g ∈ G` pertenece a algún coseto (está en `gH` porque `G.id ∈ H`
     ⟹ `g·id = g ∈ gH`).
   - Cosetos distintos son disjuntos (de `cosetRel` equivalencia:
     `gH ∩ g'H ≠ ∅ → gH = g'H`).

3. **Conteo por fibras**: `|G| = |H| · (número de cosetos)`.
   Necesita un lema general de conteo:

   ```lean
   theorem card_partition (G : ℕ₀FSet) (parts : List ℕ₀FSet)
     (h_cover : ∀ x ∈ G.elems, ∃ P ∈ parts, x ∈ P.elems)
     (h_disjoint : ∀ P Q ∈ parts, P ≠ Q → ∀ x, x ∉ P.elems ∨ x ∉ Q.elems)
     (h_sub : ∀ P ∈ parts, ∀ x ∈ P.elems, x ∈ G.elems)
     (h_size : ∀ P ∈ parts, P.card = k) :
     G.card = mul k (lengthₚ parts)
   ```

**Infraestructura nueva requerida** (significativa):

- `cosetList` o equivalente para enumerar cosetos
- `card_partition`: conteo por fibras equi-cardinales (~40 líneas)
- Lema de disjunción de cosetos vía `cosetRel` (~20 líneas)
- Lema de cobertura: todo `g ∈ G` pertenece a `gH` (~5 líneas)

**Dificultad**: Alta. ~80-100 líneas de infraestructura nueva.

---

### Paso 4: `orbit_stabilizer` (Action.lean:116)

**Enunciado**: `mul (α.orb x).card (α.stab x hx).carrier.card = G.carrier.card`

**Estrategia**: Aplicar `lagrange` al subgrupo `Stab(x)`, más una biyección
`Orb(x) ≅ G/Stab(x)`:

1. Por `lagrange G (α.stab x hx)` obtenemos `k` con `|Stab(x)| · k = |G|`.

2. Construir biyección `φ : G/Stab(x) → Orb(x)` definida por
   `φ(gStab(x)) = α(g, x)`. Mostrar:
   - Bien definida: si `g₁ ~ g₂` (mod Stab), entonces `α(g₁,x) = α(g₂,x)`.
   - Inyectiva: si `α(g₁,x) = α(g₂,x)`, entonces `g₁⁻¹g₂ ∈ Stab(x)`.
   - Sobreyectiva: todo `y ∈ Orb(x)` tiene preimagen por definición de órbita.

3. De la biyección: `k = |Orb(x)|`, luego `|Stab(x)| · |Orb(x)| = |G|`.

**Dependencias**: `lagrange` (Paso 3), biyección explícita como MapOn.

**Dificultad**: Alta. ~50 líneas, pero depende de Lagrange.

---

### Paso 5: Infraestructura para Sylow

Los tres teoremas de Sylow requieren infraestructura que **no existe aún**
en el proyecto. Se necesita construir:

#### 5a. Centro del grupo `Z(G)`

```lean
def center (G : FinGroup) : Subgroup G where
  carrier := ℕ₀FSet.filter (fun g =>
    G.carrier.elems.all (fun h => decide (G.op g h = G.op h g))) G.carrier
  ...
```

Demostrar que es subgrupo (~20 líneas) y que es normal (~10 líneas).

#### 5b. Subgrupo normal

```lean
def Subgroup.IsNormal (G : FinGroup) (N : Subgroup G) : Prop :=
  ∀ g n, g ∈ G.carrier.elems → n ∈ N.carrier.elems →
    G.op (G.op g n) (G.inv g) ∈ N.carrier.elems
```

~5 líneas para la definición, ~15 líneas para lemas básicos.

#### 5c. Grupo cociente `G/N`

```lean
def quotientGroup (G : FinGroup) (N : Subgroup G)
    (hN : N.IsNormal) : FinGroup
```

Construir el grupo cuyo carrier es el conjunto de cosetos, con la operación
`(gN)·(hN) = (gh)N`. Requiere buena definición + verificación de bien-definido.
~60-80 líneas.

#### 5d. Teorema de Cauchy

```lean
theorem cauchy (G : FinGroup) (p : ℕ₀)
    (hp : Prime p) (hdvd : dvd_card p G.carrier) :
    ∃ g, g ∈ G.carrier.elems ∧ order G g = p
```

Donde `order G g` es el menor `n > 0` tal que `G.op^n g = G.id`.
Requiere:

- Definición de `order` (~15 líneas)
- Lema: `order` divide `|G|` (~20 líneas, usa Lagrange sobre `⟨g⟩`)
- Prueba de Cauchy por inducción sobre `|G|` (~40 líneas)

#### 5e. Ecuación de clases

```lean
theorem class_equation (G : FinGroup) :
    G.carrier.card = (center G).carrier.card +
      sum_over_nontrivial_orbits (...)
```

Usa `orbits_partition` + conteo. ~40 líneas.

**Total infraestructura Paso 5**: ~200-250 líneas de código nuevo.

---

### Paso 6: `sylow_first` (Sylow.lean:71)

**Enunciado**: Si `p` primo y `p^n | |G|`, existe `H ≤ G` con `|H| = p^n`.

**Estrategia** (prueba clásica por inducción fuerte sobre `|G|`):

1. **Caso base**: `|G| = 1` ⟹ `n = 0`, `H = {e}`.

2. **Paso inductivo**: Considerar la ecuación de clases:
   `|G| = |Z(G)| + Σᵢ [G : C_G(xᵢ)]`

   - **Caso A**: `p | |Z(G)|`. Entonces por Cauchy en `Z(G)` (abeliano),
     existe `g ∈ Z(G)` de orden `p`. El subgrupo `⟨g⟩` es normal en `G`
     (porque `g ∈ Z(G)`). Aplicar hipótesis de inducción al cociente
     `G/⟨g⟩` de orden `|G|/p`.

   - **Caso B**: `p ∤ |Z(G)|`. Entonces algún sumando `[G : C_G(xᵢ)]`
     no es divisible por `p`, lo que implica `p^n | |C_G(xᵢ)|` con
     `|C_G(xᵢ)| < |G|`. Aplicar hipótesis de inducción a `C_G(xᵢ)`.

**Dependencias**: center, normal, quotient group, Cauchy, class equation,
orbit_stabilizer, lagrange.

**Dificultad**: Muy alta. ~80-100 líneas (asumiendo toda la infraestructura).

---

### Paso 7: `sylow_second` (Sylow.lean:88)

**Enunciado**: Todos los p-subgrupos de Sylow son conjugados.

**Estrategia**:

1. Sea `H` un p-subgrupo de Sylow. Hacer actuar `H` sobre `G/K`
   (cosetos de otro p-subgrupo de Sylow `K`) por multiplicación izquierda:
   `h · (gK) = (hg)K`.

2. `|G/K| = |G|/p^n`, y como `p^n | |H|` con `|H| = p^n`, el número de
   órbitas cumple: `|G/K| = Σ |orb|` donde cada `|orb|` divide `|H| = p^n`,
   así que cada `|orb|` es una potencia de `p`.

3. `|G/K|` no es divisible por `p` (porque `p^n ‖ |G|`). Entonces existe
   al menos una órbita de tamaño 1, es decir un `gK` fijo por `H`:
   `hgK = gK` para todo `h ∈ H`.

4. Esto implica `g⁻¹hg ∈ K` para todo `h ∈ H`, es decir `g⁻¹Hg ⊆ K`.
   Como `|g⁻¹Hg| = |H| = |K|`, tenemos `g⁻¹Hg = K`.

**Dependencias**: sylow_first (para la existencia), orbit_stabilizer,
lagrange, acción sobre cosetos.

**Dificultad**: Muy alta. ~60-80 líneas.

---

### Paso 8: `sylow_third` (Sylow.lean:105)

**Enunciado**: `n_p ≡ 1 (mod p)` y `n_p | [G:H]`.

**Estrategia**:

1. **`n_p | [G:H]`**: Por Sylow II, G actúa transitivamente sobre los
   p-subgrupos de Sylow por conjugación. Luego `n_p = |G|/|N_G(H)| = [G:N_G(H)]`.
   Como `H ≤ N_G(H)` y `[G:H] = [G:N_G(H)] · [N_G(H):H]`, tenemos
   `n_p | [G:H]`.

2. **`n_p ≡ 1 (mod p)`**: Hacer actuar `H` sobre el conjunto de p-subgrupos
   de Sylow por conjugación. Los puntos fijos son exactamente los `K` tales
   que `hKh⁻¹ = K` para todo `h ∈ H`, es decir `K ≤ N_G(H)`.
   Si `K` es punto fijo, entonces `HK` es subgrupo y `|HK| = |H|·|K|/|H∩K|`.
   Como `|HK|` divide `|G|` y `|H| = |K| = p^n`, se deduce `H = K`.
   Luego `H` es el único punto fijo. Por conteo mod p: `n_p ≡ 1 (mod p)`.

**Dependencias**: sylow_second, normalizador `N_G(H)`, lagrange, ModEq.

**Infraestructura adicional**:

- Normalizador `N_G(H)` (~20 líneas)
- `|HK| = |H|·|K|/|H∩K|` (~30 líneas)
- Conteo de puntos fijos mod p (~20 líneas)

**Dificultad**: Muy alta. ~70-90 líneas.

---

### Resumen del esfuerzo total

| Paso | Sorry | Líneas estimadas | Infraestructura nueva |
|------|-------|------------------|-----------------------|
| 1 | `FunPerm.comp` | ~50 | sorted_lt_nodup, applyElem_injective |
| 2 | `orbits_partition` | ~30 | FSet.ext |
| 3 | `lagrange` | ~100 | card_partition, cosetList |
| 4 | `orbit_stabilizer` | ~50 | biyección G/Stab ≅ Orb |
| 5 | (infraestructura) | ~250 | Z(G), Normal, G/N, Cauchy, class eq |
| 6 | `sylow_first` | ~100 | inducción + ecuación de clases |
| 7 | `sylow_second` | ~80 | acción sobre cosetos |
| 8 | `sylow_third` | ~90 | normalizador, conteo mod p |
| **Total** | **7 sorry** | **~750 líneas** | |

---

## Prioridad inmediata

1. **Paso 1**: `FunPerm.comp` (Perm.lean) — independiente, dificultad media
2. **Paso 2**: `orbits_partition` (Action.lean) — casi terminado, falta FSet.ext
3. **Paso 3**: `lagrange` (Cosets.lean) — abre la puerta a Pasos 4-8
4. **Paso 4**: `orbit_stabilizer` (Action.lean) — usa lagrange
5. **Pasos 5-8**: Sylow completo — requiere toda la cadena
6. **Phase 22 (ℤ)**: Extensión a enteros
7. **Phase 23 (ℚ)**: Extensión a racionales
