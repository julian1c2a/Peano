# Next Steps — Peano

**Last updated:** 2026-04-09
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
**Status**: 🔶 In progress

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
21.1 Digits.lean
21.2 Pairing.lean
21.3 ModEq.lean ✅
21.4 Totient.lean ✅
21.5 ChineseRemainder.lean ✅
21.6 Fermat.lean
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

## Prioridad inmediata

1. **Phase 21.7**: Instancias algebraicas (`HSub`, `HDiv`, `HMod`, `HPow`, `DecidableRel`)
2. **Phase 21.8**: `IsEven`/`IsOdd`
3. **Phase 21.1**: `Digits.lean`
4. **Phase 21.2**: `Pairing.lean`
5. **Phase 21.3**: `ModEq.lean`
6. Continuar con 21.4–21.6 o saltar a Phase 22 (ℤ) según preferencia
