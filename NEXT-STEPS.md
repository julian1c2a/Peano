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

## Build Issues (2026-04-17)

**Toolchain**: leanprover/lean4:v4.29.0
**Build command**: `lake build`
**Result**: 51/51 modules OK, 0 errors, 8 sorry warnings

### sorry warnings (non-blocking)

| File | Lines | Count | Description |
|------|-------|-------|-------------|
| `Combinatorics/Group.lean` | 311, 344 | 2 | `cyclicSubgroup` op·inv⁻¹, `cyclicSubgroup'` inv_closed (bloqueados en B2.3 `order`) |
| `Combinatorics/GroupTheory/Action.lean` | 116, 132 | 2 | `orbit_stabilizer`, `orbits_partition` (rama left) |
| `Combinatorics/GroupTheory/Sylow/Cosets.lean` | 126 | 1 | `lagrange` |
| `Combinatorics/GroupTheory/Sylow/Sylow.lean` | 71, 88, 105 | 3 | `sylow_first`, `sylow_second`, `sylow_third` |

### Sorry eliminados en sesión 2026-04-17

- `Perm.lean:39` `FunPerm.comp is_perm` ✅ — probado vía `perm_map_of_injective_on_nodup`
  (nuevo lema añadido a `FSetFunction.lean` tras `perm_of_nodup_subset_same_length`)

Todos los sorry restantes están en módulos de teoría de grupos (Phase 25 + B3 cíclico).
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
- **ListsAndSets/FSetFunction.lean** (~92 declaraciones exportadas):
  - § 1: `MapOn` (funciones totales A → B), `id`, `comp`, `comp_assoc`
  - § 2: `Im` (imagen), `rightInverse`, `leftInverse`, `inverse`, involution
  - § 3: Pigeonhole, desigualdades de cardinalidad, iff characterizations
  - § 3b: `card_le_of_injective`, `card_le_of_surjective`,
    **`not_injective_of_card_lt`** ✅ (2026-04-16),
    **`collision_of_card_lt`** ✅ (2026-04-16) — clave para B2.3 `order`
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

Tras la sesión de limpieza de sorry de Phase 25 + añadido B3 cíclico, el proyecto tiene **9 sorry** (7 Phase-25 preexistentes − 5 resueltos + 2 nuevos B3.2 + 2 nuevos orphan → neto 9).

Desglose actual:

| # | Archivo | Línea | Teorema | Dificultad |
|---|---------|-------|---------|------------|
| 1 | `Perm.lean` | 39 | `FunPerm.comp is_perm` | Media |
| 2 | `Group.lean` | 311 | `cyclicSubgroup` op·inv⁻¹ closed | Media (bloqueado en B2.3) |
| 3 | `Group.lean` | 344 | `cyclicSubgroup'` inv_closed | Media (bloqueado en B2.3) |
| 4 | `Action.lean` | 116 | `orbit_stabilizer` | Alta |
| 5 | `Action.lean` | 132 | `orbits_partition` (rama left) | Media |
| 6 | `Cosets.lean` | 126 | `lagrange` | Alta |
| 7 | `Sylow.lean` | 71 | `sylow_first` | Muy alta |
| 8 | `Sylow.lean` | 88 | `sylow_second` | Muy alta |
| 9 | `Sylow.lean` | 105 | `sylow_third` | Muy alta |
| 10 | `Sylow.lean` | 105 | `sylow_third` | Muy alta |

### Sorry ya eliminados en esta sesión (7 de 14)

- `Group.lean`: Sym/Perm duplicado → eliminada definición con sorry (−1)
- `Cosets.lean`: `mem_leftCoset_iff` → demostrado con `List.mem_filter` + `List.any_eq_true` (−1)
- `Cosets.lean`: `cosetRel_symm` → demostrado con `inv_op_eq` + `inv_inv_eq` + `H.inv_closed` (−1)
- `Cosets.lean`: `cosetRel_trans` → demostrado con asociatividad + `H.op_closed` (−1)
- `Cosets.lean`: `coset_card_eq_subgroup_card` → demostrado con biyección `h ↦ g·h` (MapOn.Bijective.card_eq) (−1)
- `Action.lean`: `mem_orb_iff` → demostrado con `List.mem_filter` + `List.any_eq_true` (−1)
- `Action.lean`: `GroupAction.stab` → construido como Subgroup vía `ℕ₀FSet.filter` (−1)

---

## Plan completo de teoría de grupos finitos

### A. Dependencias globales

```
                  ┌─── FunPerm.comp (Perm.lean) ──── independiente
                  │
                  │    FSet.ext (FSet.lean) ──── infraestructura base
                  │         │
 § 4b lemas  ────┤    orbits_partition (Action.lean)
 § 4c order  ────┤         │
 § 5  subgr  ────┤    ┌────┴──────────────┐
 § 5b tipos  ────┤    │                   │
                  │    lagrange            │
                  │    (Cosets.lean)       │
 § 6  hom    ────┤         │              │
 § 6b Im/ker ────┤    orbit_stabilizer    │
                  │    (Action.lean)       │
 § 5c normal ────┤         │              │
 § 5d gen⟨S⟩ ────┤    ┌────┴───────┐      │
                  │    │            │      │
 § 7  Sym(n) ────┤    center Z(G)  │      │
                  │    │            │      │
                  │    Cauchy       class_equation
                  │    │                   │
                  │    quotientGroup        │
                  │         │              │
                  │    sylow_first ────────┘
                  │         │
                  │    sylow_second
                  │         │
                  └──── sylow_third
```

### B. Orden de ejecución por bloques

| Bloque | Contenido | Dependencias |
|--------|-----------|-------------|
| B1 | Infraestructura de listas/conjuntos | Ninguna |
| B2 | Orden de elemento, potencia iterada | § 4b |
| B3 | Tipos de subgrupos (cíclico, normal, inter, producto, join) | § 5 + B2 |
| B4 | Homomorfismos (Im, ker, comp, mono⟺ker) | § 6 + B3 |
| B5 | Subgrupo generado ⟨S⟩, grupos simples | B3 (B3.8 join requiere B5.1) |
| B6 | Sorry 1-2: FunPerm.comp, orbits_partition | B1 |
| B7 | Sorry 3-4: lagrange, orbit_stabilizer | B6 + B4 |
| B8 | Grupo simétrico Sym(Fin₀Set n) | B6 |
| B9 | Infraestructura Sylow (center, Cauchy, class eq, cocientes) | B2-B7 |
| B10 | Sorry 5-7: sylow_first/second/third | B9 |

---

### B1. Infraestructura de listas y conjuntos

**Archivo**: `List.lean`, `FSet.lean`, `FSetFunction.lean`

#### B1.1 `sorted_lt_nodup` (List.lean, ~10 lín.)

```
theorem sorted_lt_nodup {l : List ℕ₀} (h : Sorted (· < ·) l) : l.Nodup
```

*Sub-lemas*:

- `pairwise_lt_imp_pairwise_ne`: `Pairwise (· < ·) l → Pairwise (· ≠ ·) l`
  (de irreflexividad de `<`)
- `nodup_of_pairwise_ne`: `Pairwise (· ≠ ·) l → l.Nodup`
  (equivalencia standard, puede estar en stdlib)

#### B1.2 `FSet.ext` (FSet.lean, ~5 lín.)

```
theorem FSet.ext {s₁ s₂ : FSet α} (h : s₁.elems = s₂.elems) : s₁ = s₂
```

*Prueba*: `cases s₁; cases s₂; subst h; congr` (proof irrelevance en `sorted`).

#### B1.3 `applyElem_injective_on_elems` (FSetFunction.lean, ~20 lín.)

```
theorem FunPerm.applyElem_injective {A : ℕ₀FSet} (g : FunPerm A)
    (dflt : ℕ₀) {a₁ a₂ : ℕ₀}
    (h₁ : a₁ ∈ A.elems) (h₂ : a₂ ∈ A.elems)
    (heq : g.applyElem a₁ dflt = g.applyElem a₂ dflt) : a₁ = a₂
```

*Sub-lemas*:

- `indexOfₚ_injective`: `a ∈ l → b ∈ l → l.Nodup → indexOfₚ a l = indexOfₚ b l → a = b`
  (~8 lín., usa `getDₚ_indexOfₚ`)
- `getDₚ_injective_of_nodup`: `l.Nodup → i < len → j < len → getDₚ d l i = getDₚ d l j → i = j`
  (~10 lín., inducción sobre `l`)

#### B1.4 `perm_map_of_injective_on_nodup` (List.lean, ~15 lín.)

```
theorem perm_map_of_injective_on_nodup {f : α → α} {l : List α}
    (h_nodup : l.Nodup)
    (h_mem : ∀ a ∈ l, f a ∈ l)
    (h_inj : ∀ a b, a ∈ l → b ∈ l → f a = f b → a = b) :
    List.Perm (l.map f) l
```

*Sub-lemas*:

- `map_nodup_of_injective`: `l.Nodup → injective_on f l → (l.map f).Nodup` (~8 lín.)
- `perm_of_nodup_nodup_same_length_subset`: dos listas nodup de igual longitud
  donde una es sublista de la otra son permutación (~10 lín., vía
  `List.perm_iff_count` o `List.Nodup.perm_of_subset`)

---

### B2. Orden de un elemento y potencia iterada

**Archivo**: `Group.lean` § 4c (nuevo)

#### B2.1 `gpow` — potencia iterada (Group.lean, ~8 lín.)

```
def gpow (G : FinGroup) (g : ℕ₀) : ℕ₀ → ℕ₀
  | .zero   => G.id
  | .succ n => G.op (gpow G g n) g
```

#### B2.2 Lemas de `gpow` (~25 lín.)

- `gpow_zero`: `gpow G g 𝟘 = G.id`
- `gpow_one`: `gpow G g 𝟙 = g`
- `gpow_succ`: `gpow G g (σ n) = G.op (gpow G g n) g`
- `gpow_mem`: `g ∈ G.carrier.elems → gpow G g n ∈ G.carrier.elems`
  (inducción: base `id_in`, paso `op_mem`)
- `gpow_add`: `gpow G g (add m n) = G.op (gpow G g m) (gpow G g n)`
  (inducción sobre `n`, usa `op_assoc`)
- `gpow_inv`: `gpow G (G.inv g) n = G.inv (gpow G g n)`
  (inducción sobre `n`, usa `inv_op_eq`)

#### B2.3 `order` — orden del elemento (Group.lean, ~30 lín.)

**Dependencia resuelta**: `collision_of_card_lt` ya está en `FSetFunction.lean` (§ 3b, ✅).

**Estrategia para `orderExists`** (existencia del orden):

1. Definir `f := MapOn (Fin₀Set (σ |G|)) G.carrier` con `f.toFun i := gpow G g i`.
   El dominio tiene cardinal `σ |G| = |G| + 1`, el codominio tiene cardinal `|G|`.
2. Aplicar `collision_of_card_lt f (lt_self_σ_self G.carrier.card)`:
   obtiene `∃ i j, i ∈ Fin₀Set(σ|G|) ∧ j ∈ Fin₀Set(σ|G|) ∧ i ≠ j ∧ gpow G g i = gpow G g j`.
3. WLOG `i > j` (usando `trichotomy`): entonces `gpow G g (sub i j) = G.id`
   con `sub i j > 0` (pues `i ≠ j` y `i > j`).
   *Sub-lema*: `gpow_sub_eq_id` (~8 lín.): si `gpow G g i = gpow G g j` e `i > j`,
   entonces `gpow G g (sub i j) = G.id`.
   Proof: `G.id = op (gpow G g i) (gpow G g i)⁻¹ = op (gpow G g j) (gpow G g (sub i j)) · (gpow G g j)⁻¹ = gpow G g (sub i j)` por cancelación.

4. `orderExists` : `∃ n, lt₀ 𝟘 n ∧ gpow G g n = G.id`.

**Definición formal** (~10 lín.):

```
noncomputable def order (G : FinGroup) (g : ℕ₀)
    (hg : g ∈ G.carrier.elems) : ℕ₀ :=
  -- el menor n > 0 tal que gpow G g n = G.id,
  -- cuya existencia la da collision_of_card_lt via gpow_sub_eq_id
  Peano.choose (well_ordering_principle
    (fun n => lt₀ 𝟘 n ∧ gpow G g n = G.id) orderExists)
  |>.val
```

(En la práctica: usar `well_ordering_principle` de `WellFounded.lean` sobre el predicado
`P n := lt₀ 𝟘 n ∧ gpow G g n = G.id`; la existencia es `orderExists`.)

#### B2.4 Lemas de `order` (~40 lín.)

- `order_pos`: `lt₀ 𝟘 (order G g hg)`
- `gpow_order_eq_id`: `gpow G g (order G g hg) = G.id`
- `gpow_sub_eq_id` *(sub-lema auxiliar, ~8 lín.)*:
  `gpow G g i = gpow G g j → lt₀ j i → gpow G g (sub i j) = G.id`
  (cancelación: `g^i = g^j → g^(i-j) = id`)
- `gpow_mod_order` *(~10 lín.)*: `gpow G g n = gpow G g (mod n (order G g hg))`
  (inducción: si `n ≥ order`, reducir a `n - order` usando `gpow_order_eq_id`)
- `gpow_eq_id_iff_order_dvd`: `gpow G g n = G.id ↔ Divides (order G g hg) n`
  (usa `gpow_mod_order`)
- `order_dvd_card`: `Divides (order G g hg) G.carrier.card`
  (usa Lagrange sobre el subgrupo cíclico `⟨g⟩`, ver B3.2)
- `order_id_eq_one`: `order G G.id G.id_in = 𝟙`
- `order_inv`: `order G (G.inv g) (inv_mem G hg) = order G g hg`

---

### B3. Tipos de subgrupos

**Archivo**: `Group.lean` § 5b (nuevo)

#### B3.1 Subgrupo trivial y subgrupo impropio (~10 lín.)

```
def trivialSubgroup (G : FinGroup) : Subgroup G where
  carrier := ℕ₀FSet.singleton G.id
  ...

def improperSubgroup (G : FinGroup) : Subgroup G where
  carrier := G.carrier
  ...

def Subgroup.IsTrivial (H : Subgroup G) : Prop := H.carrier.card = 𝟙
def Subgroup.IsProper (H : Subgroup G) : Prop := H.carrier.card ≠ G.carrier.card
```

#### B3.2 Subgrupo cíclico generado por un elemento (~20 lín.)

**Estado actual**: implementado en Group.lean con **2 sorry** (líneas 311 y 344).
**Ambos sorry se desbloquean cuando B2.3 (`order`) esté disponible.**

```
def cyclicSubgroup' (G : FinGroup) (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
    Subgroup G where
  carrier := cyclicCarrier G g   -- { gpow G g i | i < σ|G| }
  ...
```

*Sub-lemas bloqueados por B2.3*:

- **Sorry 1** — `op_closed` en `cyclicSubgroup`: el testigo `add m n` puede superar
  `σ |G|`. Solución: reducir `mod (add m n) (order G g hg)` como testigo, usando
  `gpow_mod_order` (que requiere `order`).
  
- **Sorry 2** — `inv_closed` en `cyclicSubgroup'`: `G.inv (gpow G g n) = gpow G (G.inv g) n`
  pero `(G.inv g)^n` no está en `cyclicCarrier` (que solo tiene potencias de `g`).
  Solución: con `order`, `G.inv (gpow G g n) = gpow G g (sub (order G g hg) n)`,
  que sí es un elemento de `cyclicCarrier`.

*Sub-lemas adicionales en B3.2 (post B2.3)*:

- `cyclicSubgroup_id_in`: `G.id ∈ (cyclicSubgroup' G g hg).carrier.elems`
  (testigo: `gpow G g 𝟘 = G.id`)
- `cyclicSubgroup_op_closed`: si `x = g^m` y `y = g^n`, entonces `x·y = g^(m+n mod ord)`
  (usa `gpow_add` + `gpow_mod_order`)
- `cyclicSubgroup_inv_closed`: si `x = g^n`, entonces `x⁻¹ = g^(ord - n)`
  (usa `order` + `gpow_order_eq_id`)
- `cyclicSubgroup_card_eq_order`: `(cyclicSubgroup' G g hg).carrier.card = order G g hg`

#### B3.3 Subgrupo normal (definición directa, no por cosetos) (~15 lín.)

```
def Subgroup.IsNormal (G : FinGroup) (N : Subgroup G) : Prop :=
  ∀ g n, g ∈ G.carrier.elems → n ∈ N.carrier.elems →
    G.op (G.op g n) (G.inv g) ∈ N.carrier.elems
```

*Lemas*:

- `trivialSubgroup_normal`: el subgrupo trivial es normal
- `improperSubgroup_normal`: `G` como subgrupo de sí mismo es normal
- `normal_iff_cosets_eq`: `N.IsNormal ↔ ∀ g, leftCoset G N g = rightCoset G N g`
  (equivalencia clásica, ~15 lín.)
- `normal_of_index_two`: `[G:N] = 𝟚 → N.IsNormal`
  (~10 lín., hay exactamente dos cosetos)

#### B3.4 Subgrupo transitivamente normal (~5 lín.)

```
def Subgroup.IsSubnormal (G : FinGroup) (H : Subgroup G) : Prop :=
  ∃ chain : List (Subgroup G),
    chain.head? = some H ∧ chain.getLast? = some (improperSubgroup G) ∧
    ∀ i, i + 1 < chain.length →
      (chain.get ⟨i, _⟩).IsNormal -- como subgrupo de chain.get ⟨i+1, _⟩
```

(Cadena subnormal finita de `H` a `G`.)

#### B3.5 Subgrupo característico (~5 lín.)

```
def Subgroup.IsCharacteristic (G : FinGroup) (H : Subgroup G) : Prop :=
  ∀ φ : GroupHom G G, ∀ h, h ∈ H.carrier.elems →
    φ.map h ∈ H.carrier.elems
```

*Lema*:

- `characteristic_is_normal`: `H.IsCharacteristic → H.IsNormal`
  (~10 lín., la conjugación `x ↦ gxg⁻¹` es un automorfismo)

---

#### B3.6 Intersección de subgrupos (~15 lín.)

```
def Subgroup.inter (G : FinGroup) (H₁ H₂ : Subgroup G) : Subgroup G where
  carrier := G.carrier.filter (fun x =>
    decide (x ∈ H₁.carrier.elems) && decide (x ∈ H₂.carrier.elems))
  ...
```

*Lemas*:

- `inter_id_in`: `G.id ∈ (Subgroup.inter G H₁ H₂).carrier.elems`
  (de `H₁.id_in` y `H₂.id_in`)
- `inter_op_closed`: si `a, b ∈ H₁ ∩ H₂`, entonces `a·b ∈ H₁ ∩ H₂`
  (de `H₁.op_closed` y `H₂.op_closed`)
- `inter_inv_closed`: si `a ∈ H₁ ∩ H₂`, entonces `a⁻¹ ∈ H₁ ∩ H₂`
  (de `H₁.inv_closed` y `H₂.inv_closed`)
- `inter_subset_left`: `Subgroup.inter G H₁ H₂ ⊆ H₁`
- `inter_subset_right`: `Subgroup.inter G H₁ H₂ ⊆ H₂`
- `inter_normal_of_normal`: si `N₁.IsNormal` y `N₂.IsNormal`, entonces
  `(Subgroup.inter G N₁ N₂).IsNormal`

#### B3.7 Producto de subgrupos H·K (~20 lín.)

```
def Subgroup.product (G : FinGroup) (H K : Subgroup G) : ℕ₀FSet :=
  G.carrier.filter (fun x =>
    H.carrier.elems.any (fun h =>
      K.carrier.elems.any (fun k => decide (G.op h k = x))))
```

*Nota*: `H·K` no es subgrupo en general; lo es sii `H·K = K·H`.

*Lemas*:

- `product_subset`: `∀ x ∈ (Subgroup.product G H K).elems, x ∈ G.carrier.elems`
- `product_mem`: `h ∈ H → k ∈ K → G.op h k ∈ Subgroup.product G H K`
- `product_comm_iff_subgroup`:
  `Subgroup.product G H K = Subgroup.product G K H ↔
    ∃ S : Subgroup G, S.carrier = Subgroup.product G H K`
  (~30 lín., dirección → usa que `HK = KH` implica `(HK)⁻¹ = K⁻¹H⁻¹ = KH = HK`)
- `product_of_normal_left`: si `N.IsNormal`, entonces
  `Subgroup.product G N K` es subgrupo de `G`
  (~15 lín., `N·K = K·N` cuando `N` es normal)
- `product_card`: `|H·K| · |H ∩ K| = |H| · |K|`
  (fórmula de Poincaré, requiere B3.6 intersección)

#### B3.8 Suma (join) de subgrupos: ⟨H₁ ∪ H₂⟩ (~10 lín.)

```
def Subgroup.join (G : FinGroup) (H₁ H₂ : Subgroup G) : Subgroup G :=
  generatedSubgroup G (H₁.carrier.union H₂.carrier)
    (fun a ha => ... H₁.subset ∨ H₂.subset ...)
```

*Nota*: `H₁ + H₂ := ⟨H₁ ∪ H₂⟩` es el menor subgrupo que contiene a ambos.

*Lemas*:

- `join_contains_left`: `∀ a ∈ H₁.carrier.elems, a ∈ (Subgroup.join G H₁ H₂).carrier.elems`
- `join_contains_right`: `∀ a ∈ H₂.carrier.elems, a ∈ (Subgroup.join G H₁ H₂).carrier.elems`
- `join_minimal`: si `S : Subgroup G` con `H₁ ⊆ S` y `H₂ ⊆ S`, entonces
  `Subgroup.join G H₁ H₂ ⊆ S`
- `join_eq_product_of_normal`: si `N.IsNormal`, entonces
  `Subgroup.join G N H = Subgroup.product G N H`
  (~15 lín., `N·H` ya es subgrupo y contiene a ambos)
- `join_comm`: `Subgroup.join G H₁ H₂ = Subgroup.join G H₂ H₁`
  (de la conmutatividad de la unión)

---

### B4. Homomorfismos: Im, ker, composición, mono⟺ker

**Archivo**: `Group.lean` § 6b (nuevo)

#### B4.1 Imagen de un homomorfismo (~20 lín.)

```
def GroupHom.Im (f : GroupHom G H) : Subgroup H where
  carrier := H.carrier.filter (fun y =>
    G.carrier.elems.any (fun x => decide (f.map x = y)))
  ...
```

*Sub-lemas* (cada uno ~3-5 lín.):

- `Im.id_in`: `H.id ∈ Im.carrier.elems` (testigo: `f.map G.id = H.id`)
- `Im.op_closed`: si `y₁ = f(x₁)` y `y₂ = f(x₂)`, entonces
  `H.op y₁ y₂ = f(G.op x₁ x₂)` por `map_op`
- `Im.inv_closed`: si `y = f(x)`, entonces `H.inv y = f(G.inv x)` por `map_inv`

#### B4.2 Núcleo de un homomorfismo (~20 lín.)

```
def GroupHom.ker (f : GroupHom G H) : Subgroup G where
  carrier := G.carrier.filter (fun x => decide (f.map x = H.id))
  ...
```

*Sub-lemas* (cada uno ~3-5 lín.):

- `ker.id_in`: `G.id ∈ ker.carrier.elems` (de `f.map_id`)
- `ker.op_closed`: si `f(a) = H.id` y `f(b) = H.id`, entonces
  `f(G.op a b) = H.op (f a) (f b) = H.op H.id H.id = H.id`
- `ker.inv_closed`: si `f(a) = H.id`, entonces
  `f(G.inv a) = H.inv (f a) = H.inv H.id = H.id` (usa `inv_id_eq`)

#### B4.3 Composición de homomorfismos (~10 lín.)

```
def GroupHom.comp (g : GroupHom H K) (f : GroupHom G H) : GroupHom G K where
  map := MapOn.comp g.map f.map
  map_op := ...   -- reescrito via f.map_op + g.map_op
  map_id := ...   -- f.map_id ▸ g.map_id
  map_inv := ...  -- f.map_inv ▸ g.map_inv
```

*Sub-lemas*:

- `comp_map_op`: `(g.comp f).map (G.op a b) = K.op ((g.comp f).map a) ((g.comp f).map b)`
  (directo de `f.map_op` + `g.map_op`)
- `comp_map_id`: `(g.comp f).map G.id = K.id`
  (directo de `f.map_id` + `g.map_id`)

#### B4.4 Ker es normal (~15 lín.)

```
theorem ker_isNormal (f : GroupHom G H) : f.ker.IsNormal G
```

*Prueba*: Sea `g ∈ G`, `n ∈ ker f`. Entonces `f(n) = H.id`.
`f(g·n·g⁻¹) = f(g)·f(n)·f(g⁻¹) = f(g)·H.id·H.inv(f(g)) = H.id`.
Luego `g·n·g⁻¹ ∈ ker f`.

*Sub-lemas*:

- `map_conjugate`: `f.map (G.op (G.op g n) (G.inv g)) = H.op (H.op (f.map g) (f.map n)) (H.inv (f.map g))`
  (~5 lín., dos aplicaciones de `map_op` + `map_inv`)

#### B4.5 Mono ⟺ ker trivial (~20 lín.)

```
theorem mono_iff_ker_trivial (f : GroupHom G H) :
    f.map.Injective ↔ f.ker.IsTrivial
```

*Sub-lemas*:

- `injective_imp_ker_trivial` (→): Si `f` inyectiva y `x ∈ ker`, entonces
  `f(x) = H.id = f(G.id)`, luego `x = G.id`. Así `ker = {G.id}`.
  (~8 lín.)
- `ker_trivial_imp_injective` (←): Si `ker = {G.id}` y `f(a) = f(b)`,
  entonces `f(a·b⁻¹) = f(a)·f(b)⁻¹ = H.id`, luego `a·b⁻¹ ∈ ker`,
  luego `a·b⁻¹ = G.id`, luego `a = b`.
  (~10 lín., usa `op_cancel_right`)

---

### B5. Subgrupo generado y grupos simples

**Archivo**: `Group.lean` § 5d-5e (nuevo)

#### B5.1 Subgrupo generado por un subconjunto (~25 lín.)

```
def generatedSubgroup (G : FinGroup) (S : ℕ₀FSet)
    (h_sub : ∀ a, a ∈ S.elems → a ∈ G.carrier.elems) : Subgroup G
```

*Definición*: la intersección de todos los subgrupos de `G` que contienen `S`.
En el caso finito, equivalente a: cerrar `S` bajo `op` e `inv` iteradamente.

*Estrategia constructiva* (mejor para finito):

```
def closure_step (G : FinGroup) (T : ℕ₀FSet) : ℕ₀FSet :=
  G.carrier.filter (fun x =>
    T.elems.any (fun a => decide (x = a)) ||     -- T ⊆ resultado
    T.elems.any (fun a => decide (x = G.inv a)) || -- inv
    T.elems.any (fun a =>
      T.elems.any (fun b => decide (x = G.op a b)))) -- op

def closure_iterate (G : FinGroup) (S : ℕ₀FSet) : ℕ₀ → ℕ₀FSet
  | .zero   => S ∪ {G.id}   -- asegurar id
  | .succ n => closure_step G (closure_iterate G S n)

def generatedSubgroup (G : FinGroup) (S : ℕ₀FSet) ... : Subgroup G :=
  -- closure_iterate converge en ≤ |G| pasos (monotone + bounded)
  subgroup_of_op_inv_closed G (closure_iterate G S G.carrier.card) ...
```

*Sub-lemas*:

- `S_subset_generated`: `∀ a ∈ S.elems, a ∈ (generatedSubgroup G S h_sub).carrier.elems`
- `generated_minimal`: si `H : Subgroup G` y `S ⊆ H.carrier`, entonces
  `generatedSubgroup G S ⊆ H` (intersección es mínima)
- `generated_of_singleton`: `generatedSubgroup G {g} = cyclicSubgroup G g hg`
  (cuando `S` es un solo elemento)

#### B5.2 Grupo simple (~5 lín.)

```
def FinGroup.IsSimple (G : FinGroup) : Prop :=
  G.carrier.card ≠ 𝟙 ∧
  ∀ N : Subgroup G, N.IsNormal G → N.IsTrivial ∨ ¬N.IsProper
```

*Lemas*:

- `prime_order_simple`: `Prime G.carrier.card → G.IsSimple`
  (~15 lín., por Lagrange: subgrupo propio tiene orden que divide `|G|`,
  pero `|G|` primo ⟹ solo 1 y `|G|`, luego subgrupo es trivial o impropio)

---

### B6. Sorry 1–2: FunPerm.comp y orbits_partition

#### B6.1 `FunPerm.comp is_perm` (Perm.lean:39)

**Enunciado**: `(FunTable.comp g f dflt).table ~ A.elems`

**Cadena de lemas** (ver B1.1–B1.4):

```
sorted_lt_nodup ──► applyElem_injective ──► perm_map_of_injective_on_nodup
         │                    │                          │
         └─── B1.1            └─── B1.3                  └─── B1.4
                                                            │
                                               FunPerm.comp is_perm
```

*Prueba final* (~5 lín.): aplicar `List.Perm.trans`:

1. `comp_table = f.table.map (g.applyElem · dflt)`
2. `f.table.map ... ~ A.elems.map ...` (de `f.is_perm` + `List.Perm.map`)
3. `A.elems.map (g.applyElem · dflt) ~ A.elems` (de B1.4 con
   h_nodup = `sorted_lt_nodup A.sorted`, h_inj = `applyElem_injective`,
   h_mem = `applyElem_mem`)

#### B6.2 `orbits_partition` rama left (Action.lean:132)

**Cadena de lemas**:

```
FSet.ext ────────────────────────────────── B1.2
    │
orb_subset (nuevo, ~15 lín.)
    │    Si z ∈ orb(x) ∩ orb(y), entonces orb(x) ⊆ orb(y)
    │    Sub-lemas:
    │    - orb_subset_aux: α(g₁,x)=z ∧ α(g₂,y)=z → x = α(g₁⁻¹·g₂, y)
    │      (usa act_compat + act_id + op_inv)
    │    - orb_mem_trans: w ∈ orb(x) ∧ x ∈ orb(y) → w ∈ orb(y)
    │      (w=α(h,x), x=α(k,y) ⟹ w=α(G.op h k, y))
    │
sorted_perm_eq (nuevo, ~8 lín.)
    │    Sorted (· < ·) l₁ → Sorted (· < ·) l₂ →
    │    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
    │    Sub-lemas:
    │    - mutual_subset_perm: inclusión mutua de sorted listas → Perm
    │    - List.Perm.eq_of_pairwise (stdlib): perm + anti-simétrica → eq
    │
orbits_partition (rama left)
```

---

### B7. Sorry 3–4: lagrange y orbit_stabilizer

#### B7.1 `lagrange` (Cosets.lean:126)

**Cadena de lemas**:

```
coset_disjoint_or_eq (nuevo, ~20 lín.)
    │    leftCoset G H g₁ = leftCoset G H g₂ ∨ disjoint
    │    Sub-lemas:
    │    - cosetRel_iff_coset_eq: cosetRel a b ↔ leftCoset a = leftCoset b
    │      (~10 lín., extensionalidad de filtros sorted)
    │    - coset_nonempty_inter_eq: si x ∈ gH ∩ g'H entonces gH = g'H
    │      (~8 lín., de cosetRel_trans + cosetRel_symm)
    │
coset_cover (nuevo, ~5 lín.)
    │    ∀ g ∈ G, g ∈ leftCoset G H g
    │    (testigo: G.id ∈ H, G.op g G.id = g)
    │
cosetList (nuevo, ~10 lín.)
    │    def cosetList G H : List ℕ₀FSet :=
    │      G.carrier.elems.foldl (deduplicated coset accumulation)
    │
card_of_uniform_partition (nuevo, ~30 lín.)
    │    Partición de S en partes de tamaño k ⟹ |S| = k · (nº partes)
    │    Sub-lemas:
    │    - card_disjoint_union: |A ∪ B| = |A| + |B| si disjuntos (~8 lín.)
    │    - card_partition_ind: inducción sobre nº de partes (~15 lín.)
    │
lagrange
```

#### B7.2 `orbit_stabilizer` (Action.lean:116)

**Cadena de lemas**:

```
coset_to_orbit_map (nuevo, ~15 lín.)
    │    Construir MapOn (cosetFSet G (stab x)) (orb x)
    │    definido por: representante g del coseto ↦ α(g, x)
    │    Sub-lemas:
    │    - coset_to_orbit_welldefined: g₁ ~ g₂ mod Stab → α(g₁,x) = α(g₂,x)
    │      (~5 lín., g₁⁻¹g₂ ∈ Stab ⟹ α(g₁⁻¹g₂, x) = x ⟹ α(g₂,x) = α(g₁,x))
    │    - coset_to_orbit_injective: α(g₁,x) = α(g₂,x) → g₁ ~ g₂ mod Stab
    │      (~5 lín., α(g₁⁻¹g₂, x) = x ⟹ g₁⁻¹g₂ ∈ Stab)
    │    - coset_to_orbit_surjective: ∀ y ∈ orb(x), ∃ g tal que α(g,x) = y
    │      (directa de la definición de órbita)
    │
orbit_stabilizer
    │    |orb(x)| = nº cosetos de Stab(x) = |G|/|Stab(x)|
    │    Luego |orb(x)| · |Stab(x)| = |G| (de lagrange + biyección)
```

---

### B8. Grupo simétrico Sym(Fin₀Set n)

**Archivos**: `Perm.lean` § 2, `Group.lean` § 7

#### B8.1 Lehmer code — codificación (Perm.lean, ~20 lín.)

```
def lehmerCode (n : ℕ₀) (σ : FunPerm (Fin₀Set n)) : List ℕ₀
-- lehmerCode[i] = #{j > i | σ(j) < σ(i)}
```

*Sub-lemas*:

- `lehmerCode_length`: `lengthₚ (lehmerCode n σ) = n`
- `lehmerCode_bound`: `∀ i < n, getDₚ 𝟘 (lehmerCode n σ) i < sub n i`

#### B8.2 Lehmer encode/decode (Perm.lean, ~25 lín.)

```
def lehmerEncode (n : ℕ₀) (σ : FunPerm (Fin₀Set n)) : ℕ₀
-- Σᵢ lehmerCode[i] · (n-1-i)!

def lehmerDecode (n : ℕ₀) (k : ℕ₀) : FunPerm (Fin₀Set n)
-- inversa: extraer dígitos factoráicos, reconstruir permutación
```

*Sub-lemas*:

- `lehmerEncode_lt`: `lehmerEncode n σ < factorial n`
- `lehmerDecode_encode`: `lehmerDecode n (lehmerEncode n σ) = σ`
- `lehmerEncode_decode`: `k < factorial n → lehmerEncode n (lehmerDecode n k) = k`

#### B8.3 `SymGroup n : FinGroup` (Group.lean § 7, ~30 lín.)

```
def SymGroup (n : ℕ₀) : FinGroup where
  carrier := Fin₀Set (factorial n)
  op a b  := lehmerEncode n
               (FunPerm.comp (lehmerDecode n a) (lehmerDecode n b) 𝟘)
  id      := lehmerEncode n (FunPerm.id (Fin₀Set n))
  inv a   := lehmerEncode n (... inversa de lehmerDecode n a ...)
```

*Axiomas*: se transfieren de `Perm.comp_assoc`, `Perm.comp_id_fn`,
`Perm.comp_inv_left`, etc., vía round-trip `encode ∘ decode = id`.

*Sub-lemas*:

- `SymGroup_carrier_card`: `(SymGroup n).carrier.card = factorial n`
  (directo de `Fin₀Set_card`)
- `SymGroup_op_assoc`: transferencia de `Perm.comp_assoc`
- `SymGroup_op_id`: transferencia de `Perm.comp_id_fn`
- `SymGroup_op_inv`: transferencia de `Perm.inv_left`/`inv_right`

---

### B9. Infraestructura Sylow

#### B9.1 Centro `Z(G)` (Group.lean § 5f, ~25 lín.)

```
def center (G : FinGroup) : Subgroup G where
  carrier := G.carrier.filter (fun g =>
    G.carrier.elems.all (fun h => decide (G.op g h = G.op h g)))
  ...
```

*Sub-lemas*:

- `center_id_in`: `G.id ∈ (center G).carrier.elems`
- `center_op_closed`: `a, b ∈ Z(G) → G.op a b ∈ Z(G)`
  (si `ag = ga` y `bg = gb` para todo `g`, entonces `(ab)g = a(bg) = a(gb) = (ag)b = (ga)b = g(ab)`)
- `center_inv_closed`: `a ∈ Z(G) → G.inv a ∈ Z(G)`
  (si `ag = ga`, invertir ambos lados: `g⁻¹a⁻¹ = a⁻¹g⁻¹`, equivalente a `a⁻¹g = ga⁻¹`)
- `center_normal`: `(center G).IsNormal G`
  (`g·z·g⁻¹ = g·g⁻¹·z = z ∈ Z(G)` por definición de centro)
- `center_is_characteristic`: `(center G).IsCharacteristic G`

#### B9.2 Conjugación y normalizador (Group.lean § 5g, ~25 lín.)

```
def conjugate (G : FinGroup) (g x : ℕ₀) : ℕ₀ :=
  G.op (G.op g x) (G.inv g)

def normalizer (G : FinGroup) (H : Subgroup G) : Subgroup G where
  carrier := G.carrier.filter (fun g =>
    H.carrier.elems.all (fun h => decide (conjugate G g h ∈ H.carrier.elems)))
  ...
```

*Sub-lemas*:

- `conjugate_mem`: `g ∈ G → x ∈ G → conjugate G g x ∈ G`
- `H_le_normalizer`: `∀ h ∈ H, h ∈ (normalizer G H).carrier.elems`
- `normalizer_op_closed`, `normalizer_inv_closed`
- `normal_iff_normalizer_eq_G`: `H.IsNormal ↔ (normalizer G H).carrier = G.carrier`

#### B9.2b Centralizador de un elemento (Group.lean § 5g, ~20 lín.)

```
def centralizer (G : FinGroup) (x : ℕ₀) : Subgroup G where
  carrier := G.carrier.filter (fun g =>
    decide (G.op g x = G.op x g))
  ...
```

*Sub-lemas*:

- `centralizer_id_in`: `G.id ∈ (centralizer G x).carrier.elems`
  (de `G.op G.id x = x = G.op x G.id`)
- `centralizer_op_closed`: `a, b ∈ C_G(x) → G.op a b ∈ C_G(x)`
  (si `ax = xa` y `bx = xb`, entonces `(ab)x = a(bx) = a(xb) = (ax)b = (xa)b = x(ab)`)
- `centralizer_inv_closed`: `a ∈ C_G(x) → G.inv a ∈ C_G(x)`
  (si `ax = xa`, invertir: `x⁻¹a⁻¹ = a⁻¹x⁻¹`, equivale a `a⁻¹x = xa⁻¹`)
- `center_eq_inter_centralizers`:
  `(center G).carrier = ⋂_{x ∈ G} (centralizer G x).carrier`
  (caracterización: `g ∈ Z(G) ↔ g ∈ C_G(x)` para todo `x`)
- `centralizer_normal_contains_center`:
  `(center G).carrier ⊆ (centralizer G x).carrier`
  (el centro está contenido en todo centralizador)
- `H_le_centralizer_of_abelian`:
  `(∀ a b ∈ H, G.op a b = G.op b a) → ∀ x ∈ H, H.carrier ⊆ (centralizer G x).carrier`

*Relación normalizer–centralizer*:

- `centralizer_le_normalizer`:
  `(centralizer G x).carrier ⊆ (normalizer G (cyclicSubgroup G x hx)).carrier`
  (si `g` conmuta con `x`, entonces `g` normaliza `⟨x⟩`)

**Complejidad**: Media (similar al centro, pero parametrizado en `x`)

---

#### B9.3 Grupo cociente `G/N` (Cosets.lean ampliado, ~60 lín.)

```
def quotientGroup (G : FinGroup) (N : Subgroup G)
    (hN : N.IsNormal G) : FinGroup where
  carrier := cosetFSet G N  -- FSet de cosetos como ℕ₀FSet
  op := cosetOp G N hN      -- (gN)·(hN) = (gh)N
  id := leftCoset G N G.id  -- eN = N
  inv := cosetInv G N hN    -- (gN)⁻¹ = g⁻¹N
```

*Sub-lemas para buena-definición*:

- `cosetOp_welldefined`: si `g₁N = g₂N` y `h₁N = h₂N`, entonces `(g₁h₁)N = (g₂h₂)N`
  (~15 lín., usa normalidad: `g₂⁻¹g₁ ∈ N` y `h₂⁻¹h₁ ∈ N` ⟹
  `(g₂h₂)⁻¹(g₁h₁) = h₂⁻¹(g₂⁻¹g₁)h₁ = h₂⁻¹·n·h₁`; por normalidad
  `h₂⁻¹·n = n'·h₂⁻¹`, luego `n'·h₂⁻¹·h₁ = n'·m ∈ N`)
- `cosetOp_assoc`: `((aN)·(bN))·(cN) = (aN)·((bN)·(cN))`
  (directo de `G.op_assoc`)
- `cosetOp_id`: `(eN)·(gN) = gN` y `(gN)·(eN) = gN`
- `cosetOp_inv`: `(gN)·(g⁻¹N) = eN`

---

#### B9.3b Tres teoremas de isomorfismo (~115 lín.)

**Dependencias**: `GroupHom` (B4), `quotientGroup` (B9.3), `Subgroup.inter` (B3.6), `Subgroup.product` (B3.7)

##### Definición previa: isomorfismo de grupos (~15 lín.)

```lean
structure GroupIso (G H : FinGroup) extends GroupHom G H where
  map_bijective : map.Bijective
```

*Lemas auxiliares*:

- `groupIso_symm`: si `φ : GroupIso G H`, entonces `∃ ψ : GroupIso H G, ...`
  (inyectividad + sobreyectividad dan la inversa)
- `groupIso_trans`: composición de isomorfismos es isomorfismo

##### Primer teorema — G/ker(φ) ≅ Im(φ) (~30 lín.)

**Enunciado**: si `φ : GroupHom G H`, entonces `GroupIso (quotientGroup G φ.ker (ker_isNormal φ)) φ.Im`

*Sub-lemas*:

- `first_iso_welldefined`: `g₁N = g₂N → φ.map g₁ = φ.map g₂`
  (g₂⁻¹·g₁ ∈ ker ⟹ φ(g₂⁻¹g₁) = H.id ⟹ φ(g₁) = φ(g₂))
- `first_iso_map_op`: `φ̄((g₁N)·(g₂N)) = H.op (φ̄(g₁N)) (φ̄(g₂N))`
  (de `φ.map_op`)
- `first_iso_injective`: ker(φ̄) = {eN}, usa `mono_iff_ker_trivial`
- `first_iso_surjective`: Im(φ̄) = φ.Im (por definición)
- `first_isomorphism`: `GroupIso (quotientGroup G φ.ker ...) φ.Im`

##### Segundo teorema — H/(H∩N) ≅ HN/N (~40 lín.)

**Hipótesis**: `N : Subgroup G` con `N.IsNormal G`, `H : Subgroup G`

*Sub-lemas previos*:

- `N_normal_in_HN`: `N.IsNormal (productSubgroup G H N)`
  (N ◁ G implica N ◁ HN, por restricción)
- `H_inter_N_normal_in_H`: `(Subgroup.inter G H N).IsNormal H`
  (H∩N ◁ H cuando N ◁ G)

*Construcción del homomorfismo φ: H → HN/N por h ↦ hN*:

- `second_iso_map_op`: `φ(G.op h₁ h₂) = cosetOp (φ h₁) (φ h₂)`
- `second_iso_ker_eq_inter`: `φ.ker.carrier = (Subgroup.inter G H N).carrier`
  (φ(h) = N ↔ h ∈ N ↔ h ∈ H∩N)
- `second_iso_surjective`: Im(φ) = HN/N
  (todo coseto hnN tiene representante en H: hn·N ∋ hn, h ↦ hn·N)
- `second_isomorphism`: `GroupIso (quotientGroup H (Subgroup.inter G H N) ...) (quotientGroup (HNSubgroup) N ...)`

##### Tercer teorema — (G/N)/(K/N) ≅ G/K (~30 lín.)

**Hipótesis**: `N K : Subgroup G`, `N.IsNormal G`, `K.IsNormal G`, `N.carrier ⊆ K.carrier`

*Sub-lemas previos*:

- `quotient_subgroup_of_nested`: K/N es subgrupo normal de G/N
  (`N ≤ K` hace que la proyección `gN ↦ gK` sea bien-definida)
- `third_iso_welldefined`: `gN = g'N → gK = g'K`
  (g'⁻¹g ∈ N ⊆ K)
- `third_iso_map_op`: `π((g₁N)·(g₂N)) = cosetOp_K (π(g₁N)) (π(g₂N))`
- `third_iso_ker_eq_quotient`: ker(π) = {gN | g ∈ K} = K/N
- `third_iso_surjective`: Im(π) = G/K
- `third_isomorphism`: `GroupIso (quotientGroup (G/N) (K/N) ...) (quotientGroup G K ...)`

---

#### B9.4 Teorema de Cauchy (~50 lín.)

```
theorem cauchy (G : FinGroup) (p : ℕ₀)
    (hp : Prime p) (hdvd : Divides p G.carrier.card) :
    ∃ g, g ∈ G.carrier.elems ∧ order G g (G.subset_mem g) = p
```

**Cadena de sub-lemas**:

```
order_dvd_card ────────────────── (de B2.4, usa lagrange sobre ⟨g⟩)
    │
cauchy_abelian (caso abeliano, ~20 lín.)
    │    Si G es abeliano y p | |G|, existe g de orden p.
    │    Inducción sobre |G|: tomar g ≠ e, si p | ord(g) done;
    │    si no, G/⟨g⟩ tiene |G|/ord(g) divisible por p,
    │    por HI existe elemento de orden p en cociente, levantar.
    │
cauchy_general (caso general, ~25 lín.)
    │    Ecuación de clases: |G| = |Z(G)| + Σ [G:C_G(xᵢ)]
    │    Si p | |Z(G)| → cauchy_abelian en Z(G) (Z(G) es abeliano)
    │    Si p ∤ |Z(G)| → existe C_G(xᵢ) con p ∤ [G:C_G(xᵢ)],
    │       luego p | |C_G(xᵢ)| (pues p | |G| = [G:C_G(xᵢ)]·|C_G(xᵢ)|)
    │       Inducción: |C_G(xᵢ)| < |G|
```

#### B9.5 Ecuación de clases (~35 lín.)

```
theorem class_equation (G : FinGroup) :
    G.carrier.card = add (center G).carrier.card
      (finSum (fun i => index G (centralizer G (rep i))) ...)
```

**Sub-lemas**:

- `conjugation_action`: la conjugación define una `GroupAction G G.carrier`
  (~10 lín.)
- `orb_conjugation_singleton_iff_center`: `|orb_conj(g)| = 1 ↔ g ∈ Z(G)`
  (~8 lín.)
- `class_eq_center_plus_nontrivial`: partición en órbitas triviales (= centro)
  y no triviales (usa `orbits_partition`)

---

### B10. Sorry 5–7: Tres teoremas de Sylow

#### B10.1 `sylow_first` (Sylow.lean:71)

**Cadena de sub-lemas**:

```
trivial_subgroup_of_card_one (nuevo, ~5 lín.)
    │    |G| = 𝟙 → G tiene un solo subgrupo: {e}
    │
sylow_first_base (nuevo, ~5 lín.)
    │    p^0 | |G| → ∃ H, |H| = 𝟙 (= p^0), testigo: trivialSubgroup
    │
sylow_first_center_case (nuevo, ~20 lín.)
    │    p | |Z(G)| → por cauchy en Z(G) existe ⟨g⟩ normal de orden p
    │    → G/⟨g⟩ tiene |G|/p, aplicar HI para p^(n-1) en G/⟨g⟩
    │    → levantar subgrupo del cociente al grupo original
    │    Sub-lema: lift_subgroup_from_quotient (~15 lín.)
    │
sylow_first_noncenter_case (nuevo, ~20 lín.)
    │    p ∤ |Z(G)| → class equation ⟹ ∃ C_G(x) con |C_G(x)| < |G|
    │    y p^n | |C_G(x)| → aplicar HI
    │    Sub-lema: centralizer_card_lt (~8 lín.)
    │    Sub-lema: p_dvd_centralizer (~8 lín.)
    │
sylow_first := strongInductionOn |G|
    │    (sylow_first_base, sylow_first_center_case, sylow_first_noncenter_case)
```

#### B10.2 `sylow_second` (Sylow.lean:88)

**Cadena de sub-lemas**:

```
coset_action (nuevo, ~15 lín.)
    │    Definir GroupAction H (cosetFSet G K) por h · (gK) = (hg)K
    │    Sub-lema: coset_action_closed (~5 lín.)
    │    Sub-lema: coset_action_id (~3 lín.)
    │    Sub-lema: coset_action_compat (~5 lín.)
    │
fixed_coset_imp_conjugate (nuevo, ~15 lín.)
    │    Si gK es fijo bajo toda la acción de H, entonces g⁻¹Hg ⊆ K
    │    Sub-lema: fixed_means_in_K: h·(gK) = gK → g⁻¹hg ∈ K (~8 lín.)
    │    Sub-lema: conjugate_subgroup_card: |g⁻¹Hg| = |H| (~5 lín.)
    │
orbit_size_divides_p_power (nuevo, ~10 lín.)
    │    |H| = p^n ⟹ cada |orb| divide p^n (orbit_stabilizer + lagrange)
    │
exists_fixed_point (nuevo, ~15 lín.)
    │    |G/K| = |G|/p^n no divisible por p
    │    Σ |orb| = |G/K| ≡ |fixed_points| (mod p)
    │    Luego |fixed_points| ≢ 0 (mod p), existe al menos un fixed_point
    │
sylow_second := exists_fixed_point + fixed_coset_imp_conjugate
    │    + conjugate_subgroup_card → g⁻¹Hg = K
```

#### B10.3 `sylow_third` (Sylow.lean:105)

**Cadena de sub-lemas**:

```
sylow_conjugation_action (nuevo, ~15 lín.)
    │    G actúa sobre {Sylow p-subgrupos} por conjugación
    │    (sylow_second ⟹ acción transitiva)
    │
np_eq_index_normalizer (nuevo, ~10 lín.)
    │    n_p = [G : N_G(H)] (por orbit_stabilizer sobre la acción de conjugación)
    │
np_divides_index (nuevo, ~5 lín.)
    │    n_p = [G:N_G(H)] y H ≤ N_G(H) ⟹ n_p | [G:H]
    │    (pues [G:H] = [G:N_G(H)]·[N_G(H):H])
    │
unique_fixed_point (nuevo, ~20 lín.)
    │    H actúa sobre Sylow p-subgrupos por conjugación
    │    Mostrar: K es punto fijo ⟹ K = H
    │    Sub-lema: fixed_K_imp_HK_subgroup: K fijo → H·K subgrupo (~8 lín.)
    │    Sub-lema: HK_card_formula: |HK| = |H|·|K|/|H∩K| (~10 lín.)
    │    Sub-lema: p_subgroups_equal: |H| = |K| = p^n y |HK| | |G| ⟹ H = K
    │
np_cong_one_mod_p (nuevo, ~10 lín.)
    │    #fixed_points = 1 (unique_fixed_point)
    │    n_p = 1 + (non-fixed orbits), cada non-fixed orbit has size divisible by p
    │    Luego n_p ≡ 1 (mod p)
    │
sylow_third := ⟨np_cong_one_mod_p, np_divides_index⟩
```

---

### Resumen del esfuerzo total (revisado)

| Bloque | Contenido | Lemas | Líneas est. |
|--------|-----------|-------|-------------|
| B1 | Infraestructura listas/conjuntos | 6 | ~60 |
| B2 | Potencia iterada + orden de elemento | 10 | ~90 |
| B3 | Tipos de subgrupos | 12+ | ~80 |
| B4 | Homomorfismos (Im, ker, comp, mono⟺ker) | 12 | ~85 |
| B5 | Subgrupo generado + grupo simple | 5 | ~50 |
| B6 | Sorry 1-2 (FunPerm.comp, orbits_partition) | 8 | ~60 |
| B7 | Sorry 3-4 (lagrange, orbit_stabilizer) | 10 | ~130 |
| B8 | Grupo simétrico Sym(Fin₀Set n) | 9 | ~100 |
| B9 | Infraestructura Sylow | 20+ | ~200 |
| B9.3b | Tres teoremas de isomorfismo | 15 | ~115 |
| B10 | Sorry 5-7 (tres Sylow) | 15+ | ~150 |
| **Total** | | **~122 lemas** | **~1120 líneas** |

---

## Prioridad inmediata

1. **B1**: Infraestructura de listas — desbloquea B6
2. **B2**: Orden de elemento — desbloquea B3, B9
3. **B3**: Tipos de subgrupos (normal, cíclico, etc.) — desbloquea B4, B5, B9
4. **B4**: Homomorfismos (Im, ker, comp, mono⟺ker) — desbloquea B9
5. **B5**: Subgrupo generado + grupo simple — independiente tras B3
6. **B6**: Sorry 1-2 (FunPerm.comp, orbits_partition) — desbloquea B7
7. **B7**: Sorry 3-4 (lagrange, orbit_stabilizer) — desbloquea B9
8. **B8**: Grupo simétrico Sym(Fin₀Set n) — independiente tras B6
9. **B9**: Infraestructura Sylow — en orden:
   - B9.1 `center Z(G)`
   - **B9.2 `normalizer N_G(H)`** — normalizador de un subgrupo ❌ Pendiente
   - **B9.2b `centralizer C_G(x)`** — centralizador de un elemento ❌ Pendiente
   - B9.3 Grupo cociente `G/N`
   - **B9.3b Tres teoremas de isomorfismo** ❌ Pendiente
   - B9.4 Cauchy
   - B9.5 Ecuación de clases
10. **B10**: Sorry 5-7 — requiere todo lo anterior
11. **Phase 22 (ℤ)**: Extensión a enteros
12. **Phase 23 (ℚ)**: Extensión a racionales
