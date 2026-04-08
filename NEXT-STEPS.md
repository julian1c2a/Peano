# Next Steps — Peano

**Last updated:** 2026-04-08
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
| 11 | Warning Cleanup | ❌ Pending |
| 12 | Update REFERENCE.md with new names | ❌ Pending |

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
| `PeanoNatMaxMin.lean` | `Peano.MaxMin` | `Peano.MaxMin` | ✅ No change |
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
PeanoNatMaxMin.lean    (5th — MOST renames here)
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

#### PeanoNatMaxMin.lean (namespace Peano.MaxMin) — MOST RENAMES

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
**Status**: ❌ Pending
**Dependencies**: Phase 10 complete (or can be done independently)

### 11.1. Current warnings (as of 2026-04-08)

| File | Line | Warning | Linter | Fix |
|------|------|---------|--------|-----|
| `PeanoNatSub.lean` | 484 | Unused simp argument `Nat.sub` | `linter.unusedSimpArgs` | Remove `Nat.sub` from `simp [Nat.sub, Λ, sub_zero]` → `simp [Λ, sub_zero]` |

### 11.2. Protocol

1. **Audit**: Run `lake build 2>&1` and collect all lines containing `warning:`.
2. **Fix** each warning individually:
   - `unusedSimpArgs`: Remove the flagged argument from the `simp` call. Verify the proof still closes.
   - `unusedVariables`: Prefix with `_` or remove if truly unused.
   - `deprecated`: Replace with the recommended replacement.
3. **Verify**: `lake build 2>&1 | Select-String "warning"` must produce **no output**.
4. **Commit**: `git commit -m "chore: fix all build warnings"`

### 11.3. Policy going forward

After this phase, **zero warnings** is a project invariant. Any new warning introduced by a commit must be fixed before merging.

---

## Phase 12: Update REFERENCE.md with New Names

**Objective**: Regenerate REFERENCE.md to reflect all identifier renames from Phase 10.
**Status**: ❌ Pending
**Dependencies**: Phase 10 and 11 complete

**Steps**:

1. "Proyectar" each of the 16 modules into REFERENCE.md per AI-GUIDE §12.
2. Verify all exported names match the actual `export` blocks.
3. Update the module table and any cross-references.
4. Commit: `git commit -m "docs: update REFERENCE.md with new naming conventions"`

---

## Future Phases

### Phase N: Integer Extension (ℤ)

**Objective**: Construct integers from ℕ₀ using equivalence classes of pairs.

**Modules**:

- [ ] `Peano/Integer/Basic.lean` — ℤ definition
- [ ] `Peano/Integer/Arithmetic.lean` — ℤ operations

**Dependencies**: Phase 11 complete
**Complexity**: Complex
