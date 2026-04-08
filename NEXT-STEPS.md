# Next Steps — Peano

**Last updated:** 2026-04-08 21:00
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
| 6 | Export/Glob Architecture | ❌ Pending |
| 7 | Naming Migration | ❌ Pending |

---

## Phase 5: Infrastructure Modernization (CURRENT)

**Objective**: Bring project infrastructure to template standard.

**Steps**:

- [x] Add git-lock.bash, check-sorry.bash, gen-root.bash, new-module.bash, update-toolchain.bash
- [x] Add Makefile
- [x] Add AI-GUIDE.md, NAMING-CONVENTIONS.md, WORKFLOW.md, DECISIONS.md, THOUGHTS.md
- [x] Add _template.lean, frozen_files.txt, locked_files.txt
- [x] Fix .gitignore
- [x] Remove obsolete files (AIDER-AI-GUIDE.md, .bat scripts, etc.)
- [x] Update toolchain to v4.29.0

**Complexity**: Simple (infrastructure only, no .lean code changes)

---

## Phase 6: Export/Glob Architecture

**Objective**: Add export blocks to all 16 leaf modules per AI-GUIDE.md §30–31.

**Modules**: All Peano/*.lean files

**Steps**:

1. Add `export Peano.XXX (...)` blocks to each leaf module
2. Verify `gen-root.bash` correctly regenerates Peano.lean
3. Update REFERENCE.md with module status codes

**Dependencies**: Phase 5 complete
**Complexity**: Medium

---

## Phase 7: Naming Migration

**Objective**: Ensure all identifiers follow Mathlib naming conventions.

**Modules**: All existing modules
**Reference**: [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md)

**Steps**:

1. Audit all exported names against NAMING-CONVENTIONS.md
2. Rename definitions: `UpperCamelCase` for Prop, `lowerCamelCase` for functions
3. Rename theorems: `subject_predicate` pattern with standard suffixes
4. Verify full compilation after each rename batch
5. Update REFERENCE.md with new names

**Dependencies**: Phase 6 complete
**Complexity**: Medium (mechanical but requires full recompilation)

---

## Future Phases

### Phase N: Integer Extension (ℤ)

**Objective**: Construct integers from ℕ₀ using equivalence classes of pairs.

**Modules**:

- [ ] `Peano/Integer/Basic.lean` — ℤ definition
- [ ] `Peano/Integer/Arithmetic.lean` — ℤ operations

**Dependencies**: Phase 7
**Complexity**: Complex
