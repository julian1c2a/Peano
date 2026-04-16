# Design Decisions — Peano

**Last updated:** 2026-04-16
**Author**: Julián Calderón Almendros

Architectural Decision Records (ADR) for this project.
Each entry records *what* was decided and *why*, for future reference.

---

## ADR-001: No Mathlib dependency

**Date**: 2025-01-01
**Status**: Accepted

**Decision**: This project does not depend on Mathlib.

**Rationale**: Educational goal — formalize Peano arithmetic from scratch using only Lean 4's core. Building all infrastructure (induction, recursion, arithmetic) from the inductive type ℕ₀ is the entire purpose of the project.

**Consequences**: All necessary infrastructure (ExistsUnique, recursion principles, div/mod, etc.) must be built from scratch.

---

## ADR-002: autoImplicit = false

**Date**: 2025-01-01
**Status**: Accepted

**Decision**: `moreServerArgs := #["-DautoImplicit=false"]` is set in `lakefile.lean`.

**Rationale**: Explicit type annotations prevent accidental universe polymorphism issues and make code easier to read and maintain.

**Consequences**: All variables must be explicitly declared or annotated.

---

## ADR-003: File locking system

**Date**: 2026-04-08
**Status**: Accepted

**Decision**: Use `git-lock.bash` + `locked_files.txt` + pre-commit hook to prevent accidental edits to completed modules. Replaces the old `.bat`-based freeze system.

**Rationale**: Lean 4 proofs are fragile — small changes to completed modules can break dependent proofs. The locking system makes this explicit. Bash scripts are cross-platform (Windows Git Bash + Linux/macOS).

**Consequences**: Workflow requires locking/unlocking files. See AI-GUIDE.md §20.

---

## ADR-004: Mathlib naming conventions

**Date**: 2026-04-08
**Status**: Accepted

**Decision**: All identifiers follow Mathlib4 naming conventions as documented in NAMING-CONVENTIONS.md.

**Rationale**: Consistency with the broader Lean 4 ecosystem. Makes theorems discoverable by name pattern (`subject_predicate`). Facilitates future Mathlib integration if desired.

**Consequences**: Existing names may need migration. See NAMING-CONVENTIONS.md for the full dictionary and 12 formation rules.

---

## ADR-005: Module directory = Peano

**Date**: 2025-01-01
**Status**: Accepted

**Decision**: Source modules live in `Peano/` while the lean_lib name is `Peano` and the root file is `Peano.lean`. Imports use `Peano.` prefix. Namespaces use `Peano.` prefix.

**Rationale**: Historical architecture from the project's inception. The `Peano` directory name reflects the library's content, while `Peano` is the public-facing namespace.

**Consequences**: Scripts (gen-root.bash, new-module.bash) detect the module directory from `Glob.submodules` in lakefile.lean. The namespace/import prefix mismatch requires awareness.

---

## ADR-006: Inductive type ℕ₀ as foundation

**Date**: 2025-01-01
**Status**: Accepted

**Decision**: All Peano axioms are derived as theorems from the inductive type `ℕ₀`, not postulated as axioms.

**Rationale**: Maximum rigor — the 8 Peano axioms are proven, not assumed. This gives a constructive foundation where every property is traceable to the inductive type definition.

**Consequences**: The module `PeanoNatAxioms.lean` contains theorems (not axioms).

---

## ADR-007: FSet as Quotient type (not sorted list)

**Date**: 2026-05
**Status**: Accepted

**Decision**: `FSet α` is defined as `Quotient (Perm.setoid α)` — the quotient of `List α` by permutation equivalence. Not as a structure with a sorted list + `Sorted` invariant.

**Rationale**: Avoids requiring `LT` and `DecidableRel LT` on element types. Only needs `DecidableEq α`. More mathematically elegant — two lists represent the same set iff they are permutations. Aligns with Mathlib's `Finset` philosophy.

**Consequences**: Some operations become `noncomputable` (e.g., `DecidableEq FSet`). The original plan in THOUGHTS.md §11 and LISTS_FSETS_N_FSETFUNCTIONS.md was overridden.

---

## ADR-008: Thematic subdirectories for module organization

**Date**: 2026-04
**Status**: Accepted

**Decision**: Group modules into thematic subdirectories: `Combinatorics/`, `ListsAndSets/`, `NumberTheory/`, `Combinatorics/GroupTheory/`, `Combinatorics/GroupTheory/Sylow/`, `Prelim/`.

**Rationale**: With 49+ modules, flat organization became unmanageable. Subdirectories mirror mathematical domains and enable focused navigation.

**Consequences**: Imports use full paths (`Peano.PeanoNat.Combinatorics.Pow`). `Peano.lean` barrel file imports all sub-modules.

---

## ADR-009: No custom algebraic typeclasses

**Date**: 2026-05
**Status**: Accepted

**Decision**: Do not define custom typeclasses like `CommMonoid ℕ₀` or `OrderedCommSemiring ℕ₀`. Instead, prove the properties as standalone lemmas.

**Rationale**: Without Mathlib, custom typeclasses would duplicate Mathlib's hierarchy poorly. Standalone lemmas suffice for current needs and avoid a premature abstraction.

**Consequences**: No `instance : CommMonoid ℕ₀` etc. Properties like commutativity and associativity exist as named theorems.

---

## Template for new decisions

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]
