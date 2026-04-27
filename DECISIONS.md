# Design Decisions — Peano

**Last updated:** 2026-04-27
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

## ADR-007: FSet as sorted-list structure (not Quotient)

**Date**: 2026-04 (revised 2026-04-27)
**Status**: Accepted

**Decision**: `FSet α` is defined as a `structure` with a sorted list and a `Sorted` invariant:

```lean
structure FSet (α : Type) [LT α] [StrictLinearOrder α] where
  elems  : List α
  sorted : Sorted (· < ·) elems
  nodup  : elems.Nodup
```

Not as `Quotient (Perm.setoid α)`.

**Rationale**: The sorted-list approach keeps all operations computable (no `noncomputable` needed), gives canonical representatives for equality (`FSet.eq_of_mem_iff`), and is directly amenable to decidable equality via `DecidableEq (List α)`. It requires `LT α` with `StrictLinearOrder α` on element types — already available for all types used in this project (ℕ₀, Tuple, List, FSet itself). The Quotient approach would make `DecidableEq FSet` noncomputable and block universe-computable proofs.

**Consequences**: `FSet α` requires `[StrictLinearOrder α]` on the element type. All current element types (`ℕ₀`, `Tuple ℕ₀ n`, `List α`, `FSet α`) have this instance. `sortedInsert` is the core insertion primitive. Two FSets are equal iff they have the same elements (extensionality via `FSet.eq_of_mem_iff`).

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

## ADR-010: FinGroup polymorphic over arbitrary type with StrictLinearOrder

**Date**: 2026-04-27
**Status**: Accepted

**Decision**: `FinGroup` is parameterized over an arbitrary element type `α`:

```lean
structure FinGroup (α : Type) [DecidableEq α] [LT α] [StrictLinearOrder α] where
  carrier  : FSet α
  op       : BinOpOn carrier
  id       : α
  inv      : MapOn carrier carrier
  id_in    : id ∈ carrier.elems
  op_assoc : ...
  op_id    : ...
  op_inv   : ...

abbrev ℕ₀FinGroup := FinGroup ℕ₀
```

Previously `FinGroup` was hardwired to `ℕ₀` (carrier was `ℕ₀FSet`, id was `ℕ₀`).

**Rationale**: The hardwired-ℕ₀ approach blocked key developments: (1) `FinGroup (Subgroup G)` for the conjugation action needed by Sylow III, (2) quotient groups for future use. Making `FinGroup` polymorphic over `α` with `StrictLinearOrder α` unblocks both. The `abbrev ℕ₀FinGroup := FinGroup ℕ₀` alias preserves backward compatibility with all existing Sylow/Cosets/Action code.

**Consequences**:
- `Action.lean`, `Cosets.lean`, `Sylow.lean` use `(G : FinGroup ℕ₀)` (explicit type annotation) — mechanical change, proofs unaffected.
- `Group.lean` theorems now quantify over `{α} [DecidableEq α] [LT α] [StrictLinearOrder α]`.
- `FSet (Tuple ℕ₀ n)` works automatically via `instStrictLinearOrderTuple`.
- Build: 51 jobs (ListList.lean and FSetFSet.lean eliminated, merged into List.lean and FSet.lean).

---

## Template for new decisions

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]
