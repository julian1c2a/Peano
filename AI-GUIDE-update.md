# AI-GUIDE Update — Prelim.lean Cross-Project Standard

**Date:** 2026-04-08
**Author:** Julián Calderón Almendros
**Scope:** Template rule for all Lean4 projects by this author

---

## New Rule: Prelim.lean as shared infrastructure

### Summary

Every Lean 4 project by this author **MUST** include a `Prelim.lean` file at the root
of its source directory. This file contains project-agnostic definitions and theorems
that are common across all projects (currently: Peano and ZfcSetTheory).

### Canonical contents of Prelim.lean

```lean
-- Prelim.lean — Shared infrastructure across projects
import Init.Classical

namespace <ProjectNamespace>

  -- 1. ExistsUnique and its API
  def ExistsUnique {α : Type} (p : α → Prop) : Prop :=
    ∃ x, (p x ∧ (∀ y, (p y → y = x)))

  -- 2. Syntax macros for ∃¹ / ∃!
  syntax "∃¹ " ident ", " term : term
  -- ... (all 4 variants)

  -- 3. Classical choice
  noncomputable def choose ...
  theorem choose_spec ...

  -- 4. ExistsUnique utilities
  def ExistsUnique.exists ...
  noncomputable def choose_unique ...
  theorem choose_spec_unique ...
  theorem choose_uniq ...

end <ProjectNamespace>

export <ProjectNamespace> (ExistsUnique choose choose_spec ...)
```

### Rules

| # | Rule |
|---|------|
| 1 | `Prelim.lean` lives at the source root: `<Project>/<ProjectDir>/Prelim.lean` |
| 2 | It imports ONLY `Init.Classical` — no project-specific dependencies |
| 3 | The main type module (e.g., `PeanoNat.lean`) imports `Prelim.lean` and re-exports its content |
| 4 | When forking to a new project, copy `Prelim.lean` verbatim; change only the namespace |
| 5 | API additions to `Prelim.lean` must be mirrored across all projects |
| 6 | `Prelim.lean` MUST have an export block listing all public declarations |
| 7 | The ZfcSetTheory project has its equivalent at `ZfcSetTheory/Core/Prelim.lean` |

### Migration path

For existing projects that have Prelim content inline (e.g., inside `PeanoNat.lean`):

1. Extract `ExistsUnique` + choice infrastructure to `Prelim.lean`
2. Replace the inline definitions with `import <Project>.Prelim`
3. Verify the export block in both `Prelim.lean` and the original module
4. Clean build

### Project inventory

| Project | Prelim location | Status |
|---------|-----------------|--------|
| ZfcSetTheory | `ZfcSetTheory/Core/Prelim.lean` | ✅ Extracted |
| Peano | `Peano/Prelim.lean` | 🔄 Pending extraction (content in PeanoNat.lean) |

---

## Directory structure standard (updated)

All non-trivial projects should organize modules in subdirectories:

```
<Project>/
├── Prelim.lean              # Shared infrastructure
├── <MainType>.lean          # Core type definitions
├── _template.lean           # Template (not imported)
└── <MainType>/
    ├── Axioms.lean          # Foundational theorems
    ├── <Topic>.lean         # Grouped by mathematical topic
    └── Isomorph.lean        # Bridge theorems with Lean4 core (if applicable)
```

Barrel file `<MainType>.lean` (peer of the directory) acts as single import point.
