/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: Peano.PeanoNat (add more as needed)
-- @axiom_system: Peano
-- @importance: medium

import Peano.PeanoNat
-- import Peano.PeanoNatAxioms

namespace Peano.ModuleName

-- ============================================================
-- Section 1: Definitions
-- ============================================================
-- Naming: UpperCamelCase for Prop predicates (IsXxx)
--         lowerCamelCase for functions/constructors

-- def myDef : Type := ...

-- ============================================================
-- Section 2: Basic Properties
-- ============================================================
-- Naming: subject_predicate pattern (snake_case)
--         Suffixes: _iff, _eq, _of_, _comm, _assoc, _cancel

-- theorem myTheorem : ... := by ...

-- ============================================================
-- Section 3: Advanced Theorems
-- ============================================================
-- Naming: conclusion_of_hypothesis pattern
--         Use .mp/.mpr for iff directions

-- ============================================================
-- Section 4: Exports (AI-GUIDE.md §30–31)
-- ============================================================
-- List ALL public (non-private) declarations alphabetically.
-- This block goes AFTER end namespace, at top level.
-- Notation/syntax propagates automatically — do not list here.

end Peano.ModuleName

-- export Peano.ModuleName (
--   myDef
--   myTheorem
-- )
