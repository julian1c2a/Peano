/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Isomorph.lean
-- Módulo de reexportación: reúne todos los teoremas de isomorfismo
-- Nat ↔ ℕ₀ (vía Λ y Ψ) dispersos en los módulos de la cadena principal.
-- No contiene demostraciones nuevas.

import Peano.PeanoNat.Sub


-- ─────────────────────────────────────────────────────────────────
-- Axioms: inyectividad, biyección, composición, conmutación
-- ─────────────────────────────────────────────────────────────────
export Peano.Axioms (
  Λ_inj
  Λ_surj
  Λ_bij
  Ψ_inj
  Ψ_surj
  Ψ_bij
  comp_Λ_eq_Ψ
  comp_Ψ_eq_Λ
  ΨΛ
  ΛΨ
  Ψ_σ_eq_σ_Λ
  Λ_σ_eq_σ_Ψ
  Ψ_τ_eq_τ_Λ
  Λ_τ_eq_τ_Ψ
  isomorph_0_Λ
  isomorph_0_Ψ
  isomorph_σ_Λ
  isomorph_σ_Ψ
  isomorph_τ_Λ
  isomorph_τ_Ψ
  isomorph_ρ_Ψ
  isomorph_Λ_ρ
)

-- ─────────────────────────────────────────────────────────────────
-- StrictOrder: Lt ↔ Nat.lt
-- ─────────────────────────────────────────────────────────────────
export Peano.StrictOrder (
  isomorph_Λ_lt
  isomorph_Ψ_lt
)

-- ─────────────────────────────────────────────────────────────────
-- Order: Le ↔ Nat.le
-- ─────────────────────────────────────────────────────────────────
export Peano.Order (
  isomorph_Ψ_le
  isomorph_Λ_le
)

-- ─────────────────────────────────────────────────────────────────
-- MaxMin: max/min ↔ Nat.max/Nat.min
-- ─────────────────────────────────────────────────────────────────
export Peano.MaxMin (
  isomorph_Λ_max
  isomorph_Λ_min
  isomorph_Ψ_max
  isomorph_Ψ_min
)

-- ─────────────────────────────────────────────────────────────────
-- Add: add ↔ Nat.add
-- ─────────────────────────────────────────────────────────────────
export Peano.Add (
  isomorph_Ψ_add
  isomorph_Λ_add
)

-- ─────────────────────────────────────────────────────────────────
-- Sub: sub ↔ Nat.sub
-- ─────────────────────────────────────────────────────────────────
export Peano.Sub (
  isomorph_Λ_sub
  isomorph_Ψ_sub
)
