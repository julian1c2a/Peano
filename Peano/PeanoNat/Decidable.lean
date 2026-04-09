/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Decidable.lean
-- Módulo de reexportación: reúne todas las instancias Decidable,
-- funciones booleanas de comparación (blt, bgt, ble, bge) y sus
-- teoremas de equivalencia iff dispersos en StrictOrder y Order.
-- No contiene demostraciones nuevas.

import Peano.PeanoNat.Order


-- ─────────────────────────────────────────────────────────────────
-- StrictOrder: blt, bgt, decidableLt, decidableGt
-- ─────────────────────────────────────────────────────────────────
export Peano.StrictOrder (
  blt
  bgt
  blt_iff_Lt
  blt_then_Lt_wp
  bgt_iff_Gt
  nblt_iff_nLt
  nbgt_iff_nGt
  decidableLt
  decidableGt
)

-- ─────────────────────────────────────────────────────────────────
-- Order: ble, bge, decidableLe, decidableGe
-- ─────────────────────────────────────────────────────────────────
export Peano.Order (
  ble
  bge
  ble_iff_Le
  bge_iff_Ge
  decidableLe
  decidableGe
  bexLe
  decidableBExLe_of_bool
)
