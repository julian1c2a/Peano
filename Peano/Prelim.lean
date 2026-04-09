/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/Prelim.lean
-- Fachada: re-exporta ambos sub-módulos para compatibilidad.
--   • Prelim.ExistsUnique  — constructivo (sin Classical)
--   • Prelim.Classical      — noncomputable choose / unicidad
-- Los módulos que NO necesitan lógica clásica deben importar
--   import Peano.Prelim.ExistsUnique
-- en lugar de este archivo.

import Peano.Prelim.ExistsUnique
import Peano.Prelim.Classical

export Peano (
  ExistsUnique
  choose
  choose_spec
  choose_unique
  choose_spec_unique
  choose_uniq
)
