/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/Prelim/Classical.lean
-- Parte clásica (no-computable): choose, unicidad.
-- Importar SOLO cuando se necesite lógica clásica explícitamente.

import Init.Classical
import Peano.Prelim.ExistsUnique

namespace Peano

  noncomputable def choose {α : Type} {p : α → Prop} (h : ∃ x, p x) : α :=
    (Classical.indefiniteDescription p h).val

  theorem choose_spec {α : Type} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
    (Classical.indefiniteDescription p h).property

  noncomputable def choose_unique {α : Type} {p : α → Prop} (h : ExistsUnique p) : α :=
    choose (ExistsUnique.exists h)

  theorem choose_spec_unique {α : Type} {p : α → Prop}
    (h : ExistsUnique p) : p (choose_unique h)
      := by
        unfold choose_unique
        exact choose_spec (ExistsUnique.exists h)

  theorem choose_uniq {α : Type} {p : α → Prop}
    (h : ExistsUnique p) {y : α} (hy : p y) :
      y = choose_unique h
        :=
    let ⟨x, ⟨_, uniq⟩⟩ := h
    have hcu : p (choose_unique h) := choose_spec_unique h
    have y_eq_x : y = x := uniq y hy
    have cu_eq_x : choose_unique h = x := uniq (choose_unique h) hcu
    y_eq_x.trans cu_eq_x.symm

end Peano

export Peano (
  choose
  choose_spec
  choose_unique
  choose_spec_unique
  choose_uniq
)
