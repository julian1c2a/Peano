/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/Prelim.lean
-- Infraestructura compartida: ExistsUnique, choose, unicidad.
-- No depende de ℕ₀ ni de ningún otro módulo de Peano.

import Init.Classical


namespace Peano

  def ExistsUnique {α : Type} (p : α → Prop) : Prop :=
    ∃ x, (p x ∧ (∀ y, (p y → y = x)))

  syntax "∃¹ " ident ", " term : term
  syntax "∃¹ " "(" ident ")" ", " term : term
  syntax "∃¹ " "(" ident " : " term ")" ", " term : term
  syntax "∃¹ " ident " : " term ", " term : term

  macro_rules
    | `(∃¹ $x:ident, $p:term) => `(ExistsUnique (fun $x => $p))
    | `(∃¹ ($x:ident), $p:term) => `(ExistsUnique (fun $x => $p))
    | `(∃¹ ($x:ident : $t:term), $p:term) => `(ExistsUnique (fun ($x : $t) => $p))
    | `(∃¹ $x:ident : $t:term, $p:term) => `(ExistsUnique (fun ($x : $t) => $p))


  noncomputable def choose {α : Type} {p : α → Prop} (h : ∃ x, p x) : α :=
    (Classical.indefiniteDescription p h).val

  theorem choose_spec {α : Type} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
    (Classical.indefiniteDescription p h).property

  def ExistsUnique.exists {α : Type} {p : α → Prop} (h : ExistsUnique p) : (∃ x, p x) := by
    cases h with
    | intro x hx =>
      exact ⟨x, hx.left⟩

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
  ExistsUnique
  choose
  choose_spec
  choose_unique
  choose_spec_unique
  choose_uniq
)
