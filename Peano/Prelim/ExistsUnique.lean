/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/Prelim/ExistsUnique.lean
-- Parte constructiva de la infraestructura preliminar.
-- NO depende de Classical.

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

  def ExistsUnique.exists {α : Type} {p : α → Prop} (h : ExistsUnique p) : (∃ x, p x) := by
    cases h with
    | intro x hx =>
      exact ⟨x, hx.left⟩

end Peano

export Peano (
  ExistsUnique
  ExistsUnique.exists
)
