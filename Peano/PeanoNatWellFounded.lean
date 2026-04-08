/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatWellFounded.lean
--
-- Este fichero contiene la prueba de que el orden estricto '<'
-- en ℕ₀ es una relación bien fundada. La demostración se construye
-- directamente a partir de la estructura inductiva de ℕ₀, sin
-- depender del isomorfismo con Nat para la prueba principal.

-- También demostramos que el orden estricto '<' en ℕ₀ es un buen orden.

import Peano.PeanoNat
import Peano.PeanoNatAxioms
import Peano.PeanoNatStrictOrder
import Peano.PeanoNatOrder
import Peano.PeanoNatMaxMin
import Init.Classical

namespace Peano
  open Peano

  namespace WellFounded
    open Axioms
    open StrictOrder
    open Order
    open MaxMin

    /--
      Define el "tamaño" de un número ℕ₀ para que Lean pueda usarlo
      en tácticas de terminación como `decreasing_by`. Usamos el
      isomorfismo `Ψ` a `Nat`, ya que `SizeOf` espera un `Nat`.
      Esta instancia es una herramienta práctica y no interfiere con
      la prueba fundamental de buen orden.
    -/
    instance : SizeOf ℕ₀ where
      sizeOf := Ψ

    /--
      Lema principal que demuestra que cada número `n : ℕ₀` es "accesible"
      a través de la relación `Lt`. Un elemento es accesible si todos sus
      predecesores (elementos menores que él) también lo son. Esta es la
      base para demostrar el buen orden.

      La prueba se realiza por inducción sobre `n`.
    -/
    theorem acc_lt_wf (n : ℕ₀) : Acc Lt n := by
      induction n with
      | zero =>
        -- Caso base: 𝟘 es accesible porque no existe ningún `y` tal que `Lt y 𝟘`.
        exact Acc.intro 𝟘 (fun y h_lt_y_zero => False.elim (lt_zero y h_lt_y_zero))
      | succ n' ih =>
        -- Caso inductivo: La hipótesis de inducción `ih` es que `n'` es accesible (`Acc Lt n'`).
        -- Queremos probar que `σ n'` es accesible.
        apply Acc.intro (σ n')
        -- Para ello, debemos mostrar que cualquier `y` tal que `Lt y (σ n')` es accesible.
        intro y h_lt_y_sn'
        -- Por el lema `lt_succ_iff_le`, si `y < σ n'`, entonces `y ≤ n'`.
        have h_le_y_n' : Le y n' := (lt_succ_iff_le y n').mp h_lt_y_sn'
        -- Descomponemos `y ≤ n'` en los dos casos posibles: `y < n'` o `y = n'`.
        rcases (le_iff_lt_or_eq y n').mp h_le_y_n' with h_lt_y_n' | h_eq_y_n'
        · -- Caso 1: Lt y n'.
          -- Si `y < n'`, `y` es un predecesor de `n'`. La hipótesis de inducción `ih`
          -- nos dice que `n'` es accesible, lo que implica que todos sus
          -- predecesores también lo son. Usamos `Acc.inv` para aplicar esta propiedad.
          exact Acc.inv ih h_lt_y_n'
        · -- Caso 2: y = n'.
          -- Si `y = n'`, entonces `y` es accesible porque `n'` es accesible (por `ih`).
          rw [h_eq_y_n']
          exact ih

    /--
      Teorema final que establece que la relación `Lt` es bien fundada (`WellFounded`).
      Una relación es bien fundada si todos los elementos de su dominio son accesibles.
      La prueba consiste en aplicar el lema `acc_lt_wf` a cualquier `n`.
    -/
    theorem well_founded_lt : WellFounded Lt :=
      WellFounded.intro acc_lt_wf

    /--
      El Principio de Buen Orden para ℕ₀.
      Afirma que todo conjunto no vacío de números (descrito por una propiedad `P`)
      contiene un único elemento mínimo. Es una consecuencia directa de `well_founded_lt`.
    -/
    theorem well_ordering_principle (P : ℕ₀ → Prop) (h_nonempty : ∃ k, P k) :
      ∃¹ (n : ℕ₀), (P n) ∧ ∀ (m : ℕ₀), (P m) → (n ≤ m )
        := by
      -- 1. Existencia del mínimo
      -- Probamos que existe un elemento minimal (ninguno es estrictamente menor).
      have h_minimal_exists : ∃ n, P n ∧ ∀ m, Lt m n → ¬ P m := by
        -- Prueba por contradicción: asumimos que no hay ningún elemento minimal.
        apply Classical.byContradiction
        intro h_no_minimal
        -- `h_no_minimal` es `¬(∃ n, P n ∧ ...)` que es `∀ n, ¬(P n ∧ ...)`
        -- Esto implica que para cualquier `n` con la propiedad `P`, siempre
        -- existe un `m` más pequeño con la propiedad `P`.
        have h_can_descend : ∀ n, P n → ∃ m, Lt m n ∧ P m := by
          intro n hn
          -- La negación de "n es minimal" es "existe un m < n con P m".
          have h_not_minimal : ¬(P n ∧ ∀ (m : ℕ₀), Lt m n → ¬P m) := (not_exists.mp h_no_minimal) n
          -- Usamos lógica clásica para simplificar la negación.
          simp [not_and, Classical.not_forall, Classical.not_not] at h_not_minimal
          exact h_not_minimal hn

        -- Esta capacidad de descender siempre contradice que `Lt` es bien fundada.
        -- Lo probamos mostrando que `P` no puede ser cierto para ningún número.
        have h_not_P_all : ∀ n, ¬ P n := by
          intro n
          -- Usamos inducción bien fundada sobre `n` usando well_founded_lt.fix.
          exact well_founded_lt.fix (fun x ih =>
              fun h_Px =>
                let ⟨y, ⟨h_lt_yx, h_Py⟩⟩ := h_can_descend x h_Px
                ih y h_lt_yx h_Py
            ) n
        -- Si `P` no es cierto para ningún número, contradice que el conjunto no es vacío.
        let ⟨k, hk⟩ := h_nonempty
        exact h_not_P_all k hk

      -- Usamos `choose` para obtener un término `n` que es minimal.
      let n := choose h_minimal_exists
      have h_n_props : P n ∧ ∀ m, Lt m n → ¬ P m := choose_spec h_minimal_exists
      let h_Pn := h_n_props.left
      let h_n_is_minimal := h_n_props.right

      -- Probamos que este `n` minimal es también un elemento mínimo (menor o igual).
      have h_exists : ∃ n_min, P n_min ∧ ∀ m, P m → Le n_min m := by
        exists n
        exact ⟨h_Pn, fun m h_Pm =>
          match trichotomy n m with
          | Or.inl h_lt_nm =>
              Or.inl h_lt_nm
          | Or.inr (Or.inl h_eq_nm) =>
              Or.inr h_eq_nm
          | Or.inr (Or.inr h_lt_mn) =>
              False.elim (h_n_is_minimal m h_lt_mn h_Pm)
        ⟩

      -- 2. Unicidad del mínimo
      rcases h_exists with ⟨n_min, ⟨h_Pn_min, h_is_least⟩⟩
      exists n_min
      constructor
      · exact ⟨h_Pn_min, h_is_least⟩
      · intro n' ⟨h_Pn', h_is_least'⟩
        have h_le1 : Le n_min n' := h_is_least n' h_Pn'
        have h_le2 : Le n' n_min := h_is_least' n_min h_Pn_min
        exact le_antisymm n' n_min h_le2 h_le1

  end WellFounded

end Peano

export Peano.WellFounded (
  well_founded_lt
  well_ordering_principle
)
