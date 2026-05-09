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
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Lattice


namespace Peano
  open Peano

  namespace WellFounded
    open Axioms
    open StrictOrder
    open Order
    open Lattice

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
      a través de la relación `lt₀`. Un elemento es accesible si todos sus
      predecesores (elementos menores que él) también lo son. Esta es la
      base para demostrar el buen orden.

      La prueba se realiza por inducción sobre `n`.
    -/
    theorem acc_lt_wf (n : ℕ₀) : Acc lt₀ n := by
      induction n with
      | zero =>
        -- Caso base: 𝟘 es accesible porque no existe ningún `y` tal que `lt₀ y 𝟘`.
        exact Acc.intro 𝟘 (fun y h_lt_y_zero => False.elim (lt_zero y h_lt_y_zero))
      | succ n' ih =>
        -- Caso inductivo: La hipótesis de inducción `ih` es que `n'` es accesible (`Acc lt₀ n'`).
        -- Queremos probar que `σ n'` es accesible.
        apply Acc.intro (σ n')
        -- Para ello, debemos mostrar que cualquier `y` tal que `lt₀ y (σ n')` es accesible.
        intro y h_lt_y_sn'
        -- Por el lema `lt_succ_iff_le`, si `y < σ n'`, entonces `y ≤ n'`.
        have h_le_y_n' : le₀ y n' := (lt_succ_iff_le y n').mp h_lt_y_sn'
        -- Descomponemos `y ≤ n'` en los dos casos posibles: `y < n'` o `y = n'`.
        rcases (le_iff_lt_or_eq y n').mp h_le_y_n' with h_lt_y_n' | h_eq_y_n'
        · -- Caso 1: lt₀ y n'.
          -- Si `y < n'`, `y` es un predecesor de `n'`. La hipótesis de inducción `ih`
          -- nos dice que `n'` es accesible, lo que implica que todos sus
          -- predecesores también lo son. Usamos `Acc.inv` para aplicar esta propiedad.
          exact Acc.inv ih h_lt_y_n'
        · -- Caso 2: y = n'.
          -- Si `y = n'`, entonces `y` es accesible porque `n'` es accesible (por `ih`).
          rw [h_eq_y_n']
          exact ih

    /--
      Teorema final que establece que la relación `lt₀` es bien fundada (`WellFounded`).
      Una relación es bien fundada si todos los elementos de su dominio son accesibles.
      La prueba consiste en aplicar el lema `acc_lt_wf` a cualquier `n`.
    -/
    theorem well_founded_lt : WellFounded lt₀ :=
      WellFounded.intro acc_lt_wf

    instance : WellFoundedRelation ℕ₀ where
      rel := lt₀
      wf := well_founded_lt

    /--
      El Principio de Buen Orden para ℕ₀.
      Afirma que todo conjunto no vacío de números (descrito por una propiedad `P`)
      contiene un único elemento mínimo. Es una consecuencia directa de `well_founded_lt`.
    -/
    theorem well_ordering_principle (P : ℕ₀ → Prop) (h_nonempty : ∃ k, P k) :
      ∃¹ (n : ℕ₀), (P n) ∧ ∀ (m : ℕ₀), (P m) → (n ≤ m )
        := by
      -- 1. Existencia del mínimo (delegamos a la versión de Order.lean)
      have h_minimal_exists : ∃ n, P n ∧ ∀ m, lt₀ m n → ¬ P m :=
        Peano.Order.well_ordering_principle h_nonempty
      obtain ⟨n, h_Pn, h_n_is_minimal⟩ := h_minimal_exists

      -- n es mínimo (menor o igual a todo m con P m)
      have h_least : ∀ m, P m → le₀ n m := fun m h_Pm =>
        match trichotomy n m with
        | Or.inl h_lt => Or.inl h_lt
        | Or.inr (Or.inl h_eq) => Or.inr h_eq
        | Or.inr (Or.inr h_gt) => absurd h_Pm (h_n_is_minimal m h_gt)

      -- 2. Existencia + unicidad
      exists n
      exact ⟨⟨h_Pn, h_least⟩, fun n' ⟨h_Pn', h_least'⟩ =>
        le_antisymm n' n (h_least' n h_Pn) (h_least n' h_Pn')⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § Strong recursion / strong induction
    -- ══════════════════════════════════════════════════════════════════

    /-- Recursión fuerte sobre ℕ₀: para construir `C n` podemos
        suponer que ya tenemos `C k` para todo `k < n`. -/
    def strongRecOn {C : ℕ₀ → Sort _} (n : ℕ₀)
        (h : ∀ m : ℕ₀, (∀ k : ℕ₀, lt₀ k m → C k) → C m) : C n :=
      well_founded_lt.fix h n

    /-- Inducción fuerte sobre ℕ₀ (caso proposicional). -/
    theorem strongInductionOn {P : ℕ₀ → Prop} (n : ℕ₀)
        (h : ∀ m : ℕ₀, (∀ k : ℕ₀, lt₀ k m → P k) → P m) : P n :=
      strongRecOn n h

  end WellFounded

end Peano

export Peano.WellFounded (
  well_founded_lt
  well_ordering_principle
  strongRecOn
  strongInductionOn
)
