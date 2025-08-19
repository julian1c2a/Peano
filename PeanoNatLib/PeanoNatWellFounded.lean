-- PeanoNatLib/PeanoNatWellFounded.lean
--
-- Este fichero contiene la prueba de que el orden estricto '<'
-- en ℕ₀ es una relación bien fundada. La demostración se construye
-- directamente a partir de la estructura inductiva de ℕ₀, sin
-- depender del isomorfismo con Nat para la prueba principal.

-- También demostramos que el orden estricto '<' en ℕ₀ es un buen orden.

import Init.WF
import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin

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
      ∃¹ n, P n ∧ ∀ m, P m → Le n m := by
      -- 1. Existencia del mínimo
      -- `WellFounded.min_exists` nos da la prueba de que existe un elemento minimal.
      have h_minimal_exists : ∃ n, P n ∧ ∀ m, Lt m n → ¬ P m :=
        @_root_.WellFounded.min_exists well_founded_lt P h_nonempty

      -- Usamos `choose` (definido en PeanoNatLib) para obtener un término `n` que satisface esta propiedad.
      let n := choose h_minimal_exists
      have h_n_props : P n ∧ ∀ m, Lt m n → ¬ P m := choose_spec h_minimal_exists
      let h_Pn := h_n_props.left
      let h_n_is_minimal := h_n_props.right

      -- Probamos que este `n` es un elemento mínimo (el más pequeño o igual).
      have h_exists : ∃ n_min, P n_min ∧ ∀ m, P m → Le n_min m := by
        exists n
        exact ⟨h_Pn, fun m h_Pm =>
          match trichotomy n m with
          | Or.inl h_lt_nm => Or.inl h_lt_nm -- Caso n < m, que implica n ≤ m.
          | Or.inr (Or.inl h_eq_nm) => Or.inr h_eq_nm -- Caso n = m, que implica n ≤ m.
          | Or.inr (Or.inr h_lt_mn) => -- Caso m < n.
            -- Esto contradice que `n` es minimal, porque hemos encontrado
            -- un `m` más pequeño que también tiene la propiedad `P`.
            False.elim (h_n_is_minimal m h_lt_mn h_Pm)
        ⟩

      -- 2. Unicidad del mínimo
      -- Extraemos el mínimo `n_min` que acabamos de probar que existe.
      rcases h_exists with ⟨n_min, ⟨h_Pn_min, h_is_least⟩⟩
      exists n_min
      constructor
      · -- La parte de existencia que ya probamos.
        exact ⟨h_Pn_min, h_is_least⟩
      · -- La parte de unicidad.
        intro n' ⟨h_Pn', h_is_least'⟩
        -- Asumimos que `n'` es otro mínimo.
        -- Como `n_min` es un mínimo y `P n'`, entonces `Le n_min n'`.
        have h_le1 : Le n_min n' := h_is_least n' h_Pn'
        -- Como `n'` es un mínimo y `P n_min`, entonces `Le n' n_min`.
        have h_le2 : Le n' n_min := h_is_least' n_min h_Pn_min
        -- Por la antisimetría de `Le`, si `n_min ≤ n'` y `n' ≤ n_min`,
        -- entonces `n_min = n'`.
        exact le_antisymm n' n_min h_le2 h_le1

  end WellFounded

end Peano

export Peano.WellFounded (
  well_founded_lt
  well_ordering_principle
)
