/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Foundation/CantorPairing.lean
--
-- Enuncia y bosqueja la prueba de que ℕ₀ × ℕ₀ ≅ ℕ₀ (apareamiento de Cantor).
-- Las pruebas aritméticas están marcadas como sorry pendientes de completar.
--
-- NOTAS PARA COMPLETAR:
--  · triag_succ : requiere  div_add_exact  y  two_dvd_mul_succ
--  · antidiag_exists : el caso succ necesita T estrictamente creciente
--  · antidiag_unique : el caso lt/gt por tricotomía de lt₀
--  · fst_pair : requiere  sub_add_left : a + b - a = b
--  · snd_pair : requiere  add_sub_cancel_left : (m + n) - m = n
--  · pair_surj : combina los anteriores con antidiag_spec

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Arith
import Peano.Prelim.Classical

namespace Peano
  open Peano

  namespace Foundation
    open Foundation

  -- ─────────────────────────────────────────────────────────────────────────
  -- 1. Número triangular T(n) = n*(n+1)/2
  -- ─────────────────────────────────────────────────────────────────────────

  /-- T(n) = n*(n+1)/2. La división es exacta (uno de n, n+1 es par). -/
  def triag (n : ℕ₀) : ℕ₀ := (n * (ℕ₀.succ n)) / (ℕ₀.succ (ℕ₀.succ ℕ₀.zero))

  theorem triag_zero : triag 𝟘 = 𝟘 := by sorry

  theorem triag_succ (n : ℕ₀) : triag (σ n) = triag n + σ n := by sorry

  theorem triag_strict_mono {m n : ℕ₀} (h : Peano.StrictOrder.lt₀ m n) :
      Peano.StrictOrder.lt₀ (triag m) (triag n) := by sorry

  theorem triag_le_of_le {m n : ℕ₀} (h : Peano.Order.le₀ m n) :
      Peano.Order.le₀ (triag m) (triag n) := by sorry

  -- ─────────────────────────────────────────────────────────────────────────
  -- 2. Función de apareamiento de Cantor
  -- ─────────────────────────────────────────────────────────────────────────

  /-- pair(m,n) = T(m+n) + m. -/
  def pair (m n : ℕ₀) : ℕ₀ := triag (m + n) + m

  theorem triag_le_pair (m n : ℕ₀) :
      Peano.Order.le₀ (triag (m + n)) (pair m n) := by sorry

  theorem pair_lt_triag_succ (m n : ℕ₀) :
      Peano.StrictOrder.lt₀ (pair m n) (triag (σ (m + n))) := by sorry

  -- ─────────────────────────────────────────────────────────────────────────
  -- 3. Anti-diagonal
  -- ─────────────────────────────────────────────────────────────────────────

  theorem antidiag_exists (z : ℕ₀) :
      ∃ w : ℕ₀,
        Peano.Order.le₀ (triag w) z ∧
        Peano.StrictOrder.lt₀ z (triag (σ w)) := by sorry

  theorem antidiag_unique (z : ℕ₀) :
      ExistsUnique (fun w =>
        Peano.Order.le₀ (triag w) z ∧
        Peano.StrictOrder.lt₀ z (triag (σ w))) := by sorry

  /-- La anti-diagonal de z: único w con T(w) ≤ z < T(w+1). -/
  noncomputable def antidiag (z : ℕ₀) : ℕ₀ :=
    choose_unique (antidiag_unique z)

  theorem antidiag_spec (z : ℕ₀) :
      Peano.Order.le₀ (triag (antidiag z)) z ∧
      Peano.StrictOrder.lt₀ z (triag (σ (antidiag z))) :=
    choose_spec_unique (antidiag_unique z)

  theorem antidiag_pair (m n : ℕ₀) : antidiag (pair m n) = m + n :=
    choose_uniq (antidiag_unique (pair m n)) ⟨triag_le_pair m n, pair_lt_triag_succ m n⟩

  -- ─────────────────────────────────────────────────────────────────────────
  -- 4. Proyecciones y biyectividad
  -- ─────────────────────────────────────────────────────────────────────────

  /-- Primera proyección (columna). -/
  noncomputable def fst (z : ℕ₀) : ℕ₀ := z - triag (antidiag z)

  /-- Segunda proyección (fila - columna). -/
  noncomputable def snd (z : ℕ₀) : ℕ₀ := antidiag z - fst z

  /-- fst(pair m n) = m. -/
  theorem pair_fst (m n : ℕ₀) : fst (pair m n) = m := by sorry

  /-- snd(pair m n) = n. -/
  theorem pair_snd (m n : ℕ₀) : snd (pair m n) = n := by sorry

  /-- pair(fst z, snd z) = z  (sobreyectividad). -/
  theorem pair_surj (z : ℕ₀) : pair (fst z) (snd z) = z := by sorry

  end Foundation

end Peano
