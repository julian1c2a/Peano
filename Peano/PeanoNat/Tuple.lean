/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Tuple.lean
-- Tuplas de naturales de Peano de longitud finita.
--
-- § 1. Definición de `Tuple n`
-- § 2. Constructores y proyecciones
-- § 3. Igualdad decidible y representación
-- § 4. Orden lexicográfico (lexLt, lexLe)

import Peano.PeanoNat
import Peano.PeanoNat.StrictOrder -- For Lt

namespace Peano

  /-- Tuplas de naturales de Peano de longitud `n`.
      `Tuple 𝟘` es `Unit`, `Tuple (σ n)` es `ℕ₀ × Tuple n`. -/
  def Tuple : ℕ₀ → Type
    | 𝟘 => Unit
    | σ n => ℕ₀ × Tuple n

  -- ══════════════════════════════════════════════════════════════════
  -- § 2. Constructores y proyecciones
  -- ══════════════════════════════════════════════════════════════════

  /-- Constructor de tupla vacía. -/
  def emptyTuple : Tuple 𝟘 := ()

  /-- Constructor de tupla por concatenación (cons). -/
  def consTuple {n : ℕ₀} (x : ℕ₀) (xs : Tuple n) : Tuple (σ n) :=
    (x, xs)

  /-- Proyección: obtener la cabeza de una tupla no vacía. -/
  def headTuple {n : ℕ₀} (t : Tuple (σ n)) : ℕ₀ :=
    t.1

  /-- Proyección: obtener la cola de una tupla no vacía. -/
  def tailTuple {n : ℕ₀} (t : Tuple (σ n)) : Tuple n :=
    t.2

  -- Notación para tuplas
  notation "⟨⟩" => emptyTuple
  notation "⟨" x "⟩" => consTuple x emptyTuple

  /-- Función para construir una tupla desde una función. -/
  def mkTuple : (n : ℕ₀) → (proj : ℕ₀ → ℕ₀) → Tuple n
    | 𝟘, _ => emptyTuple
    | σ n, proj => consTuple (proj 𝟘) (mkTuple n (fun k => proj (σ k)))

  -- ══════════════════════════════════════════════════════════════════
  -- § 3. Igualdad decidible y representación
  -- ══════════════════════════════════════════════════════════════════

  /-- Igualdad decidible para tuplas. -/
  instance tupleDecEq : (n : ℕ₀) → DecidableEq (Tuple n)
    | 𝟘 => fun _ _ => isTrue rfl
    | σ n => fun t1 t2 =>
        match decEq t1.1 t2.1, tupleDecEq n t1.2 t2.2 with
        | isTrue h1, isTrue h2 => isTrue (by
            have : t1.1 = t2.1 := h1
            have : t1.2 = t2.2 := h2
            cases t1; cases t2
            congr)
        | isFalse h1, _ => isFalse (fun h => h1 (by cases h; rfl))
        | _, isFalse h2 => isFalse (fun h => h2 (by cases h; rfl))

  /-- Representación para tuplas. -/
  instance tupleRepr : (n : ℕ₀) → Repr (Tuple n)
    | 𝟘 => ⟨fun _ _ => "⟨⟩"⟩
    | σ n => ⟨fun t _ =>
        let head := repr t.1
        let tailRepr := (tupleRepr n).reprPrec t.2 0
        let tailStr := toString tailRepr
        if tailStr = "⟨⟩" then
          s!"⟨{head}⟩"
        else
          s!"⟨{head}, {tailStr.drop 1}"⟩

  -- ══════════════════════════════════════════════════════════════════
  -- § 4. Orden lexicográfico (lexLt, lexLe)
  -- ══════════════════════════════════════════════════════════════════

  open Peano.StrictOrder

  /-- Orden lexicográfico estricto para tuplas. -/
  def lexLt : {n : ℕ₀} → Tuple n → Tuple n → Prop
    | 𝟘, _, _ => False
    | (σ _), (x, xs), (y, ys) => Lt x y ∨ (x = y ∧ lexLt xs ys)

  /-- Orden lexicográfico no estricto para tuplas. -/
  def lexLe : {n : ℕ₀} → Tuple n → Tuple n → Prop
    | 𝟘, _, _ => True
    | (σ _), (x, xs), (y, ys) => Lt x y ∨ (x = y ∧ lexLe xs ys)

  instance instLTTuple {n : ℕ₀} : LT (Tuple n) := ⟨lexLt⟩
  instance instLETuple {n : ℕ₀} : LE (Tuple n) := ⟨lexLe⟩

  instance instDecidableRelLtTuple : {n : ℕ₀} → DecidableRel (@lexLt n)
    | 𝟘, _, _ => isFalse id
    | σ _, (x, xs), (y, ys) =>
      match decidableLt x y with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq x y with
        | isTrue h_eq =>
          match instDecidableRelLtTuple xs ys with
          | isTrue h_rest_lt => isTrue (Or.inr ⟨h_eq, h_rest_lt⟩)
          | isFalse h_rest_nlt =>
            isFalse (fun h => (Or.resolve_left h h_nlt).right |> h_rest_nlt)
        | isFalse h_neq =>
          isFalse (fun h => Or.elim h h_nlt (fun h_and => h_neq h_and.left))

  instance instDecidableRelLeTuple : {n : ℕ₀} → DecidableRel (@lexLe n)
    | 𝟘, _, _ => isTrue trivial
    | σ _, (x, xs), (y, ys) =>
      match decidableLt x y with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq x y with
        | isTrue h_eq =>
          match instDecidableRelLeTuple xs ys with
          | isTrue h_rest_le => isTrue (Or.inr ⟨h_eq, h_rest_le⟩)
          | isFalse h_rest_nle =>
            isFalse (fun h => (Or.resolve_left h h_nlt).right |> h_rest_nle)
        | isFalse h_neq =>
          isFalse (fun h => Or.elim h h_nlt (fun h_and => h_neq h_and.left))

end Peano

export Peano (
  Tuple
  emptyTuple
  consTuple
  headTuple
  tailTuple
  mkTuple
  tupleDecEq
  tupleRepr
  lexLt
  lexLe
  instLTTuple
  instLETuple
  instDecidableRelLtTuple
  instDecidableRelLeTuple
)
