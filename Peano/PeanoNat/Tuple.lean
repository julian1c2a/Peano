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

  /-- Tupla heterogénea específica para el sistema numérico.
      El esquema es una lista de etiquetas `Nats` que Lean convierte a tipos. -/
  def NatsTuple : List Nats → Type
  | [] => Unit
  | (t :: ts) => t × NatsTuple ts

  /-- Tupla homogénea genérica. Construye `α^n`. Todos los elementos son de tipo `α`. -/
  def GTuple (α : Type) : ℕ₀ → Type
  | 𝟘 => Unit
  | σ n => α × GTuple α n

  /-- Tupla heterogénea genérica (HList). El esquema es una lista explícita de tipos.
      Permite instanciar, por ejemplo: `HTuple [ℕ₀, ℕ₁, Bool]`. -/
  def HTuple : List Type → Type
  | [] => Unit
  | (α :: αs) => α × HTuple αs
  -- ══════════════════════════════════════════════════════════════════
  -- § 2. Constructores y proyecciones
  -- ══════════════════════════════════════════════════════════════════

  /-- Constructor de tupla vacía. -/
  def emptyTuple : Tuple 𝟘 := ()

  /-- Constructor de tupla por concatenación (cons). -/
  def consTuple {n : ℕ₀}
    (x : ℕ₀) (xs : Tuple n) :
      Tuple (σ n)
        :=
    (x, xs)

  /-- Proyección: obtener la cabeza de una tupla no vacía. -/
  def headTuple {n : ℕ₀}
    (t : Tuple (σ n)) :
      ℕ₀
        :=
    t.1

  /-- Proyección: obtener la cola de una tupla no vacía. -/
  def tailTuple {n : ℕ₀}
    (t : Tuple (σ n)) :
      Tuple n
        :=
    t.2

  -- Notación para tuplas
  notation "⟨⟩" => emptyTuple
  notation "⟨" x "⟩" => consTuple x emptyTuple

  /-- Función para construir una tupla desde una función. -/
  def mkTuple : (n : ℕ₀) → (proj : ℕ₀ → ℕ₀) → Tuple n
    | 𝟘, _ => emptyTuple
    | σ n, proj => consTuple (proj 𝟘) (mkTuple n (fun k => proj (σ k)))

  /-- Constructor de tupla vacía (NatsTuple). -/
  def emptyNatsTuple : NatsTuple [] := ()

  /-- Constructor por concatenación (NatsTuple). -/
  def consNatsTuple {t : Nats} {ts : List Nats}
    (x : t) (xs : NatsTuple ts) :
      NatsTuple (t :: ts)
        :=
    (x, xs)

  /-- Proyección de la cabeza (NatsTuple). -/
  def headNatsTuple {t : Nats} {ts : List Nats}
    (x : NatsTuple (t :: ts)) :
      t
        :=
    x.1

  /-- Proyección de la cola (NatsTuple). -/
  def tailNatsTuple {t : Nats} {ts : List Nats}
    (x : NatsTuple (t :: ts)) :
      NatsTuple ts
        :=
    x.2

  /-- Constructor de tupla vacía (GTuple). -/
  def emptyGTuple {α : Type} : GTuple α 𝟘 := ()

  /-- Constructor por concatenación (GTuple). -/
  def consGTuple {α : Type} {n : ℕ₀}
    (x : α) (xs : GTuple α n) :
      GTuple α (σ n)
        :=
    (x, xs)

  /-- Proyección de la cabeza (GTuple). -/
  def headGTuple {α : Type} {n : ℕ₀}
    (x : GTuple α (σ n)) :
      α
        :=
    x.1

  /-- Proyección de la cola (GTuple). -/
  def tailGTuple {α : Type} {n : ℕ₀}
    (x : GTuple α (σ n)) :
      GTuple α n
        :=
    x.2

  /-- Construir una GTuple desde una función. -/
  def mkGTuple {α : Type} : (n : ℕ₀) → (proj : ℕ₀ → α) → GTuple α n
    | 𝟘, _ => emptyGTuple
    | σ n, proj => consGTuple (proj 𝟘) (mkGTuple n (fun k => proj (σ k)))

  /-- Constructor de tupla vacía (HTuple). -/
  def emptyHTuple : HTuple [] := ()

  /-- Constructor por concatenación (HTuple). -/
  def consHTuple {α : Type} {ts : List Type}
    (x : α) (xs : HTuple ts) :
      HTuple (α :: ts)
        :=
    (x, xs)

  /-- Proyección de la cabeza (HTuple). -/
  def headHTuple {α : Type} {ts : List Type}
    (x : HTuple (α :: ts)) :
      α
        :=
    x.1

  /-- Proyección de la cola (HTuple). -/
  def tailHTuple {α : Type} {ts : List Type}
    (x : HTuple (α :: ts)) :
      HTuple ts
        :=
    x.2

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

  -- Instancias auxiliares para Nats
  instance instDecidableEqNatsType : (t : Nats) → DecidableEq t
    | Nats.ℕ₀ => inferInstance
    | Nats.ℕ₁ => inferInstance
    | Nats.ℕ₂ => inferInstance

  instance instReprNatsType : (t : Nats) → Repr t
    | Nats.ℕ₀ => inferInstance
    | Nats.ℕ₁ => inferInstance
    | Nats.ℕ₂ => inferInstance

  /-- Igualdad decidible para NatsTuple. -/
  instance natsTupleDecEq : (ts : List Nats) → DecidableEq (NatsTuple ts)
    | [] => fun _ _ => isTrue rfl
    | _ :: ts => fun t1 t2 =>
        match decEq t1.1 t2.1, natsTupleDecEq ts t1.2 t2.2 with
        | isTrue h1, isTrue h2 => isTrue (Prod.ext h1 h2)
        | isFalse h1, _ => isFalse (fun h => h1 (congrArg Prod.fst h))
        | _, isFalse h2 => isFalse (fun h => h2 (congrArg Prod.snd h))

  /-- Representación para NatsTuple. -/
  instance natsTupleRepr : (ts : List Nats) → Repr (NatsTuple ts)
    | [] => ⟨fun _ _ => "⟨⟩"⟩
    | _ :: ts => ⟨fun tup _ =>
        let head := repr tup.1
        let tailRepr := (natsTupleRepr ts).reprPrec tup.2 0
        let tailStr := toString tailRepr
        if tailStr = "⟨⟩" then
          s!"⟨{head}⟩"
        else
          s!"⟨{head}, {tailStr.drop 1}"⟩

  /-- Igualdad decidible para GTuple. -/
  instance gtupleDecEq {α : Type} [DecidableEq α] : (n : ℕ₀) → DecidableEq (GTuple α n)
    | 𝟘 => fun _ _ => isTrue rfl
    | σ n => fun t1 t2 =>
        match decEq t1.1 t2.1, gtupleDecEq n t1.2 t2.2 with
        | isTrue h1, isTrue h2 => isTrue (Prod.ext h1 h2)
        | isFalse h1, _ => isFalse (fun h => h1 (congrArg Prod.fst h))
        | _, isFalse h2 => isFalse (fun h => h2 (congrArg Prod.snd h))

  /-- Representación para GTuple. -/
  instance gtupleRepr {α : Type} [Repr α] : (n : ℕ₀) → Repr (GTuple α n)
    | 𝟘 => ⟨fun _ _ => "⟨⟩"⟩
    | σ n => ⟨fun tup _ =>
        let head := repr tup.1
        let tailRepr := (gtupleRepr n).reprPrec tup.2 0
        let tailStr := toString tailRepr
        if tailStr = "⟨⟩" then
          s!"⟨{head}⟩"
        else
          s!"⟨{head}, {tailStr.drop 1}"⟩

  -- Nota: HTupleDecidableEq ya está implementada en la sección § 7.

  class HTupleRepr (ts : List Type) where
    reprPrec : HTuple ts → Nat → Std.Format

  instance instHTupleReprNil : HTupleRepr [] where
    reprPrec _ _ := "⟨⟩"

  instance instHTupleReprCons {α : Type} {ts : List Type} [Repr α] [HTupleRepr ts] : HTupleRepr (α :: ts) where
    reprPrec tup _ :=
      let head := repr tup.1
      let tailRepr := HTupleRepr.reprPrec tup.2 0
      let tailStr := toString tailRepr
      if tailStr = "⟨⟩" then
        s!"⟨{head}⟩"
      else
        s!"⟨{head}, {tailStr.drop 1}"

  instance htupleRepr {ts : List Type} [HTupleRepr ts] : Repr (HTuple ts) :=
    ⟨HTupleRepr.reprPrec⟩

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

  -- ══════════════════════════════════════════════════════════════════
  -- § 5. Orden lexicográfico para NatsTuple
  -- ══════════════════════════════════════════════════════════════════

  /-- Extrae el valor `ℕ₀` subyacente de cualquier elemento de un `NatsTuple` de forma dinámica. -/
  def natsVal : (t : Nats) → t → ℕ₀
    | Nats.ℕ₀, x => x
    | Nats.ℕ₁, x => x.val
    | Nats.ℕ₂, x => x.val.val

  /-- Orden lexicográfico estricto para NatsTuple apoyado en los valores `ℕ₀`. -/
  def natsLexLt : {ts : List Nats} → NatsTuple ts → NatsTuple ts → Prop
    | [], _, _ => False
    | (t :: _ts), (x, xs), (y, ys) =>
      Lt (natsVal t x) (natsVal t y) ∨ (natsVal t x = natsVal t y ∧ natsLexLt xs ys)

  /-- Orden lexicográfico no estricto para NatsTuple. -/
  def natsLexLe : {ts : List Nats} → NatsTuple ts → NatsTuple ts → Prop
    | [], _, _ => True
    | (t :: _ts), (x, xs), (y, ys) =>
      Lt (natsVal t x) (natsVal t y) ∨ (natsVal t x = natsVal t y ∧ natsLexLe xs ys)

  instance instLTNatsTuple {ts : List Nats} : LT (NatsTuple ts) := ⟨natsLexLt⟩
  instance instLENatsTuple {ts : List Nats} : LE (NatsTuple ts) := ⟨natsLexLe⟩

  instance instDecidableRelLtNatsTuple : {ts : List Nats} → DecidableRel (@natsLexLt ts)
    | [], _, _ => isFalse id
    | t :: _ts, (x, xs), (y, ys) =>
      match decidableLt (natsVal t x) (natsVal t y) with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq (natsVal t x) (natsVal t y) with
        | isTrue h_eq =>
          match instDecidableRelLtNatsTuple xs ys with
          | isTrue h_rest_lt => isTrue (Or.inr ⟨h_eq, h_rest_lt⟩)
          | isFalse h_rest_nlt =>
            isFalse (fun h => (Or.resolve_left h h_nlt).right |> h_rest_nlt)
        | isFalse h_neq =>
          isFalse (fun h => Or.elim h h_nlt (fun h_and => h_neq h_and.left))

  instance instDecidableRelLeNatsTuple : {ts : List Nats} → DecidableRel (@natsLexLe ts)
    | [], _, _ => isTrue trivial
    | t :: _ts, (x, xs), (y, ys) =>
      match decidableLt (natsVal t x) (natsVal t y) with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq (natsVal t x) (natsVal t y) with
        | isTrue h_eq =>
          match instDecidableRelLeNatsTuple xs ys with
          | isTrue h_rest_le => isTrue (Or.inr ⟨h_eq, h_rest_le⟩)
          | isFalse h_rest_nle =>
            isFalse (fun h => (Or.resolve_left h h_nlt).right |> h_rest_nle)
        | isFalse h_neq =>
          isFalse (fun h => Or.elim h h_nlt (fun h_and => h_neq h_and.left))

  -- ══════════════════════════════════════════════════════════════════
  -- § 6. Orden lexicográfico para GTuple
  -- ══════════════════════════════════════════════════════════════════

  /-- Orden lexicográfico estricto para GTuple. -/
  def glexLt {α : Type} [LT α] : {n : ℕ₀} → GTuple α n → GTuple α n → Prop
    | 𝟘, _, _ => False
    | (σ _), (x, xs), (y, ys) => x < y ∨ (x = y ∧ glexLt xs ys)

  /-- Orden lexicográfico no estricto para GTuple. -/
  def glexLe {α : Type} [LT α] : {n : ℕ₀} → GTuple α n → GTuple α n → Prop
    | 𝟘, _, _ => True
    | (σ _), (x, xs), (y, ys) => x < y ∨ (x = y ∧ glexLe xs ys)

  instance instLTGTuple {α : Type} [LT α] {n : ℕ₀} : LT (GTuple α n) := ⟨glexLt⟩
  instance instLEGTuple {α : Type} [LT α] {n : ℕ₀} : LE (GTuple α n) := ⟨glexLe⟩

  instance instDecidableRelLtGTuple {α : Type} [LT α] [DecidableEq α] [DecidableRel (@LT.lt α _)] : {n : ℕ₀} → DecidableRel (@glexLt α _ n)
    | 𝟘, _, _ => isFalse id
    | σ _, (x, xs), (y, ys) =>
      if h_lt : x < y then isTrue (Or.inl h_lt)
      else if h_eq : x = y then
        match instDecidableRelLtGTuple xs ys with
        | isTrue h_rest_lt => isTrue (Or.inr ⟨h_eq, h_rest_lt⟩)
        | isFalse h_rest_nlt => isFalse (fun h => (Or.resolve_left h h_lt).right |> h_rest_nlt)
      else isFalse (fun h => Or.elim h h_lt (fun h_and => h_eq h_and.left))

  instance instDecidableRelLeGTuple {α : Type} [LT α] [DecidableEq α] [DecidableRel (@LT.lt α _)] : {n : ℕ₀} → DecidableRel (@glexLe α _ n)
    | 𝟘, _, _ => isTrue trivial
    | σ _, (x, xs), (y, ys) =>
      if h_lt : x < y then isTrue (Or.inl h_lt)
      else if h_eq : x = y then
        match instDecidableRelLeGTuple xs ys with
        | isTrue h_rest_le => isTrue (Or.inr ⟨h_eq, h_rest_le⟩)
        | isFalse h_rest_nle => isFalse (fun h => (Or.resolve_left h h_lt).right |> h_rest_nle)
      else isFalse (fun h => Or.elim h h_lt (fun h_and => h_eq h_and.left))

  -- ══════════════════════════════════════════════════════════════════
  -- § 7. Igualdad y Orden lexicográfico para HTuple
  -- ══════════════════════════════════════════════════════════════════

  class HTupleDecidableEq (ts : List Type) where
    decEq : (x y : HTuple ts) → Decidable (x = y)

  instance instHTupleDecEqNil : HTupleDecidableEq [] where
    decEq | (), () => isTrue rfl

  instance instHTupleDecEqCons {α : Type} {ts : List Type} [DecidableEq α] [HTupleDecidableEq ts] : HTupleDecidableEq (α :: ts) where
    decEq x y :=
      match decEq x.1 y.1 with
      | isTrue h1 =>
        match HTupleDecidableEq.decEq x.2 y.2 with
        | isTrue h2 => isTrue (Prod.ext h1 h2)
        | isFalse h2 => isFalse (fun h => h2 (congrArg Prod.snd h))
      | isFalse h1 => isFalse (fun h => h1 (congrArg Prod.fst h))

  instance instDecidableEqHTuple {ts : List Type} [HTupleDecidableEq ts] : DecidableEq (HTuple ts) :=
    HTupleDecidableEq.decEq

  class HTupleLT (ts : List Type) where
    lt : HTuple ts → HTuple ts → Prop

  instance instHTupleLTNil : HTupleLT [] where
    lt _ _ := False

  instance instHTupleLTCons {α : Type} {ts : List Type} [LT α] [HTupleLT ts] : HTupleLT (α :: ts) where
    lt x y := x.1 < y.1 ∨ (x.1 = y.1 ∧ HTupleLT.lt x.2 y.2)

  instance instLTHTuple {ts : List Type} [HTupleLT ts] : LT (HTuple ts) := ⟨HTupleLT.lt⟩

  class HTupleLE (ts : List Type) where
    le : HTuple ts → HTuple ts → Prop

  instance instHTupleLENil : HTupleLE [] where
    le _ _ := True

  instance instHTupleLECons {α : Type} {ts : List Type} [LT α] [HTupleLE ts] : HTupleLE (α :: ts) where
    le x y := x.1 < y.1 ∨ (x.1 = y.1 ∧ HTupleLE.le x.2 y.2)

  instance instLEHTuple {ts : List Type} [HTupleLE ts] : LE (HTuple ts) := ⟨HTupleLE.le⟩

  class HTupleDecidableLT (ts : List Type) [HTupleLT ts] where
    decLt : (x y : HTuple ts) → Decidable (x < y)

  instance instHTupleDecLTNil : HTupleDecidableLT [] where
    decLt _ _ := isFalse id

  instance instHTupleDecLTCons {α : Type} {ts : List Type} [LT α] [DecidableEq α] [DecidableRel (@LT.lt α _)]
      [HTupleLT ts] [HTupleDecidableLT ts] : HTupleDecidableLT (α :: ts) where
    decLt x y :=
      if h_lt : x.1 < y.1 then isTrue (Or.inl h_lt)
      else if h_eq : x.1 = y.1 then
        match HTupleDecidableLT.decLt x.2 y.2 with
        | isTrue h_rest_lt => isTrue (Or.inr ⟨h_eq, h_rest_lt⟩)
        | isFalse h_rest_nlt => isFalse (fun h => (Or.resolve_left h h_lt).right |> h_rest_nlt)
      else isFalse (fun h => Or.elim h h_lt (fun h_and => h_eq h_and.left))

  instance instDecidableRelLtHTuple {ts : List Type} [HTupleLT ts] [HTupleDecidableLT ts] : DecidableRel (@LT.lt (HTuple ts) _) :=
    HTupleDecidableLT.decLt

  class HTupleDecidableLE (ts : List Type) [HTupleLE ts] where
    decLe : (x y : HTuple ts) → Decidable (x ≤ y)

  instance instHTupleDecLENil : HTupleDecidableLE [] where
    decLe _ _ := isTrue trivial

  instance instHTupleDecLECons {α : Type} {ts : List Type} [LT α] [DecidableEq α] [DecidableRel (@LT.lt α _)]
      [HTupleLE ts] [HTupleDecidableLE ts] : HTupleDecidableLE (α :: ts) where
    decLe x y :=
      if h_lt : x.1 < y.1 then isTrue (Or.inl h_lt)
      else if h_eq : x.1 = y.1 then
        match HTupleDecidableLE.decLe x.2 y.2 with
        | isTrue h_rest_le => isTrue (Or.inr ⟨h_eq, h_rest_le⟩)
        | isFalse h_rest_nle => isFalse (fun h => (Or.resolve_left h h_lt).right |> h_rest_nle)
      else isFalse (fun h => Or.elim h h_lt (fun h_and => h_eq h_and.left))

  instance instDecidableRelLeHTuple {ts : List Type} [HTupleLE ts] [HTupleDecidableLE ts] : DecidableRel (@LE.le (HTuple ts) _) :=
    HTupleDecidableLE.decLe

end Peano

export Peano (
  Tuple
  NatsTuple
  GTuple
  HTuple
  emptyTuple
  consTuple
  headTuple
  tailTuple
  mkTuple
  tupleDecEq
  tupleRepr
  emptyNatsTuple
  consNatsTuple
  headNatsTuple
  tailNatsTuple
  instDecidableEqNatsType
  instReprNatsType
  natsTupleDecEq
  natsTupleRepr
  emptyGTuple
  consGTuple
  headGTuple
  tailGTuple
  mkGTuple
  gtupleDecEq
  gtupleRepr
  emptyHTuple
  consHTuple
  headHTuple
  tailHTuple
  HTupleRepr
  instHTupleReprNil
  instHTupleReprCons
  htupleRepr
  lexLt
  lexLe
  instLTTuple
  instLETuple
  instDecidableRelLtTuple
  instDecidableRelLeTuple
  natsVal
  natsLexLt
  natsLexLe
  instLTNatsTuple
  instLENatsTuple
  instDecidableRelLtNatsTuple
  instDecidableRelLeNatsTuple
  glexLt
  glexLe
  instLTGTuple
  instLEGTuple
  instDecidableRelLtGTuple
  instDecidableRelLeGTuple
  HTupleDecidableEq
  instHTupleDecEqNil
  instHTupleDecEqCons
  instDecidableEqHTuple
  HTupleLT
  instHTupleLTNil
  instHTupleLTCons
  instLTHTuple
  HTupleLE
  instHTupleLENil
  instHTupleLECons
  instLEHTuple
  HTupleDecidableLT
  instHTupleDecLTNil
  instHTupleDecLTCons
  instDecidableRelLtHTuple
  HTupleDecidableLE
  instHTupleDecLENil
  instHTupleDecLECons
  instDecidableRelLeHTuple
)
