/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Tuple.lean
-- Tuplas polimórficas de longitud finita.
--
-- § 1. Definición de `Tuple α n`
-- § 2. Constructores y proyecciones
-- § 3. Igualdad decidible y representación
-- § 4. Orden lexicográfico (lexLt, lexLe) y propiedades
-- § 5. Orden lexicográfico para NatsTuple
-- § 6. Igualdad y Orden lexicográfico para HTuple

import Peano.PeanoNat
import Peano.PeanoNat.StrictOrder

namespace Peano

  -- ══════════════════════════════════════════════════════════════════
  -- § 1. Definiciones de tipos tupla
  -- ══════════════════════════════════════════════════════════════════

  /-- Tupla homogénea polimórfica de longitud `n` sobre el tipo `α`.
      `Tuple α 𝟘` es `Unit`, `Tuple α (σ n)` es `α × Tuple α n`. -/
  def Tuple (α : Type) : ℕ₀ → Type
    | .zero => Unit
    | .succ n => α × Tuple α n

  /-- Tupla heterogénea específica para el sistema numérico.
      El esquema es una lista de etiquetas `Nats` que Lean convierte a tipos. -/
  def NatsTuple : List Nats → Type
  | [] => Unit
  | (t :: ts) => t.toType × NatsTuple ts

  /-- Tupla heterogénea genérica (HList). El esquema es una lista explícita de tipos.
      Permite instanciar, por ejemplo: `HTuple [ℕ₀, ℕ₁, Bool]`. -/
  def HTuple : List Type → Type
  | [] => Unit
  | (α :: αs) => α × HTuple αs

  -- ══════════════════════════════════════════════════════════════════
  -- § 2. Constructores y proyecciones
  -- ══════════════════════════════════════════════════════════════════

  /-- Constructor de tupla vacía. -/
  def emptyTuple {α : Type} : Tuple α 𝟘 := ()

  /-- Constructor de tupla por concatenación (cons). -/
  def consTuple {α : Type} {n : ℕ₀}
    (x : α) (xs : Tuple α n) :
      Tuple α (σ n)
        :=
    (x, xs)

  /-- Proyección: obtener la cabeza de una tupla no vacía. -/
  def headTuple {α : Type} {n : ℕ₀}
    (t : Tuple α (σ n)) :
      α
        :=
    t.1

  /-- Proyección: obtener la cola de una tupla no vacía. -/
  def tailTuple {α : Type} {n : ℕ₀}
    (t : Tuple α (σ n)) :
      Tuple α n
        :=
    t.2

  -- Notación para tuplas
  notation "⟨⟩" => emptyTuple
  notation "⟨" x "⟩" => consTuple x emptyTuple

  /-- Función para construir una tupla desde una función. -/
  def mkTuple {α : Type} : (n : ℕ₀) → (proj : ℕ₀ → α) → Tuple α n
    | .zero, _ => emptyTuple
    | .succ n, proj => consTuple (proj 𝟘) (mkTuple n (fun k => proj (σ k)))

  /-- Constructor de tupla vacía (NatsTuple). -/
  def emptyNatsTuple : NatsTuple [] := ()

  /-- Constructor por concatenación (NatsTuple). -/
  def consNatsTuple {t : Nats} {ts : List Nats}
    (x : Nats.toType t) (xs : NatsTuple ts) :
      NatsTuple (t :: ts)
        :=
    (x, xs)

  /-- Proyección de la cabeza (NatsTuple). -/
  def headNatsTuple {t : Nats} {ts : List Nats}
    (x : NatsTuple (t :: ts)) :
      t.toType
        :=
    x.1

  /-- Proyección de la cola (NatsTuple). -/
  def tailNatsTuple {t : Nats} {ts : List Nats}
    (x : NatsTuple (t :: ts)) :
      NatsTuple ts
        :=
    x.2

  /-- Construir un NatsTuple desde una función. -/
  def mkNatsTuple : (ts : List Nats) → (proj : ℕ₀ → (t : Nats) → Nats.toType t) → NatsTuple ts
    | [], _ => emptyNatsTuple
    | t :: ts, proj => consNatsTuple (proj 𝟘 t) (mkNatsTuple ts (fun k => proj (σ k)))

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

  /-- Construir un HTuple desde una función. -/
  def mkHTuple : (ts : List Type) → (proj : ℕ₀ → (α : Type) → α) → HTuple ts
    | [], _ => emptyHTuple
    | α :: ts, proj => consHTuple (proj 𝟘 α) (mkHTuple ts (fun k => proj (σ k)))

  -- ══════════════════════════════════════════════════════════════════
  -- § 3. Igualdad decidible y representación
  -- ══════════════════════════════════════════════════════════════════

  /-- Igualdad decidible para tuplas polimórficas. -/
  instance tupleDecEq {α : Type} [DecidableEq α] : (n : ℕ₀) → DecidableEq (Tuple α n)
    | .zero => fun _ _ => isTrue rfl
    | .succ n => fun t1 t2 =>
        match decEq t1.1 t2.1, tupleDecEq n t1.2 t2.2 with
        | isTrue h1, isTrue h2 => isTrue (Prod.ext h1 h2)
        | isFalse h1, _ => isFalse (fun h => h1 (congrArg Prod.fst h))
        | _, isFalse h2 => isFalse (fun h => h2 (congrArg Prod.snd h))

  /-- Representación para tuplas polimórficas. -/
  instance tupleRepr {α : Type} [Repr α] : (n : ℕ₀) → Repr (Tuple α n)
    | .zero => ⟨fun _ _ => "⟨⟩"⟩
    | .succ n => ⟨fun t _ =>
        let head := repr t.1
        let tailRepr := (tupleRepr n).reprPrec t.2 0
        let tailStr := toString tailRepr
        if tailStr = "⟨⟩" then
          s!"⟨{head}⟩"
        else
          s!"⟨{head}, {tailStr.drop 1}⟩"⟩

  -- Instancias auxiliares para Nats
  instance instDecidableEqNatsType : (t : Nats) → DecidableEq t
    | Nats.nat0 => inferInstance
    | Nats.nat1 => inferInstance
    | Nats.nat2 => inferInstance

  instance instReprNatsType : (t : Nats) → Repr t
    | Nats.nat0 => inferInstance
    | Nats.nat1 => inferInstance
    | Nats.nat2 => inferInstance

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
          s!"⟨{head}, {tailStr.drop 1}⟩"⟩

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
        s!"⟨{head}, {tailStr.drop 1}⟩"

  instance htupleRepr {ts : List Type} [HTupleRepr ts] : Repr (HTuple ts) :=
    ⟨HTupleRepr.reprPrec⟩

  -- ══════════════════════════════════════════════════════════════════
  -- § 4. Orden lexicográfico para Tuple α n
  -- ══════════════════════════════════════════════════════════════════

  /-- Orden lexicográfico estricto para tuplas polimórficas. -/
  def lexLt {α : Type} [LT α] : {n : ℕ₀} → Tuple α n → Tuple α n → Prop
    | .zero, _, _ => False
    | (.succ _), (x, xs), (y, ys) => x < y ∨ (x = y ∧ lexLt xs ys)

  /-- Orden lexicográfico no estricto para tuplas polimórficas. -/
  def lexLe {α : Type} [LT α] : {n : ℕ₀} → Tuple α n → Tuple α n → Prop
    | .zero, _, _ => True
    | (.succ _), (x, xs), (y, ys) => x < y ∨ (x = y ∧ lexLe xs ys)

  instance instLTTuple {α : Type} [LT α] {n : ℕ₀} : LT (Tuple α n) := ⟨lexLt⟩

  abbrev TupleLE (α : Type) [LT α] (n : ℕ₀) : LE (Tuple α n) := ⟨lexLe⟩

  @[default_instance 100] instance instLETuple {α : Type} [LT α] {n : ℕ₀} : LE (Tuple α n) := TupleLE α n

  instance instDecidableRelLtTuple {α : Type} [LT α] [DecidableEq α]
      [DecidableRel (@LT.lt α _)] :
      {n : ℕ₀} → DecidableRel (@lexLt α _ n)
    | .zero, _, _ => isFalse id
    | .succ _, (x, xs), (y, ys) =>
      if h_lt : x < y then isTrue (Or.inl h_lt)
      else if h_eq : x = y then
        match instDecidableRelLtTuple xs ys with
        | isTrue h_rest_lt => isTrue (Or.inr ⟨h_eq, h_rest_lt⟩)
        | isFalse h_rest_nlt =>
          isFalse (fun h => (Or.resolve_left h h_lt).right |> h_rest_nlt)
      else isFalse (fun h => Or.elim h h_lt (fun h_and => h_eq h_and.left))

  instance instDecidableRelLeTuple {α : Type} [LT α] [DecidableEq α]
      [DecidableRel (@LT.lt α _)] :
      {n : ℕ₀} → DecidableRel (@lexLe α _ n)
    | .zero, _, _ => isTrue trivial
    | .succ _, (x, xs), (y, ys) =>
      if h_lt : x < y then isTrue (Or.inl h_lt)
      else if h_eq : x = y then
        match instDecidableRelLeTuple xs ys with
        | isTrue h_rest_le => isTrue (Or.inr ⟨h_eq, h_rest_le⟩)
        | isFalse h_rest_nle =>
          isFalse (fun h => (Or.resolve_left h h_lt).right |> h_rest_nle)
      else isFalse (fun h => Or.elim h h_lt (fun h_and => h_eq h_and.left))

  /-- Decidabilidad de `LE.le` para `Tuple α n`.
      Esta instancia usa `inline` para que Lean vea directamente `lexLe`. -/
  @[inline] instance instDecidableRelLeTuple' {α : Type} [LT α] [DecidableEq α]
      [DecidableRel (@LT.lt α _)] {n : ℕ₀} :
      DecidableRel (@LE.le (Tuple α n) (instLETuple)) :=
    instDecidableRelLeTuple

  /-- Igualdad decidible para `Tuple α n` con `n` implícito. -/
  instance instDecidableEqTuple {α : Type} [DecidableEq α] {n : ℕ₀} :
      DecidableEq (Tuple α n) := tupleDecEq n

  -- ══════════════════════════════════════════════════════════════════
  -- § 4b. Propiedades del orden lexicográfico y StrictLinearOrder
  -- ══════════════════════════════════════════════════════════════════

  /-- El orden lexicográfico estricto sobre `Tuple α n` es irreflexivo. -/
  theorem lexLt_irrefl {α : Type} [LT α]
      [Std.Irrefl (fun a b : α => a < b)] :
      ∀ {n : ℕ₀} (t : Tuple α n), ¬ lexLt t t
    | .zero, () => id
    | .succ _, (x, xs) => fun h =>
      h.elim (fun h_lt => Std.Irrefl.irrefl x h_lt)
        (fun ⟨_, h_rest⟩ => lexLt_irrefl xs h_rest)

  /-- El orden lexicográfico estricto sobre `Tuple α n` es transitivo. -/
  theorem lexLt_trans {α : Type} [LT α] [DecidableEq α]
      [Trans (fun a b : α => a < b) (fun a b : α => a < b) (fun a b : α => a < b)] :
      ∀ {n : ℕ₀} {a b c : Tuple α n}, lexLt a b → lexLt b c → lexLt a c
    | .zero, _, _, _ => fun h _ => False.elim h
    | .succ _, (_, _xs), (_, _ys), (_, _zs) => fun h_ab h_bc =>
      h_ab.elim
        (fun h_xy =>
          h_bc.elim
            (fun h_yz => Or.inl (Trans.trans h_xy h_yz))
            (fun ⟨h_eq_yz, _⟩ => h_eq_yz ▸ Or.inl h_xy))
        (fun ⟨h_eq_xy, h_xs_ys⟩ =>
          h_bc.elim
            (fun h_yz => h_eq_xy ▸ Or.inl h_yz)
            (fun ⟨h_eq_yz, h_ys_zs⟩ =>
              Or.inr ⟨h_eq_xy ▸ h_eq_yz, lexLt_trans h_xs_ys h_ys_zs⟩))

  /-- El orden lexicográfico estricto sobre `Tuple α n` satisface la tricotomía. -/
  theorem lexLt_trich {α : Type} [LT α] [DecidableEq α]
      [Std.Trichotomous (fun a b : α => a < b)] :
      ∀ {n : ℕ₀} (a b : Tuple α n), ¬ lexLt a b → ¬ lexLt b a → a = b
    | .zero, (), () => fun _ _ => rfl
    | .succ _, (x, xs), (y, ys) => fun h_nab h_nba =>
      have h_eq : x = y :=
        Std.Trichotomous.trichotomous (r := fun a b : α => a < b) x y
          (fun h => h_nab (Or.inl h)) (fun h => h_nba (Or.inl h))
      have h_eq_rest : xs = ys :=
        lexLt_trich xs ys
          (fun h => h_nab (Or.inr ⟨h_eq, h⟩))
          (fun h => h_nba (Or.inr ⟨h_eq.symm, h⟩))
      h_eq ▸ h_eq_rest ▸ rfl

  instance instStrictLinearOrderTuple {α : Type} [LT α] [DecidableEq α]
      [DecidableRel (@LT.lt α _)]
      [Std.Irrefl (fun a b : α => a < b)]
      [Trans (fun a b : α => a < b) (fun a b : α => a < b) (fun a b : α => a < b)]
      [Std.Trichotomous (fun a b : α => a < b)]
      {n : ℕ₀} : StrictLinearOrder (Tuple α n) where
    decLt  := instDecidableRelLtTuple
    irrefl := lexLt_irrefl
    trans  := fun h1 h2 => lexLt_trans h1 h2
    trich  := lexLt_trich

  -- § 4c. Instancias Std.* para Tuple α n

  instance instIrreflTuple {α : Type} [LT α]
      [Std.Irrefl (fun a b : α => a < b)]
      {n : ℕ₀} : Std.Irrefl (fun a b : Tuple α n => a < b) where
    irrefl := lexLt_irrefl

  instance instAsymmTuple {α : Type} [LT α] [DecidableEq α]
      [Std.Irrefl (fun a b : α => a < b)]
      [Trans (fun a b : α => a < b) (fun a b : α => a < b) (fun a b : α => a < b)]
      {n : ℕ₀} : Std.Asymm (fun a b : Tuple α n => a < b) where
    asymm := fun _ _ h1 h2 => lexLt_irrefl _ (lexLt_trans h1 h2)

  instance instTransTuple {α : Type} [LT α] [DecidableEq α]
      [Trans (fun a b : α => a < b) (fun a b : α => a < b) (fun a b : α => a < b)]
      {n : ℕ₀} : Trans (fun a b : Tuple α n => a < b) (fun a b : Tuple α n => a < b)
        (fun a b : Tuple α n => a < b) where
    trans := fun h1 h2 => lexLt_trans h1 h2

  instance instTrichotomousTuple {α : Type} [LT α] [DecidableEq α]
      [Std.Trichotomous (fun a b : α => a < b)]
      {n : ℕ₀} : Std.Trichotomous (fun a b : Tuple α n => a < b) where
    trichotomous := lexLt_trich

  instance instIrreflLTTuple {α : Type} [LT α]
      [Std.Irrefl (fun a b : α => a < b)]
      {n : ℕ₀} : StrictOrder.IrreflLT (Tuple α n) :=
    ⟨fun t h => lexLt_irrefl t h⟩

  -- ══════════════════════════════════════════════════════════════════
  -- § 5. Orden lexicográfico para NatsTuple
  -- ══════════════════════════════════════════════════════════════════

  open Peano.StrictOrder

  /-- Extrae el valor `ℕ₀` subyacente de cualquier elemento de un `NatsTuple` de forma dinámica. -/
  def natsVal : (t : Nats) → t → ℕ₀
    | Nats.nat0, x => x
    | Nats.nat1, x => x.val
    | Nats.nat2, x => x.val.val

  /-- Orden lexicográfico estricto para NatsTuple apoyado en los valores `ℕ₀`. -/
  def natsLexLt : {ts : List Nats} → NatsTuple ts → NatsTuple ts → Prop
    | [], _, _ => False
    | (t :: _ts), (x, xs), (y, ys) =>
      lt₀ (natsVal t x) (natsVal t y) ∨ (natsVal t x = natsVal t y ∧ natsLexLt xs ys)

  /-- Orden lexicográfico no estricto para NatsTuple. -/
  def natsLexLe : {ts : List Nats} → NatsTuple ts → NatsTuple ts → Prop
    | [], _, _ => True
    | (t :: _ts), (x, xs), (y, ys) =>
      lt₀ (natsVal t x) (natsVal t y) ∨ (natsVal t x = natsVal t y ∧ natsLexLe xs ys)

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
  -- § 6. Igualdad y Orden lexicográfico para HTuple
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

  instance htupleDecEq {ts : List Type} [HTupleDecidableEq ts] : DecidableEq (HTuple ts) :=
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

  /-- Orden lexicográfico estricto para HTuple. -/
  def hlexLt {ts : List Type} [HTupleLT ts] (x y : HTuple ts) : Prop := HTupleLT.lt x y

  /-- Orden lexicográfico no estricto para HTuple. -/
  def hlexLe {ts : List Type} [HTupleLE ts] (x y : HTuple ts) : Prop := HTupleLE.le x y

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
  mkNatsTuple
  instDecidableEqNatsType
  instReprNatsType
  natsTupleDecEq
  natsTupleRepr
  emptyHTuple
  consHTuple
  headHTuple
  tailHTuple
  mkHTuple
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
  instDecidableRelLeTuple'
  instDecidableEqTuple
  lexLt_irrefl
  lexLt_trans
  lexLt_trich
  instStrictLinearOrderTuple
  instIrreflTuple
  instAsymmTuple
  instTransTuple
  instTrichotomousTuple
  instIrreflLTTuple
  natsVal
  natsLexLt
  natsLexLe
  instLTNatsTuple
  instLENatsTuple
  instDecidableRelLtNatsTuple
  instDecidableRelLeNatsTuple
  HTupleDecidableEq
  instHTupleDecEqNil
  instHTupleDecEqCons
  htupleDecEq
  HTupleLT
  instHTupleLTNil
  instHTupleLTCons
  instLTHTuple
  HTupleLE
  instHTupleLENil
  instHTupleLECons
  instLEHTuple
  hlexLt
  hlexLe
  HTupleDecidableLT
  instHTupleDecLTNil
  instHTupleDecLTCons
  instDecidableRelLtHTuple
  HTupleDecidableLE
  instHTupleDecLENil
  instHTupleDecLECons
  instDecidableRelLeHTuple
)
