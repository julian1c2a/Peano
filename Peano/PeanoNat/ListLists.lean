import Peano.PeanoNat.Lists

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/ListLists.lean
-- Órdenes avanzados sobre listas y el tipo suma `PeanoVal`.
--
-- § 11. LE y DecidableRel (≤) para List α
--       (LT ya viene de Lean 4 stdlib via List.Lex)
-- § 12. LT, LE, DecidableRel para Nats   (nat0 < nat1 < nat2)
-- § 13. Codificación canónica PeanoVal → List Nat
-- § 14. LT, LE, DecidableRel para PeanoVal (por pesos vía codificación)
-- § 15. Repr para PeanoVal

namespace Peano
  open Peano

  namespace Lists
    open Peano.StrictOrder

    -- ══════════════════════════════════════════════════════════════════
    -- § 11. LE y Decidable para List α
    -- ══════════════════════════════════════════════════════════════════

    /-- Lean 4 stdlib provee `LT (List α)` = `List.Lex (· < ·)`.
        Aquí añadimos `LE`: `as ≤ bs ↔ as < bs ∨ as = bs`. -/
    instance instLEList {α : Type} [LT α] [DecidableEq α] : LE (List α) :=
      ⟨fun as bs => as < bs ∨ as = bs⟩

    /-- Decidabilidad de `≤` sobre `List α` cuando los elementos
        tienen igualdad y orden estricto decidibles. -/
    instance instDecidableLeList {α : Type} [LT α] [DecidableEq α]
        [DecidableRel (@LT.lt α _)] :
        DecidableRel (@LE.le (List α) instLEList) :=
      fun as bs =>
        let hlt : Decidable (as < bs) := inferInstance
        match hlt, (inferInstance : Decidable (as = bs)) with
        | isTrue h,   _           => isTrue (Or.inl h)
        | isFalse _,  isTrue heq  => isTrue (Or.inr heq)
        | isFalse hn, isFalse hne => isFalse (fun h => h.elim hn hne)

    -- ══════════════════════════════════════════════════════════════════
    -- § 12. Orden sobre Nats  (nat0 < nat1 < nat2)
    -- ══════════════════════════════════════════════════════════════════

    /-- Orden estricto finito sobre las etiquetas de tipo `Nats`:
        `nat0 < nat1 < nat2`. -/
    @[reducible]
    def natsKindLt : Nats → Nats → Prop
      | .nat0, .nat1 | .nat0, .nat2 | .nat1, .nat2  => True
      | _,     _                                    => False

    instance instLTNats : LT Nats := ⟨natsKindLt⟩

    /-- `a ≤ b` si `a < b` o `a = b`. -/
    instance instLENats : LE Nats :=
      ⟨fun a b => natsKindLt a b ∨ a = b⟩

    /-- Decidabilidad de `<` en `Nats` (9 casos explícitos). -/
    instance instDecidableRelLtNats : DecidableRel (@LT.lt Nats instLTNats) :=
      fun a b => match a, b with
        | .nat0, .nat1 => isTrue  trivial
        | .nat0, .nat2 => isTrue  trivial
        | .nat1, .nat2 => isTrue  trivial
        | .nat0, .nat0 => isFalse id
        | .nat1, .nat0 => isFalse id
        | .nat1, .nat1 => isFalse id
        | .nat2, .nat0 => isFalse id
        | .nat2, .nat1 => isFalse id
        | .nat2, .nat2 => isFalse id

    /-- Decidabilidad de `≤` en `Nats`. -/
    instance instDecidableRelLeNats : DecidableRel (@LE.le Nats instLENats) :=
      fun a b =>
        match instDecidableRelLtNats a b with
        | isTrue h  => isTrue (Or.inl h)
        | isFalse hn =>
          match decEq a b with
          | isTrue heq  => isTrue (Or.inr heq)
          | isFalse hne => isFalse (fun h => h.elim hn hne)

    -- ══════════════════════════════════════════════════════════════════
    -- § 13. Codificación canónica  PeanoVal → List Nat
    -- ══════════════════════════════════════════════════════════════════

    /-- Convierte una etiqueta `Nats` a un índice `Nat` (0, 1, 2). -/
    private def natsKindNat : Nats → Nat
      | .nat0 => 0 | .nat1 => 1 | .nat2 => 2

    /-- Aplana un `Tuple n` en una lista de `Nat`
        proyectando cada componente `ℕ₀` via `Ψ`. -/
    private def tupleToNatList : {n : ℕ₀} → Tuple n → List Nat
      | 𝟘,    _          => []
      | σ _, (x, xs)    => Ψ x :: tupleToNatList xs

    /-- Aplana un `NatsTuple ts` en una lista de `Nat`
        proyectando cada componente al ℕ₀ subyacente vía `natsVal`. -/
    private def natstupleToNatList : {ts : List Nats} → NatsTuple ts → List Nat
      | [],     _        => []
      | t :: _, (x, xs)  => Ψ (natsVal t x) :: natstupleToNatList xs

    /-- Codificación canónica de un `PeanoVal` como `List Nat`.

        Estructura:
          posición 0 — peso (1 = nat escalar, 2 = tupla, 3 = lista)
          posición 1 — índice de constructor dentro del mismo peso
          resto      — contenido, codificado lex-inyectivamente.

        Jerarquía semántica por la codificación:
          Peso 1 (nat individual)
            0: ofNat k x           → [1, 0, kind_k, val_ℕ₀]
          Peso 2 (tuplas)
            0: ofTuple n t         → [2, 0, Ψ n, t₁, t₂, ...]
            1: ofNatsTuple ts tup  → [2, 1, |ts|, k₁...kₘ, v₁...vₘ]
          Peso 3 (listas)
            0: ofNatList k xs      → [3, 0, kind_k, x₁, x₂, ...]
            1: ofTupleList n ts    → [3, 1, Ψ n, |ts|, t₁₁...tₘₙ]
            2: ofNatsTupleList ts  → [3, 2, |ts|, k₁...kₘ, v₁₁...vₘₙ]

        El prefijo de peso + prefijo de esquema (|ts| + kinds) garantiza
        inyectividad: valores con distintos esquemas no colisionan. -/
    def peanoValEncode : PeanoVal → List Nat
      | .ofNat k x =>
          [1, 0, natsKindNat k, Ψ (natsVal k x)]
      | .ofTuple n t =>
          2 :: 0 :: Ψ n :: tupleToNatList t
      | .ofNatsTuple ts tup =>
          2 :: 1 :: ts.length :: (ts.map natsKindNat ++ natstupleToNatList tup)
      | .ofNatList k xs =>
          3 :: 0 :: natsKindNat k :: xs.map (fun x => Ψ (natsVal k x))
      | .ofTupleList n ts =>
          3 :: 1 :: Ψ n :: ts.length :: ts.flatMap tupleToNatList
      | .ofNatsTupleList ts xs =>
          3 :: 2 :: ts.length :: (ts.map natsKindNat ++ xs.flatMap natstupleToNatList)

    -- ══════════════════════════════════════════════════════════════════
    -- § 14. LT, LE, DecidableRel para PeanoVal
    -- ══════════════════════════════════════════════════════════════════

    /-- Orden estricto sobre `PeanoVal` inducido por la codificación canónica
        y el orden lexicográfico de `List Nat` (stdlib).

        Jerarquía efectiva:
          Peso 1 < Peso 2 < Peso 3      (nats < tuplas < listas)
          Dentro del mismo peso, menor índice de constructor primero.
          Mismo constructor y mismo esquema: lex de los valores. -/
    instance instLTPeanoVal : LT PeanoVal :=
      ⟨fun a b => List.lt (peanoValEncode a) (peanoValEncode b)⟩

    /-- `a ≤ b` si `a < b` o `a = b`. -/
    instance instLEPeanoVal : LE PeanoVal :=
      ⟨fun a b => a < b ∨ a = b⟩

    /-- Decidabilidad de `<` sobre `PeanoVal`.
        Lean 4 infiere `DecidableRel (· < ·)` sobre `List Nat` a partir de
        `Nat.decLt` + `DecidableEq Nat` + `instDecidableListLex` (core). -/
    instance instDecidableRelLtPeanoVal : DecidableRel (@LT.lt PeanoVal instLTPeanoVal) :=
      fun a b =>
        let ea := peanoValEncode a
        let eb := peanoValEncode b
        (inferInstance : Decidable (ea < eb))

    /-- Decidabilidad de `≤` sobre `PeanoVal`. -/
    instance instDecidableRelLePeanoVal : DecidableRel (@LE.le PeanoVal instLEPeanoVal) :=
      fun a b =>
        match instDecidableRelLtPeanoVal a b with
        | isTrue h   => isTrue (Or.inl h)
        | isFalse hn =>
          match instDecidableEqPeanoVal a b with
          | isTrue heq  => isTrue (Or.inr heq)
          | isFalse hne => isFalse (fun h => h.elim hn hne)

    -- ══════════════════════════════════════════════════════════════════
    -- § 15. Repr PeanoVal
    -- ══════════════════════════════════════════════════════════════════

    /-- Función auxiliar: representa una lista como cadena usando
        el `Repr` de sus elementos. -/
    private def reprListFmt {α : Type} (r : Repr α) (l : List α) : String :=
      "[" ++ String.intercalate ", "
        (l.map (fun x => toString (r.reprPrec x 0))) ++ "]"

    /-- Representación legible para `PeanoVal`.
        Los parámetros `ℕ₀` se muestran como su valor decimal (vía `Ψ`). -/
    instance instReprPeanoVal : Repr PeanoVal where
      reprPrec pv _ :=
        let s : String := match pv with
          | .ofNat k x =>
              s!"ofNat .{repr k} {(instReprNatsType k).reprPrec x 0}"
          | .ofNatList k xs =>
              s!"ofNatList .{repr k} {reprListFmt (instReprNatsType k) xs}"
          | .ofTuple n t =>
              s!"ofTuple {Ψ n} {(tupleRepr n).reprPrec t 0}"
          | .ofNatsTuple ts tup =>
              s!"ofNatsTuple {repr ts} {(natsTupleRepr ts).reprPrec tup 0}"
          | .ofTupleList n ts =>
              s!"ofTupleList {Ψ n} {reprListFmt (tupleRepr n) ts}"
          | .ofNatsTupleList ts xs =>
              s!"ofNatsTupleList {repr ts} {reprListFmt (natsTupleRepr ts) xs}"
        s

  end Lists

end Peano

export Peano.Lists (
  instLEList
  instDecidableLeList
  natsKindLt
  instLTNats
  instLENats
  instDecidableRelLtNats
  instDecidableRelLeNats
  peanoValEncode
  instLTPeanoVal
  instLEPeanoVal
  instDecidableRelLtPeanoVal
  instDecidableRelLePeanoVal
  instReprPeanoVal
)
