/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/ListsAndSets/FSetFSet.lean
-- Conjuntos finitos de tipos "peso 3" (listas).
-- Alias y operaciones básicas para FSet de los tipos definidos en ListList.lean.
--
-- § 16. FSet de listas de naturales  (Nat0ListFSet, Nat1ListFSet, Nat2ListFSet)
-- § 17. FSet de listas de tuplas     (NatsTupleListFSet, GTupleListFSet, HTupleListFSet)
-- § 18. FSet de PeanoVal             (PeanoValFSet)
--
-- Nota: `LT (List α)` viene de la stdlib Lean 4 (`List.Lex (· < ·)`).
--       `DecidableEq (List α)` también viene de la stdlib cuando `DecidableEq α`.
--       `LT PeanoVal` y `DecidableEq PeanoVal` vienen de ListList.lean y List.lean.

import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.ListList

namespace Peano
  open Peano

  namespace FSet
    open Peano.StrictOrder

    -- ══════════════════════════════════════════════════════════════════
    -- § 16. FSet de listas de naturales
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de listas de ℕ₀, ordenadas por el orden lexicográfico
        de listas sobre `LT ℕ₀` (stdlib `List.Lex`). -/
    abbrev Nat0ListFSet := FSet (List ℕ₀)

    /-- Conjunto finito de listas de ℕ₁. -/
    abbrev Nat1ListFSet := FSet (List ℕ₁)

    /-- Conjunto finito de listas de ℕ₂. -/
    abbrev Nat2ListFSet := FSet (List ℕ₂)

    /-- Conjunto finito de listas de `Nats`.
        Requiere `instLTNats` de ListList.lean. -/
    abbrev NatsListFSet := FSet (List Nats)

    namespace Nat0ListFSet
      def empty    : Nat0ListFSet              := FSet.empty
      def singleton (l : List ℕ₀) : Nat0ListFSet := FSet.singleton l
      def ofSortedList (l : List (List ℕ₀)) (h : Sorted (· < ·) l) :
          Nat0ListFSet := ⟨l, h⟩
    end Nat0ListFSet

    namespace Nat1ListFSet
      def empty    : Nat1ListFSet              := FSet.empty
      def singleton (l : List ℕ₁) : Nat1ListFSet := FSet.singleton l
      def ofSortedList (l : List (List ℕ₁)) (h : Sorted (· < ·) l) :
          Nat1ListFSet := ⟨l, h⟩
    end Nat1ListFSet

    namespace Nat2ListFSet
      def empty    : Nat2ListFSet              := FSet.empty
      def singleton (l : List ℕ₂) : Nat2ListFSet := FSet.singleton l
      def ofSortedList (l : List (List ℕ₂)) (h : Sorted (· < ·) l) :
          Nat2ListFSet := ⟨l, h⟩
    end Nat2ListFSet

    namespace NatsListFSet
      def empty    : NatsListFSet                 := FSet.empty
      def singleton (l : List Nats) : NatsListFSet := FSet.singleton l
      def ofSortedList (l : List (List Nats)) (h : Sorted (· < ·) l) :
          NatsListFSet := ⟨l, h⟩
    end NatsListFSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 17. FSet de listas de tuplas
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de listas de tuplas homogéneas de ℕ₀ de longitud `n`.
        `LT (List (Tuple n))` viene de `List.Lex` + `instLTTuple`. -/
    abbrev TupleListFSet (n : ℕ₀) := FSet (List (Tuple n))

    /-- Conjunto finito de listas de NatsTuple con esquema `ts`. -/
    abbrev NatsTupleListFSet (ts : List Nats) := FSet (List (NatsTuple ts))

    /-- Conjunto finito de listas de GTuple de tipo `α` y longitud `n`. -/
    abbrev GTupleListFSet (α : Type) [LT α] [DecidableEq α] (n : ℕ₀) :=
      FSet (List (GTuple α n))

    /-- Conjunto finito de listas de HTuple con esquema `ts`. -/
    abbrev HTupleListFSet (ts : List Type)
        [HTupleDecidableEq ts] [HTupleLT ts] :=
      FSet (List (HTuple ts))

    namespace TupleListFSet
      def empty (n : ℕ₀) : TupleListFSet n := FSet.empty
      def singleton (n : ℕ₀) (l : List (Tuple n)) : TupleListFSet n :=
        FSet.singleton l
      def ofSortedList (n : ℕ₀) (l : List (List (Tuple n)))
          (h : Sorted (· < ·) l) : TupleListFSet n := ⟨l, h⟩
    end TupleListFSet

    namespace NatsTupleListFSet
      def empty (ts : List Nats) : NatsTupleListFSet ts := FSet.empty
      def singleton (ts : List Nats) (l : List (NatsTuple ts)) :
          NatsTupleListFSet ts := FSet.singleton l
      def ofSortedList (ts : List Nats) (l : List (List (NatsTuple ts)))
          (h : Sorted (· < ·) l) : NatsTupleListFSet ts := ⟨l, h⟩
    end NatsTupleListFSet

    namespace GTupleListFSet
      def empty (α : Type) [LT α] [DecidableEq α] (n : ℕ₀) :
          GTupleListFSet α n := FSet.empty
      def singleton (α : Type) [LT α] [DecidableEq α] (n : ℕ₀)
          (l : List (GTuple α n)) : GTupleListFSet α n := FSet.singleton l
      def ofSortedList (α : Type) [LT α] [DecidableEq α] (n : ℕ₀)
          (l : List (List (GTuple α n))) (h : Sorted (· < ·) l) :
          GTupleListFSet α n := ⟨l, h⟩
    end GTupleListFSet

    namespace HTupleListFSet
      def empty (ts : List Type) [HTupleDecidableEq ts] [HTupleLT ts] :
          HTupleListFSet ts := FSet.empty
      def singleton (ts : List Type) [HTupleDecidableEq ts] [HTupleLT ts]
          (l : List (HTuple ts)) : HTupleListFSet ts := FSet.singleton l
      def ofSortedList (ts : List Type) [HTupleDecidableEq ts] [HTupleLT ts]
          (l : List (List (HTuple ts))) (h : Sorted (· < ·) l) :
          HTupleListFSet ts := ⟨l, h⟩
    end HTupleListFSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 18. FSet de PeanoVal
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de valores `PeanoVal`.
        Ordenado por `instLTPeanoVal` (codificación canónica en `List Nat`).
        La igualdad usa `instDecidableEqPeanoVal` de List.lean. -/
    abbrev PeanoValFSet := FSet PeanoVal

    namespace PeanoValFSet
      def empty    : PeanoValFSet                  := FSet.empty
      def singleton (v : PeanoVal) : PeanoValFSet  := FSet.singleton v
      def ofSortedList (l : List PeanoVal) (h : Sorted (· < ·) l) :
          PeanoValFSet := ⟨l, h⟩
    end PeanoValFSet

  end FSet

end Peano

export Peano.FSet (
  Nat0ListFSet
  Nat1ListFSet
  Nat2ListFSet
  NatsListFSet
  TupleListFSet
  NatsTupleListFSet
  GTupleListFSet
  HTupleListFSet
  PeanoValFSet
)
