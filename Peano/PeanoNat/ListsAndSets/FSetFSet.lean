/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/ListsAndSets/FSetFSet.lean
-- Conjuntos finitos de tipos "peso 3" (listas).
-- Alias y operaciones básicas para FSet de los tipos compuestos.
--
-- § 11. LE y DecidableRel para List α
-- § 16. FSet de listas de naturales  (Nat0ListFSet, Nat1ListFSet, Nat2ListFSet)
-- § 17. FSet de listas de tuplas     (NatsTupleListFSet, GTupleListFSet, HTupleListFSet)
-- § 18. FSet de PeanoVal             (PeanoValFSet)
--
-- Nota: `LT (List α)` viene de la stdlib Lean 4 (`List.Lex (· < ·)`).
--       `DecidableEq (List α)` también viene de la stdlib cuando `DecidableEq α`.
--       `LT PeanoVal`, `DecidableEq PeanoVal`, `instLTNats` vienen de List.lean.

import Peano.PeanoNat.ListsAndSets.FSet

namespace Peano
  open Peano

  namespace FSet
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
        Requiere `instLTNats` de List.lean. -/
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

    -- ══════════════════════════════════════════════════════════════════
    -- § 19. FSet de FSet (conjuntos de conjuntos)
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de conjuntos finitos de `ℕ₀`. -/
    abbrev Nat0FSetFSet := FSet ℕ₀FSet

    /-- Igualdad decidible en `ℕ₀FSet` (heredada de `FSet`). -/
    instance instDecidableEqNat0FSet : DecidableEq ℕ₀FSet := inferInstance

    /-- Orden en `ℕ₀FSet` (heredado de `FSet`). -/
    instance instLTNat0FSet : LT ℕ₀FSet := inferInstance

    /-- Comparación decidible en `ℕ₀FSet`. -/
    instance instDecidableRelLtNat0FSet : DecidableRel (@LT.lt ℕ₀FSet instLTNat0FSet) :=
      inferInstance

    /-- Igualdad decidible en `Nat0FSetFSet`. -/
    instance instDecidableEqNat0FSetFSet : DecidableEq Nat0FSetFSet := inferInstance

    /-- Orden en `Nat0FSetFSet`. -/
    instance instLTNat0FSetFSet : LT Nat0FSetFSet := inferInstance

    /-- Comparación decidible en `Nat0FSetFSet`. -/
    instance instDecidableRelLtNat0FSetFSet :
        DecidableRel (@LT.lt Nat0FSetFSet instLTNat0FSetFSet) := inferInstance

    namespace Nat0FSetFSet
      def empty : Nat0FSetFSet := FSet.empty
      def singleton (s : ℕ₀FSet) : Nat0FSetFSet := FSet.singleton s
      def ofSortedList (l : List ℕ₀FSet) (h : Sorted (· < ·) l) :
          Nat0FSetFSet := ⟨l, h⟩
    end Nat0FSetFSet

    /-- Inserta un coset (`ℕ₀FSet`) en una lista manteniendo el orden por `<`.
        Implementación básica por inserción, eliminando duplicados. -/
    def sortedInsertFSet (x : ℕ₀FSet) : List ℕ₀FSet → List ℕ₀FSet
      | [] => [x]
      | y :: ys =>
          if x < y then x :: y :: ys
          else if x = y then y :: ys
          else y :: sortedInsertFSet x ys

    /-- Ordenación básica por inserción para listas de cosets (`List ℕ₀FSet`). -/
    def sortFSetList : List ℕ₀FSet → List ℕ₀FSet
      | [] => []
      | x :: xs => sortedInsertFSet x (sortFSetList xs)

    /-- Caracterización de pertenencia para `sortedInsertFSet`. -/
    theorem mem_sortedInsertFSet_iff {z x : ℕ₀FSet} {l : List ℕ₀FSet} :
        z ∈ sortedInsertFSet x l ↔ z = x ∨ z ∈ l := by
      induction l with
      | nil => simp [sortedInsertFSet]
      | cons y ys ih =>
        simp only [sortedInsertFSet]
        split
        · constructor
          · intro h
            rcases List.mem_cons.mp h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr h
          · intro h
            rcases h with rfl | h
            · exact List.mem_cons.mpr (Or.inl rfl)
            · exact List.mem_cons.mpr (Or.inr h)
        · split
          · rename_i _ heq
            constructor
            · intro h
              exact Or.inr h
            · intro h
              rcases h with rfl | h
              · rw [heq]
                exact List.mem_cons.mpr (Or.inl rfl)
              · exact h
          · constructor
            · intro h
              rcases List.mem_cons.mp h with rfl | h
              · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
              · rcases ih.mp h with rfl | hmem
                · exact Or.inl rfl
                · exact Or.inr (List.mem_cons.mpr (Or.inr hmem))
            · intro h
              rcases h with rfl | h
              · exact List.mem_cons.mpr (Or.inr (ih.mpr (Or.inl rfl)))
              · rcases List.mem_cons.mp h with rfl | hmem
                · exact List.mem_cons.mpr (Or.inl rfl)
                · exact List.mem_cons.mpr (Or.inr (ih.mpr (Or.inr hmem)))

    /-- `sortedInsertFSet` preserva el invariante de orden estricto. -/
    theorem sorted_sortedInsertFSet {l : List ℕ₀FSet}
        (hs : Sorted (· < ·) l) (x : ℕ₀FSet) :
        Sorted (· < ·) (sortedInsertFSet x l) := by
      induction l with
      | nil => exact sorted_singleton _ x
      | cons y ys ih =>
        unfold sortedInsertFSet
        split
        next hlt =>
          exact List.Pairwise.cons
            (fun z hz =>
              match List.mem_cons.mp hz with
              | Or.inl h => h ▸ hlt
              | Or.inr h => Trans.trans hlt (List.rel_of_pairwise_cons hs h))
            hs
        next hnotlt =>
          split
          next heq =>
            exact hs
          next hneq =>
            have hys := (List.pairwise_cons.mp hs).2
            exact List.Pairwise.cons
              (fun z hz =>
                match mem_sortedInsertFSet_iff.mp hz with
                | Or.inl hzx =>
                    hzx ▸
                    by
                      by_cases hyx : y < x
                      · exact hyx
                      · have hxy : x = y :=
                          Std.Trichotomous.trichotomous x y hnotlt hyx
                        exact False.elim (hneq hxy)
                | Or.inr hmem => List.rel_of_pairwise_cons hs hmem)
              (ih hys)

    /-- La ordenación por inserción produce una lista estrictamente ordenada. -/
    theorem sorted_sortFSetList (l : List ℕ₀FSet) :
        Sorted (· < ·) (sortFSetList l) := by
      induction l with
      | nil => exact sorted_nil _
      | cons x xs ih =>
          exact sorted_sortedInsertFSet ih x

    /-- La ordenación por inserción preserva pertenencia. -/
    theorem mem_sortFSetList_iff {x : ℕ₀FSet} {l : List ℕ₀FSet} :
        x ∈ sortFSetList l ↔ x ∈ l := by
      induction l with
      | nil => simp [sortFSetList]
      | cons y ys ih =>
          simp [sortFSetList, mem_sortedInsertFSet_iff, ih];

  end FSet

end Peano

export Peano.FSet (
  instLEList
  instDecidableLeList
  Nat0ListFSet
  Nat1ListFSet
  Nat2ListFSet
  NatsListFSet
  TupleListFSet
  NatsTupleListFSet
  GTupleListFSet
  HTupleListFSet
  PeanoValFSet
  Nat0FSetFSet
)
