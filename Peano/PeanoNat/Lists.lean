/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Lists.lean
-- Infraestructura base para listas tipadas sobre ℕ₀, ℕ₁, ℕ₂.
--
-- § 1. DecidableEq para ℕ₁ y ℕ₂
-- § 2. Órdenes inducidos sobre ℕ₁ y ℕ₂
-- § 3. Decidabilidad de órdenes sobre subtipos
-- § 4. Orden lexicográfico sobre ℕ₂ × ℕ₁
-- § 5. Longitud en ℕ₀ (lengthₚ)
-- § 6. Sorted (via Pairwise)
-- § 7. Decidabilidad de pertenencia a listas
-- § 8. Segmento inicial Fin₀ y alias de tipos

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order


namespace Peano
  open Peano

  namespace Lists
      open Peano.Axioms
      open Peano.StrictOrder
      open Peano.Order

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. DecidableEq para ℕ₁ y ℕ₂
    -- ══════════════════════════════════════════════════════════════════

    instance instDecidableEqN1 : DecidableEq ℕ₁ := fun a b =>
      if h : a.val = b.val then isTrue (Subtype.ext h)
      else isFalse (fun hab => h (congrArg Subtype.val hab))

    instance instDecidableEqN2 : DecidableEq ℕ₂ := fun a b =>
      if h : a.val = b.val then isTrue (Subtype.ext h)
      else isFalse (fun hab => h (congrArg Subtype.val hab))

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. Órdenes inducidos sobre ℕ₁ y ℕ₂
    -- ══════════════════════════════════════════════════════════════════

    instance instLTN1 : LT ℕ₁ := ⟨fun a b => Lt a.val b.val⟩
    instance instLEN1 : LE ℕ₁ := ⟨fun a b => Le a.val b.val⟩
    instance instLTN2 : LT ℕ₂ := ⟨fun a b => @LT.lt ℕ₁ instLTN1 a.val b.val⟩
    instance instLEN2 : LE ℕ₂ := ⟨fun a b => @LE.le ℕ₁ instLEN1 a.val b.val⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Decidabilidad de órdenes sobre subtipos
    -- ══════════════════════════════════════════════════════════════════

    instance decidableLtN1 (a b : ℕ₁) : Decidable (a < b) :=
      decidableLt a.val b.val

    instance decidableLeN1 (a b : ℕ₁) : Decidable (a ≤ b) :=
      decidableLe a.val b.val

    instance decidableLtN2 (a b : ℕ₂) : Decidable (a < b) :=
      decidableLtN1 a.val b.val

    instance decidableLeN2 (a b : ℕ₂) : Decidable (a ≤ b) :=
      decidableLeN1 a.val b.val

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Orden lexicográfico sobre ℕ₂ × ℕ₁
    -- ══════════════════════════════════════════════════════════════════

    def lexLt (a b : ℕ₂ × ℕ₁) : Prop :=
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

    instance instLTProdN2N1 : LT (ℕ₂ × ℕ₁) := ⟨lexLt⟩

    instance decidableLexLt (a b : ℕ₂ × ℕ₁) : Decidable (a < b) :=
      match decidableLtN2 a.1 b.1 with
      | isTrue h => isTrue (Or.inl h)
      | isFalse h_not_lt =>
        match instDecidableEqN2 a.1 b.1 with
        | isFalse h_neq => isFalse (fun h_lt =>
            h_lt.elim h_not_lt (fun ⟨h_eq, _⟩ => h_neq h_eq))
        | isTrue h_eq =>
          match decidableLtN1 a.2 b.2 with
          | isTrue h_lt => isTrue (Or.inr ⟨h_eq, h_lt⟩)
          | isFalse h_not_lt₂ => isFalse (fun h_lt =>
              h_lt.elim h_not_lt (fun ⟨_, h⟩ => h_not_lt₂ h))

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Longitud en ℕ₀ (lengthₚ)
    -- ══════════════════════════════════════════════════════════════════

    def lengthₚ {α : Type} (l : List α) : ℕ₀ := Λ l.length

    @[simp] theorem lengthₚ_nil {α : Type} :
      lengthₚ ([] : List α) = 𝟘 := rfl

    @[simp] theorem lengthₚ_cons {α : Type} (x : α) (xs : List α) :
        lengthₚ (x :: xs) = σ (lengthₚ xs) := by
      simp [lengthₚ, List.length_cons, Λ]

    -- ══════════════════════════════════════════════════════════════════
    -- § 5. Sorted (via Pairwise)
    -- ══════════════════════════════════════════════════════════════════

    /-- Una lista está ordenada respecto a una relación `r` si todos
        los pares `(aᵢ, aⱼ)` con `i < j` satisfacen `r aᵢ aⱼ`.
        Definido como alias de `List.Pairwise`. -/
    abbrev Sorted {α : Type}
      (r : α → α → Prop) (l : List α) :
        Prop
          :=
      List.Pairwise r l

    theorem sorted_nil {α : Type}
      (r : α → α → Prop) :
        Sorted r []
          :=
      List.Pairwise.nil

    theorem sorted_singleton {α : Type}
      (r : α → α → Prop) (x : α) :
        Sorted r [x]
          :=
      List.Pairwise.cons (fun _ h => absurd h List.not_mem_nil) List.Pairwise.nil

    -- ══════════════════════════════════════════════════════════════════
    -- § 6. Decidabilidad de pertenencia a listas
    -- ══════════════════════════════════════════════════════════════════

    /-- Pertenencia decidible a `List α` cuando `α` tiene `DecidableEq`. -/
    instance decidableMemList {α : Type} [DecidableEq α]
      (a : α) :
        (l : List α) → Decidable (a ∈ l)
      | [] => isFalse List.not_mem_nil
      | x :: xs =>
        if h : a = x then isTrue (List.mem_cons.mpr (Or.inl h))
        else match decidableMemList a xs with
          | isTrue h_mem => isTrue (List.mem_cons.mpr (Or.inr h_mem))
          | isFalse h_nmem => isFalse (fun h_in =>
              (List.mem_cons.mp h_in).elim h h_nmem)

    -- ══════════════════════════════════════════════════════════════════
    -- § 7. Alias de tipos para listas tipadas
    -- ══════════════════════════════════════════════════════════════════

    /-- Segmento inicial: `Fin₀ b` es el subtipo de `ℕ₀` con `x < b`. -/
    def Fin₀ (b : ℕ₀) := {x : ℕ₀ // Lt x b}

    instance instDecidableEqFin0 (b : ℕ₀) : DecidableEq (Fin₀ b) := fun a c =>
      if h : a.val = c.val then isTrue (Subtype.ext h)
      else isFalse (fun hac => h (congrArg Subtype.val hac))

    /-- Lista de naturales ℕ₀. -/
    abbrev Nat0List := List ℕ₀

    /-- Lista de naturales positivos ℕ₁. -/
    abbrev Nat1List := List ℕ₁

    /-- Lista de naturales ≥ 2 (ℕ₂). -/
    abbrev Nat2List := List ℕ₂

    /-- Lista de pares (primo, exponente) para factorizaciones. -/
    abbrev FactList := List (ℕ₂ × ℕ₁)

    /-- Lista de dígitos en base `b`. -/
    abbrev DigitList (b : ℕ₀) := List (Fin₀ b)

  end Lists

end Peano

export Peano.Lists (
  instDecidableEqN1
  instDecidableEqN2
  instLTN1
  instLEN1
  instLTN2
  instLEN2
  decidableLtN1
  decidableLeN1
  decidableLtN2
  decidableLeN2
  lexLt
  instLTProdN2N1
  decidableLexLt
  lengthₚ
  lengthₚ_nil
  lengthₚ_cons
  Sorted
  sorted_nil
  sorted_singleton
  decidableMemList
  Nat0List
  Nat1List
  Nat2List
  FactList
  Fin₀
  instDecidableEqFin0
  DigitList
)
