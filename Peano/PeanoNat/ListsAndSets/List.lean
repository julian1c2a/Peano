import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Tuple

/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
-- § 1. DecidableEq para ℕ₁ y ℕ₂
-- § 2. Órdenes inducidos sobre ℕ₁ y ℕ₂
-- § 3. Decidabilidad de órdenes sobre subtipos
-- § 4. Orden lexicográfico sobre ℕ₂ × ℕ₁
-- § 5. Longitud en ℕ₀ (lengthₚ)
-- § 6. Sorted (via Pairwise)
-- § 7. Decidabilidad de pertenencia a listas
-- § 7. Segmento inicial Fin₀ y alias de tipos para listas básicas
-- § 8. Alias de tipos para listas de tuplas
-- § 9. Listas de listas
-- § 10. Tipo suma `PeanoVal` y lista heterogénea
-- § 12. LT, LE, DecidableRel para Nats   (nat0 < nat1 < nat2)
-- § 13. Codificación canónica PeanoVal → List Nat
-- § 14. LT, LE, DecidableRel para PeanoVal
-- § 15. Repr para PeanoVal

namespace Peano
  open Peano

  namespace List
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

    instance instLTN1 : LT ℕ₁ := ⟨fun a b => lt₀ a.val b.val⟩
    instance instLEN1 : LE ℕ₁ := ⟨fun a b => le₀ a.val b.val⟩
    instance instLTN2 : LT ℕ₂ := ⟨fun a b => @LT.lt ℕ₁ instLTN1 a.val b.val⟩
    instance instLEN2 : LE ℕ₂ := ⟨fun a b => @LE.le ℕ₁ instLEN1 a.val b.val⟩

    instance : StrictOrder.IrreflLT ℕ₁ :=
      ⟨fun x h => StrictOrder.nlt_self x.val h⟩
    instance : StrictOrder.IrreflLT ℕ₂ :=
      ⟨fun x h => StrictOrder.nlt_self x.val.val h⟩

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
    -- § 3b. StrictLinearOrder para ℕ₁ y ℕ₂
    -- ══════════════════════════════════════════════════════════════════

    instance instStrictLinearOrderNat1 : StrictLinearOrder ℕ₁ where
      decLt  := fun a b => decidableLtN1 a b
      irrefl := fun n => StrictOrder.nlt_self n.val
      trans  := fun {_ _ _} h1 h2 => StrictOrder.lt_trans_wp h1 h2
      trich  := fun a b h_nab h_nba =>
        Subtype.ext (StrictOrder.lt_nor_gt_then_eq a.val b.val ⟨h_nab, h_nba⟩)

    instance instStrictLinearOrderNat2 : StrictLinearOrder ℕ₂ where
      decLt  := fun a b => decidableLtN2 a b
      irrefl := fun n => StrictOrder.nlt_self n.val.val
      trans  := fun {_ _ _} h1 h2 => StrictOrder.lt_trans_wp h1 h2
      trich  := fun a b h_nab h_nba =>
        Subtype.ext (Subtype.ext (StrictOrder.lt_nor_gt_then_eq a.val.val b.val.val ⟨h_nab, h_nba⟩))

    -- § 3c. Instancias Std.* para ℕ₁ y ℕ₂ (requeridas por FSet genérico)

    instance : Std.Irrefl (fun a b : ℕ₁ => a < b) where
      irrefl := fun a h => StrictOrder.nlt_self a.val h

    instance : Std.Asymm (fun a b : ℕ₁ => a < b) where
      asymm := fun _ _ h1 h2 => StrictOrder.lt_asymm _ _ h1 h2

    instance : Trans (fun a b : ℕ₁ => a < b) (fun a b : ℕ₁ => a < b)
        (fun a b : ℕ₁ => a < b) where
      trans := fun h1 h2 => StrictOrder.lt_trans_wp h1 h2

    instance : Std.Trichotomous (fun a b : ℕ₁ => a < b) where
      trichotomous := fun a b h_nab h_nba =>
        Subtype.ext (StrictOrder.lt_nor_gt_then_eq a.val b.val ⟨h_nab, h_nba⟩)

    instance : Std.Irrefl (fun a b : ℕ₂ => a < b) where
      irrefl := fun a h => StrictOrder.nlt_self a.val.val h

    instance : Std.Asymm (fun a b : ℕ₂ => a < b) where
      asymm := fun _ _ h1 h2 => StrictOrder.lt_asymm _ _ h1 h2

    instance : Trans (fun a b : ℕ₂ => a < b) (fun a b : ℕ₂ => a < b)
        (fun a b : ℕ₂ => a < b) where
      trans := fun h1 h2 => StrictOrder.lt_trans_wp h1 h2

    instance : Std.Trichotomous (fun a b : ℕ₂ => a < b) where
      trichotomous := fun a b h_nab h_nba =>
        Subtype.ext (Subtype.ext (StrictOrder.lt_nor_gt_then_eq a.val.val b.val.val ⟨h_nab, h_nba⟩))

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

    -- ══════════════════════════════════════════════════════════════════
    -- § 4b. Acceso por índice (getD) e índice de un elemento (indexOfₚ)
    -- ══════════════════════════════════════════════════════════════════

    /-- Acceso por índice en `ℕ₀`.  Devuelve `dflt` si el índice está fuera de rango. -/
    def getDₚ {α : Type} (dflt : α) : List α → ℕ₀ → α
      | [],       _   => dflt
      | x :: _,  .zero   => x
      | _ :: xs, .succ i  => getDₚ dflt xs i

    /-- `getDₚ` en posición cero de una lista no vacía. -/
    theorem getDₚ_cons_zero {α : Type} (dflt x : α) (xs : List α) :
        getDₚ dflt (x :: xs) 𝟘 = x := rfl

    /-- `getDₚ` en posición sucesor. -/
    @[simp] theorem getDₚ_cons_succ {α : Type} (dflt x : α) (xs : List α) (i : ℕ₀) :
        getDₚ dflt (x :: xs) (σ i) = getDₚ dflt xs i := rfl

    @[simp] theorem lengthₚ_nil {α : Type} :
      lengthₚ ([] : List α) = 𝟘 := rfl

    @[simp] theorem lengthₚ_cons {α : Type} (x : α) (xs : List α) :
        lengthₚ (x :: xs) = σ (lengthₚ xs) := by
      simp [lengthₚ, List.length_cons, Λ]

    /-- Si `i < lengthₚ l`, entonces `getDₚ dflt l i ∈ l`. -/
    theorem getDₚ_mem {α : Type} (dflt : α) (l : List α) (i : ℕ₀)
        (hi : lt₀ i (lengthₚ l)) : getDₚ dflt l i ∈ l := by
      induction l generalizing i with
      | nil =>
          -- lengthₚ [] = 𝟘, pero hi : lt₀ i 𝟘, contradicción
          exact absurd hi (nlt_n_0 i)
      | cons x xs ih =>
          cases i with
          | zero =>
              -- getDₚ dflt (x::xs) 𝟘 = x ∈ x::xs
              exact List.mem_cons.mpr (Or.inl rfl)
          | succ i' =>
              -- getDₚ dflt (x::xs) (σ i') = getDₚ dflt xs i'
              -- hi : lt₀ (σ i') (lengthₚ (x::xs)) = lt₀ (σ i') (σ (lengthₚ xs))
              -- ⇒ lt₀ i' (lengthₚ xs)
              have hi' : lt₀ i' (lengthₚ xs) := by
                rw [lengthₚ_cons] at hi
                exact (succ_lt_succ_iff i' (lengthₚ xs)).mp hi
              exact List.mem_cons.mpr (Or.inr (ih i' hi'))

    /-- Primera posición de `a` en `l` (en ℕ₀); devuelve `𝟘` si no está. -/
    def List.indexOfₚ {α : Type} [DecidableEq α] (a : α) : List α → ℕ₀
      | []       => 𝟘
      | x :: xs  => if x = a then 𝟘 else σ (List.indexOfₚ a xs)

    @[simp] theorem List.indexOfₚ_nil {α : Type} [DecidableEq α] (a : α) :
        List.indexOfₚ a [] = 𝟘 := rfl

    theorem List.indexOfₚ_cons_eq {α : Type} [DecidableEq α] (a x : α) (xs : List α)
        (h : x = a) : List.indexOfₚ a (x :: xs) = 𝟘 := by
      simp [List.indexOfₚ, h]

    theorem List.indexOfₚ_cons_ne {α : Type} [DecidableEq α] (a x : α) (xs : List α)
        (h : x ≠ a) : List.indexOfₚ a (x :: xs) = σ (List.indexOfₚ a xs) := by
      simp [List.indexOfₚ, h]

    /-- Si `a ∈ l`, entonces `getDₚ dflt l (indexOfₚ a l) = a`. -/
    theorem getDₚ_indexOfₚ {α : Type} [DecidableEq α] (dflt a : α) (l : List α)
        (hmem : a ∈ l) : getDₚ dflt l (List.indexOfₚ a l) = a := by
      induction l with
      | nil => cases hmem
      | cons x xs ih =>
        by_cases hxa : x = a
        · -- indexOfₚ a (x::xs) = 𝟘, getDₚ dflt (x::xs) 𝟘 = x = a
          rw [List.indexOfₚ_cons_eq a x xs hxa, getDₚ_cons_zero, hxa]
        · have hmem' : a ∈ xs := (List.mem_cons.mp hmem).resolve_left (Ne.symm hxa)
          rw [List.indexOfₚ_cons_ne a x xs hxa, getDₚ_cons_succ]
          exact ih hmem'

    /-- `indexOfₚ a l < lengthₚ l` cuando `a ∈ l`. -/
    theorem List.indexOfₚ_lt_length {α : Type} [DecidableEq α] (a : α) (l : List α)
        (hmem : a ∈ l) : lt₀ (List.indexOfₚ a l) (lengthₚ l) := by
      induction l with
      | nil => cases hmem
      | cons x xs ih =>
          by_cases hxa : x = a
          · -- indexOfₚ a (x::xs) = 𝟘 < σ (lengthₚ xs) = lengthₚ (x::xs)
            rw [List.indexOfₚ_cons_eq a x xs hxa, lengthₚ_cons]
            exact zero_lt_succ (lengthₚ xs)
          · -- indexOfₚ a (x::xs) = σ (indexOfₚ a xs)
            -- IH: lt₀ (indexOfₚ a xs) (lengthₚ xs)
            have hmem' : a ∈ xs := (List.mem_cons.mp hmem).resolve_left (Ne.symm hxa)
            rw [List.indexOfₚ_cons_ne a x xs hxa, lengthₚ_cons]
            exact (succ_lt_succ_iff (List.indexOfₚ a xs) (lengthₚ xs)).mpr (ih hmem')

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
    def Fin₀ (b : ℕ₀) := {x : ℕ₀ // lt₀ x b}

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

    -- ══════════════════════════════════════════════════════════════════
    -- § 8. Alias de tipos para listas de tuplas
    -- ══════════════════════════════════════════════════════════════════

    /-- Lista de tuplas homogéneas de ℕ₀ de longitud `n`. -/
    abbrev TupleList (n : ℕ₀) := List (Tuple ℕ₀ n)

    /-- Lista de tuplas heterogéneas sobre esquema `ts : List Nats`. -/
    abbrev NatsTupleList (ts : List Nats) := List (NatsTuple ts)

    /-- Lista de tuplas homogéneas genéricas de tipo `α` y longitud `n`.
        Nota: con `Tuple` polimórfico, `GTupleList` es alias de compatibilidad. -/
    abbrev GTupleList (α : Type) (n : ℕ₀) := List (Tuple α n)

    /-- Lista de tuplas heterogéneas con esquema de tipos `ts : List Type`. -/
    abbrev HTupleList (ts : List Type) := List (HTuple ts)

    -- ══════════════════════════════════════════════════════════════════
    -- § 9. Tipo suma `PeanoVal` y lista heterogénea
    -- ══════════════════════════════════════════════════════════════════

    /-- Tipo suma que unifica en un único tipo:
        · naturales ℕ₀/ℕ₁/ℕ₂  (vía el índice `Nats`),
        · listas de naturales,
        · tuplas homogéneas `Tuple ℕ₀ n` y heterogéneas `NatsTuple ts`,
        · listas de tuplas `TupleList n` y `NatsTupleList ts`. -/
    inductive PeanoVal : Type where
      | ofNat           (k : Nats)       (x  : k.toType)            : PeanoVal
      | ofNatList       (k : Nats)       (xs : List k.toType)       : PeanoVal
      | ofTuple         (n : ℕ₀)         (t  : Tuple ℕ₀ n)           : PeanoVal
      | ofNatsTuple     (ts : List Nats) (t  : NatsTuple ts)        : PeanoVal
      | ofTupleList     (n : ℕ₀)         (ts : TupleList n)         : PeanoVal
      | ofNatsTupleList (ts : List Nats) (xs : NatsTupleList ts)    : PeanoVal

    /-- `DecidableEq` para `PeanoVal`. -/
    instance instDecidableEqPeanoVal : DecidableEq PeanoVal := by
      intro a b
      match a, b with
      | .ofNat k1 x1, .ofNat k2 x2 =>
          by_cases hk : k1 = k2
          · subst hk
            cases instDecidableEqNatsType k1 x1 x2 with
            | isTrue  h => exact isTrue  (congrArg (PeanoVal.ofNat k1) h)
            | isFalse h => exact isFalse (fun e => h (by cases e; rfl))
          · exact isFalse (fun e => hk (by cases e; rfl))
      | .ofNatList k1 xs1, .ofNatList k2 xs2 =>
          by_cases hk : k1 = k2
          · subst hk
            haveI := instDecidableEqNatsType k1
            cases decEq xs1 xs2 with
            | isTrue  h => exact isTrue  (congrArg (PeanoVal.ofNatList k1) h)
            | isFalse h => exact isFalse (fun e => h (by cases e; rfl))
          · exact isFalse (fun e => hk (by cases e; rfl))
      | .ofTuple n1 t1, .ofTuple n2 t2 =>
          by_cases hn : n1 = n2
          · subst hn
            cases tupleDecEq n1 t1 t2 with
            | isTrue  h => exact isTrue  (congrArg (PeanoVal.ofTuple n1) h)
            | isFalse h => exact isFalse (fun e => h (by cases e; rfl))
          · exact isFalse (fun e => hn (by cases e; rfl))
      | .ofNatsTuple ts1 t1, .ofNatsTuple ts2 t2 =>
          by_cases hts : ts1 = ts2
          · subst hts
            cases natsTupleDecEq ts1 t1 t2 with
            | isTrue  h => exact isTrue  (congrArg (PeanoVal.ofNatsTuple ts1) h)
            | isFalse h => exact isFalse (fun e => h (by cases e; rfl))
          · exact isFalse (fun e => hts (by cases e; rfl))
      | .ofTupleList n1 ts1, .ofTupleList n2 ts2 =>
          by_cases hn : n1 = n2
          · subst hn
            haveI := @tupleDecEq ℕ₀ _ n1
            cases decEq ts1 ts2 with
            | isTrue  h => exact isTrue  (congrArg (PeanoVal.ofTupleList n1) h)
            | isFalse h => exact isFalse (fun e => h (by cases e; rfl))
          · exact isFalse (fun e => hn (by cases e; rfl))
      | .ofNatsTupleList ts1 xs1, .ofNatsTupleList ts2 xs2 =>
          by_cases hts : ts1 = ts2
          · subst hts
            haveI := natsTupleDecEq ts1
            cases decEq xs1 xs2 with
            | isTrue  h => exact isTrue  (congrArg (PeanoVal.ofNatsTupleList ts1) h)
            | isFalse h => exact isFalse (fun e => h (by cases e; rfl))
          · exact isFalse (fun e => hts (by cases e; rfl))
      -- 30 casos cross-constructor: diferentes constructores nunca son iguales
      | .ofNat _ _,           .ofNatList _ _        => exact isFalse (by intro h; cases h)
      | .ofNat _ _,           .ofTuple _ _          => exact isFalse (by intro h; cases h)
      | .ofNat _ _,           .ofNatsTuple _ _      => exact isFalse (by intro h; cases h)
      | .ofNat _ _,           .ofTupleList _ _      => exact isFalse (by intro h; cases h)
      | .ofNat _ _,           .ofNatsTupleList _ _  => exact isFalse (by intro h; cases h)
      | .ofNatList _ _,       .ofNat _ _            => exact isFalse (by intro h; cases h)
      | .ofNatList _ _,       .ofTuple _ _          => exact isFalse (by intro h; cases h)
      | .ofNatList _ _,       .ofNatsTuple _ _      => exact isFalse (by intro h; cases h)
      | .ofNatList _ _,       .ofTupleList _ _      => exact isFalse (by intro h; cases h)
      | .ofNatList _ _,       .ofNatsTupleList _ _  => exact isFalse (by intro h; cases h)
      | .ofTuple _ _,         .ofNat _ _            => exact isFalse (by intro h; cases h)
      | .ofTuple _ _,         .ofNatList _ _        => exact isFalse (by intro h; cases h)
      | .ofTuple _ _,         .ofNatsTuple _ _      => exact isFalse (by intro h; cases h)
      | .ofTuple _ _,         .ofTupleList _ _      => exact isFalse (by intro h; cases h)
      | .ofTuple _ _,         .ofNatsTupleList _ _  => exact isFalse (by intro h; cases h)
      | .ofNatsTuple _ _,     .ofNat _ _            => exact isFalse (by intro h; cases h)
      | .ofNatsTuple _ _,     .ofNatList _ _        => exact isFalse (by intro h; cases h)
      | .ofNatsTuple _ _,     .ofTuple _ _          => exact isFalse (by intro h; cases h)
      | .ofNatsTuple _ _,     .ofTupleList _ _      => exact isFalse (by intro h; cases h)
      | .ofNatsTuple _ _,     .ofNatsTupleList _ _  => exact isFalse (by intro h; cases h)
      | .ofTupleList _ _,     .ofNat _ _            => exact isFalse (by intro h; cases h)
      | .ofTupleList _ _,     .ofNatList _ _        => exact isFalse (by intro h; cases h)
      | .ofTupleList _ _,     .ofTuple _ _          => exact isFalse (by intro h; cases h)
      | .ofTupleList _ _,     .ofNatsTuple _ _      => exact isFalse (by intro h; cases h)
      | .ofTupleList _ _,     .ofNatsTupleList _ _  => exact isFalse (by intro h; cases h)
      | .ofNatsTupleList _ _, .ofNat _ _            => exact isFalse (by intro h; cases h)
      | .ofNatsTupleList _ _, .ofNatList _ _        => exact isFalse (by intro h; cases h)
      | .ofNatsTupleList _ _, .ofTuple _ _          => exact isFalse (by intro h; cases h)
      | .ofNatsTupleList _ _, .ofNatsTuple _ _      => exact isFalse (by intro h; cases h)
      | .ofNatsTupleList _ _, .ofTupleList _ _      => exact isFalse (by intro h; cases h)

    /-- Lista heterogénea de valores de Peano. -/
    abbrev PeanoValList := List PeanoVal

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

    /-- Aplana un `Tuple ℕ₀ n` en una lista de `Nat`
        proyectando cada componente `ℕ₀` via `Ψ`. -/
    private def tupleToNatList : {n : ℕ₀} → Tuple ℕ₀ n → List Nat
      | .zero,    _          => []
      | .succ _, (x, xs)    => Ψ x :: tupleToNatList xs

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

    -- ══════════════════════════════════════════════════════════════════
    -- § 16. LE, Trichotomous y Decidable para List α (antes en FSetFSet.lean § 11)
    -- ══════════════════════════════════════════════════════════════════

    /-- Irreflexividad del orden lexicográfico sobre `List α`. -/
    instance instIrreflListLt {α : Type} [LT α]
        [Std.Irrefl (fun a b : α => a < b)] :
        Std.Irrefl (fun (l₁ l₂ : List α) => l₁ < l₂) where
      irrefl := fun l => List.lt_irrefl l

    /-- Asimetría del orden lexicográfico sobre `List α`. -/
    instance instAsymmListLt {α : Type} [LT α]
        [Std.Asymm (fun a b : α => a < b)] :
        Std.Asymm (fun (l₁ l₂ : List α) => l₁ < l₂) where
      asymm := fun _ _ h1 h2 => List.lt_asymm h1 h2

    /-- Tricotomía del orden lexicográfico sobre `List α`.
        Si `¬(as < bs)` y `¬(bs < as)` entonces `as = bs`. -/
    instance instTrichotomousListLt {α : Type} [DecidableEq α] [LT α]
        [DecidableRel (@LT.lt α _)]
        [Std.Irrefl (fun a b : α => a < b)]
        [Std.Trichotomous (fun a b : α => a < b)] :
        Std.Trichotomous (fun l₁ l₂ : List α => l₁ < l₂) where
      trichotomous := by
        intro as bs h_nlt h_ngt
        induction as generalizing bs with
        | nil =>
          match bs with
          | [] => rfl
          | _ :: _ => exact absurd (List.Lex.nil) h_nlt
        | cons a at_ ih =>
          match bs with
          | [] => exact absurd (List.Lex.nil) h_ngt
          | b :: bt =>
            by_cases heq : a = b
            · subst heq
              have h1 : ¬ at_ < bt := fun h => h_nlt (List.Lex.cons h)
              have h2 : ¬ bt < at_ := fun h => h_ngt (List.Lex.cons h)
              exact congrArg (a :: ·) (ih bt h1 h2)
            · have hab : ¬ a < b := fun h => h_nlt (List.Lex.rel h)
              have hba : ¬ b < a := fun h => h_ngt (List.Lex.rel h)
              exact absurd (Std.Trichotomous.trichotomous
                (r := fun x y : α => x < y) a b hab hba) heq

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

  end List

end Peano

export Peano.List (
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
  instStrictLinearOrderNat1
  instStrictLinearOrderNat2
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
  TupleList
  NatsTupleList
  GTupleList
  HTupleList
  PeanoVal
  instDecidableEqPeanoVal
  PeanoValList
  getDₚ
  getDₚ_cons_zero
  getDₚ_cons_succ
  getDₚ_mem
  List.indexOfₚ
  List.indexOfₚ_nil
  List.indexOfₚ_cons_eq
  List.indexOfₚ_cons_ne
  getDₚ_indexOfₚ
  List.indexOfₚ_lt_length
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
  instIrreflListLt
  instAsymmListLt
  instTrichotomousListLt
  instLEList
  instDecidableLeList
)
