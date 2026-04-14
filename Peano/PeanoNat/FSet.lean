/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/FSet.lean
-- Conjuntos finitos decidibles, genéricos sobre cualquier tipo con orden.
-- Representación: listas estrictamente ordenadas (forma canónica).
--
-- § 0. FSet α   — estructura genérica (cualquier α con DecidableEq + LT)
-- § 1. Aliases  — ℕ₀FSet, ℕ₁FSet, ℕ₂FSet
-- § 2. FactFSet — conjunto especial de factorizaciones (ℕ₂ × ℕ₁, claves únicas)
-- § 3. Operaciones genéricas (empty, singleton, card, membership, filter)
-- § 4. Inserción ordenada sobre ℕ₀ (sortedInsert + proof de correctitud)
-- § 5. Operaciones ℕ₀FSet (insert, ofList, filter) — compatibilidad backward
-- § 6. Operaciones básicas ℕ₁FSet y ℕ₂FSet
-- § 7. Notación {[ ... ]} para ℕ₀FSet
-- § 8. Operaciones sobre FactFSet (addFactor, lookup)

import Peano.PeanoNat.Lists
import Peano.PeanoNat.Add


namespace Peano
  open Peano
  open Peano.Lists

  namespace FSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 0. FSet α — estructura genérica
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito genérico sobre un tipo `α` con igualdad decidible y
        orden estricto. Representado como lista estrictamente ordenada
        (`Sorted (· < ·)`), que garantiza unicidad de representación
        (forma canónica) y ausencia de duplicados.

        Requisitos mínimos:
        - `DecidableEq α` — para decidir pertenencia.
        - `LT α`          — para el invariante de ordenación. -/
    structure FSet (α : Type) [DecidableEq α] [LT α] where
      elems  : List α
      sorted : Sorted (· < ·) elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Aliases de tipos concretos
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de naturales ℕ₀. -/
    abbrev ℕ₀FSet := FSet ℕ₀

    /-- Conjunto finito de naturales positivos ℕ₁. -/
    abbrev ℕ₁FSet := FSet ℕ₁

    /-- Conjunto finito de naturales ≥ 2 (ℕ₂). -/
    abbrev ℕ₂FSet := FSet ℕ₂

    /-- Conjunto finito de naturales Nats. -/
    abbrev NatsFSet := FSet Nats

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. FactFSet — conjunto especial de factorizaciones (ℕ₂ × ℕ₁)
    --
    -- A diferencia de FSet (ℕ₂ × ℕ₁), FactFSet exige dos invariantes
    -- adicionales: claves únicas (ninguna base se repite) y orden por
    -- la primera componente (base). Esto refleja su semántica como
    -- representación canónica de una factorización prima.
    -- ══════════════════════════════════════════════════════════════════

    /-- Claves únicas en una lista de pares: ninguna base se repite. -/
    def UniqueKeys : List (ℕ₂ × ℕ₁) → Prop
      | []            => True
      | (p, _) :: rest => (∀ q e, (q, e) ∈ rest → q ≠ p) ∧ UniqueKeys rest

    /-- Lista ordenada estrictamente por la primera componente (base). -/
    abbrev SortedByKey (l : List (ℕ₂ × ℕ₁)) : Prop :=
      List.Pairwise (fun a b : ℕ₂ × ℕ₁ => a.1 < b.1) l

    open Peano.StrictOrder in
    /-- SortedByKey implica UniqueKeys: claves estrictamente crecientes
        no pueden repetirse. -/
    theorem sortedByKey_imp_uniqueKeys :
        ∀ l : List (ℕ₂ × ℕ₁), SortedByKey l → UniqueKeys l := by
      intro l
      induction l with
      | nil => intro _; trivial
      | cons hd tl ih =>
        intro hs
        have ⟨hall, htl⟩ := List.pairwise_cons.mp hs
        exact ⟨fun q e hmem hqp => by
          have h_lt := hall (q, e) hmem
          rw [hqp] at h_lt
          exact lt_irrefl hd.1.val.val h_lt, ih htl⟩

    /-- Conjunto finito de pares (base ≥ 2, exponente ≥ 1) para factorizaciones.
        Ordenado estrictamente por la primera componente (base),
        lo que garantiza unicidad de representación y claves únicas. -/
    structure FactFSet where
      elems       : List (ℕ₂ × ℕ₁)
      sortedByKey : SortedByKey elems
      uniqueKeys  : UniqueKeys elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Operaciones genéricas sobre FSet α
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto vacío. -/
    def FSet.empty {α : Type} [DecidableEq α] [LT α] : FSet α :=
      ⟨[], sorted_nil _⟩

    /-- Singleton: conjunto con un único elemento. -/
    def FSet.singleton {α : Type} [DecidableEq α] [LT α] (x : α) : FSet α :=
      ⟨[x], sorted_singleton _ x⟩

    /-- Cardinalidad del conjunto (número de elementos). -/
    def FSet.card {α : Type} [DecidableEq α] [LT α] (s : FSet α) : ℕ₀ :=
      lengthₚ s.elems

    /-- Pertenencia genérica: `x ∈ s` iff `x ∈ s.elems`.
        Marcada `@[reducible]` para que `x ∈ s` y `x ∈ s.elems` sean
        definitoriamente iguales en todos los contextos. -/
    @[reducible] instance {α : Type} [DecidableEq α] [LT α] :
      Membership α (FSet α) where
        mem (s : FSet α) (x : α) := List.Mem x s.elems

    /-- La pertenencia en `FSet α` es decidible (requiere `DecidableEq α`). -/
    instance {α : Type} [DecidableEq α] [LT α] (x : α) (s : FSet α) :
        Decidable (x ∈ s)
          :=
      decidableMemList x s.elems

    /-- Filtrado genérico preservando el invariante de orden. -/
    def FSet.filter {α : Type} [DecidableEq α] [LT α]
      (p : α → Bool) (s : FSet α) :
        FSet α
          :=
      ⟨s.elems.filter p, List.Pairwise.filter p s.sorted⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Inserción ordenada sobre List ℕ₀
    --
    -- La función `sortedInsert` es genérica en su definición, pero la
    -- demostración de correctitud (`sorted_sortedInsert`) usa propiedades
    -- específicas de `ℕ₀` (transitividad y tricotomía de `Lt`).
    -- Para generalizar el proof se necesitaría una clase `LinearOrder α`.
    -- ══════════════════════════════════════════════════════════════════

    open Peano.StrictOrder in
    /-- Inserta `x` en una lista ordenada de ℕ₀ manteniendo el orden
        estricto y descartando duplicados. -/
    def sortedInsert (x : ℕ₀) : List ℕ₀ → List ℕ₀
      | []      => [x]
      | y :: ys =>
        if Lt x y      then x :: y :: ys
        else if x = y  then y :: ys
        else                y :: sortedInsert x ys

    /-- Lema de pertenencia para `sortedInsert`. -/
    theorem mem_sortedInsert_iff {z x : ℕ₀} {l : List ℕ₀} :
        z ∈ sortedInsert x l ↔ z = x ∨ z ∈ l := by
      induction l with
      | nil => simp [sortedInsert]
      | cons y ys ih =>
        simp only [sortedInsert]
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
            · intro h; exact Or.inr h
            · intro h
              rcases h with rfl | h
              · rw [heq]; exact List.mem_cons.mpr (Or.inl rfl)
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

    open Peano.StrictOrder in
    /-- La inserción ordenada preserva `Sorted (· < ·)` sobre `List ℕ₀`.
        (La prueba usa `lt_trans_wp` y `trichotomy`, específicos de ℕ₀.) -/
    theorem sorted_sortedInsert {l : List ℕ₀}
        (hs : Sorted (· < ·) l) (x : ℕ₀) :
        Sorted (· < ·) (sortedInsert x l) := by
      induction l with
      | nil => exact sorted_singleton _ x
      | cons y ys ih =>
        unfold sortedInsert
        split
        next hlt =>
          exact List.Pairwise.cons
            (fun z hz =>
              match List.mem_cons.mp hz with
              | Or.inl h => h ▸ hlt
              | Or.inr h => lt_trans_wp hlt (List.rel_of_pairwise_cons hs h))
            hs
        next =>
          split
          next heq => exact hs
          next hneq =>
            have hys := (List.pairwise_cons.mp hs).2
            exact List.Pairwise.cons
              (fun z hz =>
                match mem_sortedInsert_iff.mp hz with
                | Or.inl h => h ▸ (match trichotomy x y with
                    | Or.inl hlt  => absurd hlt (by assumption)
                    | Or.inr (Or.inl heq) => absurd heq hneq
                    | Or.inr (Or.inr hgt) => hgt)
                | Or.inr h => List.rel_of_pairwise_cons hs h)
              (ih hys)

    -- ══════════════════════════════════════════════════════════════════
    -- § 5. Operaciones ℕ₀FSet (compatibilidad backward)
    --
    -- Estas definiciones mantienen los nombres `ℕ₀FSet.xxx` que usan
    -- los clientes existentes (NumberSets.lean, Group.lean, etc.).
    -- Internamente delegan a las operaciones genéricas o a sortedInsert.
    -- ══════════════════════════════════════════════════════════════════

    namespace ℕ₀FSet

      def empty    : FSet ℕ₀ := FSet.empty
      def singleton (x : ℕ₀) : FSet ℕ₀ := FSet.singleton x

      /-- Inserta `x` en un `ℕ₀FSet`, manteniendo la forma canónica. -/
      def insert (x : ℕ₀) (s : FSet ℕ₀) : FSet ℕ₀ :=
        ⟨sortedInsert x s.elems, sorted_sortedInsert s.sorted x⟩

      /-- Construye un `ℕ₀FSet` a partir de una lista. -/
      def ofList : List ℕ₀ → FSet ℕ₀
        | []      => empty
        | x :: xs => insert x (ofList xs)

      /-- Filtra un `ℕ₀FSet` según un predicado decidible. -/
      def filter (p : ℕ₀ → Bool) (s : FSet ℕ₀) : FSet ℕ₀ :=
        FSet.filter p s

    end ℕ₀FSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 6. Operaciones básicas ℕ₁FSet y ℕ₂FSet
    -- ══════════════════════════════════════════════════════════════════

    namespace ℕ₁FSet
      def empty    : FSet ℕ₁ := FSet.empty
      def singleton (x : ℕ₁) : FSet ℕ₁ := FSet.singleton x
    end ℕ₁FSet

    namespace ℕ₂FSet
      def empty    : FSet ℕ₂ := FSet.empty
      def singleton (x : ℕ₂) : FSet ℕ₂ := FSet.singleton x
    end ℕ₂FSet

    namespace NatsFSet
      def empty    : FSet Nats := FSet.empty
      def singleton (x : Nats) : FSet Nats := FSet.singleton x
    end NatsFSet

    -- FactFSet básicos
    def FactFSet.empty : FactFSet :=
      FactFSet.mk [] (sorted_nil _) trivial
    def FactFSet.card (s : FactFSet) : ℕ₀ := lengthₚ s.elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 7. Notación {[ ... ]} para ℕ₀FSet
    -- ══════════════════════════════════════════════════════════════════

    /-- `{[ a, b, c ]}` construye un `ℕ₀FSet` con los elementos dados. -/
    syntax "{[" term,* "]}" : term

    macro_rules
      | `({[ $xs:term,* ]}) => do
          let mut e ← `(ℕ₀FSet.empty)
          for x in xs.getElems.reverse do
            e ← `(ℕ₀FSet.insert $x $e)
          return e

    /-- `{[ s | p ]}` filtra un `ℕ₀FSet` según el predicado `p`. -/
    syntax "{[" term " | " term "]}" : term

    macro_rules
      | `({[ $s | $p ]}) => `(ℕ₀FSet.filter $p $s)

    -- ══════════════════════════════════════════════════════════════════
    -- § 8. Operaciones sobre FactFSet (addFactor, lookup)
    -- ══════════════════════════════════════════════════════════════════

    open Peano.Axioms in
    /-- Sucesor en ℕ₁: σ n como natural positivo. -/
    def succN1 (n : ℕ₁) : ℕ₁ :=
      Subtype.mk (σ n.val) (succ_neq_zero n.val)

    open Peano.Axioms in
    /-- El uno como elemento de ℕ₁. -/
    def oneN1 : ℕ₁ :=
      Subtype.mk 𝟙 (succ_neq_zero 𝟘)

    /-- Busca el exponente asociado a la base `n` en una lista de factores.
        Devuelve `none` si `n` no aparece como primera componente. -/
    def factListLookup (n : ℕ₂) : List (ℕ₂ × ℕ₁) → Option ℕ₁
      | []           => none
      | (p, c) :: rest => if p = n then some c else factListLookup n rest

    /-- Añade un factor `n` a una lista de factores ordenada por clave:
        — si `n` no aparece, inserta `(n, 1)` en su posición;
        — si aparece como `(n, c)`, lo reemplaza por `(n, σ c)`.
        Preserva el orden por clave y la unicidad de claves. -/
    def factListAddFactor (n : ℕ₂) : List (ℕ₂ × ℕ₁) → List (ℕ₂ × ℕ₁)
      | []           => [(n, oneN1)]
      | (p, c) :: rest =>
        if n < p       then (n, oneN1) :: (p, c) :: rest
        else if p = n  then (n, succN1 c) :: rest
        else                (p, c) :: factListAddFactor n rest

    open Peano.StrictOrder in
    /-- `factListAddFactor` preserva las claves. -/
    private theorem factListAddFactor_keys (n : ℕ₂)
        (l : List (ℕ₂ × ℕ₁)) :
        ∀ x, x ∈ factListAddFactor n l →
          x.1 = n ∨ ∃ e, (x.1, e) ∈ l := by
      induction l with
      | nil =>
        intro x hx
        simp [factListAddFactor] at hx
        exact Or.inl (congrArg Prod.fst hx)
      | cons hd tl ih =>
        intro x hx
        simp only [factListAddFactor] at hx
        split at hx
        · rcases List.mem_cons.mp hx with rfl | htail
          · exact Or.inl rfl
          · exact Or.inr ⟨x.2, htail⟩
        · split at hx
          · rcases List.mem_cons.mp hx with rfl | htail
            · exact Or.inl rfl
            · exact Or.inr ⟨x.2, List.mem_cons.mpr (Or.inr htail)⟩
          · rcases List.mem_cons.mp hx with rfl | htail
            · exact Or.inr ⟨hd.2, List.mem_cons.mpr (Or.inl rfl)⟩
            · rcases ih x htail with h | ⟨e, he⟩
              · exact Or.inl h
              · exact Or.inr ⟨e, List.mem_cons.mpr (Or.inr he)⟩

    open Peano.StrictOrder in
    /-- `factListAddFactor` preserva `SortedByKey`. -/
    theorem sortedByKey_factListAddFactor (n : ℕ₂)
        (l : List (ℕ₂ × ℕ₁)) (hs : SortedByKey l) :
        SortedByKey (factListAddFactor n l) := by
      induction l with
      | nil => exact sorted_singleton _ (n, oneN1)
      | cons hd tl ih =>
        simp only [factListAddFactor]
        have ⟨hall, htl⟩ := List.pairwise_cons.mp hs
        split
        next h_n_lt =>
          exact List.Pairwise.cons
            (fun z hz => match List.mem_cons.mp hz with
              | Or.inl h => h ▸ h_n_lt
              | Or.inr h => lt_trans_wp h_n_lt (hall z h))
            hs
        next h_nlt =>
          split
          next h_eq =>
            exact List.Pairwise.cons
              (fun z hz => h_eq ▸ hall z hz) htl
          next h_neq =>
            have h_hd_lt_n : hd.1 < n := by
              rcases trichotomy hd.1.val.val n.val.val with h | h | h
              · exact h
              · exact absurd (Subtype.ext (Subtype.ext h)) h_neq
              · exact absurd h h_nlt
            exact List.Pairwise.cons
              (fun z hz =>
                match factListAddFactor_keys n tl z hz with
                | Or.inl hfst => hfst ▸ h_hd_lt_n
                | Or.inr ⟨e, he⟩ => hall (z.1, e) he)
              (ih htl)

    open Peano.StrictOrder in
    /-- `factListAddFactor` preserva `UniqueKeys`. -/
    theorem uniqueKeys_factListAddFactor (n : ℕ₂)
        (l : List (ℕ₂ × ℕ₁)) (hs : SortedByKey l) :
        UniqueKeys (factListAddFactor n l) :=
      sortedByKey_imp_uniqueKeys _ (sortedByKey_factListAddFactor n l hs)

    /-- Busca el exponente del factor `n` en un `FactFSet`. -/
    def FactFSet.lookup (n : ℕ₂) (s : FactFSet) : Option ℕ₁ :=
      factListLookup n s.elems

    /-- Añade (o incrementa) el exponente del factor `n`.
        — Si `n` no está: inserta `(n, 1)`.
        — Si está como `(n, c)`: lo reemplaza por `(n, c+1)`. -/
    def FactFSet.addFactor (n : ℕ₂) (s : FactFSet) : FactFSet :=
      FactFSet.mk
        (factListAddFactor n s.elems)
        (sortedByKey_factListAddFactor n s.elems s.sortedByKey)
        (uniqueKeys_factListAddFactor n s.elems s.sortedByKey)

  end FSet

end Peano

export Peano.FSet (
  FSet
  ℕ₀FSet
  ℕ₁FSet
  ℕ₂FSet
  NatsFSet
  FactFSet
  UniqueKeys
  SortedByKey
  sortedByKey_imp_uniqueKeys
  sortedInsert
  mem_sortedInsert_iff
  sorted_sortedInsert
  sortedByKey_factListAddFactor
  uniqueKeys_factListAddFactor
)
