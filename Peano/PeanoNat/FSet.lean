/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/FSet.lean
-- Conjuntos finitos decidibles sobre ℕ₀, ℕ₁, ℕ₂ y ℕ₂ × ℕ₁.
-- Representación: listas estrictamente ordenadas (forma canónica).
--
-- § 1. ℕ₀FSet — conjuntos finitos de ℕ₀
-- § 2. ℕ₁FSet — conjuntos finitos de ℕ₁ (positivos)
-- § 3. ℕ₂FSet — conjuntos finitos de ℕ₂ (≥ 2)
-- § 4. FactFSet — conjuntos finitos de ℕ₂ × ℕ₁ (factorizaciones)
-- § 5. Constructores básicos (empty, singleton)
-- § 6. Cardinal (cardinalidad en ℕ₀)
-- § 7. Pertenencia (Membership)
-- § 8. Inserción ordenada sobre List ℕ₀
-- § 9. insert y ofList para ℕ₀FSet
-- § 10. Filtrado preservando orden
-- § 11. Notación {[ ... ]} para ℕ₀FSet
-- § 12. Operaciones sobre FactFSet (addFactor, lookup)

import Peano.PeanoNat.Lists
import Peano.PeanoNat.Add


namespace Peano
  open Peano
  open Peano.Lists

  namespace FSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. ℕ₀FSet — conjuntos finitos de ℕ₀
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de naturales ℕ₀, representado como lista
        estrictamente ordenada. La invariante `Sorted (· < ·)` garantiza
        unicidad de representación (forma canónica) y ausencia de duplicados. -/
    structure ℕ₀FSet where
      elems : List ℕ₀
      sorted : Sorted (· < ·) elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. ℕ₁FSet — conjuntos finitos de ℕ₁
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de naturales positivos ℕ₁. -/
    structure ℕ₁FSet where
      elems : List ℕ₁
      sorted : Sorted (· < ·) elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. ℕ₂FSet — conjuntos finitos de ℕ₂
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de naturales ≥ 2 (ℕ₂). -/
    structure ℕ₂FSet where
      elems : List ℕ₂
      sorted : Sorted (· < ·) elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. FactFSet — conjuntos finitos de ℕ₂ × ℕ₁ (factorizaciones)
    -- ══════════════════════════════════════════════════════════════════

    /-- Claves únicas en una lista de pares: ninguna base se repite. -/
    def UniqueKeys : List (ℕ₂ × ℕ₁) → Prop
      | [] => True
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
      elems : List (ℕ₂ × ℕ₁)
      sortedByKey : SortedByKey elems
      uniqueKeys : UniqueKeys elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 5. Constructores básicos
    -- ══════════════════════════════════════════════════════════════════

    def ℕ₀FSet.empty : ℕ₀FSet := ⟨[], sorted_nil _⟩
    def ℕ₁FSet.empty : ℕ₁FSet := ⟨[], sorted_nil _⟩
    def ℕ₂FSet.empty : ℕ₂FSet := ⟨[], sorted_nil _⟩
    def FactFSet.empty : FactFSet :=
      FactFSet.mk [] (sorted_nil _) trivial

    def ℕ₀FSet.singleton (x : ℕ₀) : ℕ₀FSet := ⟨[x], sorted_singleton _ x⟩
    def ℕ₁FSet.singleton (x : ℕ₁) : ℕ₁FSet := ⟨[x], sorted_singleton _ x⟩
    def ℕ₂FSet.singleton (x : ℕ₂) : ℕ₂FSet := ⟨[x], sorted_singleton _ x⟩
    def FactFSet.singleton (x : ℕ₂ × ℕ₁) : FactFSet :=
      FactFSet.mk [x] (sorted_singleton _ x) ⟨fun _ _ h => absurd h List.not_mem_nil, trivial⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § 6. Cardinal (cardinalidad en ℕ₀)
    -- ══════════════════════════════════════════════════════════════════

    def ℕ₀FSet.card (s : ℕ₀FSet) : ℕ₀ := lengthₚ s.elems
    def ℕ₁FSet.card (s : ℕ₁FSet) : ℕ₀ := lengthₚ s.elems
    def ℕ₂FSet.card (s : ℕ₂FSet) : ℕ₀ := lengthₚ s.elems
    def FactFSet.card (s : FactFSet) : ℕ₀ := lengthₚ s.elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 7. Pertenencia (Membership)
    -- ══════════════════════════════════════════════════════════════════

    instance : Membership ℕ₀ ℕ₀FSet :=
      Membership.mk (fun (s : ℕ₀FSet) (x : ℕ₀) => x ∈ s.elems)
    instance : Membership ℕ₁ ℕ₁FSet :=
      Membership.mk (fun (s : ℕ₁FSet) (x : ℕ₁) => x ∈ s.elems)
    instance : Membership ℕ₂ ℕ₂FSet :=
      Membership.mk (fun (s : ℕ₂FSet) (x : ℕ₂) => x ∈ s.elems)
    instance : Membership (ℕ₂ × ℕ₁) FactFSet :=
      Membership.mk (fun (s : FactFSet) (x : ℕ₂ × ℕ₁) => x ∈ s.elems)

    instance instDecMemN0FSet (x : ℕ₀) (s : ℕ₀FSet) : Decidable (x ∈ s) :=
      decidableMemList x s.elems
    instance instDecMemN1FSet (x : ℕ₁) (s : ℕ₁FSet) : Decidable (x ∈ s) :=
      decidableMemList x s.elems
    instance instDecMemN2FSet (x : ℕ₂) (s : ℕ₂FSet) : Decidable (x ∈ s) :=
      decidableMemList x s.elems

    -- ══════════════════════════════════════════════════════════════════
    -- § 8. Inserción ordenada sobre List ℕ₀
    -- ══════════════════════════════════════════════════════════════════

    open Peano.StrictOrder in
    /-- Inserta `x` en una lista ordenada de ℕ₀ manteniendo el orden
        estricto y descartando duplicados. -/
    def sortedInsert (x : ℕ₀) : List ℕ₀ → List ℕ₀
      | [] => [x]
      | y :: ys =>
        if Lt x y then x :: y :: ys
        else if x = y then y :: ys
        else y :: sortedInsert x ys

    /-- Lema de pertenencia para `sortedInsert`. -/
    theorem mem_sortedInsert_iff {z x : ℕ₀} {l : List ℕ₀} :
        z ∈ sortedInsert x l ↔ z = x ∨ z ∈ l := by
      induction l with
      | nil => simp [sortedInsert]
      | cons y ys ih =>
        simp only [sortedInsert]
        split
        · -- Lt x y → resultado = x :: y :: ys
          constructor
          · intro h
            rcases List.mem_cons.mp h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr h
          · intro h
            rcases h with rfl | h
            · exact List.mem_cons.mpr (Or.inl rfl)
            · exact List.mem_cons.mpr (Or.inr h)
        · split
          · -- x = y → resultado = y :: ys
            rename_i _ heq
            constructor
            · intro h; exact Or.inr h
            · intro h
              rcases h with rfl | h
              · rw [heq]; exact List.mem_cons.mpr (Or.inl rfl)
              · exact h
          · -- else → resultado = y :: sortedInsert x ys
            constructor
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
    /-- La inserción ordenada preserva `Sorted (· < ·)`. -/
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
                    | Or.inl hlt => absurd hlt (by assumption)
                    | Or.inr (Or.inl heq) => absurd heq hneq
                    | Or.inr (Or.inr hgt) => hgt)
                | Or.inr h => List.rel_of_pairwise_cons hs h)
              (ih hys)

    -- ══════════════════════════════════════════════════════════════════
    -- § 9. insert y ofList para ℕ₀FSet
    -- ══════════════════════════════════════════════════════════════════

    /-- Inserta un elemento en un `ℕ₀FSet`, manteniendo la
        forma canónica (ordenada y sin duplicados). -/
    def ℕ₀FSet.insert (x : ℕ₀) (s : ℕ₀FSet) : ℕ₀FSet :=
      ℕ₀FSet.mk (sortedInsert x s.elems) (sorted_sortedInsert s.sorted x)

    /-- Construye un `ℕ₀FSet` a partir de una lista, insertando
        cada elemento en orden. -/
    def ℕ₀FSet.ofList : List ℕ₀ → ℕ₀FSet
      | [] => ℕ₀FSet.empty
      | x :: xs => (ℕ₀FSet.ofList xs).insert x

    -- ══════════════════════════════════════════════════════════════════
    -- § 10. Filtrado preservando orden
    -- ══════════════════════════════════════════════════════════════════

    /-- El filtrado de una lista ordenada es ordenado. -/
    theorem sorted_filter {l : List ℕ₀} (p : ℕ₀ → Bool)
        (hs : Sorted (· < ·) l) :
        Sorted (· < ·) (List.filter p l) :=
      List.Pairwise.filter p hs

    /-- Filtra un `ℕ₀FSet` según un predicado decidible,
        preservando la forma canónica. -/
    def ℕ₀FSet.filter (p : ℕ₀ → Bool) (s : ℕ₀FSet) : ℕ₀FSet :=
      ℕ₀FSet.mk (s.elems.filter p) (sorted_filter p s.sorted)

    -- ══════════════════════════════════════════════════════════════════
    -- § 11. Notación {[ ... ]} para ℕ₀FSet
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
    -- § 12. Operaciones sobre FactFSet (addFactor, lookup)
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
      | [] => none
      | (p, c) :: rest => if p = n then some c else factListLookup n rest

    /-- Añade un factor `n` a una lista de factores ordenada por clave:
        — si `n` no aparece, inserta `(n, 1)` en su posición;
        — si aparece como `(n, c)`, lo reemplaza por `(n, σ c)`.
        Preserva el orden por clave y la unicidad de claves. -/
    def factListAddFactor (n : ℕ₂) : List (ℕ₂ × ℕ₁) → List (ℕ₂ × ℕ₁)
      | [] => [(n, oneN1)]
      | (p, c) :: rest =>
        if n < p then (n, oneN1) :: (p, c) :: rest
        else if p = n then (n, succN1 c) :: rest
        else (p, c) :: factListAddFactor n rest

    open Peano.StrictOrder in
    /-- `factListAddFactor` preserva las claves: la primera componente
        de cada par del resultado es clave original o `n`. -/
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
        · -- n < hd.1: resultado = (n, oneN1) :: hd :: tl
          rcases List.mem_cons.mp hx with rfl | htail
          · exact Or.inl rfl
          · exact Or.inr ⟨x.2, htail⟩
        · split at hx
          · -- hd.1 = n: resultado = (n, succN1 _) :: tl
            rcases List.mem_cons.mp hx with rfl | htail
            · exact Or.inl rfl
            · exact Or.inr ⟨x.2, List.mem_cons.mpr (Or.inr htail)⟩
          · -- otro: resultado = hd :: factListAddFactor n tl
            rcases List.mem_cons.mp hx with rfl | htail
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
          -- n < hd.1 → resultado = (n, _) :: hd :: tl
          exact List.Pairwise.cons
            (fun z hz => match List.mem_cons.mp hz with
              | Or.inl h => h ▸ h_n_lt
              | Or.inr h => lt_trans_wp h_n_lt (hall z h))
            hs
        next h_nlt =>
          split
          next h_eq =>
            -- hd.1 = n → resultado = (n, succN1 _) :: tl
            exact List.Pairwise.cons
              (fun z hz => h_eq ▸ hall z hz) htl
          next h_neq =>
            -- hd.1 < n (por tricotomía) → resultado = hd :: factListAddFactor n tl
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
  ℕ₀FSet
  ℕ₁FSet
  ℕ₂FSet
  FactFSet
)
