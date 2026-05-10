/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/ListsAndSets/FSet.lean
-- Conjuntos finitos decidibles, genéricos sobre cualquier tipo con orden.
-- Representación: listas estrictamente ordenadas (forma canónica).
--
-- § 0. FSet α   — estructura genérica (cualquier α con DecidableEq + LT)
-- § 1. Aliases  — ℕ₀FSet, ℕ₁FSet, ℕ₂FSet
-- § 2. FactFSet — conjunto especial de factorizaciones (ℕ₂ × ℕ₁, claves únicas)
-- § 3. Operaciones genéricas (empty, singleton, card, membership, filter)
-- § 4. Inserción ordenada genérica (StrictLinearOrder α)
-- § 5. Operaciones ℕ₀FSet (insert, ofList, filter) — compatibilidad backward
-- § 6. Operaciones básicas ℕ₁FSet y ℕ₂FSet
-- § 7. Notación {[ ... ]} para ℕ₀FSet
-- § 8. Operaciones sobre FactFSet (addFactor, lookup)

import Peano.PeanoNat.ListsAndSets.List
import Peano.PeanoNat.Add


namespace Peano
  open Peano
  open Peano.List

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

    /-- Extensionalidad de `FSet`: dos conjuntos con la misma lista de elementos
        son iguales (la prueba de `sorted` es irrelevante por proof irrelevance). -/
    theorem FSet.ext {α : Type} [DecidableEq α] [LT α]
        {s₁ s₂ : FSet α} (h : s₁.elems = s₂.elems) : s₁ = s₂ := by
      cases s₁; cases s₂; cases h; rfl

    /-- Igualdad decidible en `FSet α`: dos conjuntos son iguales si y solo si
        sus listas canónicas de elementos coinciden. -/
    instance {α : Type} [DecidableEq α] [LT α] : DecidableEq (FSet α) :=
      fun s₁ s₂ =>
        if h : s₁.elems = s₂.elems then
          isTrue (FSet.ext h)
        else
          isFalse (fun hs => h (congrArg FSet.elems hs))

    /-- Orden en `FSet α` inducido por el orden lexicográfico de `List α`
        sobre la representación canónica `elems`. -/
    instance {α : Type} [DecidableEq α] [LT α] : LT (FSet α) where
      lt s₁ s₂ := s₁.elems < s₂.elems

    /-- Decidabilidad del orden en `FSet α`, heredada de `List α`. -/
    instance {α : Type} [DecidableEq α] [LT α] [DecidableRel (@LT.lt α _)] :
        DecidableRel (@LT.lt (FSet α) _) :=
      fun s₁ s₂ => inferInstanceAs (Decidable (s₁.elems < s₂.elems))

    /-- Orden no estricto en `FSet α`: `s ≤ t ↔ s < t ∨ s = t`. -/
    instance {α : Type} [DecidableEq α] [LT α] : LE (FSet α) where
      le s t := s < t ∨ s = t

    /-- Decidabilidad de `≤` en `FSet α`. -/
    instance {α : Type} [DecidableEq α] [LT α] [DecidableRel (@LT.lt α _)] :
        DecidableRel (@LE.le (FSet α) _) :=
      fun s₁ s₂ =>
        match inferInstanceAs (Decidable (s₁ < s₂)),
              inferInstanceAs (Decidable (s₁ = s₂)) with
        | isTrue hlt,  _            => isTrue (Or.inl hlt)
        | isFalse _,   isTrue heq   => isTrue (Or.inr heq)
        | isFalse hn1, isFalse hn2  => isFalse (fun h => h.elim hn1 hn2)

    /-- Irreflexividad estándar en `FSet α`, heredada de `List α`. -/
    instance {α : Type} [DecidableEq α] [LT α]
        [Std.Irrefl (fun a b : α => a < b)] :
        Std.Irrefl (fun s t : FSet α => s < t) where
      irrefl := fun s hs => (List.lt_irrefl s.elems) hs

    /-- Asimetría estándar en `FSet α`, heredada de `List α`. -/
    instance {α : Type} [DecidableEq α] [LT α]
        [Std.Asymm (fun a b : α => a < b)] :
        Std.Asymm (fun s t : FSet α => s < t) where
      asymm := fun _ _ hst hts =>
        (List.lt_asymm hst) hts

    /-- Transitividad de `<` en `FSet α`, heredada del orden lexicográfico
        de listas cuando `<` en `α` es transitivo. -/
    instance {α : Type} [DecidableEq α] [LT α]
        [Trans (fun a b : α => a < b) (fun a b : α => a < b) (fun a b : α => a < b)] :
        Trans (fun s t : FSet α => s < t) (fun s t : FSet α => s < t)
          (fun s t : FSet α => s < t) where
      trans := by
        intro s t u hst htu
        exact List.lt_trans hst htu

    /-- Tricotomía estándar en `FSet α`, heredada de `List α`. -/
    instance {α : Type} [DecidableEq α] [LT α]
        [Std.Irrefl (fun a b : α => a < b)]
        [Std.Trichotomous (fun a b : α => a < b)]
        [Std.Asymm (fun a b : α => a < b)]
        [DecidableRel (@LT.lt α _)] :
        Std.Trichotomous (fun s t : FSet α => s < t) where
      trichotomous := fun s t hs_not_st hs_not_ts =>
        FSet.ext <| instTrichotomousListLt.trichotomous s.elems t.elems hs_not_st hs_not_ts

    /-- Irreflexividad de `<` en `FSet α`, heredada del orden lexicográfico
        en listas cuando `<` en `α` es irreflexivo (instancia stdlib). -/
    instance {α : Type} [DecidableEq α] [LT α]
        [Std.Irrefl (fun a b : α => a < b)] :
        Peano.StrictOrder.IrreflLT (FSet α) :=
      ⟨fun s hs => (List.lt_irrefl s.elems) hs⟩

    /-- `Std.Irrefl` derivado de `StrictLinearOrder α` (prioridad baja para no
        competir con instancias específicas como la de `ℕ₀`). -/
    instance (priority := 50) instStdIrreflOfSLO {α : Type} [LT α] [DecidableEq α]
        [slo : StrictLinearOrder α] : Std.Irrefl (fun a b : α => a < b) where
      irrefl := slo.irrefl

    /-- `Std.Asymm` derivado de `StrictLinearOrder α` (irrefl + trans ⇒ asymm). -/
    instance (priority := 50) instStdAsymmOfSLO {α : Type} [LT α] [DecidableEq α]
        [slo : StrictLinearOrder α] : Std.Asymm (fun a b : α => a < b) where
      asymm := fun _ _ hab hba => slo.irrefl _ (slo.trans hab hba)

    /-- `Std.Trichotomous` derivado de `StrictLinearOrder α`. -/
    instance (priority := 50) instStdTrichotomousOfSLO {α : Type} [LT α] [DecidableEq α]
        [slo : StrictLinearOrder α] : Std.Trichotomous (fun a b : α => a < b) where
      trichotomous := slo.trich

    /-- `Trans` derivado de `StrictLinearOrder α`. -/
    instance (priority := 50) instTransOfSLO {α : Type} [LT α] [DecidableEq α]
        [slo : StrictLinearOrder α] :
        Trans (fun a b : α => a < b) (fun a b : α => a < b) (fun a b : α => a < b) where
      trans := slo.trans

    /-- Orden lineal estricto sobre `FSet α`, heredado del orden lexicográfico
        sobre listas cuando `α` tiene `StrictLinearOrder`. -/
    instance instStrictLinearOrderFSet {α : Type} [DecidableEq α] [LT α]
        [slo : StrictLinearOrder α] : StrictLinearOrder (FSet α) where
      decLt := fun _s _t =>
        have : DecidableRel (@LT.lt α _) := slo.decLt
        inferInstance
      irrefl := fun s hs => List.lt_irrefl s.elems hs
      trans := fun h1 h2 => List.lt_trans h1 h2
      trich := fun s t hs ht =>
        FSet.ext (instTrichotomousListLt.trichotomous s.elems t.elems hs ht)

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Aliases de tipos concretos

    /-- Conjunto finito de naturales de Peano (ℕ₀). -/
    abbrev ℕ₀FSet := FSet ℕ₀

    /-- Conjunto finito de naturales positivos (ℕ₁). -/
    abbrev ℕ₁FSet := FSet ℕ₁

    /-- Conjunto finito de naturales ≥ 2 (ℕ₂). -/
    abbrev ℕ₂FSet := FSet ℕ₂

    /-- Decidabilidad de `<` en `ℕ₀`, expuesta como `DecidableRel`.
        Esto permite heredar comparación decidible en `FSet ℕ₀` y, por extensión,
        en niveles anidados como `FSet (FSet ℕ₀)`. -/
    instance : DecidableRel (@LT.lt ℕ₀ _) :=
      fun a b => Peano.StrictOrder.decidableLt a b

    -- ─────────────────────────────────────────────────────────────────
    -- Instancias nombradas de DecidableEq para los alias concretos.
    -- La instancia genérica `DecidableEq (FSet α)` vive más arriba;
    -- estos alias permiten al elaborador resolverlas sin búsqueda.
    -- ─────────────────────────────────────────────────────────────────
    instance instDecidableEqℕ₀FSet : DecidableEq ℕ₀FSet := inferInstance
    instance instDecidableEqℕ₁FSet : DecidableEq ℕ₁FSet := inferInstance
    instance instDecidableEqℕ₂FSet : DecidableEq ℕ₂FSet := inferInstance

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
      | []             => True
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

  end FSet

  /-- Dos listas de ℕ₀ estrictamente ordenadas con la misma pertenencia son iguales.
      Unicidad de la forma canónica sorted. -/
  private theorem sorted_nodup_unique_list :
      ∀ {l₁ l₂ : List ℕ₀},
      List.Pairwise (· < ·) l₁ → List.Pairwise (· < ·) l₂ →
      (∀ z : ℕ₀, z ∈ l₁ ↔ z ∈ l₂) → l₁ = l₂
    | [], [], _, _, _ => rfl
    | [], y :: ys, _, _, hmem =>
        absurd ((hmem y).mpr List.mem_cons_self) List.not_mem_nil
    | x :: xs, [], _, _, hmem =>
        absurd ((hmem x).mp List.mem_cons_self) List.not_mem_nil
    | x :: xs, y :: ys, hs₁, hs₂, hmem =>
        have hxs₁ := List.pairwise_cons.mp hs₁
        have hxs₂ := List.pairwise_cons.mp hs₂
        have hxy : x = y := by
          have hx_in : x ∈ y :: ys := (hmem x).mp List.mem_cons_self
          have hy_in : y ∈ x :: xs := (hmem y).mpr List.mem_cons_self
          rcases List.mem_cons.mp hx_in with rfl | hx_ys
          · rfl
          · rcases List.mem_cons.mp hy_in with rfl | hy_xs
            · rfl
            · exact absurd
                (Peano.StrictOrder.lt_trans_wp
                  (List.rel_of_pairwise_cons hs₁ hy_xs)
                  (List.rel_of_pairwise_cons hs₂ hx_ys))
                (Peano.StrictOrder.nlt_self x)
        have htail : xs = ys := by
          apply sorted_nodup_unique_list hxs₁.2 hxs₂.2
          intro z
          constructor
          · intro hz
            have hzy := (hmem z).mp (List.mem_cons.mpr (Or.inr hz))
            rcases List.mem_cons.mp hzy with h_eq | h
            · -- h_eq : z = y; hz : z ∈ xs; hence x < z with hxy : x = y → x < x
              have h_lt : lt₀ x z := List.rel_of_pairwise_cons hs₁ hz
              rw [h_eq, ← hxy] at h_lt
              exact absurd h_lt (Peano.StrictOrder.nlt_self x)
            · exact h
          · intro hz
            have hzx := (hmem z).mpr (List.mem_cons.mpr (Or.inr hz))
            rcases List.mem_cons.mp hzx with h_eq | h
            · -- h_eq : z = x; hz : z ∈ ys; hence y < z with hxy : x = y → y < y
              have h_lt : lt₀ y z := List.rel_of_pairwise_cons hs₂ hz
              rw [h_eq, hxy] at h_lt
              exact absurd h_lt (Peano.StrictOrder.nlt_self y)
            · exact h
        Eq.trans (congrArg (List.cons x) htail) (congrArg (· :: ys) hxy)

  /-- Versión genérica: dos listas de `α` estrictamente ordenadas con la misma
      pertenencia son iguales. Requiere `StrictLinearOrder α`. -/
  private theorem sorted_nodup_unique_list' {α : Type} [DecidableEq α] [LT α]
      [slo : StrictLinearOrder α] :
      ∀ {l₁ l₂ : List α},
      List.Pairwise (· < ·) l₁ → List.Pairwise (· < ·) l₂ →
      (∀ z : α, z ∈ l₁ ↔ z ∈ l₂) → l₁ = l₂
    | [], [], _, _, _ => rfl
    | [], y :: ys, _, _, hmem =>
        absurd ((hmem y).mpr List.mem_cons_self) List.not_mem_nil
    | x :: xs, [], _, _, hmem =>
        absurd ((hmem x).mp List.mem_cons_self) List.not_mem_nil
    | x :: xs, y :: ys, hs₁, hs₂, hmem =>
        have hxs₁ := List.pairwise_cons.mp hs₁
        have hxs₂ := List.pairwise_cons.mp hs₂
        have hxy : x = y := by
          have hx_in : x ∈ y :: ys := (hmem x).mp List.mem_cons_self
          have hy_in : y ∈ x :: xs := (hmem y).mpr List.mem_cons_self
          rcases List.mem_cons.mp hx_in with rfl | hx_ys
          · rfl
          · rcases List.mem_cons.mp hy_in with rfl | hy_xs
            · rfl
            · exact absurd
                (slo.trans
                  (List.rel_of_pairwise_cons hs₁ hy_xs)
                  (List.rel_of_pairwise_cons hs₂ hx_ys))
                (slo.irrefl x)
        have htail : xs = ys := by
          apply sorted_nodup_unique_list' hxs₁.2 hxs₂.2
          intro z
          constructor
          · intro hz
            have hzy := (hmem z).mp (List.mem_cons.mpr (Or.inr hz))
            rcases List.mem_cons.mp hzy with h_eq | h
            · have h_lt : x < z := List.rel_of_pairwise_cons hs₁ hz
              rw [h_eq, hxy] at h_lt
              exact absurd h_lt (slo.irrefl y)
            · exact h
          · intro hz
            have hzx := (hmem z).mpr (List.mem_cons.mpr (Or.inr hz))
            rcases List.mem_cons.mp hzx with h_eq | h
            · have h_lt : y < z := List.rel_of_pairwise_cons hs₂ hz
              rw [h_eq, hxy] at h_lt
              exact absurd h_lt (slo.irrefl y)
            · exact h
        Eq.trans (congrArg (List.cons x) htail) (congrArg (· :: ys) hxy)

  namespace FSet

    /-- Extensionalidad semántica de `ℕ₀FSet`: dos conjuntos con la misma
        pertenencia (∀ z, z ∈ s₁ ↔ z ∈ s₂) son iguales. -/
    theorem FSet.eq_of_mem_iff {s₁ s₂ : FSet ℕ₀}
        (h : ∀ z : ℕ₀, z ∈ s₁.elems ↔ z ∈ s₂.elems) : s₁ = s₂ :=
      FSet.ext (sorted_nodup_unique_list s₁.sorted s₂.sorted h)

    /-- Extensionalidad semántica genérica de `FSet α`:
        dos conjuntos con la misma pertenencia son iguales. -/
    theorem FSet.eq_of_mem_iff' {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {s₁ s₂ : FSet α}
        (h : ∀ z : α, z ∈ s₁.elems ↔ z ∈ s₂.elems) : s₁ = s₂ :=
      FSet.ext (sorted_nodup_unique_list' s₁.sorted s₂.sorted h)

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Inserción ordenada genérica (StrictLinearOrder α)
    -- ══════════════════════════════════════════════════════════════════

    /-- Inserta `x` en una lista ordenada manteniendo el orden estricto
        y descartando duplicados. Requiere `StrictLinearOrder α` para
        decidibilidad, transitividad y tricotomía. -/
    def sortedInsert {α : Type} [LT α] [DecidableEq α] [StrictLinearOrder α]
        (x : α) : List α → List α
      | []      => [x]
      | y :: ys =>
        if x < y       then x :: y :: ys
        else if x = y  then y :: ys
        else                y :: sortedInsert x ys

    /-- Lema de pertenencia para `sortedInsert`. -/
    theorem mem_sortedInsert_iff {α : Type} [LT α] [DecidableEq α] [StrictLinearOrder α]
        {z x : α} {l : List α} :
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
    /-- La inserción ordenada preserva `Sorted (· < ·)`.
        Requiere `StrictLinearOrder α` para transitividad y tricotomía. -/
    theorem sorted_sortedInsert {α : Type} [LT α] [DecidableEq α] [StrictLinearOrder α]
        {l : List α} (hs : Sorted (· < ·) l) (x : α) :
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
              | Or.inr h => StrictLinearOrder.trans hlt (List.rel_of_pairwise_cons hs h))
            hs
        next h_nlt =>
          split
          next heq => exact hs
          next hneq =>
            have hys := (List.pairwise_cons.mp hs).2
            have hyx : y < x :=
              Decidable.byContradiction (fun h => hneq (StrictLinearOrder.trich x y h_nlt h))
            refine List.Pairwise.cons (fun z hz => ?_) (ih hys)
            rcases mem_sortedInsert_iff.mp hz with h | h
            · exact h ▸ hyx
            · exact List.rel_of_pairwise_cons hs h

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

      /-- El segmento inicial `{0, 1, …, n-1}` como `ℕ₀FSet`.
          `Fin₀Set 𝟘 = ∅`, `Fin₀Set (σ n) = Fin₀Set n ∪ {n}`. -/
      def Fin₀Set : ℕ₀ → ℕ₀FSet
        | .zero   => empty
        | .succ n => insert n (Fin₀Set n)

      /-- `k ∈ Fin₀Set n ↔ k < n`. -/
      theorem mem_Fin₀Set_iff (n k : ℕ₀) :
          k ∈ (Fin₀Set n).elems ↔ lt₀ k n := by
        induction n with
        | zero =>
          simp only [Fin₀Set, empty, FSet.empty, List.not_mem_nil, false_iff]
          exact Peano.StrictOrder.nlt_n_0 k
        | succ n' ih =>
          simp only [Fin₀Set, insert]
          rw [mem_sortedInsert_iff]
          rw [Peano.StrictOrder.lt_succ_iff_lt_or_eq]
          constructor
          · rintro (rfl | hk)
            · exact Or.inr rfl
            · exact Or.inl (ih.mp hk)
          · rintro (hlt | rfl)
            · exact Or.inr (ih.mpr hlt)
            · exact Or.inl rfl

      /-! `Fin₀Set n` tiene exactamente `n` elementos. -/
      open Peano.StrictOrder in
      private theorem sortedInsert_length_of_not_mem
        (x : ℕ₀) (l : List ℕ₀) (hnotin : x ∉ l) :
          (sortedInsert x l).length = l.length.succ
            := by
        induction l with
        | nil => simp [sortedInsert]
        | cons y ys ih =>
          have hnotin_ys : x ∉ ys := fun h => hnotin (List.mem_cons.mpr (Or.inr h))
          have hxney : x ≠ y := fun heq => hnotin (heq ▸ List.mem_cons.mpr (Or.inl rfl))
          unfold sortedInsert
          by_cases hlt : x < y
          · rw [if_pos hlt]; simp [List.length_cons]
          · rw [if_neg hlt, if_neg hxney]
            simp [List.length_cons, ih hnotin_ys]

      open Peano.StrictOrder in
      theorem Fin₀Set_card (n : ℕ₀) : (Fin₀Set n).card = n := by
        induction n with
        | zero => rfl
        | succ n' ih =>
          have hnotin : n' ∉ (Fin₀Set n').elems :=
            fun hmem => nlt_self n' ((mem_Fin₀Set_iff n' n').mp hmem)
          show Λ (sortedInsert n' (Fin₀Set n').elems).length = σ n'
          rw [sortedInsert_length_of_not_mem n' _ hnotin]
          exact congrArg ℕ₀.succ ih

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
    namespace FactFSet

    def empty : FactFSet :=
      FactFSet.mk [] (sorted_nil _) trivial

    def card (s : FactFSet) : ℕ₀ := lengthₚ s.elems

    /-- Singleton: el conjunto que contiene exactamente el factor `(p, e)`. -/
    def singleton (pe : ℕ₂ × ℕ₁) : FactFSet :=
      FactFSet.mk [pe]
        (List.Pairwise.cons (fun _ h => absurd h List.not_mem_nil) List.Pairwise.nil)
        ⟨fun _ _ h => absurd h List.not_mem_nil, trivial⟩

    /-- Par ordenado: el conjunto que contiene exactamente los factores `p1` y `p2`,
        con la condición de que la base de `p1` sea estrictamente menor que la de `p2`.
        Esto asegura el invariante `SortedByKey`. -/
    def pair (p1 p2 : ℕ₂ × ℕ₁) (h : p1.1 < p2.1) : FactFSet :=
      let sk : SortedByKey [p1, p2] :=
        List.Pairwise.cons
          (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact h)
          (List.Pairwise.cons (fun _ hx => absurd hx List.not_mem_nil) List.Pairwise.nil)
      FactFSet.mk [p1, p2] sk (sortedByKey_imp_uniqueKeys _ sk)

    end FactFSet

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

    -- ══════════════════════════════════════════════════════════════════
    -- § 9. FSet para tipos de peso 2 (tuplas)
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de tuplas homogéneas de ℕ₀ de longitud `n`.
        Requiere `LT (Tuple ℕ₀ n)` (via `instLTTuple`) y
        `DecidableEq (Tuple ℕ₀ n)` (via `tupleDecEq`). -/
    abbrev TupleFSet (n : ℕ₀) := FSet (Tuple ℕ₀ n)

    /-- Conjunto finito de tuplas heterogéneas con esquema `ts : List Nats`.
        Requiere `instLTNatsTuple` y `natsTupleDecEq`. -/
    abbrev NatsTupleFSet (ts : List Nats) := FSet (NatsTuple ts)

    /-- Conjunto finito de tuplas homogéneas genéricas de tipo `α` y longitud `n`.
        Requiere `[LT α]`, `[DecidableEq α]` para poder instanciar `FSet`. -/
    abbrev GTupleFSet (α : Type) [LT α] [DecidableEq α] (n : ℕ₀) :=
      FSet (Tuple α n)

    /-- Conjunto finito de tuplas heterogéneas con esquema `ts : List Type`.
        Requiere las typeclasses `HTupleDecidableEq ts` y `HTupleLT ts`. -/
    abbrev HTupleFSet (ts : List Type)
        [HTupleDecidableEq ts] [HTupleLT ts] :=
      FSet (HTuple ts)

    namespace TupleFSet
      def empty (n : ℕ₀) : TupleFSet n := FSet.empty
      def singleton (n : ℕ₀) (t : Tuple ℕ₀ n) : TupleFSet n := FSet.singleton t
      /-- Construye un `TupleFSet` desde una lista ya ordenada. -/
      def ofSortedList (n : ℕ₀) (l : List (Tuple ℕ₀ n))
          (h : Sorted (· < ·) l) : TupleFSet n := ⟨l, h⟩
    end TupleFSet

    namespace NatsTupleFSet
      def empty (ts : List Nats) : NatsTupleFSet ts := FSet.empty
      def singleton (ts : List Nats) (t : NatsTuple ts) : NatsTupleFSet ts :=
        FSet.singleton t
      def ofSortedList (ts : List Nats) (l : List (NatsTuple ts))
          (h : Sorted (· < ·) l) : NatsTupleFSet ts := ⟨l, h⟩
    end NatsTupleFSet

    namespace GTupleFSet
      def empty (α : Type) [LT α] [DecidableEq α] (n : ℕ₀) :
          GTupleFSet α n := FSet.empty
      def singleton (α : Type) [LT α] [DecidableEq α] (n : ℕ₀)
          (t : Tuple α n) : GTupleFSet α n := FSet.singleton t
      def ofSortedList (α : Type) [LT α] [DecidableEq α] (n : ℕ₀)
          (l : List (Tuple α n)) (h : Sorted (· < ·) l) :
          GTupleFSet α n := ⟨l, h⟩
    end GTupleFSet

    namespace HTupleFSet
      def empty (ts : List Type) [HTupleDecidableEq ts] [HTupleLT ts] :
          HTupleFSet ts := FSet.empty
      def singleton (ts : List Type) [HTupleDecidableEq ts] [HTupleLT ts]
          (t : HTuple ts) : HTupleFSet ts := FSet.singleton t
      def ofSortedList (ts : List Type) [HTupleDecidableEq ts] [HTupleLT ts]
          (l : List (HTuple ts)) (h : Sorted (· < ·) l) :
          HTupleFSet ts := ⟨l, h⟩
    end HTupleFSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 10. FSet de listas (antes en FSetFSet.lean §16-§18)
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de listas de ℕ₀. -/
    abbrev Nat0ListFSet := FSet (List ℕ₀)
    /-- Conjunto finito de listas de ℕ₁. -/
    abbrev Nat1ListFSet := FSet (List ℕ₁)
    /-- Conjunto finito de listas de ℕ₂. -/
    abbrev Nat2ListFSet := FSet (List ℕ₂)
    /-- Conjunto finito de listas de `Nats`. -/
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

    -- FSet de listas de tuplas

    abbrev TupleListFSet (n : ℕ₀) := FSet (List (Tuple ℕ₀ n))
    abbrev NatsTupleListFSet (ts : List Nats) := FSet (List (NatsTuple ts))
    abbrev GTupleListFSet (α : Type) [LT α] [DecidableEq α] (n : ℕ₀) :=
      FSet (List (Tuple α n))
    abbrev HTupleListFSet (ts : List Type)
        [HTupleDecidableEq ts] [HTupleLT ts] :=
      FSet (List (HTuple ts))

    namespace TupleListFSet
      def empty (n : ℕ₀) : TupleListFSet n := FSet.empty
      def singleton (n : ℕ₀) (l : List (Tuple ℕ₀ n)) : TupleListFSet n :=
        FSet.singleton l
      def ofSortedList (n : ℕ₀) (l : List (List (Tuple ℕ₀ n)))
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
          (l : List (Tuple α n)) : GTupleListFSet α n := FSet.singleton l
      def ofSortedList (α : Type) [LT α] [DecidableEq α] (n : ℕ₀)
          (l : List (List (Tuple α n))) (h : Sorted (· < ·) l) :
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

    -- FSet de PeanoVal

    abbrev PeanoValFSet := FSet PeanoVal

    namespace PeanoValFSet
      def empty    : PeanoValFSet                  := FSet.empty
      def singleton (v : PeanoVal) : PeanoValFSet  := FSet.singleton v
      def ofSortedList (l : List PeanoVal) (h : Sorted (· < ·) l) :
          PeanoValFSet := ⟨l, h⟩
    end PeanoValFSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 11. FSet de FSet (antes en FSetFSet.lean §19)
    -- ══════════════════════════════════════════════════════════════════

    /-- Conjunto finito de conjuntos finitos de `ℕ₀`. -/
    abbrev Nat0FSetFSet := FSet ℕ₀FSet

    instance instDecidableEqNat0FSet : DecidableEq ℕ₀FSet := inferInstance
    instance instLTNat0FSet : LT ℕ₀FSet := inferInstance
    instance instDecidableRelLtNat0FSet : DecidableRel (@LT.lt ℕ₀FSet instLTNat0FSet) :=
      inferInstance

    instance instDecidableEqNat0FSetFSet : DecidableEq Nat0FSetFSet := inferInstance
    instance instLTNat0FSetFSet : LT Nat0FSetFSet := inferInstance
    instance instDecidableRelLtNat0FSetFSet :
        DecidableRel (@LT.lt Nat0FSetFSet instLTNat0FSetFSet) := inferInstance

    namespace Nat0FSetFSet
      def empty : Nat0FSetFSet := FSet.empty
      def singleton (s : ℕ₀FSet) : Nat0FSetFSet := FSet.singleton s
      def ofSortedList (l : List ℕ₀FSet) (h : Sorted (· < ·) l) :
          Nat0FSetFSet := ⟨l, h⟩
    end Nat0FSetFSet

    /-- Inserta un coset (`ℕ₀FSet`) en una lista manteniendo el orden por `<`. -/
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

    theorem sorted_sortFSetList (l : List ℕ₀FSet) :
        Sorted (· < ·) (sortFSetList l) := by
      induction l with
      | nil => exact sorted_nil _
      | cons x xs ih =>
          exact sorted_sortedInsertFSet ih x

    theorem mem_sortFSetList_iff {x : ℕ₀FSet} {l : List ℕ₀FSet} :
        x ∈ sortFSetList l ↔ x ∈ l := by
      induction l with
      | nil => simp [sortFSetList]
      | cons y ys ih =>
          simp [sortFSetList, mem_sortedInsertFSet_iff, ih];

    -- ══════════════════════════════════════════════════════════════════
    -- § 11b. Ordenación genérica de listas: sortedInsert' / sortList'
    -- ══════════════════════════════════════════════════════════════════

    /-- Inserta un elemento en una lista ya ordenada, manteniendo el orden.
        Versión genérica para cualquier `β` con `StrictLinearOrder β`. -/
    def sortedInsert' {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        (x : β) : List β → List β
      | [] => [x]
      | y :: ys =>
          if x < y then x :: y :: ys
          else if x = y then y :: ys
          else y :: sortedInsert' x ys

    /-- Ordenación por inserción genérica para `List β`. -/
    def sortList' {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        : List β → List β
      | [] => []
      | x :: xs => sortedInsert' x (sortList' xs)

    theorem mem_sortedInsert'_iff {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        {z x : β} {l : List β} :
        z ∈ sortedInsert' x l ↔ z = x ∨ z ∈ l := by
      induction l with
      | nil => simp [sortedInsert']
      | cons y ys ih =>
        simp only [sortedInsert']
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

    theorem sorted_sortedInsert' {β : Type} [DecidableEq β] [LT β]
        [slo : StrictLinearOrder β] {l : List β}
        (hs : Sorted (· < ·) l) (x : β) :
        Sorted (· < ·) (sortedInsert' x l) := by
      induction l with
      | nil => exact sorted_singleton _ x
      | cons y ys ih =>
        unfold sortedInsert'
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
                match mem_sortedInsert'_iff.mp hz with
                | Or.inl hzx =>
                    hzx ▸
                    have : Decidable (y < x) := slo.decLt y x
                    Decidable.byContradiction (fun hyx => hneq (slo.trich x y hnotlt hyx))
                | Or.inr hmem => List.rel_of_pairwise_cons hs hmem)
              (ih hys)

    theorem sorted_sortList' {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        (l : List β) :
        Sorted (· < ·) (sortList' l) := by
      induction l with
      | nil => exact sorted_nil _
      | cons x xs ih =>
          exact sorted_sortedInsert' ih x

    theorem mem_sortList'_iff {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        {x : β} {l : List β} :
        x ∈ sortList' l ↔ x ∈ l := by
      induction l with
      | nil => simp [sortList']
      | cons y ys ih =>
          simp [sortList', mem_sortedInsert'_iff, ih]

    /-- Construye un `FSet β` a partir de una lista genérica (posiblemente no ordenada). -/
    def FSet.ofList {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        (l : List β) : FSet β :=
      ⟨sortList' l, sorted_sortList' l⟩

    theorem FSet.mem_ofList_iff {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
        {x : β} {l : List β} :
        x ∈ (FSet.ofList l).elems ↔ x ∈ l :=
      mem_sortList'_iff

    -- ══════════════════════════════════════════════════════════════════
    -- § 12. Unión, intersección, imagen, cociente
    -- ══════════════════════════════════════════════════════════════════

    /-- Inserción genérica en `FSet α` (requiere `StrictLinearOrder α`). -/
    def FSet.insert {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (x : α) (s : FSet α) : FSet α :=
      ⟨sortedInsert x s.elems, sorted_sortedInsert s.sorted x⟩

    /-- `x ∈ FSet.insert y s ↔ x = y ∨ x ∈ s`. -/
    theorem mem_insert_iff {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {x y : α} {s : FSet α} :
        x ∈ FSet.insert y s ↔ x = y ∨ x ∈ s :=
      mem_sortedInsert_iff

    -- ── unión ────────────────────────────────────────────────────────

    private def fsetFoldInsert {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (l : List α) (acc : FSet α) : FSet α :=
      l.foldl (fun a x => FSet.insert x a) acc

    private theorem mem_fsetFoldInsert_iff
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {z : α} (l : List α) (acc : FSet α) :
        z ∈ fsetFoldInsert l acc ↔ z ∈ l ∨ z ∈ acc := by
      induction l generalizing acc with
      | nil => simp [fsetFoldInsert]
      | cons x xs ih =>
        have key : fsetFoldInsert (x :: xs) acc =
                   fsetFoldInsert xs (FSet.insert x acc) := rfl
        rw [key, ih, mem_insert_iff, List.mem_cons]
        constructor
        · rintro (hxs | rfl | hacc)
          · exact Or.inl (Or.inr hxs)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr hacc
        · rintro ((rfl | hxs) | hacc)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl hxs
          · exact Or.inr (Or.inr hacc)

    /-- Unión de dos `FSet α`. Requiere `StrictLinearOrder α`. -/
    def FSet.union {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (s₁ s₂ : FSet α) : FSet α :=
      fsetFoldInsert s₁.elems s₂

    /-- `z ∈ s₁ ∪ s₂ ↔ z ∈ s₁ ∨ z ∈ s₂`. -/
    theorem mem_union_iff {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {z : α} {s₁ s₂ : FSet α} :
        z ∈ FSet.union s₁ s₂ ↔ z ∈ s₁ ∨ z ∈ s₂ :=
      mem_fsetFoldInsert_iff s₁.elems s₂

    -- ── intersección ─────────────────────────────────────────────────

    /-- Intersección de dos `FSet α`. Requiere sólo `[DecidableEq α] [LT α]`. -/
    def FSet.inter {α : Type} [DecidableEq α] [LT α]
        (s₁ s₂ : FSet α) : FSet α :=
      FSet.filter (fun x => decide (x ∈ s₂)) s₁

    /-- `z ∈ s₁ ∩ s₂ ↔ z ∈ s₁ ∧ z ∈ s₂`. -/
    theorem mem_inter_iff {α : Type} [DecidableEq α] [LT α]
        {z : α} {s₁ s₂ : FSet α} :
        z ∈ FSet.inter s₁ s₂ ↔ z ∈ s₁ ∧ z ∈ s₂ := by
      simp only [FSet.inter, FSet.filter]
      constructor
      · intro h
        have ⟨hmem, hdec⟩ := List.mem_filter.mp h
        exact ⟨hmem, of_decide_eq_true hdec⟩
      · rintro ⟨h₁, h₂⟩
        exact List.mem_filter.mpr ⟨h₁, decide_eq_true h₂⟩

    -- ── imagen ────────────────────────────────────────────────────────

    /-- Imagen de `s` bajo `f`. Requiere `StrictLinearOrder β`. -/
    def FSet.image {α β : Type} [DecidableEq α] [LT α]
        [DecidableEq β] [LT β] [StrictLinearOrder β]
        (f : α → β) (s : FSet α) : FSet β :=
      fsetFoldInsert (s.elems.map f) FSet.empty

    /-- `y ∈ FSet.image f s ↔ ∃ x ∈ s, f x = y`. -/
    theorem mem_image_iff {α β : Type} [DecidableEq α] [LT α]
        [DecidableEq β] [LT β] [StrictLinearOrder β]
        {y : β} {f : α → β} {s : FSet α} :
        y ∈ FSet.image f s ↔ ∃ x ∈ s, f x = y := by
      simp only [FSet.image]
      rw [mem_fsetFoldInsert_iff]
      constructor
      · rintro (h | hempty)
        · rw [List.mem_map] at h
          obtain ⟨x, hx, hfx⟩ := h
          exact ⟨x, hx, hfx⟩
        · exact nomatch hempty
      · rintro ⟨x, hx, hfx⟩
        exact Or.inl (List.mem_map.mpr ⟨x, hx, hfx⟩)

    -- ── cociente ──────────────────────────────────────────────────────

    private def insertIntoClass
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (r : α → α → Bool) (x : α) : List (FSet α) → List (FSet α)
      | []      => [FSet.singleton x]
      | d :: ds =>
          if d.elems.any (fun y => r x y)
          then FSet.insert x d :: ds
          else d :: insertIntoClass r x ds

    private theorem mem_insertIntoClass
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (r : α → α → Bool) (x : α) (classes : List (FSet α)) :
        ∃ c ∈ insertIntoClass r x classes, x ∈ c := by
      induction classes with
      | nil =>
        exact ⟨FSet.singleton x, List.mem_cons.mpr (Or.inl rfl),
               List.mem_cons.mpr (Or.inl rfl)⟩
      | cons d ds ih =>
        simp only [insertIntoClass]
        split
        · exact ⟨FSet.insert x d, List.mem_cons.mpr (Or.inl rfl),
                 mem_insert_iff.mpr (Or.inl rfl)⟩
        · obtain ⟨c, hc, hxc⟩ := ih
          exact ⟨c, List.mem_cons.mpr (Or.inr hc), hxc⟩

    private theorem mem_preserved_by_insertIntoClass
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (r : α → α → Bool) (a : α) {z : α} :
        ∀ (classes : List (FSet α)),
        (∃ c ∈ classes, z ∈ c) → ∃ c ∈ insertIntoClass r a classes, z ∈ c := by
      intro classes
      induction classes with
      | nil => rintro ⟨_, h, _⟩; exact nomatch h
      | cons d ds ih =>
        rintro ⟨c, hclist, hzc⟩
        simp only [insertIntoClass]
        rcases List.mem_cons.mp hclist with rfl | hcds <;> split
        · exact ⟨FSet.insert a c, List.mem_cons.mpr (Or.inl rfl),
                 mem_insert_iff.mpr (Or.inr hzc)⟩
        · exact ⟨c, List.mem_cons.mpr (Or.inl rfl), hzc⟩
        · exact ⟨c, List.mem_cons.mpr (Or.inr hcds), hzc⟩
        · obtain ⟨c', hc', hzc'⟩ := ih ⟨c, hcds, hzc⟩
          exact ⟨c', List.mem_cons.mpr (Or.inr hc'), hzc'⟩

    private theorem mem_preserved_by_foldl
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (r : α → α → Bool) (l : List α) {z : α} (classes : List (FSet α))
        (h : ∃ c ∈ classes, z ∈ c) :
        ∃ c ∈ l.foldl (fun cs y => insertIntoClass r y cs) classes, z ∈ c := by
      induction l generalizing classes with
      | nil => exact h
      | cons a as ih =>
        simp only [List.foldl_cons]
        exact ih _ (mem_preserved_by_insertIntoClass r a classes h)

    private theorem mem_quotient_foldl
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (r : α → α → Bool) {x : α} (l : List α) (classes : List (FSet α))
        (hx : x ∈ l) :
        ∃ c ∈ l.foldl (fun cs y => insertIntoClass r y cs) classes, x ∈ c := by
      induction l generalizing classes with
      | nil => exact nomatch hx
      | cons a as ih =>
        simp only [List.foldl_cons]
        rcases List.mem_cons.mp hx with rfl | hxas
        · exact mem_preserved_by_foldl r as _ (mem_insertIntoClass r x classes)
        · exact ih (insertIntoClass r a classes) hxas

    /-- Cociente de `s` por la relación `r` (debe ser de equivalencia).
        Devuelve la lista de clases; `r` no se verifica en tiempo de ejecución. -/
    def FSet.quotient {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        (r : α → α → Bool) (s : FSet α) : List (FSet α) :=
      s.elems.foldl (fun classes x => insertIntoClass r x classes) []

    /-- Todo elemento de `s` pertenece a alguna clase en `FSet.quotient r s`. -/
    theorem mem_quotient_classes
        {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {r : α → α → Bool} {s : FSet α} {x : α} (hx : x ∈ s) :
        ∃ c ∈ FSet.quotient r s, x ∈ c :=
      mem_quotient_foldl r s.elems [] hx

  end FSet

end Peano

export Peano.FSet (
  FSet
  FSet.ext
  FSet.eq_of_mem_iff
  FSet.eq_of_mem_iff'
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
  TupleFSet
  NatsTupleFSet
  GTupleFSet
  HTupleFSet
  ℕ₀FSet.Fin₀Set
  ℕ₀FSet.mem_Fin₀Set_iff
  ℕ₀FSet.Fin₀Set_card
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
  sortedInsertFSet
  sortFSetList
  mem_sortedInsertFSet_iff
  sorted_sortedInsertFSet
  sorted_sortFSetList
  mem_sortFSetList_iff
  sortedInsert'
  sortList'
  mem_sortedInsert'_iff
  sorted_sortedInsert'
  sorted_sortList'
  mem_sortList'_iff
  FSet.ofList
  FSet.mem_ofList_iff
  FSet.insert
  mem_insert_iff
  FSet.union
  mem_union_iff
  FSet.inter
  mem_inter_iff
  FSet.image
  mem_image_iff
  FSet.quotient
  mem_quotient_classes
)
