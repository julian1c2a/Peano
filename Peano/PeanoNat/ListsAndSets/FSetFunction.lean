import Peano.PeanoNat.ListsAndSets.List
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFSet

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/ListsAndSets/FSetFunction.lean
-- Funciones entre conjuntos finitos (FSets) arbitrarios.
-- Generalización polimórfica de MapOn/BinOpOn de Group.lean.
--
-- § 1. MapOn             — función entre FSet α y FSet β
-- § 2. Im                — imagen de un MapOn como FSet
-- § 3. Principio del Palomar
-- § 4. BinOpOn           — operación binaria cerrada sobre un FSet
-- § 5. CoeFun            — coerción a funciones ordinarias

set_option autoImplicit false

namespace Peano
  open Peano
  open Peano.List
  open Peano.FSet

  namespace FSetFunction

    /-!
    # § 1. MapOn — funciones entre conjuntos finitos arbitrarios
    -/

    /-- Función entre dos conjuntos finitos `A : FSet α` y `B : FSet β`.
        Representada como `toFun : α → β` con prueba de que mapea cada
        elemento de `A` a un elemento de `B`. -/
    structure MapOn {α β : Type} [DecidableEq α] [LT α]
        [DecidableEq β] [LT β]
        (A : FSet α) (B : FSet β) where
      toFun        : α → β
      map_carrier  : ∀ a, a ∈ A.elems → toFun a ∈ B.elems

    /-- Composición: si `f : MapOn A B` y `g : MapOn B C`,
        entonces `g.comp f : MapOn A C`. -/
    def MapOn.comp {α β γ : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β] [DecidableEq γ] [LT γ]
        {A : FSet α} {B : FSet β} {C : FSet γ}
        (g : MapOn B C) (f : MapOn A B) : MapOn A C where
      toFun       := g.toFun ∘ f.toFun
      map_carrier := fun a ha =>
        g.map_carrier (f.toFun a) (f.map_carrier a ha)

    /-- `f` es inyectiva sobre `A`: elementos distintos tienen imágenes distintas. -/
    def InjectiveOn {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        (f : α → β) (A : FSet α) : Prop :=
      ∀ a b, a ∈ A.elems → b ∈ A.elems → f a = f b → a = b

    /-- `f` es sobreyectiva de `A` a `B`: todo elemento de `B` tiene preimagen en `A`. -/
    def SurjectiveOn {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        (f : α → β) (A : FSet α) (B : FSet β) : Prop :=
      ∀ b, b ∈ B.elems → ∃ a, a ∈ A.elems ∧ f a = b

    /-- Un `MapOn` es inyectivo si `toFun` es inyectiva sobre el dominio. -/
    def MapOn.Injective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : Prop :=
      InjectiveOn f.toFun A

    /-- Un `MapOn` es sobreyectivo si `toFun` es sobreyectiva del dominio al codominio. -/
    def MapOn.Surjective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : Prop :=
      SurjectiveOn f.toFun A B

    /-- Un `MapOn` es biyectivo si es inyectivo y sobreyectivo. -/
    structure MapOn.Bijective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : Prop where
      inj  : f.Injective
      surj : f.Surjective

    /-- La composición de dos `MapOn` inyectivos es inyectiva. -/
    theorem MapOn.comp_injective {α β γ : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β] [DecidableEq γ] [LT γ]
        {A : FSet α} {B : FSet β} {C : FSet γ}
        {f : MapOn A B} {g : MapOn B C}
        (hf_inj : f.Injective) (hg_inj : g.Injective) :
        (g.comp f).Injective := by
      unfold MapOn.Injective InjectiveOn MapOn.comp
      intro a₁ a₂ ha₁ ha₂ h_comp_eq
      have h_fa₁_in_B : f.toFun a₁ ∈ B.elems := f.map_carrier a₁ ha₁
      have h_fa₂_in_B : f.toFun a₂ ∈ B.elems := f.map_carrier a₂ ha₂
      have h_f_eq := hg_inj (f.toFun a₁) (f.toFun a₂) h_fa₁_in_B h_fa₂_in_B h_comp_eq
      exact hf_inj a₁ a₂ ha₁ ha₂ h_f_eq

    /-- La composición de dos `MapOn` sobreyectivos es sobreyectiva. -/
    theorem MapOn.comp_surjective {α β γ : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β] [DecidableEq γ] [LT γ]
        {A : FSet α} {B : FSet β} {C : FSet γ}
        {f : MapOn A B} {g : MapOn B C}
        (hf_surj : f.Surjective) (hg_surj : g.Surjective) :
        (g.comp f).Surjective := by
      unfold MapOn.Surjective SurjectiveOn MapOn.comp
      intro c hc
      obtain ⟨b, hb_in_B, hg_b_eq_c⟩ := hg_surj c hc
      obtain ⟨a, ha_in_A, hf_a_eq_b⟩ := hf_surj b hb_in_B
      exact ⟨a, ha_in_A, by dsimp; rw [hf_a_eq_b]; exact hg_b_eq_c⟩

    /-- La composición de dos `MapOn` biyectivos es biyectiva. -/
    theorem MapOn.comp_bijective {α β γ : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β] [DecidableEq γ] [LT γ]
        {A : FSet α} {B : FSet β} {C : FSet γ}
        {f : MapOn A B} {g : MapOn B C}
        (hf_bij : f.Bijective) (hg_bij : g.Bijective) :
        (g.comp f).Bijective :=
      ⟨MapOn.comp_injective hf_bij.inj hg_bij.inj,
       MapOn.comp_surjective hf_bij.surj hg_bij.surj⟩

    /-!
    # § 2. Imagen de un MapOn
    -/

    /-- Imagen de `f : MapOn A B`: subconjunto de `B` formado por los valores
        `f(a)` para `a ∈ A`. Se construye filtrando `B` (preserva el orden)
        usando `map_carrier` como garantía de contención. -/
    def MapOn.Im {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : FSet β :=
      B.filter (fun b => A.elems.any (fun a => decide (f.toFun a = b)))

    /-!
    # § 3. Principio del Palomar
    -/

    -- ── Lemas auxiliares de lista ─────────────────────────────────────

    /-- Lista ordenada estrictamente → sin duplicados. -/
    private theorem sorted_nodup {α : Type} [DecidableEq α] [LT α]
        [StrictOrder.IrreflLT α]
        {l : List α} (hs : Sorted (· < ·) l) : l.Nodup := by
      induction l with
      | nil => exact List.nodup_nil
      | cons x xs ih =>
        have hpw := List.pairwise_cons.mp hs
        refine List.nodup_cons.mpr ⟨?_, ih hpw.2⟩
        intro hx
        exact absurd (hpw.1 x hx) (StrictOrder.IrreflLT.lt_irrefl x)

    /-- Imagen de lista sin duplicados por función inyectiva → sin duplicados. -/
    private theorem nodup_map_of_inj_on {α β : Type}
        (f : α → β) (l : List α)
        (hnd : l.Nodup)
        (hinj : ∀ a b, a ∈ l → b ∈ l → f a = f b → a = b) :
        (l.map f).Nodup := by
      induction l with
      | nil => exact List.nodup_nil
      | cons x xs ih =>
        rw [List.nodup_cons] at hnd
        obtain ⟨hx_nin, hxs⟩ := hnd
        rw [List.map_cons, List.nodup_cons]
        constructor
        · rw [List.mem_map]
          rintro ⟨y, hy, hfy⟩
          have hxy : x = y := hinj x y
            (List.mem_cons.mpr (Or.inl rfl))
            (List.mem_cons_of_mem x hy)
            hfy.symm
          exact hx_nin (hxy ▸ hy)
        · exact ih hxs (fun a b ha hb hab =>
            hinj a b (List.mem_cons_of_mem x ha)
                     (List.mem_cons_of_mem x hb) hab)

    /-- `b ∈ Im.elems ↔ ∃ a ∈ A.elems, f a = b`. -/
    private theorem mem_Im_elems_iff {α β : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (b : β) :
        b ∈ f.Im.elems ↔ ∃ a, a ∈ A.elems ∧ f.toFun a = b := by
      simp only [MapOn.Im, FSet.filter]
      rw [List.mem_filter, List.any_eq_true]
      constructor
      · rintro ⟨_, a, ha, hd⟩
        simp only [decide_eq_true_eq] at hd
        exact ⟨a, ha, hd⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨f.map_carrier a ha, a, ha, by simp⟩

    /-- Dos listas sin duplicados con los mismos elementos tienen la misma longitud. -/
    private theorem nodup_count_le_one {α : Type} [DecidableEq α]
        (a : α) (l : List α) (hn : l.Nodup) : List.count a l ≤ 1 := by
      induction l with
      | nil => simp
      | cons x xs ih =>
        rw [List.nodup_cons] at hn
        obtain ⟨hx, hxs⟩ := hn
        rw [List.count_cons]
        by_cases hax : a = x
        · subst hax
          have h0 : List.count a xs = 0 := List.count_eq_zero_of_not_mem hx
          simp [h0]
        · have hne : x ≠ a := Ne.symm hax
          have hf : (x == a) = false := by simp [hne]
          simp [hf, ih hxs]

    private theorem nodup_length_eq_of_same_elems {α : Type} [DecidableEq α]
        {l₁ l₂ : List α}
        (h1 : l₁.Nodup) (h2 : l₂.Nodup)
        (hsub12 : ∀ x, x ∈ l₁ → x ∈ l₂)
        (hsub21 : ∀ x, x ∈ l₂ → x ∈ l₁) :
        l₁.length = l₂.length := by
      apply List.Perm.length_eq
      rw [List.perm_iff_count]
      intro a
      by_cases ha1 : a ∈ l₁
      · have ha2 : a ∈ l₂ := hsub12 a ha1
        have hc1 : List.count a l₁ = 1 := by
          have := nodup_count_le_one a l₁ h1
          have := List.count_pos_iff.mpr ha1
          omega
        have hc2 : List.count a l₂ = 1 := by
          have := nodup_count_le_one a l₂ h2
          have := List.count_pos_iff.mpr ha2
          omega
        omega
      · have ha2 : a ∉ l₂ := fun h => ha1 (hsub21 a h)
        rw [List.count_eq_zero_of_not_mem ha1, List.count_eq_zero_of_not_mem ha2]

    /-- `lengthₚ` de una lista: `lengthₚ l = Λ l.length`. -/
    private theorem lengthₚ_eq_Λ_length {α : Type} (l : List α) :
        lengthₚ l = Λ l.length := rfl

    /-- `Λ` es inyectiva (del proyecto). -/
    private theorem Λ_inj_local (n m : Nat) : Λ n = Λ m → n = m :=
      Peano.Axioms.Λ_inj n m

    /-- Lema auxiliar: lista nodup contenida (como conjunto) en otra → longitud ≤. -/
    private theorem nodup_subset_length_le {α : Type} [DecidableEq α] :
        ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) →
        l₁.length ≤ l₂.length
      | [], _ => fun _ _ => Nat.zero_le _
      | a :: l₁', l₂ => fun hnd hsub => by
        rw [List.nodup_cons] at hnd
        obtain ⟨ha_nin, hnd'⟩ := hnd
        have ha2 : a ∈ l₂ := hsub a List.mem_cons_self
        have hsub' : ∀ x, x ∈ l₁' → x ∈ l₂.erase a := by
          intro x hx
          have hx_ne_a : x ≠ a := fun heq => ha_nin (heq ▸ hx)
          exact (List.mem_erase_of_ne hx_ne_a).mpr (hsub x (List.mem_cons_of_mem a hx))
        have h_ih := nodup_subset_length_le hnd' hsub'
        rw [List.length_cons]
        have h_erase_len := List.length_erase_of_mem ha2
        have h_pos : 0 < l₂.length := by
          cases l₂ with
          | nil => exact absurd ha2 List.not_mem_nil
          | cons _ _ => exact Nat.zero_lt_succ _
        omega

    /-- Lema auxiliar: si `l` es nodup, `a₁ ≠ a₂`, ambos en `l`, y `f a₁ = f a₂`,
        entonces `l.map f` no es nodup. -/
    private theorem not_nodup_map_of_ne_of_eq {α β : Type} [DecidableEq α] [DecidableEq β]
        {a₁ a₂ : α} {f : α → β}
        (h_ne : a₁ ≠ a₂) (heq : f a₁ = f a₂) :
        ∀ {l : List α}, l.Nodup → a₁ ∈ l → a₂ ∈ l →
        ¬ (l.map f).Nodup
      | [], _, ha₁, _ => absurd ha₁ List.not_mem_nil
      | x :: xs, hnd, ha₁, ha₂ => fun hnd_map => by
        rw [List.nodup_cons] at hnd
        obtain ⟨hx_nin, hnd_xs⟩ := hnd
        rw [List.map_cons, List.nodup_cons] at hnd_map
        obtain ⟨hfx_nin, hnd_map_xs⟩ := hnd_map
        rcases List.mem_cons.mp ha₁ with rfl | ha₁_xs
        · -- a₁ = x
          rcases List.mem_cons.mp ha₂ with rfl | ha₂_xs
          · exact h_ne rfl
          · exact hfx_nin (heq ▸ List.mem_map_of_mem ha₂_xs)
        · rcases List.mem_cons.mp ha₂ with rfl | ha₂_xs
          · exact hfx_nin (heq.symm ▸ List.mem_map_of_mem ha₁_xs)
          · exact not_nodup_map_of_ne_of_eq h_ne heq hnd_xs ha₁_xs ha₂_xs hnd_map_xs

    /-- Lema auxiliar: si `l₁` es nodup, `l₁` y `l₂` tienen los mismos elementos,
        y la misma longitud, entonces `l₂` es nodup. -/
    private theorem nodup_of_nodup_same_elems_length_eq {α : Type} [DecidableEq α] :
        ∀ {l₁ l₂ : List α},
        l₁.Nodup →
        (∀ x, x ∈ l₁ → x ∈ l₂) →
        (∀ x, x ∈ l₂ → x ∈ l₁) →
        l₁.length = l₂.length →
        l₂.Nodup
      | [], l₂, _, _, _, hlen => by
        have : l₂ = [] := List.eq_nil_of_length_eq_zero hlen.symm
        subst this; exact List.nodup_nil
      | a :: l₁', l₂, hnd₁, h12, h21, hlen => by
        rw [List.nodup_cons] at hnd₁
        obtain ⟨ha_nin, hnd'⟩ := hnd₁
        have ha2 : a ∈ l₂ := h12 a List.mem_cons_self
        -- Key: a ∉ l₂.erase a (por nodup_subset_length_le)
        have ha_not_erase : a ∉ l₂.erase a := by
          intro h_in_erase
          have h_le : (a :: l₁').length ≤ (l₂.erase a).length := by
            apply nodup_subset_length_le (List.nodup_cons.mpr ⟨ha_nin, hnd'⟩)
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact h_in_erase
            · have hx_ne_a : x ≠ a := fun heq => ha_nin (heq ▸ hx')
              exact (List.mem_erase_of_ne hx_ne_a).mpr
                (h12 x (List.mem_cons_of_mem a hx'))
          rw [List.length_cons] at h_le hlen
          have h_erase := List.length_erase_of_mem ha2
          omega
        -- l₂.erase a has same elements as l₁' and same length
        have h12' : ∀ x, x ∈ l₁' → x ∈ l₂.erase a := by
          intro x hx
          have hx_ne_a : x ≠ a := fun heq => ha_nin (heq ▸ hx)
          exact (List.mem_erase_of_ne hx_ne_a).mpr
            (h12 x (List.mem_cons_of_mem a hx))
        have h21' : ∀ x, x ∈ l₂.erase a → x ∈ l₁' := by
          intro x hx
          have hx_ne_a : x ≠ a := fun heq => ha_not_erase (heq ▸ hx)
          have hx_l2 : x ∈ l₂ := (List.mem_erase_of_ne hx_ne_a).mp hx
          rcases List.mem_cons.mp (h21 x hx_l2) with rfl | hx'
          · exact absurd hx ha_not_erase
          · exact hx'
        have hlen' : l₁'.length = (l₂.erase a).length := by
          rw [List.length_cons] at hlen
          have := List.length_erase_of_mem ha2
          omega
        have hnd_erase : (l₂.erase a).Nodup :=
          nodup_of_nodup_same_elems_length_eq hnd' h12' h21' hlen'
        -- l₂ = Perm(a :: l₂.erase a), and a :: l₂.erase a is nodup
        exact (List.perm_cons_erase ha2).nodup_iff.mpr
          (List.nodup_cons.mpr ⟨ha_not_erase, hnd_erase⟩)

    -- ── Los cuatro lemas del Palomar ──────────────────────────────────

    /-- Lema 1: función inyectiva → imagen tiene la misma cardinalidad que el dominio. -/
    theorem card_image_of_injective {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_inj : f.Injective) :
        f.Im.card = A.card := by
      -- Im.elems y (A.elems.map f.toFun) tienen los mismos elementos y ambos son nodup
      unfold FSet.card
      unfold lengthₚ
      congr 1
      -- Goal: f.Im.elems.length = A.elems.length (Nat)
      have h_eq_map : f.Im.elems.length = (A.elems.map f.toFun).length := by
        apply nodup_length_eq_of_same_elems
        · -- Im.elems es nodup (está ordenada)
          exact sorted_nodup f.Im.sorted
        · -- A.elems.map f.toFun es nodup (A.elems nodup + f inyectiva)
          apply nodup_map_of_inj_on
          · exact sorted_nodup A.sorted
          · intro a b ha hb hab; exact h_inj a b ha hb hab
        · -- Im.elems ⊆ A.elems.map f.toFun
          intro b hb
          rw [List.mem_map]
          rw [(mem_Im_elems_iff f b)] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          exact ⟨a, ha, rfl⟩
        · -- A.elems.map f.toFun ⊆ Im.elems
          intro b hb
          rw [List.mem_map] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          rw [mem_Im_elems_iff]
          exact ⟨a, ha, rfl⟩
      rw [h_eq_map]; exact List.length_map _

    /-- Lema 2: imagen con la misma cardinalidad que el dominio → función inyectiva. -/
    theorem injective_of_card_image {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_card : f.Im.card = A.card) :
        f.Injective
          := by
      unfold MapOn.Injective InjectiveOn
      intro a₁ a₂ ha₁ ha₂ heq
      by_cases h_eq : a₁ = a₂
      · exact h_eq
      · exfalso
        have hnd_A : A.elems.Nodup := sorted_nodup A.sorted
        -- (A.elems.map f.toFun) no es nodup: a₁ ≠ a₂ en lista nodup y f a₁ = f a₂
        have h_not_nodup : ¬ (A.elems.map f.toFun).Nodup :=
          not_nodup_map_of_ne_of_eq h_eq heq hnd_A ha₁ ha₂
        -- Pero Im nodup ↔ map (mismos elementos) y |Im|=|map| → map nodup → contradicción
        have hnd_Im : f.Im.elems.Nodup := sorted_nodup f.Im.sorted
        have h_len : f.Im.elems.length = A.elems.length :=
          Λ_inj_local _ _ h_card
        have h_Im_to_map : ∀ b, b ∈ f.Im.elems → b ∈ A.elems.map f.toFun := fun b hb => by
          rw [List.mem_map]
          obtain ⟨a, ha, hfa⟩ := (mem_Im_elems_iff f b).mp hb
          exact ⟨a, ha, hfa⟩
        have h_map_to_Im : ∀ b, b ∈ A.elems.map f.toFun → b ∈ f.Im.elems := fun b hb => by
          rw [List.mem_map] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          rw [mem_Im_elems_iff]; exact ⟨a, ha, rfl⟩
        have hnd_map : (A.elems.map f.toFun).Nodup :=
          nodup_of_nodup_same_elems_length_eq hnd_Im h_Im_to_map h_map_to_Im
            (by rw [h_len]; exact (List.length_map _).symm)
        exact h_not_nodup hnd_map

    /-- Lema 3: función sobreyectiva → imagen tiene la misma cardinalidad que el codominio. -/
    theorem card_image_of_surjective {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_surj : f.Surjective) :
        f.Im.card = B.card := by
      unfold FSet.card
      apply congrArg Λ
      apply nodup_length_eq_of_same_elems
      · exact sorted_nodup f.Im.sorted
      · exact sorted_nodup B.sorted
      · -- Im.elems ⊆ B.elems
        intro b hb
        obtain ⟨a, ha, rfl⟩ := (mem_Im_elems_iff f b).mp hb
        exact f.map_carrier a ha
      · -- B.elems ⊆ Im.elems: sobreyectividad
        intro b hb
        rw [mem_Im_elems_iff]
        obtain ⟨a, ha, hfa⟩ := h_surj b hb
        exact ⟨a, ha, hfa⟩

    /-- Lema 4: imagen con la misma cardinalidad que el codominio → función sobreyectiva. -/
    theorem surjective_of_card_image {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_card : f.Im.card = B.card) :
        f.Surjective := by
      unfold MapOn.Surjective SurjectiveOn
      intro b hb
      -- Im.elems ⊆ B.elems y |Im| = |B|, ambos nodup → Im.elems = B.elems (mismos elementos)
      have hnd_Im : f.Im.elems.Nodup := sorted_nodup f.Im.sorted
      have hnd_B  : B.elems.Nodup    := sorted_nodup B.sorted
      have h_len : f.Im.elems.length = B.elems.length :=
        Λ_inj_local _ _ h_card
      have h_Im_sub_B : ∀ x, x ∈ f.Im.elems → x ∈ B.elems := fun x hx => by
        obtain ⟨a, ha, rfl⟩ := (mem_Im_elems_iff f x).mp hx
        exact f.map_carrier a ha
      -- Por nodup_subset_length_le: si x ∈ B \ Im, entonces x :: Im.elems
      -- es nodup y ⊆ B, con longitud |Im| + 1 > |B| → contradicción.
      have h_B_sub_Im : ∀ x, x ∈ B.elems → x ∈ f.Im.elems := by
        intro x hx
        -- Si x ∉ Im, entonces x :: Im.elems es nodup, ⊆ B, longitud |Im|+1 > |B|
        by_cases hnx : x ∈ f.Im.elems
        · exact hnx
        · exfalso
          have h_le : (x :: f.Im.elems).length ≤ B.elems.length := by
            apply nodup_subset_length_le (List.nodup_cons.mpr ⟨hnx, hnd_Im⟩)
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hx
            · exact h_Im_sub_B y hy'
          rw [List.length_cons] at h_le
          omega
      -- Ahora b ∈ B.elems → b ∈ Im.elems → ∃ a, ...
      obtain ⟨a, ha, hfa⟩ := (mem_Im_elems_iff f b).mp (h_B_sub_Im b hb)
      exact ⟨a, ha, hfa⟩

    /-- Principio del Palomar: para conjuntos finitos del mismo tamaño,
        inyectividad ↔ sobreyectividad. -/
    theorem MapOn.injective_iff_surjective_of_card_eq {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (h_card_eq : A.card = B.card) (f : MapOn A B) :
        f.Injective ↔ f.Surjective
         := by
      -- h1: |Im f| = |A| ↔ f inyectiva  (mp/mpr)
      -- h2: f sobreyectiva ↔ |Im f| = |B|  (mp/mpr)
      have h1 : f.Im.card = A.card ↔ f.Injective :=
        Iff.intro (injective_of_card_image f) (card_image_of_injective f)
      have h2 : f.Surjective ↔ f.Im.card = B.card :=
        Iff.intro (card_image_of_surjective f) (surjective_of_card_image f)
      constructor
      · intro h_inj
        exact h2.mpr ((h1.mpr h_inj).trans h_card_eq)
      · intro h_surj
        exact h1.mp ((h2.mp h_surj).trans h_card_eq.symm)

    /-- Corolario: para conjuntos del mismo tamaño, inyectividad ↔ biyectividad. -/
    theorem MapOn.injective_iff_bijective_of_card_eq {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (h_card_eq : A.card = B.card) (f : MapOn A B) :
        f.Injective ↔ f.Bijective
         := by
      constructor
      · intro h_inj
        exact ⟨h_inj,
               (MapOn.injective_iff_surjective_of_card_eq h_card_eq f).mp h_inj⟩
      · intro h_bij; exact h_bij.inj

    /-- Corolario: para conjuntos del mismo tamaño, sobreyectividad ↔ biyectividad. -/
    theorem MapOn.surjective_iff_bijective_of_card_eq {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (h_card_eq : A.card = B.card) (f : MapOn A B) :
        f.Surjective ↔ f.Bijective
         := by
      constructor
      · intro h_surj
        exact ⟨(MapOn.injective_iff_surjective_of_card_eq h_card_eq f).mpr h_surj,
               h_surj⟩
      · intro h_bij; exact h_bij.surj

    /-!
    # § 4. BinOpOn — operación binaria cerrada sobre un FSet
    -/

    /-- Operación binaria `α → α → α` cerrada sobre `A : FSet α`. -/
    structure BinOpOn {α : Type} [DecidableEq α] [LT α] (A : FSet α) where
      toFun       : α → α → α
      map_carrier : ∀ a b, a ∈ A.elems → b ∈ A.elems → toFun a b ∈ A.elems

    /-!
    # § 5. CoeFun — coerción a funciones ordinarias
    -/

    /-- `f : MapOn A B` se puede llamar directamente como función `α → β`. -/
    instance {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} :
        CoeFun (MapOn A B) (fun _ => α → β) where
      coe f := f.toFun

    /-- `op : BinOpOn A` se puede llamar directamente como función `α → α → α`. -/
    instance {α : Type} [DecidableEq α] [LT α] {A : FSet α} :
        CoeFun (BinOpOn A) (fun _ => α → α → α) where
      coe f := f.toFun

    /-!
    # § 6. FunTable — representación tabular de una endomorfismo de un FSet

    Una función `f : A → A` queda completamente
    especificada por la tabla de sus imágenes:
    `table[i] = f(A.elems[i])` para `i = 0, …, A.card - 1`.

    Ventajas frente a `MapOn A A`:
    - Igualdad extensional es igualdad de lista (decidible).
    - Enumerable: hay exactamente `A.card ^ A.card` tablas.
    - Las permutaciones son `FunTable`s con `List.Perm table A.elems`.
    -/

    /-- Tabla de imágenes de una función `A → A`.
        `table` es la lista `[f(A.elems[0]), f(A.elems[1]), …]`. -/
    structure FunTable {α : Type} [DecidableEq α] [LT α] (A : FSet α) where
      /-- Lista de imágenes, en el mismo orden que `A.elems`. -/
      table    : List α
      /-- Misma longitud que el dominio. -/
      len_eq   : lengthₚ table = A.card
      /-- Todos los valores pertenecen a `A`. -/
      mem_all  : ∀ a, a ∈ table → a ∈ A.elems

    /-- Igualdad decidible de tablas. -/
    instance {α : Type} [DecidableEq α] [LT α] {A : FSet α} :
        DecidableEq (FunTable A) := fun f g =>
      if h : f.table = g.table then
        isTrue (by cases f; cases g; simp_all)
      else
        isFalse (fun heq => h (congrArg FunTable.table heq))

    namespace FunTable

      /-- Aplica la tabla: `f.apply i = table[i]`, con valor por defecto `dflt`
          si `i` está fuera de rango (no debería ocurrir para `i < A.card`). -/
      def apply {α : Type} [DecidableEq α] [LT α] {A : FSet α}
          (f : FunTable A) (dflt : α) (i : ℕ₀) : α :=
        getDₚ dflt f.table i

      /-- Aplica la función a un elemento de `A`: devuelve `f(a)`.
          Usa el índice de `a` en `A.elems` para indexar en `table`. -/
      def applyElem {α : Type} [DecidableEq α] [LT α] {A : FSet α}
          (f : FunTable A) (a : α) (dflt : α) : α :=
        getDₚ dflt f.table (List.indexOfₚ a A.elems)

      /-- `applyElem` devuelve un elemento de `A`. -/
      theorem applyElem_mem {α : Type} [DecidableEq α] [LT α] {A : FSet α}
        (f : FunTable A) (a dflt : α) (ha : a ∈ A.elems) :
          f.applyElem a dflt ∈ A.elems
            := by
        unfold applyElem
        -- El índice de a en A.elems es < A.card = lengthₚ A.elems = lengthₚ f.table
        have hlen : lengthₚ f.table = A.card := f.len_eq
        have hidx_lt : lt₀ (List.indexOfₚ a A.elems) (lengthₚ f.table) := by
          rw [hlen]; exact List.indexOfₚ_lt_length a A.elems ha
        have hmem_table : getDₚ dflt f.table (List.indexOfₚ a A.elems) ∈ f.table :=
          getDₚ_mem dflt f.table _ hidx_lt
        exact f.mem_all _ hmem_table

      /-- `FunTable` de identidad: `table = A.elems`. -/
      def id {α : Type} [DecidableEq α] [LT α] (A : FSet α) : FunTable A where
        table   := A.elems
        len_eq  := rfl
        mem_all := fun _ ha => ha

      /-- `FunTable` de composición: `(g.comp f).table[i] = g(f.table[i])`. -/
      def comp {α : Type} [DecidableEq α] [LT α] {A : FSet α}
          (g f : FunTable A) (dflt : α) :
          FunTable A where
        table   := f.table.map (fun a => g.applyElem a dflt)
        len_eq  := by
          have h : lengthₚ (f.table.map (fun a => g.applyElem a dflt)) = lengthₚ f.table :=
            congrArg Λ (List.length_map (fun a => g.applyElem a dflt))
          rw [h]; exact f.len_eq
        mem_all := fun a ha => by
          rw [List.mem_map] at ha
          obtain ⟨b, hb_in_table, rfl⟩ := ha
          exact g.applyElem_mem b dflt (f.mem_all b hb_in_table)

    end FunTable

    /-!
    # § 7. Permutación como FunTable biyectiva
    -/

    /-- Una permutación de `A` es una `FunTable` cuya tabla es una permutación
        (en el sentido de `List.Perm`) de `A.elems`. -/
    structure FunPerm {α : Type} [DecidableEq α] [LT α] (A : FSet α)
        extends FunTable A where
      is_perm : List.Perm table A.elems

    namespace FunPerm

      /-- La permutación identidad. -/
      def id {α : Type} [DecidableEq α] [LT α] (A : FSet α) : FunPerm A where
        table   := A.elems
        len_eq  := rfl
        mem_all := fun _ ha => ha
        is_perm := List.Perm.refl _

    end FunPerm

  end FSetFunction
end Peano
