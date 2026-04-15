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
--
-- Teoremas sobre funciones sobre conjuntos finitos
set_option autoImplicit false

namespace Peano
  open Peano
  open Peano.List
  open Peano.FSet

  namespace FSetFunction

    /-!
    # § 1. MapOn — definiciones básicas
    -/

    structure MapOn {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        (A : FSet α) (B : FSet β) where
      toFun        : α → β
      map_carrier  : ∀ a, a ∈ A.elems → toFun a ∈ B.elems

    def MapOn.Injective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : Prop :=
      ∀ a b, a ∈ A.elems → b ∈ A.elems → f.toFun a = f.toFun b → a = b

    def MapOn.Surjective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : Prop :=
      ∀ b, b ∈ B.elems → ∃ a, a ∈ A.elems ∧ f.toFun a = b

    /-- Una función es biyectiva si es inyectiva y sobreyectiva. -/
    structure MapOn.Bijective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : Prop where
      inj  : f.Injective
      surj : f.Surjective

    instance {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} : CoeFun (MapOn A B) (fun _ => α → β) where
      coe f := f.toFun

    /-!
    # § 2. Imagen e Inversas
    -/

    def MapOn.Im {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : FSet β :=
      B.filter (fun b => A.elems.any (fun a => decide (f.toFun a = b)))

    /-- Inversa por la derecha (sección) de una función sobreyectiva. -/
    def MapOn.rightInverse {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_surj : f.Surjective) : MapOn B A :=
      { toFun := fun b =>
          match h_match : A.elems.find? (fun a => f.toFun a = b) with
          | some a => a
          | none   => A.elems.get! 𝟘,
        map_carrier := fun b hb => by
          match h_match : A.elems.find? (fun a => f.toFun a = b) with
          | some a => exact List.mem_of_find?_eq_some h_match
          | none   =>
              obtain ⟨a, ha, hfa⟩ := h_surj b hb
              have h_any : ∃ x ∈ A.elems, f.toFun x = b := ⟨a, ha, hfa⟩
              rw [List.find?_eq_none] at h_match
              exact absurd h_any h_match
      }

    theorem MapOn.rightInverse_prop {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_surj : f.Surjective) (b : β) (hb : b ∈ B.elems) :
        f.toFun ((f.rightInverse h_surj).toFun b) = b := by
      dsimp [rightInverse]
      match h_match : A.elems.find? (fun a => f.toFun a = b) with
      | some a => exact List.find?_some_prop h_match
      | none   =>
          obtain ⟨a, ha, hfa⟩ := h_surj b hb
          rw [List.find?_eq_none] at h_match
          exact absurd ⟨a, ha, hfa⟩ h_match

    theorem MapOn.rightInverse_injective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_surj : f.Surjective) :
        (f.rightInverse h_surj).Injective := by
      intro b1 b2 hb1 hb2 h_eq
      have h_f_eq := congrArg f.toFun h_eq
      rw [f.rightInverse_prop h_surj b1 hb1, f.rightInverse_prop h_surj b2 hb2] at h_f_eq
      exact h_f_eq

    /-!
    # § 10. Desigualdades de Cardinalidad
    -/

    theorem card_image_of_injective {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_inj : f.Injective) :
        f.Im.card = A.card := sorry

    private theorem card_filter_le {α : Type} [DecidableEq α] [LT α]
        (A : FSet α) (P : α → Bool) : (A.filter P).card ≤ A.card := by
      unfold FSet.card FSet.filter
      exact Peano.Axioms.le_Λ_of_le (List.length_filter_le P A.elems)

    theorem card_le_of_injective {α β : Type}
        [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
        [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
        {A : FSet α} {B : FSet β}
        (f : MapOn A B) (h_inj : f.Injective) :
        A.card ≤ B.card := by
      rw [← card_image_of_injective f h_inj]
      exact card_filter_le B _

    theorem card_le_of_surjective {α β : Type}
        [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
        [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
        {A : FSet α} {B : FSet β}
        (f : MapOn A B) (h_surj : f.Surjective) :
        B.card ≤ A.card := by
      let g := f.rightInverse h_surj
      have h_g_inj := f.rightInverse_injective h_surj
      exact card_le_of_injective g h_g_inj

    /-!
    # § 11. Teoremas de Igualdad de Cardinalidad
    -/

    /-- Teorema de Schroeder-Bernstein (versión finita):
        Si hay inyecciones en ambos sentidos, entonces card A = card B. -/
    theorem card_eq_of_injections {α β : Type}
        [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
        [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
        {A : FSet α} {B : FSet β}
        (f : MapOn A B) (hf : f.Injective)
        (g : MapOn B A) (hg : g.Injective) :
        A.card = B.card := by
      have h1 := card_le_of_injective f hf
      have h2 := card_le_of_injective g hg
      exact Peano.Axioms.le_antisymm h1 h2

    /-- Dual para sobreyecciones:
        Si hay sobreyecciones en ambos sentidos, entonces card A = card B. -/
    theorem card_eq_of_surjections {α β : Type}
        [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
        [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
        {A : FSet α} {B : FSet β}
        (f : MapOn A B) (hf : f.Surjective)
        (g : MapOn B A) (hg : g.Surjective) :
        A.card = B.card := by
      have h1 := card_le_of_surjective f hf
      have h2 := card_le_of_surjective g hg
      exact Peano.Axioms.le_antisymm h2 h1

    /-- Si existe una biyección entre A y B, entonces card A = card B. -/
    theorem MapOn.Bijective.card_eq {α β : Type}
        [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
        [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
        {A : FSet α} {B : FSet β}
        {f : MapOn A B} (h : f.Bijective) :
        A.card = B.card := by
      -- Una biyección es inyectiva (A.card ≤ B.card) y sobreyectiva (B.card ≤ A.card)
      have h_le := card_le_of_injective f h.inj
      have h_ge := card_le_of_surjective f h.surj
      exact Peano.Axioms.le_antisymm h_le h_ge

  end FSetFunction
end Peano
