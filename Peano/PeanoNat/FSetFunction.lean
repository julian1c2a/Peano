/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/FSetFunction.lean
-- Funciones entre conjuntos finitos (FSets) arbitrarios.
-- Generalización polimórfica de MapOn/BinOpOn de Group.lean.
--
-- § 1. MapOn             — función entre FSet α y FSet β
-- § 2. Im                — imagen de un MapOn como FSet
-- § 3. Principio del Palomar
-- § 4. BinOpOn           — operación binaria cerrada sobre un FSet
-- § 5. CoeFun            — coerción a funciones ordinarias

import Peano.PeanoNat.Lists
import Peano.PeanoNat.FSet
import Peano.PeanoNat.FSetFSet

set_option autoImplicit false

namespace Peano
  open Peano
  open Peano.Lists
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

    /-- Lema 1: función inyectiva → imagen tiene la misma cardinalidad que el dominio. -/
    theorem card_image_of_injective {α β : Type}
      [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_inj : f.Injective) :
        f.Im.card = A.card
         :=
      sorry

    /-- Lema 2: imagen con la misma cardinalidad que el dominio → función inyectiva. -/
    theorem injective_of_card_image {α β : Type}
      [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_card : f.Im.card = A.card) :
        f.Injective
         :=
      sorry

    /-- Lema 3: función sobreyectiva → imagen tiene la misma cardinalidad que el codominio. -/
    theorem card_image_of_surjective {α β : Type}
      [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_surj : f.Surjective) :
        f.Im.card = B.card
         :=
      sorry

    /-- Lema 4: imagen con la misma cardinalidad que el codominio → función sobreyectiva. -/
    theorem surjective_of_card_image {α β : Type}
      [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_card : f.Im.card = B.card) :
        f.Surjective
         :=
      sorry

    /-- Principio del Palomar: para conjuntos finitos del mismo tamaño,
        inyectividad ↔ sobreyectividad. -/
    theorem MapOn.injective_iff_surjective_of_card_eq {α β : Type}
      [DecidableEq α] [LT α] [DecidableEq β] [LT β]
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
      [DecidableEq α] [LT α] [DecidableEq β] [LT β]
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
      [DecidableEq α] [LT α] [DecidableEq β] [LT β]
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

  end FSetFunction
end Peano
