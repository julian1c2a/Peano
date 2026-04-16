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
-- § 1b. id               — identidad, composición con id, cancelación
-- § 2. Im                — imagen de un MapOn como FSet
-- § 2b. rightInverse     — inversa por la derecha de sobreyecciones
-- § 2c. leftInverse      — inversa por la izquierda de inyecciones
-- § 2d. inverse          — inversa de biyecciones
-- § 2e. involución       — (f⁻¹)⁻¹ = f, composición con inversa
-- § 3. Principio del Palomar
-- § 3b. Desigualdades de cardinalidad
-- § 3c. Igualdad de cardinalidad (Schroeder-Bernstein, etc.)
-- § 3e. Endomorfismos    — especialización a f : A → A
-- § 3f. Permutaciones    — MapOn A A biyectivo (grupo simétrico)
-- § 3d. Preimagen, restricción y fibras
-- § 4. BinOpOn           — operación binaria cerrada sobre un FSet
-- § 5. CoeFun            — coerción a funciones ordinarias
-- § 6. FunTable          — representación tabular de endomorfismos
-- § 7. FunPerm           — permutación como FunTable biyectiva
-- § 8. Export            — re-exporta las declaraciones públicas

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

    /-- La composición de `MapOn` es asociativa (punto a punto, por definición). -/
    theorem MapOn.comp_assoc {α β γ δ : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        [DecidableEq γ] [LT γ] [DecidableEq δ] [LT δ]
        {A : FSet α} {B : FSet β} {C : FSet γ} {D : FSet δ}
        (f : MapOn A B) (g : MapOn B C) (h : MapOn C D) (a : α) :
        (h.comp (g.comp f)).toFun a = ((h.comp g).comp f).toFun a := rfl

    /-!
    # § 1b. Identidad y propiedades de composición
    -/

    /-- La función identidad como `MapOn A A`. -/
    def MapOn.id {α : Type} [DecidableEq α] [LT α]
        (A : FSet α) : MapOn A A where
      toFun       := _root_.id
      map_carrier := fun _ ha => ha

    theorem MapOn.id_injective {α : Type} [DecidableEq α] [LT α]
        (A : FSet α) : (MapOn.id A).Injective := by
      intro a₁ a₂ _ _ h; exact h

    theorem MapOn.id_surjective {α : Type} [DecidableEq α] [LT α]
        (A : FSet α) : (MapOn.id A).Surjective := by
      intro a ha; exact ⟨a, ha, rfl⟩

    theorem MapOn.id_bijective {α : Type} [DecidableEq α] [LT α]
        (A : FSet α) : (MapOn.id A).Bijective :=
      ⟨MapOn.id_injective A, MapOn.id_surjective A⟩

    /-- Composición con la identidad por la derecha: `f ∘ id = f` (punto a punto). -/
    theorem MapOn.comp_id {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (a : α) :
        (f.comp (MapOn.id A)).toFun a = f.toFun a := rfl

    /-- Composición con la identidad por la izquierda: `id ∘ f = f` (punto a punto). -/
    theorem MapOn.id_comp {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (a : α) :
        ((MapOn.id B).comp f).toFun a = f.toFun a := rfl

    /-- Si `g ∘ f` es inyectiva, entonces `f` es inyectiva. -/
    theorem MapOn.injective_of_comp_injective {α β γ : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β] [DecidableEq γ] [LT γ]
        {A : FSet α} {B : FSet β} {C : FSet γ}
        (f : MapOn A B) (g : MapOn B C)
        (h_comp_inj : (g.comp f).Injective) :
        f.Injective := by
      intro a₁ a₂ ha₁ ha₂ hf_eq
      exact h_comp_inj a₁ a₂ ha₁ ha₂ (congrArg g.toFun hf_eq)

    /-- Si `g ∘ f` es sobreyectiva, entonces `g` es sobreyectiva. -/
    theorem MapOn.surjective_of_comp_surjective {α β γ : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β] [DecidableEq γ] [LT γ]
        {A : FSet α} {B : FSet β} {C : FSet γ}
        (f : MapOn A B) (g : MapOn B C)
        (h_comp_surj : (g.comp f).Surjective) :
        g.Surjective := by
      intro c hc
      obtain ⟨a, ha, hgfa⟩ := h_comp_surj c hc
      exact ⟨f.toFun a, f.map_carrier a ha, hgfa⟩

    /-!
    # § 2. Imagen de un MapOn
    -/

    /-- Imagen de `f : MapOn A B`: subconjunto de `B` formado por los valores
        `f(a)` para `a ∈ A`. Se construye filtrando `B` (preserva el orden)
        usando `map_carrier` como garantía de contención. -/
    def MapOn.Im {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) : FSet β :=
      B.filter (fun b => A.elems.any (fun a => decide (f.toFun a = b)))

    /-- Inversa por la derecha (sección) de una función sobreyectiva.
        Requiere un valor por defecto `dflt` para el caso en que `find?`
        no encuentre preimagen (caso inalcanzable para `b ∈ B.elems`). -/
    def MapOn.rightInverse {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_surj : f.Surjective) (dflt : α) : MapOn B A :=
      { toFun := fun b =>
          match A.elems.find? (fun a => decide (f.toFun a = b)) with
          | some a => a
          | none   => dflt,
        map_carrier := fun b hb => by
          match h_match : A.elems.find? (fun a => decide (f.toFun a = b)) with
          | some a => exact List.mem_of_find?_eq_some h_match
          | none =>
              obtain ⟨a, ha, hfa⟩ := h_surj b hb
              have h_none := List.find?_eq_none.mp h_match a ha
              simp [hfa] at h_none
      }

    theorem MapOn.rightInverse_prop {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_surj : f.Surjective) (dflt : α)
        (b : β) (hb : b ∈ B.elems) :
        f.toFun ((f.rightInverse h_surj dflt).toFun b) = b := by
      dsimp [rightInverse]
      match h_match : A.elems.find? (fun a => decide (f.toFun a = b)) with
      | some a =>
        have := List.find?_some h_match
        simp [decide_eq_true_eq] at this
        exact this
      | none =>
          obtain ⟨a, ha, hfa⟩ := h_surj b hb
          have h_none := List.find?_eq_none.mp h_match a ha
          simp [hfa] at h_none

    theorem MapOn.rightInverse_injective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_surj : f.Surjective) (dflt : α) :
        (f.rightInverse h_surj dflt).Injective := by
      intro b1 b2 hb1 hb2 h_eq
      have h_f_eq := congrArg f.toFun h_eq
      rw [f.rightInverse_prop h_surj dflt b1 hb1,
          f.rightInverse_prop h_surj dflt b2 hb2] at h_f_eq
      exact h_f_eq

    /-- Inversa por la izquierda (retracción) de una función inyectiva.
        Para `b ∈ Im f`, devuelve la única preimagen; para `b ∉ Im f`,
        devuelve `dflt`. Requiere `dflt ∈ A.elems` para garantizar que
        el resultado sea un `MapOn B A`. -/
    def MapOn.leftInverse {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (_h_inj : f.Injective)
        (dflt : α) (h_dflt : dflt ∈ A.elems) : MapOn B A :=
      { toFun := fun b =>
          match A.elems.find? (fun a => decide (f.toFun a = b)) with
          | some a => a
          | none   => dflt,
        map_carrier := fun b _hb => by
          match h_match : A.elems.find? (fun a => decide (f.toFun a = b)) with
          | some a => exact List.mem_of_find?_eq_some h_match
          | none   => exact h_dflt
      }

    theorem MapOn.leftInverse_prop {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_inj : f.Injective)
        (dflt : α) (h_dflt : dflt ∈ A.elems)
        (a : α) (ha : a ∈ A.elems) :
        (f.leftInverse h_inj dflt h_dflt).toFun (f.toFun a) = a := by
      dsimp [leftInverse]
      match h_match : A.elems.find? (fun x => decide (f.toFun x = f.toFun a)) with
      | some x =>
        have hfx := List.find?_some h_match
        simp [decide_eq_true_eq] at hfx
        have hx_mem := List.mem_of_find?_eq_some h_match
        exact h_inj x a hx_mem ha hfx
      | none =>
        have h_none := List.find?_eq_none.mp h_match a ha
        simp at h_none

    theorem MapOn.leftInverse_surjective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_inj : f.Injective)
        (dflt : α) (h_dflt : dflt ∈ A.elems) :
        (f.leftInverse h_inj dflt h_dflt).Surjective := by
      intro a ha
      exact ⟨f.toFun a, f.map_carrier a ha,
             f.leftInverse_prop h_inj dflt h_dflt a ha⟩

    /-- `f` inyectiva si existe `g : MapOn B A` con `g(f(a)) = a` para todo `a ∈ A`. -/
    theorem MapOn.injective_of_has_leftInverse {α β : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B)
        (g : MapOn B A) (h : ∀ a, a ∈ A.elems → g.toFun (f.toFun a) = a) :
        f.Injective := by
      intro a₁ a₂ ha₁ ha₂ hf_eq
      have h₁ := h a₁ ha₁
      have h₂ := h a₂ ha₂
      rw [← h₁, ← h₂, hf_eq]

    /-- Caracterización: `f` inyectiva ⟺ existe inversa izquierda. -/
    theorem MapOn.injective_iff_has_leftInverse {α β : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B)
        (dflt : α) (h_dflt : dflt ∈ A.elems) :
        f.Injective ↔
        ∃ g : MapOn B A, ∀ a, a ∈ A.elems → g.toFun (f.toFun a) = a := by
      constructor
      · intro h_inj
        exact ⟨f.leftInverse h_inj dflt h_dflt,
               f.leftInverse_prop h_inj dflt h_dflt⟩
      · rintro ⟨g, hg⟩
        exact f.injective_of_has_leftInverse g hg

    /-- `f` sobreyectiva si existe `g : MapOn B A` con `f(g(b)) = b` para todo `b ∈ B`. -/
    theorem MapOn.surjective_of_has_rightInverse {α β : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B)
        (g : MapOn B A) (h : ∀ b, b ∈ B.elems → f.toFun (g.toFun b) = b) :
        f.Surjective := by
      intro b hb
      exact ⟨g.toFun b, g.map_carrier b hb, h b hb⟩

    /-- Caracterización: `f` sobreyectiva ⟺ existe inversa derecha. -/
    theorem MapOn.surjective_iff_has_rightInverse {α β : Type}
        [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B)
        (dflt : α) :
        f.Surjective ↔
        ∃ g : MapOn B A, ∀ b, b ∈ B.elems → f.toFun (g.toFun b) = b := by
      constructor
      · intro h_surj
        exact ⟨f.rightInverse h_surj dflt,
               f.rightInverse_prop h_surj dflt⟩
      · rintro ⟨g, hg⟩
        exact f.surjective_of_has_rightInverse g hg

    /-!
    # § 2d. Inversa de funciones biyectivas
    -/

    /-- Inversa de una función biyectiva.
        Para `b ∈ B`, devuelve la única preimagen `a ∈ A` con `f(a) = b`.
        Requiere `dflt ∈ A.elems` como valor por defecto (caso inalcanzable
        por sobreyectividad). -/
    def MapOn.inverse {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (_h_bij : f.Bijective)
        (dflt : α) (h_dflt : dflt ∈ A.elems) : MapOn B A :=
      { toFun := fun b =>
          match A.elems.find? (fun a => decide (f.toFun a = b)) with
          | some a => a
          | none   => dflt,
        map_carrier := fun b _hb => by
          match h_match : A.elems.find? (fun a => decide (f.toFun a = b)) with
          | some a => exact List.mem_of_find?_eq_some h_match
          | none   => exact h_dflt
      }

    /-- Propiedad de inversa izquierda: `f⁻¹(f(a)) = a` para `a ∈ A`. -/
    theorem MapOn.inverse_left_prop {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_bij : f.Bijective)
        (dflt : α) (h_dflt : dflt ∈ A.elems)
        (a : α) (ha : a ∈ A.elems) :
        (f.inverse h_bij dflt h_dflt).toFun (f.toFun a) = a := by
      dsimp [inverse]
      match h_match : A.elems.find? (fun x => decide (f.toFun x = f.toFun a)) with
      | some x =>
        have hfx := List.find?_some h_match
        simp [decide_eq_true_eq] at hfx
        have hx_mem := List.mem_of_find?_eq_some h_match
        exact h_bij.inj x a hx_mem ha hfx
      | none =>
        have h_none := List.find?_eq_none.mp h_match a ha
        simp at h_none

    /-- Propiedad de inversa derecha: `f(f⁻¹(b)) = b` para `b ∈ B`. -/
    theorem MapOn.inverse_right_prop {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_bij : f.Bijective)
        (dflt : α) (h_dflt : dflt ∈ A.elems)
        (b : β) (hb : b ∈ B.elems) :
        f.toFun ((f.inverse h_bij dflt h_dflt).toFun b) = b := by
      dsimp [inverse]
      match h_match : A.elems.find? (fun a => decide (f.toFun a = b)) with
      | some a =>
        have hfa := List.find?_some h_match
        simp [decide_eq_true_eq] at hfa
        exact hfa
      | none =>
        obtain ⟨a, ha, hfa⟩ := h_bij.surj b hb
        have h_none := List.find?_eq_none.mp h_match a ha
        simp [hfa] at h_none

    /-- La inversa de una biyección es inyectiva. -/
    theorem MapOn.inverse_injective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_bij : f.Bijective)
        (dflt : α) (h_dflt : dflt ∈ A.elems) :
        (f.inverse h_bij dflt h_dflt).Injective := by
      intro b1 b2 hb1 hb2 h_eq
      have h_f_eq := congrArg f.toFun h_eq
      rw [f.inverse_right_prop h_bij dflt h_dflt b1 hb1,
          f.inverse_right_prop h_bij dflt h_dflt b2 hb2] at h_f_eq
      exact h_f_eq

    /-- La inversa de una biyección es sobreyectiva. -/
    theorem MapOn.inverse_surjective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_bij : f.Bijective)
        (dflt : α) (h_dflt : dflt ∈ A.elems) :
        (f.inverse h_bij dflt h_dflt).Surjective := by
      intro a ha
      exact ⟨f.toFun a, f.map_carrier a ha,
             f.inverse_left_prop h_bij dflt h_dflt a ha⟩

    /-- La inversa de una biyección es biyectiva. -/
    theorem MapOn.inverse_bijective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_bij : f.Bijective)
        (dflt : α) (h_dflt : dflt ∈ A.elems) :
        (f.inverse h_bij dflt h_dflt).Bijective :=
      ⟨f.inverse_injective h_bij dflt h_dflt,
       f.inverse_surjective h_bij dflt h_dflt⟩

    /-!
    # § 2e. Involución de la inversa y composición con inversa
    -/

    /-- La inversa de la inversa recupera la función original (punto a punto). -/
    theorem MapOn.inverse_inverse {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_bij : f.Bijective)
        (dflt_a : α) (h_dflt_a : dflt_a ∈ A.elems)
        (dflt_b : β) (h_dflt_b : dflt_b ∈ B.elems)
        (a : α) (ha : a ∈ A.elems) :
        ((f.inverse h_bij dflt_a h_dflt_a).inverse
          (f.inverse_bijective h_bij dflt_a h_dflt_a) dflt_b h_dflt_b).toFun a =
        f.toFun a := by
      let g := f.inverse h_bij dflt_a h_dflt_a
      let h_g_bij := f.inverse_bijective h_bij dflt_a h_dflt_a
      -- g⁻¹(a) = f(a) porque g(g⁻¹(a)) = a = g(f(a)) y g es inyectiva
      have h_fa_mem : f.toFun a ∈ B.elems := f.map_carrier a ha
      have h_ginv_mem : (g.inverse h_g_bij dflt_b h_dflt_b).toFun a ∈ B.elems :=
        (g.inverse h_g_bij dflt_b h_dflt_b).map_carrier a ha
      have h1 : g.toFun ((g.inverse h_g_bij dflt_b h_dflt_b).toFun a) = a :=
        g.inverse_right_prop h_g_bij dflt_b h_dflt_b a ha
      have h2 : g.toFun (f.toFun a) = a :=
        f.inverse_left_prop h_bij dflt_a h_dflt_a a ha
      exact h_g_bij.1 _ _ h_ginv_mem h_fa_mem (h1.trans h2.symm)

    /-- `f⁻¹ ∘ f` actúa como la identidad sobre `A` (punto a punto). -/
    theorem MapOn.comp_inverse_left {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_bij : f.Bijective)
        (dflt : α) (h_dflt : dflt ∈ A.elems)
        (a : α) (ha : a ∈ A.elems) :
        ((f.inverse h_bij dflt h_dflt).comp f).toFun a = a :=
      f.inverse_left_prop h_bij dflt h_dflt a ha

    /-- `f ∘ f⁻¹` actúa como la identidad sobre `B` (punto a punto). -/
    theorem MapOn.comp_inverse_right {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
        {A : FSet α} {B : FSet β} (f : MapOn A B) (h_bij : f.Bijective)
        (dflt : α) (h_dflt : dflt ∈ A.elems)
        (b : β) (hb : b ∈ B.elems) :
        (f.comp (f.inverse h_bij dflt h_dflt)).toFun b = b :=
      f.inverse_right_prop h_bij dflt h_dflt b hb

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

    /-- Si `A.card = B.card` y `f` inyectiva, la `leftInverse` coincide
        punto a punto con la `inverse` de la biyección inducida. -/
    theorem MapOn.leftInverse_eq_inverse_of_card_eq {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (h_card_eq : A.card = B.card) (f : MapOn A B)
      (h_inj : f.Injective) (dflt : α) (h_dflt : dflt ∈ A.elems)
      (b : β) :
        (f.leftInverse h_inj dflt h_dflt).toFun b =
        (f.inverse ((MapOn.injective_iff_bijective_of_card_eq h_card_eq f).mp h_inj)
                   dflt h_dflt).toFun b
          :=
      rfl

    /-- Si `A.card = B.card` y `f` inyectiva, la `leftInverse` también es
        inversa por la derecha: `f(g(b)) = b` para todo `b ∈ B`. -/
    theorem MapOn.leftInverse_right_prop_of_card_eq {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (h_card_eq : A.card = B.card) (f : MapOn A B)
      (h_inj : f.Injective) (dflt : α) (h_dflt : dflt ∈ A.elems)
      (b : β) (hb : b ∈ B.elems) :
        f.toFun ((f.leftInverse h_inj dflt h_dflt).toFun b) = b
          := by
      have h_bij := (MapOn.injective_iff_bijective_of_card_eq h_card_eq f).mp h_inj
      rw [f.leftInverse_eq_inverse_of_card_eq h_card_eq h_inj dflt h_dflt b]
      exact f.inverse_right_prop h_bij dflt h_dflt b hb

    /-- Si `A.card = B.card` y `f` sobreyectiva, la `rightInverse` coincide
        punto a punto con la `inverse` de la biyección inducida. -/
    theorem MapOn.rightInverse_eq_inverse_of_card_eq {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (h_card_eq : A.card = B.card) (f : MapOn A B)
      (h_surj : f.Surjective) (dflt : α) (h_dflt : dflt ∈ A.elems)
      (b : β) :
        (f.rightInverse h_surj dflt).toFun b =
        (f.inverse ((MapOn.surjective_iff_bijective_of_card_eq h_card_eq f).mp h_surj)
                   dflt h_dflt).toFun b
          := by
      dsimp [rightInverse, inverse]

    /-- Si `A.card = B.card` y `f` sobreyectiva, la `rightInverse` también es
        inversa por la izquierda: `g(f(a)) = a` para todo `a ∈ A`. -/
    theorem MapOn.rightInverse_left_prop_of_card_eq {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (h_card_eq : A.card = B.card) (f : MapOn A B)
      (h_surj : f.Surjective) (dflt : α) (h_dflt : dflt ∈ A.elems)
      (a : α) (ha : a ∈ A.elems) :
        (f.rightInverse h_surj dflt).toFun (f.toFun a) = a
          := by
      have h_bij := (MapOn.surjective_iff_bijective_of_card_eq h_card_eq f).mp h_surj
      rw [f.rightInverse_eq_inverse_of_card_eq h_card_eq h_surj dflt h_dflt (f.toFun a)]
      exact f.inverse_left_prop h_bij dflt h_dflt a ha

    /-!
    # § 3b. Desigualdades de Cardinalidad
    -/

    private theorem card_filter_le {α : Type} [DecidableEq α] [LT α]
      (A : FSet α) (P : α → Bool) :
        (A.filter P).card ≤ A.card
          := by
      unfold FSet.card FSet.filter lengthₚ
      exact (isomorph_Λ_le _ _).mp (List.length_filter_le P A.elems)

    theorem card_le_of_injective {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_inj : f.Injective) :
        A.card ≤ B.card
          := by
      rw [← card_image_of_injective f h_inj]
      exact card_filter_le B _

    theorem card_le_of_surjective {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_surj : f.Surjective) :
        B.card ≤ A.card
          := by
      rw [← card_image_of_surjective f h_surj]
      -- Goal: f.Im.card ≤ A.card
      -- Im.elems is nodup and ⊆ A.elems.map f.toFun, |map| = |A|
      unfold FSet.card lengthₚ
      apply (isomorph_Λ_le _ _).mp
      have h_nodup_Im : f.Im.elems.Nodup := sorted_nodup f.Im.sorted
      have h_sub : ∀ b, b ∈ f.Im.elems → b ∈ A.elems.map f.toFun := fun b hb => by
        rw [List.mem_map]
        obtain ⟨a, ha, rfl⟩ := (mem_Im_elems_iff f b).mp hb
        exact ⟨a, ha, rfl⟩
      calc f.Im.elems.length
            ≤ (A.elems.map f.toFun).length := nodup_subset_length_le h_nodup_Im h_sub
          _ = A.elems.length := List.length_map _

    /-!
    # § 3c. Teoremas de Igualdad de Cardinalidad
    -/

    /-- Teorema de Schroeder-Bernstein (versión finita):
        Si hay inyecciones en ambos sentidos, entonces card A = card B. -/
    theorem card_eq_of_injections {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (hf : f.Injective)
      (g : MapOn B A) (hg : g.Injective) :
        A.card = B.card
        := by
      exact le_antisymm A.card B.card
        (card_le_of_injective f hf) (card_le_of_injective g hg)

    /-- Dual para sobreyecciones:
        Si hay sobreyecciones en ambos sentidos, entonces card A = card B. -/
    theorem card_eq_of_surjections {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (hf : f.Surjective)
      (g : MapOn B A) (hg : g.Surjective) :
        A.card = B.card
        := by
      exact le_antisymm A.card B.card
        (card_le_of_surjective g hg) (card_le_of_surjective f hf)

    /-- Si existe una biyección entre A y B, entonces card A = card B. -/
    theorem MapOn.Bijective.card_eq {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      {f : MapOn A B} (h : f.Bijective) :
        A.card = B.card
        := by
      exact le_antisymm A.card B.card
        (card_le_of_injective f h.inj) (card_le_of_surjective f h.surj)

    /-- Si `f` es inyectiva y su inversa izquierda es inyectiva, entonces `f` es biyectiva.
        Argumento: `g` inyectiva ⟹ `|B| ≤ |A|`; `f` inyectiva ⟹ `|A| ≤ |B|`; igualdad
        de cardinalidad + inyectividad ⟹ biyectividad. -/
    theorem MapOn.bijective_of_injective_leftInverse_injective {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β} (f : MapOn A B)
      (h_inj : f.Injective) (dflt : α) (h_dflt : dflt ∈ A.elems)
      (h_li_inj : (f.leftInverse h_inj dflt h_dflt).Injective) :
        f.Bijective
          := by
      have h_card : A.card = B.card :=
        card_eq_of_injections f h_inj (f.leftInverse h_inj dflt h_dflt) h_li_inj
      exact (MapOn.injective_iff_bijective_of_card_eq h_card f).mp h_inj

    /-- Si `f` es sobreyectiva y su inversa derecha es sobreyectiva, entonces `f` es biyectiva.
        Argumento: `g` sobreyectiva ⟹ `|A| ≤ |B|`; `f` sobreyectiva ⟹ `|B| ≤ |A|`; igualdad
        de cardinalidad + sobreyectividad ⟹ biyectividad. -/
    theorem MapOn.bijective_of_surjective_rightInverse_surjective {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β} (f : MapOn A B)
      (h_surj : f.Surjective) (dflt : α)
      (h_ri_surj : (f.rightInverse h_surj dflt).Surjective) :
        f.Bijective
          := by
      have h_card : A.card = B.card :=
        card_eq_of_surjections f h_surj (f.rightInverse h_surj dflt) h_ri_surj
      exact (MapOn.surjective_iff_bijective_of_card_eq h_card f).mp h_surj

    /-!
    # § 3e. Endomorfismos — especialización a `f : MapOn A A`

    Cuando dominio y codominio coinciden, `A.card = A.card` es trivial y
    todos los teoremas condicionados a `h_card_eq` se simplifican.
    -/

    /-- Endomorfismo inyectivo ↔ sobreyectivo (principio del Palomar). -/
    theorem MapOn.endo_injective_iff_surjective {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      {A : FSet α}
      (f : MapOn A A) :
        f.Injective ↔ f.Surjective
          :=
      MapOn.injective_iff_surjective_of_card_eq rfl f

    /-- Endomorfismo inyectivo ↔ biyectivo. -/
    theorem MapOn.endo_injective_iff_bijective {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      {A : FSet α}
      (f : MapOn A A) :
        f.Injective ↔ f.Bijective
          :=
      MapOn.injective_iff_bijective_of_card_eq rfl f

    /-- Endomorfismo sobreyectivo ↔ biyectivo. -/
    theorem MapOn.endo_surjective_iff_bijective {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      {A : FSet α}
      (f : MapOn A A) :
        f.Surjective ↔ f.Bijective
          :=
      MapOn.surjective_iff_bijective_of_card_eq rfl f

    /-- Endomorfismo inyectivo → biyectivo (dirección útil). -/
    theorem MapOn.endo_bijective_of_injective {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      {A : FSet α}
      (f : MapOn A A) (h : f.Injective) :
        f.Bijective
          :=
      f.endo_injective_iff_bijective.mp h

    /-- Endomorfismo sobreyectivo → biyectivo (dirección útil). -/
    theorem MapOn.endo_bijective_of_surjective {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      {A : FSet α}
      (f : MapOn A A) (h : f.Surjective) :
        f.Bijective
          :=
      f.endo_surjective_iff_bijective.mp h

    /-- Para endomorfismos inyectivos, `leftInverse` coincide con `inverse`. -/
    theorem MapOn.endo_leftInverse_eq_inverse {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α] {A : FSet α}
      (f : MapOn A A) (h_inj : f.Injective) (dflt : α) (h_dflt : dflt ∈ A.elems) (a : α) :
        (f.leftInverse h_inj dflt h_dflt).toFun a =
        (f.inverse (f.endo_bijective_of_injective h_inj) dflt h_dflt).toFun a
          :=
      rfl

    /-- Para endomorfismos inyectivos, `leftInverse` es también inversa derecha:
        `f(g(a)) = a` para todo `a ∈ A`. -/
    theorem MapOn.endo_leftInverse_right_prop {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α] {A : FSet α}
      (f : MapOn A A) (h_inj : f.Injective) (dflt : α) (h_dflt : dflt ∈ A.elems)
      (a : α) (ha : a ∈ A.elems) :
        f.toFun ((f.leftInverse h_inj dflt h_dflt).toFun a) = a
          :=
      f.leftInverse_right_prop_of_card_eq rfl h_inj dflt h_dflt a ha

    /-- Para endomorfismos sobreyectivos, `rightInverse` coincide con `inverse`. -/
    theorem MapOn.endo_rightInverse_eq_inverse {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α] {A : FSet α}
      (f : MapOn A A) (h_surj : f.Surjective) (dflt : α) (h_dflt : dflt ∈ A.elems) (a : α) :
        (f.rightInverse h_surj dflt).toFun a =
        (f.inverse (f.endo_bijective_of_surjective h_surj) dflt h_dflt).toFun a
          := by
      dsimp [rightInverse, inverse]

    /-- Para endomorfismos sobreyectivos, `rightInverse` es también inversa izquierda:
        `g(f(a)) = a` para todo `a ∈ A`. -/
    theorem MapOn.endo_rightInverse_left_prop {α : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α] {A : FSet α}
      (f : MapOn A A) (h_surj : f.Surjective) (dflt : α) (h_dflt : dflt ∈ A.elems)
      (a : α) (ha : a ∈ A.elems) :
        (f.rightInverse h_surj dflt).toFun (f.toFun a) = a
          :=
      f.rightInverse_left_prop_of_card_eq rfl h_surj dflt h_dflt a ha

    /-!
    # § 3f. Permutaciones — `MapOn A A` biyectivo

    Una permutación es un endomorfismo biyectivo. Empaquetamos `MapOn A A`
    junto con la prueba de biyectividad y derivamos todas las propiedades
    algebraicas como corolarios directos de los teoremas anteriores.
    -/

    /-- Permutación de un conjunto finito: `MapOn A A` junto con
        prueba de biyectividad. -/
    structure Perm {α : Type} [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
        (A : FSet α) where
      /-- La función subyacente. -/
      fn   : MapOn A A
      /-- Prueba de biyectividad. -/
      bij  : fn.Bijective

    namespace Perm

      variable {α : Type} [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
               {A : FSet α}

      /-- Inyectividad (proyección). -/
      theorem injective (p : Perm A) : p.fn.Injective := p.bij.inj

      /-- Sobreyectividad (proyección). -/
      theorem surjective (p : Perm A) : p.fn.Surjective := p.bij.surj

      /-- La permutación identidad. -/
      def id (A : FSet α) [StrictOrder.IrreflLT α] : Perm A where
        fn  := MapOn.id A
        bij := MapOn.id_bijective A

      /-- Composición de permutaciones. -/
      def comp (g f : Perm A) : Perm A where
        fn  := g.fn.comp f.fn
        bij := MapOn.comp_bijective f.bij g.bij

      /-- Composición con la identidad por la derecha (punto a punto). -/
      theorem comp_id_fn (p : Perm A) (a : α) :
        (p.comp (Perm.id A)).fn.toFun a = p.fn.toFun a
          := rfl

      /-- Composición con la identidad por la izquierda (punto a punto). -/
      theorem id_comp_fn (p : Perm A) (a : α) :
        ((Perm.id A).comp p).fn.toFun a = p.fn.toFun a
          := rfl

      /-- Inversa de una permutación (requiere un valor por defecto). -/
      def inv (p : Perm A) (dflt : α) (h_dflt : dflt ∈ A.elems) : Perm A where
        fn  := p.fn.inverse p.bij dflt h_dflt
        bij := p.fn.inverse_bijective p.bij dflt h_dflt

      /-- Propiedad de inversa izquierda: `p⁻¹(p(a)) = a`. -/
      theorem inv_left
        (p : Perm A) (dflt : α) (h_dflt : dflt ∈ A.elems) (a : α) (ha : a ∈ A.elems) :
          (p.inv dflt h_dflt).fn.toFun (p.fn.toFun a) = a
            :=
        p.fn.inverse_left_prop p.bij dflt h_dflt a ha

      /-- Propiedad de inversa derecha: `p(p⁻¹(a)) = a`. -/
      theorem inv_right
        (p : Perm A) (dflt : α) (h_dflt : dflt ∈ A.elems) (a : α) (ha : a ∈ A.elems) :
          p.fn.toFun ((p.inv dflt h_dflt).fn.toFun a) = a
            :=
        p.fn.inverse_right_prop p.bij dflt h_dflt a ha

      /-- La inversa de la inversa recupera la permutación original. -/
      theorem inv_inv
        (p : Perm A) (dflt : α) (h_dflt : dflt ∈ A.elems) (a : α) (ha : a ∈ A.elems) :
          ((p.inv dflt h_dflt).inv dflt h_dflt).fn.toFun a = p.fn.toFun a
            :=
        p.fn.inverse_inverse p.bij dflt h_dflt dflt h_dflt a ha

      /-- `p⁻¹ ∘ p` actúa como la identidad (punto a punto). -/
      theorem comp_inv_left
        (p : Perm A) (dflt : α) (h_dflt : dflt ∈ A.elems) (a : α) (ha : a ∈ A.elems) :
          ((p.inv dflt h_dflt).comp p).fn.toFun a = a
            :=
        p.fn.comp_inverse_left p.bij dflt h_dflt a ha

      /-- `p ∘ p⁻¹` actúa como la identidad (punto a punto). -/
      theorem comp_inv_right
        (p : Perm A) (dflt : α) (h_dflt : dflt ∈ A.elems) (a : α) (ha : a ∈ A.elems) :
          (p.comp (p.inv dflt h_dflt)).fn.toFun a = a
            :=
        p.fn.comp_inverse_right p.bij dflt h_dflt a ha

      /-- Composición asociativa (punto a punto, corolario de `MapOn.comp_assoc`). -/
      theorem comp_assoc
        (f g h : Perm A) (a : α) :
          (f.comp (g.comp h)).fn.toFun a = ((f.comp g).comp h).fn.toFun a
            :=
        MapOn.comp_assoc h.fn g.fn f.fn a

    end Perm

    /-!
    # § 3d. Preimagen, restricción y fibras
    -/

    /-- Preimagen: dado `f : MapOn A B` y `S : FSet β` con `S ⊆ B`,
        `f.PreIm S` es el subconjunto de `A` formado por los `a` con `f(a) ∈ S`. -/
    def MapOn.PreIm {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (S : FSet β) :
        FSet α
          :=
      A.filter (fun a => S.elems.any (fun b => decide (f.toFun a = b)))

    /-- `a ∈ f.PreIm S ↔ a ∈ A ∧ f(a) ∈ S`. -/
    theorem MapOn.mem_PreIm_iff {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (S : FSet β) (a : α) :
        a ∈ (f.PreIm S).elems ↔ a ∈ A.elems ∧ f.toFun a ∈ S.elems
          := by
      simp only [PreIm, FSet.filter]
      rw [List.mem_filter, List.any_eq_true]
      constructor
      · rintro ⟨ha, b, hb, hd⟩
        simp only [decide_eq_true_eq] at hd
        exact ⟨ha, hd ▸ hb⟩
      · rintro ⟨ha, hfa⟩
        exact ⟨ha, f.toFun a, hfa, by simp⟩

    /-- La preimagen de todo `B` es todo `A`. -/
    theorem MapOn.PreIm_full {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (a : α) (ha : a ∈ A.elems) :
        a ∈ (f.PreIm B).elems
          :=
      (f.mem_PreIm_iff B a).mpr ⟨ha, f.map_carrier a ha⟩

    /-- `|PreIm S| ≤ |A|` (la preimagen es un subconjunto del dominio). -/
    theorem MapOn.card_PreIm_le {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (S : FSet β) :
        (f.PreIm S).card ≤ A.card
          :=
      card_filter_le A _

    /-- Fibra de un elemento `b`: preimagen del singleton `{b}`. -/
    def MapOn.fiber {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (b : β) :
        FSet α
          :=
      A.filter (fun a => decide (f.toFun a = b))

    /-- `a ∈ f.fiber b ↔ a ∈ A ∧ f(a) = b`. -/
    theorem MapOn.mem_fiber_iff {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (b : β) (a : α) :
        a ∈ (f.fiber b).elems ↔ a ∈ A.elems ∧ f.toFun a = b
          := by
      simp only [fiber, FSet.filter]
      rw [List.mem_filter]
      simp [decide_eq_true_eq]

    /-- Para `f` inyectiva, cada fibra tiene a lo sumo un elemento:
        `|f.fiber b| ≤ 1`. -/
    theorem MapOn.card_fiber_le_one_of_injective {α β : Type}
      [DecidableEq α] [LT α] [StrictOrder.IrreflLT α]
      [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (h_inj : f.Injective) (b : β) :
        le₀ (f.fiber b).card (σ 𝟘)
          := by
      -- La fibra es un subconjunto de la imagen de la inyección restringida al singleton
      -- Basta ver que la fibra es nodup y todos sus elementos tienen la misma imagen,
      -- así que por inyectividad tiene ≤ 1 elemento.
      unfold FSet.card lengthₚ
      cases h_elems : (f.fiber b).elems with
      | nil =>
        -- fibra vacía: Λ 0 ≤ σ 𝟘
        exact zero_le (σ 𝟘)
      | cons a₀ tl =>
        suffices h_tl : tl = [] by
          rw [h_tl, List.length_cons, List.length_nil]
          exact Or.inr rfl
        by_cases h_tl : tl = []
        · exact h_tl
        · exfalso
          obtain ⟨a₁, tl', h_tl_eq⟩ := List.exists_cons_of_ne_nil h_tl
          have ha₀ : a₀ ∈ (f.fiber b).elems := h_elems ▸ List.mem_cons_self
          have ha₁ : a₁ ∈ (f.fiber b).elems :=
            h_elems ▸ List.mem_cons_of_mem _ (h_tl_eq ▸ List.mem_cons_self)
          have hfa₀ := ((f.mem_fiber_iff b a₀).mp ha₀).2
          have hfa₁ := ((f.mem_fiber_iff b a₁).mp ha₁).2
          have h_eq_a : a₀ = a₁ := h_inj a₀ a₁
            ((f.mem_fiber_iff b a₀).mp ha₀).1
            ((f.mem_fiber_iff b a₁).mp ha₁).1
            (hfa₀.trans hfa₁.symm)
          have h_nodup := sorted_nodup (f.fiber b).sorted
          rw [h_elems, List.nodup_cons] at h_nodup
          exact h_nodup.1 (h_eq_a ▸ h_tl_eq ▸ List.mem_cons_self)

    /-- Restricción de `f : MapOn A B` a un subconjunto `A'` de `A`. -/
    def MapOn.restrict {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (A' : FSet α) (h_sub : ∀ a, a ∈ A'.elems → a ∈ A.elems) :
        MapOn A' B where
      toFun       := f.toFun
      map_carrier := fun a ha => f.map_carrier a (h_sub a ha)

    /-- La restricción de una inyección es inyectiva. -/
    theorem MapOn.restrict_injective {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (A' : FSet α) (h_sub : ∀ a, a ∈ A'.elems → a ∈ A.elems)
      (h_inj : f.Injective) :
        (f.restrict A' h_sub).Injective
          := by
      intro a₁ a₂ ha₁ ha₂ hf_eq
      exact h_inj a₁ a₂ (h_sub a₁ ha₁) (h_sub a₂ ha₂) hf_eq

    /-- `Im (restrict f A') ⊆ Im f`: la imagen de la restricción está
        contenida en la imagen de la función original. -/
    theorem MapOn.mem_Im_restrict {α β : Type}
      [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      {A : FSet α} {B : FSet β}
      (f : MapOn A B) (A' : FSet α) (h_sub : ∀ a, a ∈ A'.elems → a ∈ A.elems)
      (b : β) (hb : b ∈ (f.restrict A' h_sub).Im.elems) :
        b ∈ f.Im.elems
          := by
      rw [mem_Im_elems_iff] at hb ⊢
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, h_sub a ha, rfl⟩

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
    structure FunTable {α : Type} [DecidableEq α] [LT α]
      (A : FSet α)
        where
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
          FunTable A
            where
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
    structure FunPerm {α : Type} [DecidableEq α] [LT α]
      (A : FSet α)
        extends FunTable A
          where
      is_perm : List.Perm table A.elems

    namespace FunPerm

      /-- La permutación identidad. -/
      def id {α : Type} [DecidableEq α] [LT α]
        (A : FSet α) :
          FunPerm A
            where
        table   := A.elems
        len_eq  := rfl
        mem_all := fun _ ha => ha
        is_perm := List.Perm.refl _

    end FunPerm

  end FSetFunction
end Peano

export Peano.FSetFunction (
  -- § 1. MapOn
  MapOn
  MapOn.comp
  InjectiveOn
  SurjectiveOn
  MapOn.Injective
  MapOn.Surjective
  MapOn.Bijective
  MapOn.comp_injective
  MapOn.comp_surjective
  MapOn.comp_bijective
  MapOn.comp_assoc
  -- § 1b. Identidad y composición
  MapOn.id
  MapOn.id_injective
  MapOn.id_surjective
  MapOn.id_bijective
  MapOn.comp_id
  MapOn.id_comp
  MapOn.injective_of_comp_injective
  MapOn.surjective_of_comp_surjective
  -- § 2. Im
  MapOn.Im
  -- § 2b. rightInverse
  MapOn.rightInverse
  MapOn.rightInverse_prop
  MapOn.rightInverse_injective
  -- § 2c. leftInverse
  MapOn.leftInverse
  MapOn.leftInverse_prop
  MapOn.leftInverse_surjective
  MapOn.injective_of_has_leftInverse
  MapOn.injective_iff_has_leftInverse
  MapOn.surjective_of_has_rightInverse
  MapOn.surjective_iff_has_rightInverse
  MapOn.bijective_of_injective_leftInverse_injective
  MapOn.bijective_of_surjective_rightInverse_surjective
  -- § 2d. inverse
  MapOn.inverse
  MapOn.inverse_left_prop
  MapOn.inverse_right_prop
  MapOn.inverse_injective
  MapOn.inverse_surjective
  MapOn.inverse_bijective
  -- § 2e. Involución de la inversa
  MapOn.inverse_inverse
  MapOn.comp_inverse_left
  MapOn.comp_inverse_right
  -- § 3. Principio del Palomar
  card_image_of_injective
  injective_of_card_image
  card_image_of_surjective
  surjective_of_card_image
  MapOn.injective_iff_surjective_of_card_eq
  MapOn.injective_iff_bijective_of_card_eq
  MapOn.surjective_iff_bijective_of_card_eq
  MapOn.leftInverse_eq_inverse_of_card_eq
  MapOn.leftInverse_right_prop_of_card_eq
  MapOn.rightInverse_eq_inverse_of_card_eq
  MapOn.rightInverse_left_prop_of_card_eq
  -- § 3b. Desigualdades de cardinalidad
  card_le_of_injective
  card_le_of_surjective
  -- § 3c. Igualdad de cardinalidad
  card_eq_of_injections
  card_eq_of_surjections
  MapOn.Bijective.card_eq
  MapOn.bijective_of_injective_leftInverse_injective
  MapOn.bijective_of_surjective_rightInverse_surjective
  -- § 3e. Endomorfismos (f : A → A)
  MapOn.endo_injective_iff_surjective
  MapOn.endo_injective_iff_bijective
  MapOn.endo_surjective_iff_bijective
  MapOn.endo_bijective_of_injective
  MapOn.endo_bijective_of_surjective
  MapOn.endo_leftInverse_eq_inverse
  MapOn.endo_leftInverse_right_prop
  MapOn.endo_rightInverse_eq_inverse
  MapOn.endo_rightInverse_left_prop
  -- § 3f. Permutaciones (MapOn A A biyectivo)
  Perm
  Perm.injective
  Perm.surjective
  Perm.id
  Perm.comp
  Perm.comp_id_fn
  Perm.id_comp_fn
  Perm.inv
  Perm.inv_left
  Perm.inv_right
  Perm.inv_inv
  Perm.comp_inv_left
  Perm.comp_inv_right
  Perm.comp_assoc
  -- § 3d. Preimagen, restricción y fibras
  MapOn.PreIm
  MapOn.mem_PreIm_iff
  MapOn.PreIm_full
  MapOn.card_PreIm_le
  MapOn.fiber
  MapOn.mem_fiber_iff
  MapOn.card_fiber_le_one_of_injective
  MapOn.restrict
  MapOn.restrict_injective
  MapOn.mem_Im_restrict
  -- § 4. BinOpOn
  BinOpOn
  -- § 6. FunTable
  FunTable
  FunTable.apply
  FunTable.applyElem
  FunTable.applyElem_mem
  FunTable.id
  FunTable.comp
  -- § 7. FunPerm
  FunPerm
  FunPerm.id
)
