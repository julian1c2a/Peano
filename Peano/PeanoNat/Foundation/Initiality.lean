/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Foundation/Initiality.lean
--
-- Demuestra que ℕ₀ es el álgebra inicial de Peano:
--   · Cualquier sistema de Peano recibe un único morfismo desde ℕ₀.
--   · Cualquier dos sistemas de Peano son únicamente isomorfos.
--   · El principio de recursión primitiva se deriva de la inicialidad.

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.Prelim.Classical
import Peano.PeanoNat.Foundation.PeanoSystem

namespace Peano
  open Peano
  open Peano.Axioms

  namespace Foundation
    open Foundation

  -- ──────────────────────────────────────────────────���──────────────────────
  -- 1. ℕ₀ satisface el principio de recursión primitiva
  -- ─────────────────────────────────────────────────────────────────────────

  /-- La función recursiva canónica sobre ℕ₀. -/
  private def ℕ₀_rec_fn {A : Type 0} (a : A) (f : A → A) : ℕ₀ → A
    | .zero   => a
    | .succ n => f (ℕ₀_rec_fn a f n)

  /-- ℕ₀ satisface el principio de recursión primitiva. -/
  theorem ℕ₀_prim_rec {A : Type 0} (a : A) (f : A → A) :
      ExistsUnique (fun h : ℕ₀ → A => h 𝟘 = a ∧ ∀ n, h (σ n) = f (h n)) := by
    refine ⟨ℕ₀_rec_fn a f, ⟨rfl, fun _ => rfl⟩, ?_⟩
    intro h' ⟨h0, hs⟩
    funext n
    induction n with
    | zero   => exact h0
    | succ k ih => rw [hs k, ih]; rfl

  -- ─────────────────────────────────────────────────────────────────────────
  -- 2. ℕ₀ como sistema de Peano
  -- ─────────────────────────────────────────────────────────────────────────

  /-- ℕ₀ junto con sus operaciones forma un sistema de Peano. -/
  def ℕ₀_PeanoSystem : PeanoSystem where
    N        := ℕ₀
    zero     := 𝟘
    succ     := ℕ₀.succ
    inj      := succ_injective
    discr    := cero_neq_succ
    ind      := induction_principle
    prim_rec := ℕ₀_prim_rec

  -- ─────────────────────────────────────────────────────────────────────────
  -- 3. El morfismo canónico de ℕ₀ a cualquier sistema de Peano
  -- ─────────────────────────────────────────────────────────────────────────

  /-- El único morfismo de ℕ₀ hacia un sistema de Peano A. -/
  def ℕ₀_to (A : PeanoSystem) : ℕ₀ → A.N
    | .zero   => A.zero
    | .succ n => A.succ (ℕ₀_to A n)

  theorem ℕ₀_to_zero (A : PeanoSystem) : ℕ₀_to A 𝟘 = A.zero := rfl

  theorem ℕ₀_to_succ (A : PeanoSystem) (n : ℕ₀) :
      ℕ₀_to A (σ n) = A.succ (ℕ₀_to A n) := rfl

  /-- `ℕ₀_to A` como morfismo de álgebras de Peano. -/
  def ℕ₀_to_morph (A : PeanoSystem) : PeanoMorphism ℕ₀_PeanoSystem A where
    map       := ℕ₀_to A
    pres_zero := rfl
    pres_succ := fun _ => rfl

  -- ─────────────────────────────────────────────────────────────────────────
  -- 4. Teorema central: ℕ₀ es el álgebra inicial
  -- ────────────────────────────────────────────────��────────────────────────

  /-- **Inicialidad de ℕ₀**: existe un único morfismo de funciones de ℕ₀ hacia
      cualquier sistema de Peano. -/
  theorem ℕ₀_initial (A : PeanoSystem) :
      ExistsUnique (fun h : ℕ₀ → A.N => h 𝟘 = A.zero ∧ ∀ n, h (σ n) = A.succ (h n)) := by
    refine ⟨ℕ₀_to A, ⟨rfl, fun _ => rfl⟩, ?_⟩
    intro h' ⟨h0, hs⟩
    funext n
    induction n with
    | zero   => exact h0
    | succ k ih => rw [hs k, ih]; rfl

  /-- Cualquier morfismo de ℕ₀ hacia A coincide con `ℕ₀_to A`. -/
  theorem ℕ₀_morph_unique (A : PeanoSystem) (h : ℕ₀ → A.N)
      (h0 : h 𝟘 = A.zero) (hs : ∀ n, h (σ n) = A.succ (h n)) :
      h = ℕ₀_to A := by
    funext n
    induction n with
    | zero   => exact h0
    | succ k ih => rw [hs k, ih]; rfl

  -- ─────────────────────────────────────────────────────────────────────────
  -- 5. El morfismo canónico entre sistemas de Peano arbitrarios
  -- ─────────────────────────────────────────────────────────────────────────

  /-- Morfismo canónico (no computable) desde A hacia B usando A.prim_rec. -/
  noncomputable def morph_fn (A B : PeanoSystem) : A.N → B.N :=
    choose_unique (A.prim_rec B.zero B.succ)

  theorem morph_fn_zero (A B : PeanoSystem) :
      morph_fn A B A.zero = B.zero :=
    (choose_spec_unique (A.prim_rec B.zero B.succ)).1

  theorem morph_fn_succ (A B : PeanoSystem) (n : A.N) :
      morph_fn A B (A.succ n) = B.succ (morph_fn A B n) :=
    (choose_spec_unique (A.prim_rec B.zero B.succ)).2 n

  /-- Unicidad: cualquier función que preserve zero y succ coincide con `morph_fn`. -/
  theorem morph_fn_unique (A B : PeanoSystem) (h : A.N → B.N)
      (h0 : h A.zero = B.zero) (hs : ∀ n, h (A.succ n) = B.succ (h n)) :
      h = morph_fn A B :=
    choose_uniq (A.prim_rec B.zero B.succ) ⟨h0, hs⟩

  /-- `morph_fn A B` como morfismo de álgebras de Peano. -/
  noncomputable def morph_as_morph (A B : PeanoSystem) : PeanoMorphism A B where
    map       := morph_fn A B
    pres_zero := morph_fn_zero A B
    pres_succ := morph_fn_succ A B

  -- ────────────────────────────────��────────────────────────────────────────
  -- 6. La composición de morfismos canónicos es la identidad
  -- ─────────────────────────────────────────────────────────────────────────

  /-- La composición `morph_fn B A ∘ morph_fn A B` es la identidad en A. -/
  theorem morph_fn_comp_id (A B : PeanoSystem) (a : A.N) :
      morph_fn B A (morph_fn A B a) = a := by
    have comp_zero : (fun x : A.N => morph_fn B A (morph_fn A B x)) A.zero = A.zero := by
      show morph_fn B A (morph_fn A B A.zero) = A.zero
      rw [morph_fn_zero A B, morph_fn_zero B A]
    have comp_succ : ∀ n : A.N,
        (fun x => morph_fn B A (morph_fn A B x)) (A.succ n) =
        A.succ ((fun x => morph_fn B A (morph_fn A B x)) n) := by
      intro n
      show morph_fn B A (morph_fn A B (A.succ n)) = A.succ (morph_fn B A (morph_fn A B n))
      rw [morph_fn_succ A B n, morph_fn_succ B A]
    have p_comp := morph_fn_unique A A (fun x => morph_fn B A (morph_fn A B x)) comp_zero comp_succ
    have p_id   := morph_fn_unique A A (fun x => x) rfl (fun _ => rfl)
    exact congrFun (p_comp.trans p_id.symm) a

  -- ─────────────────────────────────────────────────────────────────────────
  -- 7. Corolario: cualquier dos sistemas de Peano son únicamente isomorfos
  -- ─────────────────────────────────────────────────────────────────────────

  /-- **Unicidad de la estructura de Peano**: cualquier dos sistemas de Peano son
      únicamente isomorfos. El isomorfismo canónico es `morph_as_morph A B`. -/
  theorem peano_unique (A B : PeanoSystem) :
      ExistsUnique (fun f : PeanoMorphism A B => isPeanoIso A B f) := by
    refine ⟨morph_as_morph A B, ?_, ?_⟩
    · exact ⟨morph_as_morph B A,
             fun x => morph_fn_comp_id A B x,
             fun y => morph_fn_comp_id B A y⟩
    · intro f' _hiso
      ext x
      exact congrFun (morph_fn_unique A B f'.map f'.pres_zero f'.pres_succ) x

  -- ─────────────────────────────────────────────────────────────────────────
  -- 8. Corolario: principio de recursión primitiva para ℕ₀
  -- ─────────────────────────────────────────────────────────────────────────

  /-- **Principio de recursión primitiva**: se deriva de la inicialidad. -/
  theorem ℕ₀_rec_principle {A : Type 0} (a : A) (f : A → A) :
      ExistsUnique (fun h : ℕ₀ → A => h 𝟘 = a ∧ ∀ n, h (σ n) = f (h n)) :=
    ℕ₀_prim_rec a f

  end Foundation

end Peano

export Peano.Foundation (
  ℕ₀_prim_rec
  ℕ₀_PeanoSystem
  ℕ₀_to
  ℕ₀_to_zero
  ℕ₀_to_succ
  ℕ₀_to_morph
  ℕ₀_initial
  ℕ₀_morph_unique
  morph_fn
  morph_fn_zero
  morph_fn_succ
  morph_fn_unique
  morph_as_morph
  morph_fn_comp_id
  peano_unique
  ℕ₀_rec_principle
)
