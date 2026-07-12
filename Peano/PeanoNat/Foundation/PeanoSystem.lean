/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Foundation/PeanoSystem.lean
--
-- Define la categoría de álgebras de Peano: PeanoSystem, PeanoMorphism, isPeanoIso.
-- Proporciona el marco para demostrar que ℕ₀ es el objeto inicial (ver Initiality.lean).

import Peano.PeanoNat

namespace Peano
  open Peano

  namespace Foundation
    open Foundation

  /-- Un sistema de Peano (NNO — Natural Numbers Object): un tipo `N` con una constante
      `zero`, una función `succ`, los tres axiomas de Peano (inyectividad, discriminación,
      inducción) y el principio de recursión primitiva.

      El campo `rec` expresa la propiedad universal del NNO: para cualquier tipo A con
      un elemento base `a` y una función `f`, existe una única función `h : N → A`
      que satisface h(zero) = a y h(succ n) = f(h n).
      Este campo permite construir morfismos desde cualquier sistema de Peano hacia ℕ₀
      y probar que todos los sistemas de Peano son únicamente isomorfos. -/
  structure PeanoSystem where
    N    : Type 0
    zero : N
    succ : N → N
    inj   : ∀ m n : N, succ m = succ n → m = n
    discr : ∀ n : N, zero ≠ succ n
    ind   : ∀ P : N → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n
    prim_rec : ∀ {A : Type 0} (a : A) (f : A → A),
                 ExistsUnique (fun h : N → A => h zero = a ∧ ∀ n, h (succ n) = f (h n))

  /-- Un morfismo de álgebras de Peano: una función que preserva zero y succ. -/
  @[ext]
  structure PeanoMorphism (A B : PeanoSystem) where
    map       : A.N → B.N
    pres_zero : map A.zero = B.zero
    pres_succ : ∀ n : A.N, map (A.succ n) = B.succ (map n)

  /-- Un isomorfismo de álgebras de Peano: un morfismo con inverso bilateral. -/
  def isPeanoIso (A B : PeanoSystem) (f : PeanoMorphism A B) : Prop :=
    ∃ g : PeanoMorphism B A,
      (∀ x : A.N, g.map (f.map x) = x) ∧
      (∀ y : B.N, f.map (g.map y) = y)

  /-- La composición de dos morfismos de Peano es un morfismo de Peano. -/
  def compMorph
      {A B C : PeanoSystem}
      (g : PeanoMorphism B C)
      (f : PeanoMorphism A B) :
      PeanoMorphism A C where
    map       := fun x => g.map (f.map x)
    pres_zero := by rw [f.pres_zero, g.pres_zero]
    pres_succ := fun n => by rw [f.pres_succ, g.pres_succ]

  /-- El morfismo identidad en una álgebra de Peano. -/
  def idMorph (A : PeanoSystem) : PeanoMorphism A A where
    map       := fun x => x
    pres_zero := rfl
    pres_succ := fun _ => rfl

  end Foundation

end Peano

export Peano.Foundation (
  PeanoSystem
  PeanoMorphism
  isPeanoIso
  compMorph
  idMorph
)
