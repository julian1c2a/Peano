/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat.lean

import Peano.Prelim


namespace Peano

  inductive ℕ₀ : Type
    where
    | zero : ℕ₀
    | succ : ℕ₀ -> ℕ₀
    deriving Repr, BEq, DecidableEq

  def ℕ₁ : Type := {n : ℕ₀ // n ≠ ℕ₀.zero}

  def ℕ₂ : Type := {n : ℕ₁ // n.val ≠ ℕ₀.succ ℕ₀.zero}

  def idℕ₀ (n : ℕ₀) : ℕ₀ := n
  def idNat (n : Nat) : Nat := n
  def eqFnGen {α β : Type} (f : α → β) (g : α → β) :
      Prop :=
          ∀ (x : α), f x = g x
  def comp {α β : Type} (f : α → β) (g : β → α) :
      Prop :=
          ∀ (x : α), g (f x) = x
  def eqFn {α : Type}
          (f : ℕ₀ -> α)(g : ℕ₀ -> α) : Prop :=
    ∀ (x : ℕ₀), f x = g x
  def eqFn2 {α : Type}
          (f : ℕ₀ × ℕ₀ -> α)(g : ℕ₀ × ℕ₀ -> α) : Prop :=
    ∀ (x : ℕ₀), ∀ (y : ℕ₀), f (x, y) = g (x, y)
  def eqFnNat {α : Type}
          (f : Nat -> α)(g : Nat -> α) : Prop :=
    ∀ (x : Nat), f x = g x

  set_option trace.Meta.Tactic.simp true

  notation "σ" n:max => ℕ₀.succ n
  def cero : ℕ₀ := ℕ₀.zero
  notation "𝟘" => ℕ₀.zero

  def one : ℕ₀ := σ 𝟘
  def two : ℕ₀ := σ one
  def three : ℕ₀ := σ two

  notation "𝟙" => one
  notation "𝟚" => two
  notation "𝟛" => three

  def Λ(n : Nat) : ℕ₀ :=
    match n with
    | Nat.zero => 𝟘
    | Nat.succ k => σ (Λ k)

  def Ψ (n : ℕ₀) : Nat :=
    match n with
    | ℕ₀.zero => Nat.zero
    | ℕ₀.succ k => Nat.succ (Ψ k)

  instance : Coe Nat ℕ₀ where
    coe n := Λ n

  def τ (n : ℕ₀) : ℕ₀ :=
    match n with
    | ℕ₀.zero => 𝟘
    | ℕ₀.succ k => k

  def ρ (n : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) : ℕ₀ :=
    match n with
    | ℕ₀.zero =>
      False.elim (h_n_neq_0 rfl)
    | ℕ₀.succ k => k

  -- Tuplas de dimensión finita sobre ℕ₀

  def Tuple : ℕ₀ → Type
    | 𝟘 => Unit
    | σ n => ℕ₀ × Tuple n

  -- Constructor de tupla vacía
  def emptyTuple : Tuple 𝟘 := ()

  -- Constructor de tupla por concatenación (cons)
  def consTuple {n : ℕ₀} (x : ℕ₀) (xs : Tuple n) : Tuple (σ n) :=
    (x, xs)

  -- Proyección: obtener la cabeza de una tupla no vacía
  def headTuple {n : ℕ₀} (t : Tuple (σ n)) : ℕ₀ :=
    t.1

  -- Proyección: obtener la cola de una tupla no vacía
  def tailTuple {n : ℕ₀} (t : Tuple (σ n)) : Tuple n :=
    t.2

  -- Notación para tuplas
  notation "⟨⟩" => emptyTuple
  notation "⟨" x "⟩" => consTuple x emptyTuple

  -- Igualdad decidible para tuplas
  instance tupleDecEq : (n : ℕ₀) → DecidableEq (Tuple n)
    | 𝟘 => fun _ _ => isTrue rfl
    | σ n => fun t1 t2 =>
        match decEq t1.1 t2.1, tupleDecEq n t1.2 t2.2 with
        | isTrue h1, isTrue h2 => isTrue (by
            have : t1.1 = t2.1 := h1
            have : t1.2 = t2.2 := h2
            cases t1; cases t2
            congr)
        | isFalse h1, _ => isFalse (fun h => h1 (by cases h; rfl))
        | _, isFalse h2 => isFalse (fun h => h2 (by cases h; rfl))

  -- Representación para tuplas
  instance tupleRepr : (n : ℕ₀) → Repr (Tuple n)
    | 𝟘 => ⟨fun _ _ => "⟨⟩"⟩
    | σ n => ⟨fun t _ =>
        let head := repr t.1
        let tailRepr := (tupleRepr n).reprPrec t.2 0
        let tailStr := toString tailRepr
        if tailStr = "⟨⟩" then
          s!"⟨{head}⟩"
        else
          s!"⟨{head}, {tailStr.drop 1}"⟩

  -- Función para obtener el i-ésimo elemento de una tupla (con prueba de bounds)
  -- NOTA: Esta función requiere Lt de PeanoNatStrictOrder, por lo que se deja
  -- comentada hasta que ese módulo esté disponible
  /-
  def getTuple : (n : ℕ₀) → Tuple n → (i : ℕ₀) → (h : Lt i n) → ℕ₀
    | σ n, t, 𝟘, _ => headTuple t
    | σ n, t, σ i, h => getTuple n (tailTuple t) i (by sorry)
    | 𝟘, _, _, h => absurd h (by sorry)
  -/

  -- Función para construir una tupla desde una función
  def mkTuple : (n : ℕ₀) → (f : ℕ₀ → ℕ₀) → Tuple n
    | 𝟘, _ => emptyTuple
    | σ n, f => consTuple (f 𝟘) (mkTuple n (fun k => f (σ k)))

end Peano

-- Ahora puedes exportar todo lo que está dentro del namespace Peano
export Peano (
  ℕ₀ ℕ₁ ℕ₂
  idℕ₀
  idNat
  eqFnGen
  comp
  eqFn
  eqFn2
  eqFnNat
  Λ Ψ τ ρ
  Tuple
  emptyTuple
  consTuple
  headTuple
  tailTuple
  mkTuple
)
-- (legacy comment removed)
