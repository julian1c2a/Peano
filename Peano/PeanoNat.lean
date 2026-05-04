/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat.lean

import Peano.Prelim.ExistsUnique


namespace Peano

  inductive ℕ₀ : Type
    where
    | zero : ℕ₀
    | succ : ℕ₀ -> ℕ₀
    deriving Repr, BEq, DecidableEq

  private theorem ℕ₀_beq_refl : ∀ {a : ℕ₀}, (a == a) = true
    | .zero   => rfl
    | .succ n => ℕ₀_beq_refl (a := n)

  private theorem ℕ₀_beq_of_eq : ∀ {a b : ℕ₀}, (a == b) = true → a = b
    | .zero,   .zero,   _  => rfl
    | .zero,   .succ _, h  => absurd h Bool.false_ne_true
    | .succ _, .zero,   h  => absurd h Bool.false_ne_true
    | .succ _, .succ _, h  => congrArg ℕ₀.succ (ℕ₀_beq_of_eq h)

  instance instReflBEqℕ₀ : ReflBEq ℕ₀ := ⟨ℕ₀_beq_refl⟩

  instance instLawfulBEqℕ₀ : LawfulBEq ℕ₀ where
    eq_of_beq := ℕ₀_beq_of_eq

  def ℕ₁ : Type := {n : ℕ₀ // n ≠ ℕ₀.zero}
  deriving Repr, DecidableEq

  def ℕ₂ : Type := {n : ℕ₁ // n.val ≠ ℕ₀.succ ℕ₀.zero}
  deriving Repr, DecidableEq

  def idℕ₀ (n : ℕ₀) : ℕ₀ := n
  def idNat (n : Nat) : Nat := n
  def eqFnGen {α β : Type}
    (f : α → β) (g : α → β) :
      Prop
        :=
    ∀ (x : α), f x = g x
  def comp {α β : Type}
    (f : α → β) (g : β → α) :
      Prop
        :=
    ∀ (x : α), g (f x) = x
  def eqFn {α : Type}
    (f : ℕ₀ -> α)(g : ℕ₀ -> α) :
      Prop
        :=
    ∀ (x : ℕ₀), f x = g x
  def eqFn2 {α : Type}
    (f : ℕ₀ × ℕ₀ -> α)(g : ℕ₀ × ℕ₀ -> α) :
      Prop
        :=
    ∀ (x : ℕ₀), ∀ (y : ℕ₀), f (x, y) = g (x, y)
  def eqFnNat {α : Type}
    (f : Nat -> α)(g : Nat -> α) :
      Prop
        :=
    ∀ (x : Nat), f x = g x

  set_option trace.Meta.Tactic.simp true

  notation "σ" n:max => ℕ₀.succ n


  def zero : ℕ₀ := ℕ₀.zero
  def one : ℕ₀ := σ zero
  def two : ℕ₀ := σ one
  def three : ℕ₀ := σ two
  def four : ℕ₀ := σ three
  def five : ℕ₀ := σ four
  def six : ℕ₀ := σ five
  def seven : ℕ₀ := σ six
  def eight : ℕ₀ := σ seven
  def nine : ℕ₀ := σ eight
  def ten : ℕ₀ := σ nine
  def eleven : ℕ₀ := σ ten
  def twelve : ℕ₀ := σ eleven
  def thirteen : ℕ₀ := σ twelve
  def fourteen : ℕ₀ := σ thirteen
  def fifteen : ℕ₀ := σ fourteen

  notation "𝟘" => ℕ₀.zero
  notation "𝟙" => one
  notation "𝟚" => two
  notation "𝟛" => three
  notation "𝟜" => four
  notation "𝟝" => five
  notation "𝟞" => six
  notation "𝟟" => seven
  notation "𝟠" => eight
  notation "𝟡" => nine
  notation "𝔸" => ten
  notation "𝔹" => eleven
  notation "ℂ" => twelve
  notation "𝔻" => thirteen
  notation "𝔼" => fourteen
  notation "𝔽" => fifteen

  def Λ(n : Nat) : ℕ₀ :=
    match n with
    | Nat.zero => 𝟘
    | Nat.succ k => σ (Λ k)

  def Ψ (n : ℕ₀) : Nat :=
    match n with
    | .zero => Nat.zero
    | .succ k => Nat.succ (Ψ k)

  instance : Coe Nat ℕ₀ where
    coe n := Λ n

  instance : Zero ℕ₀ where zero := ℕ₀.zero
  instance : One ℕ₀ where one := one
  instance (n : Nat) : OfNat ℕ₀ n where ofNat := Λ n

  def τ (n : ℕ₀) : ℕ₀ :=
    match n with
    | .zero => 𝟘
    | .succ k => k

  def ρ (n : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) : ℕ₀ :=
    match n with
    | .zero =>
      False.elim (h_n_neq_0 rfl)
    | .succ k => k

  inductive Nats : Type
    | nat0
    | nat1
    | nat2
    deriving Repr, BEq, DecidableEq

  @[reducible]
  def Nats.toType : Nats → Type
    | Nats.nat0 => ℕ₀
    | Nats.nat1 => ℕ₁
    | Nats.nat2 => ℕ₂

  /-- Coerción para usar las etiquetas de `Nats` como si fueran los tipos reales -/
  instance : CoeSort Nats Type := ⟨Nats.toType⟩

  /-- Coerciones para extraer el valor ℕ₀ subyacente de los subtipos ℕ₁ y ℕ₂ de forma automática -/
  instance : Coe ℕ₁ ℕ₀ where coe n := n.val
  instance : Coe ℕ₂ ℕ₀ where coe n := n.val.val

end Peano

-- Ahora puedes exportar todo lo que está dentro del namespace Peano
export Peano (
  ℕ₀ ℕ₁ ℕ₂
  Nats
  Nats.toType
  idℕ₀
  idNat
  eqFnGen
  comp
  eqFn
  eqFn2
  eqFnNat
  Λ Ψ τ ρ
)
-- (legacy comment removed)
