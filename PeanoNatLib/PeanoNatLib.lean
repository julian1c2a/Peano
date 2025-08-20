-- PeanoNatLib/PeanoNatLib.lean

import Init.Classical


namespace Peano

  def ExistsUnique {α : Type} (p : α → Prop) : Prop :=
    ∃ x, (p x ∧ (∀ y, (p y → y = x)))

  syntax "∃¹ " ident ", " term : term
  syntax "∃¹ " "(" ident ")" ", " term : term
  syntax "∃¹ " "(" ident " : " term ")" ", " term : term
  syntax "∃¹ " ident " : " term ", " term : term

  macro_rules
    | `(∃¹ $x:ident, $p:term) => `(ExistsUnique (fun $x => $p))
    | `(∃¹ ($x:ident), $p:term) => `(ExistsUnique (fun $x => $p))
    | `(∃¹ ($x:ident : $t:term), $p:term) => `(ExistsUnique (fun ($x : $t) => $p))
    | `(∃¹ $x:ident : $t:term, $p:term) => `(ExistsUnique (fun ($x : $t) => $p))


  noncomputable def choose {α : Type} {p : α → Prop} (h : ∃ x, p x) : α :=
    (Classical.indefiniteDescription p h).val

  theorem choose_spec {α : Type} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
    (Classical.indefiniteDescription p h).property

  def ExistsUnique.exists {α : Type} {p : α → Prop} (h : ExistsUnique p) : (∃ x, p x) := by
    cases h with
    | intro x hx =>
      exact ⟨x, hx.left⟩

  noncomputable def choose_unique {α : Type} {p : α → Prop} (h : ExistsUnique p) : α :=
    choose (ExistsUnique.exists h)

  theorem choose_spec_unique {α : Type} {p : α → Prop}
    (h : ExistsUnique p) : p (choose_unique h)
      := by
        unfold choose_unique
        exact choose_spec (ExistsUnique.exists h)

  theorem choose_uniq {α : Type} {p : α → Prop}
    (h : ExistsUnique p) {y : α} (hy : p y) :
      y = choose_unique h
        :=
    let ⟨x, ⟨_, uniq⟩⟩ := h
    have hcu : p (choose_unique h) := choose_spec_unique h
    have y_eq_x : y = x := uniq y hy
    have cu_eq_x : choose_unique h = x := uniq (choose_unique h) hcu
    y_eq_x.trans cu_eq_x.symm

  inductive ℕ₀ : Type
    where
    | zero : ℕ₀
    | succ : ℕ₀ -> ℕ₀
    deriving Repr, BEq, DecidableEq

  def ℕ₁ : Type := {n : ℕ₀ // n ≠ ℕ₀.zero}

  def ℕ₂ : Type := {n : ℕ₁ // n.val ≠ ℕ₀.succ ℕ₀.zero}

  def idℕ₀ (n : ℕ₀) : ℕ₀ := n
  def idNat (n : Nat) : Nat := n
  def EqFnGen {α β : Type} (f : α → β) (g : α → β) :
      Prop :=
          ∀ (x : α), f x = g x
  def Comp {α β : Type} (f : α → β) (g : β → α) :
      Prop :=
          ∀ (x : α), g (f x) = x
  def EqFn {α : Type}
          (f : ℕ₀ -> α)(g : ℕ₀ -> α) : Prop :=
    ∀ (x : ℕ₀), f x = g x
  def EqFn2 {α : Type}
          (f : ℕ₀ × ℕ₀ -> α)(g : ℕ₀ × ℕ₀ -> α) : Prop :=
    ∀ (x : ℕ₀), ∀ (y : ℕ₀), f (x, y) = g (x, y)
  def EqFnNat {α : Type}
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

end Peano

-- Ahora puedes exportar todo lo que está dentro del namespace Peano
export Peano (
  ExistsUnique choose choose_spec ℕ₀ ℕ₁ ℕ₂
  idℕ₀ idNat EqFnGen Comp EqFn EqFn2 EqFnNat
  Λ Ψ τ ρ
)
-- PeanoNatLib/PeanoNatDiv.lean
