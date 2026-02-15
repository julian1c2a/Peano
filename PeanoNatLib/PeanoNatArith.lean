-- PeanoNatLib/PeanoNatArith.lean

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatSub


namespace Peano
  open Peano

  namespace NatArith
      open Peano.Axioms
      open Peano.Order
      open Peano.StrictOrder
      open Peano.Add
      open Peano.Mul
      open Peano.Sub

    def Divides (a b : ℕ₀) : Prop :=
      ∃ k : ℕ₀, b = mul a k

    infix:50 " ∣ " => Divides
    notation:50 a " ∤ " b => ¬ Divides a b

    def MultipleOf (n m : ℕ₀) : Prop :=
      Divides n m

    def DivisorOf (d n : ℕ₀) : Prop :=
      Divides d n

    inductive DList (α : Type) : Type
      | nil : DList α
      | cons : α → DList α → DList α

    def DList.append {α : Type} : DList α → DList α → DList α
      | DList.nil, ys => ys
      | DList.cons x xs, ys => DList.cons x (DList.append xs ys)

    def DList.length {α : Type} : DList α → ℕ₀
      | DList.nil => 𝟘
      | DList.cons _ xs => σ (DList.length xs)

    def DList.Mem {α : Type} (a : α) : DList α → Prop
      | DList.nil => False
      | DList.cons h t => a = h ∨ DList.Mem a t

    notation:50 a " ∈ " l => DList.Mem a l

    theorem mem_cons {α : Type} (a b : α) (xs : DList α) :
      DList.Mem a (DList.cons b xs) ↔ a = b ∨ DList.Mem a xs := by
      rfl

    theorem mem_append {α : Type} (a : α) (xs ys : DList α) :
      DList.Mem a (DList.append xs ys) ↔ DList.Mem a xs ∨ DList.Mem a ys := by
      induction xs with
      | nil =>
        simp [DList.append, DList.Mem]
      | cons x xs ih =>
        simp [DList.append, DList.Mem, ih, or_assoc]

    inductive DList.NoDup {α : Type} : DList α → Prop
      | nil : DList.NoDup DList.nil
      | cons {x : α} {xs : DList α} : (DList.Mem x xs → False) → DList.NoDup xs → DList.NoDup (DList.cons x xs)

    def DList.MemDec {α : Type} [DecidableEq α] (a : α) : (xs : DList α) → Decidable (DList.Mem a xs)
      | DList.nil => isFalse (by intro h; exact h)
      | DList.cons x xs =>
        match decEq a x with
        | isTrue h_eq => isTrue (Or.inl h_eq)
        | isFalse h_neq =>
          match DList.MemDec a xs with
          | isTrue h_mem => isTrue (Or.inr h_mem)
          | isFalse h_mem =>
            isFalse (by
              intro h
              cases h with
              | inl h_eq => exact h_neq h_eq
              | inr h_tail => exact h_mem h_tail)

    structure DivisorsList (n : ℕ₀) : Type where
      vals : DList ℕ₀
      all_divide : ∀ d : ℕ₀, DList.Mem d vals → d ∣ n
      complete : ∀ d : ℕ₀, d ∣ n → DList.Mem d vals
      symm : ∀ d k : ℕ₀, DList.Mem d vals → n = mul d k → DList.Mem k vals

    def Divisors (n : ℕ₀) : ℕ₀ → Prop :=
      fun d => d ∣ n

    inductive Multiples (n : ℕ₀) : ℕ₀ → Prop
      | zero : Multiples n 𝟘
      | add_step {k : ℕ₀} : Multiples n k → Multiples n (add k n)

    theorem multiples_to_divides {n m : ℕ₀} : Multiples n m → n ∣ m := by
      intro h
      induction h with
      | zero =>
        exact ⟨𝟘, by rw [mul_zero]⟩
      | @add_step k h_ih ih =>
        rcases ih with ⟨t, ht⟩
        refine ⟨σ t, ?_⟩
        rw [mul_succ, ht]

    theorem divides_to_multiples {n m : ℕ₀} : n ∣ m → Multiples n m := by
      intro h
      rcases h with ⟨k, hk⟩
      subst hk
      induction k with
      | zero =>
        rw [mul_zero]
        exact Multiples.zero
      | succ k' ih =>
        rw [mul_succ]
        exact Multiples.add_step ih

    theorem multiples_iff_divides (n m : ℕ₀) : Multiples n m ↔ n ∣ m := by
      constructor
      · exact multiples_to_divides
      · exact divides_to_multiples

    theorem divides_refl (a : ℕ₀) : a ∣ a := by
      exact ⟨𝟙, by rw [mul_one]⟩

    theorem one_divides (a : ℕ₀) : 𝟙 ∣ a := by
      exact ⟨a, by rw [one_mul]⟩

    theorem divides_zero (a : ℕ₀) : a ∣ 𝟘 := by
      exact ⟨𝟘, by rw [mul_zero]⟩

    theorem zero_divides_iff (b : ℕ₀) : (𝟘 ∣ b) ↔ b = 𝟘 := by
      constructor
      · intro h
        rcases h with ⟨k, hk⟩
        rw [hk, zero_mul]
      · intro h
        rw [h]
        exact divides_zero 𝟘

    theorem divides_trans {a b c : ℕ₀} : a ∣ b → b ∣ c → a ∣ c := by
      intro h_ab h_bc
      rcases h_ab with ⟨k, hk⟩
      rcases h_bc with ⟨l, hl⟩
      refine ⟨mul k l, ?_⟩
      rw [hl, hk, mul_assoc]

    theorem divides_mul_right {a b c : ℕ₀} : a ∣ b → a ∣ (mul b c) := by
      intro h_ab
      rcases h_ab with ⟨k, hk⟩
      refine ⟨mul k c, ?_⟩
      rw [hk, mul_assoc]

    theorem divides_mul_left {a b c : ℕ₀} : a ∣ b → a ∣ (mul c b) := by
      intro h_ab
      rcases h_ab with ⟨k, hk⟩
      refine ⟨mul c k, ?_⟩
      rw [hk]
      rw [mul_comm c (mul a k), mul_assoc k a c, mul_comm k c]

    theorem divides_add {a b c : ℕ₀} : a ∣ b → a ∣ c → a ∣ (add b c) := by
      intro h_ab h_ac
      rcases h_ab with ⟨k, hk⟩
      rcases h_ac with ⟨l, hl⟩
      refine ⟨add k l, ?_⟩
      rw [hk, hl, ← mul_ldistr a k l]

    def IsGCD (a b d : ℕ₀) : Prop :=
      d ∣ a ∧ d ∣ b ∧ ∀ c : ℕ₀, (c ∣ a ∧ c ∣ b) → c ∣ d

    def IsLCM (a b m : ℕ₀) : Prop :=
      a ∣ m ∧ b ∣ m ∧ ∀ c : ℕ₀, (a ∣ c ∧ b ∣ c) → m ∣ c

    def Coprime (a b : ℕ₀) : Prop :=
      IsGCD a b 𝟙

    def Prime (p : ℕ₀) : Prop :=
      p ≠ 𝟘 ∧ p ≠ 𝟙 ∧ ∀ a b : ℕ₀, p ∣ (mul a b) → p ∣ a ∨ p ∣ b

    theorem divisorslist_one_mem {n : ℕ₀} (d : DivisorsList n) : 𝟙 ∈ d.vals :=
      d.complete 𝟙 (one_divides n)

    theorem divisorslist_self_mem {n : ℕ₀} (d : DivisorsList n) : n ∈ d.vals :=
      d.complete n (divides_refl n)

  end NatArith

end Peano

export Peano.NatArith (
  Divides
  MultipleOf
  DivisorOf
  Divisors
  Multiples
  multiples_to_divides
  divides_to_multiples
  multiples_iff_divides
  DList
  DivisorsList
  DList.Mem
  DList.append
  DList.length
  DList.NoDup
  DList.MemDec
  mem_cons
  mem_append
  one_divides
  divisorslist_one_mem
  divisorslist_self_mem
  IsGCD
  IsLCM
  Coprime
  Prime
  divides_refl
  divides_zero
  zero_divides_iff
  divides_trans
  divides_mul_right
  divides_mul_left
  divides_add
)
