-- PeanoNatLib/PeanoNatArith.lean

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatDiv
import PeanoNatLib.PeanoNatMaxMin


namespace Peano
  open Peano

  namespace NatArith
      open Peano.Axioms
      open Peano.Order
      open Peano.StrictOrder
      open Peano.Add
      open Peano.Mul
      open Peano.Sub
      open Peano.Div
      open Peano.MaxMin

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

    def DList.filter {α : Type} (p : α → Bool) : DList α → DList α
      | DList.nil => DList.nil
      | DList.cons x xs =>
        if p x then DList.cons x (DList.filter p xs) else DList.filter p xs

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

    def range_from_one : ℕ₀ → DList ℕ₀
      | 𝟘 => DList.nil
      | σ n' => DList.append (range_from_one n') (DList.cons (σ n') DList.nil)

    def dividesb (d n : ℕ₀) : Bool :=
      decide ((n % d) = 𝟘)

    def Factors_of (n : ℕ₁) : DList ℕ₀ :=
      let n0 := n.val
      DList.filter (fun d => dividesb d n0) (range_from_one n0)

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

    def gcd (a b : ℕ₀) : ℕ₀ :=
      if b = 𝟘 then a else gcd b (a % b)
    termination_by b
    decreasing_by
      simp_wf
      -- Goal: sizeOf (a % b) < sizeOf b under the else branch (b ≠ 𝟘)
      -- Convert Lt to sizeOf ordering
      apply Peano.Div.lt_sizeOf
      exact Peano.Div.mod_lt_divisor a b (by assumption)

    def lcm (a b : ℕ₀) : ℕ₀ :=
      (mul a b) / (gcd a b)

    -- First prove that gcd is commutative
    private theorem gcd_comm (a b : ℕ₀) : gcd a b = gcd b a := by
      sorry -- TODO: requires careful WF induction on both arguments

    -- Helper lemmas for divisibility
    private theorem gcd_divides_both (a b : ℕ₀) : (gcd a b) ∣ a ∧ (gcd a b) ∣ b := by
      sorry -- TODO: Requires careful WF induction with proper term recursion

    private theorem gcd_divides_left (a b : ℕ₀) : (gcd a b) ∣ a :=
      (gcd_divides_both a b).1

    private theorem gcd_divides_right (a b : ℕ₀) : (gcd a b) ∣ b :=
      (gcd_divides_both a b).2 -- Similar to gcd_divides_left but simpler by symmetry

    -- Lemma 1: gcd divides any linear combination n*a + m*b
    theorem gcd_divides_linear_combo (a b n m : ℕ₀) :
        (gcd a b) ∣ add (mul a n) (mul b m) := by
      have h_left := gcd_divides_left a b
      have h_right := gcd_divides_right a b
      -- gcd a b ∣ a  implies  gcd a b ∣ a*n
      have h_an : (gcd a b) ∣ mul a n := divides_mul_right h_left
      -- gcd a b ∣ b  implies  gcd a b ∣ b*m
      have h_bm : (gcd a b) ∣ mul b m := divides_mul_right h_right
      -- Both divide the sum
      exact divides_add h_an h_bm

    -- Lemma 2: Bézout-like form using max and min (natural version)
    -- For any a, b: ∃ n m, gcd(a,b) = n*max(a,b) - m*min(a,b)
    theorem bezout_natform (a b : ℕ₀) :
        ∃ n m : ℕ₀,
          gcd a b = sub (mul n (max a b)) (mul m (min a b)) := by
      sorry -- Requires detailed case analysis and induction on Euclidean algorithm

    -- Lemma 3: gcd divides the max
    theorem gcd_divides_max (a b : ℕ₀) : gcd a b ∣ max a b := by
      have h_left := gcd_divides_left a b
      have h_right := gcd_divides_right a b
      by_cases h : Le a b
      · -- If a ≤ b, then max a b = b
        have h_eq := Peano.MaxMin.le_then_max_eq_right a b h
        rw [h_eq]
        exact h_right
      · -- If ¬(a ≤ b), then b < a and max a b = a
        have h_lt : Peano.StrictOrder.Lt b a := Peano.MaxMin.Lt_of_not_le h
        have h_le : Le b a := Or.inl h_lt
        have h_eq := Peano.MaxMin.le_then_max_eq_left a b h_le
        rw [h_eq]
        exact h_left

    -- Lemma 4: gcd divides the min
    theorem gcd_divides_min (a b : ℕ₀) : gcd a b ∣ min a b := by
      have h_left := gcd_divides_left a b
      have h_right := gcd_divides_right a b
      by_cases h : Le a b
      · -- If a ≤ b, then min a b = a
        have h_eq := Peano.MaxMin.le_then_min_eq_left a b h
        rw [h_eq]
        exact h_left
      · -- If ¬(a ≤ b), then b < a and min a b = b
        have h_lt : Peano.StrictOrder.Lt b a := Peano.MaxMin.Lt_of_not_le h
        have h_le : Le b a := Or.inl h_lt
        have h_eq := Peano.MaxMin.le_then_min_eq_right a b h_le
        rw [h_eq]
        exact h_right




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
  DList.filter
  DList.length
  DList.NoDup
  DList.MemDec
  mem_cons
  mem_append
  range_from_one
  dividesb
  Factors_of
  one_divides
  divisorslist_one_mem
  divisorslist_self_mem
  IsGCD
  IsLCM
  Coprime
  Prime
  gcd
  lcm
  divides_refl
  divides_zero
  zero_divides_iff
  divides_trans
  divides_mul_right
  divides_mul_left
  divides_add
)
