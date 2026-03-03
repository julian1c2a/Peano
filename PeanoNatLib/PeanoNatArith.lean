/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- PeanoNatLib/PeanoNatArith.lean
import Init.Classical
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
      open Peano.Sub
      open Peano.Div
      open Peano.MaxMin
      open Classical

    def Divides (a b : ℕ₀) : Prop :=
      ∃ k : ℕ₀, b = mul a k

    infix:50 " ∣ " => Divides
    notation:50 a " ∤ " b => ¬ Divides a b

    def MultipleOf (n m : ℕ₀) : Prop :=
      Divides n m

    def DivisorOf (d n : ℕ₀) : Prop :=
      Divides d n
      open Classical

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

    theorem divides_le {a b : ℕ₀} :
      a ∣ b → b ≠ 𝟘 → a ≤ b
        := by
      intro h h_b_ne_zero
      rcases h with ⟨k, hk⟩
      subst hk
      cases k with
      | zero =>
        rw [mul_zero] at h_b_ne_zero
        exfalso
        exact h_b_ne_zero rfl
      | succ k' =>
        rw [mul_succ, add_comm]
        apply le_self_add_r

    theorem antisymm_divides {a b : ℕ₀} : (a ∣ b) → (b ∣ a) → a = b := by
      intro h_ab h_ba
      cases Classical.em (a = 𝟘) with
      | inl ha0 =>
        rw [ha0] at h_ab
        have hb0 : b = 𝟘 := (zero_divides_iff b).mp h_ab
        rw [ha0, hb0]
      | inr hna0 =>
        have hnb0 : b ≠ 𝟘 := by
          intro hb0
          rw [hb0] at h_ba
          exact hna0 ((zero_divides_iff a).mp h_ba)
        have h_le_ab : a ≤ b := divides_le h_ab hnb0
        have h_le_ba : b ≤ a := divides_le h_ba hna0
        exact le_antisymm a b h_le_ab h_le_ba

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

    -- ========================================
    -- Versiones para ℕ₁ (números naturales positivos)
    -- ========================================

    -- Divisibilidad para ℕ₁
    def Divides₁ (a b : ℕ₁) : Prop :=
      a.val ∣ b.val

    infix:50 " ∣₁ " => Divides₁

    -- IsGCD para ℕ₁: d es el máximo común divisor de a y b
    def IsGCD₁ (a b d : ℕ₁) : Prop :=
      d ∣₁ a ∧ d ∣₁ b ∧ ∀ c : ℕ₁, (c ∣₁ a ∧ c ∣₁ b) → c ∣₁ d

    -- Algoritmo de Euclides para ℕ₁
    def gcd₁ (a b : ℕ₁) : ℕ₁ :=
      let r := a.val % b.val
      if hr : r = 𝟘 then
        b  -- el resto es cero, entonces b divide a a perfectamente
      else
        have r_ne_zero : r ≠ 𝟘 := hr
        gcd₁ b ⟨r, r_ne_zero⟩
    termination_by b.val
    decreasing_by
      simp_wf
      apply Peano.Div.lt_sizeOf
      exact Peano.Div.mod_lt_divisor a.val b.val b.property

    -- Coprimalidad para ℕ₁
    def Coprime₁ (a b : ℕ₁) : Prop :=
      gcd₁ a b = ⟨𝟙, by decide⟩

  private theorem gcd_divides_first (a b : ℕ₀) : (gcd a b) ∣ a := by
  have H : ∀ (b a : ℕ₀), (gcd a b ∣ a) ∧ (gcd a b ∣ b) := by
    intro b_arg
    induction b_arg using well_founded_lt.induction
    rename_i b ih
    intro a
    unfold gcd
    by_cases h_b_is_zero : b = 𝟘
    · rw [h_b_is_zero]
      simp
      exact ⟨divides_refl a, divides_zero a⟩
    · simp [if_neg h_b_is_zero]
      have h_mod_lt_b : Lt (a % b) b := mod_lt_divisor a b h_b_is_zero
      let ih_call := ih (a % b) h_mod_lt_b
      let ih_specific := ih_call b
      rcases ih_specific with ⟨h_gcd_div_b, h_gcd_div_mod⟩
      have h_gcd_div_a : gcd b (a % b) ∣ a := by
        have h_div_prod : gcd b (a % b) ∣ mul (a / b) b :=
          divides_mul_left h_gcd_div_b
        have h_div_sum : gcd b (a % b) ∣ add (mul (a / b) b) (a % b) :=
          divides_add h_div_prod h_gcd_div_mod
        unfold div mod at h_div_sum
        rw [← divMod_eq a b h_b_is_zero] at h_div_sum
        exact h_div_sum
      exact ⟨h_gcd_div_a, h_gcd_div_b⟩
  exact (H b a).1

  private theorem gcd_divides_second (a b : ℕ₀) : (gcd a b) ∣ b := by
  have H : ∀ (b a : ℕ₀), (gcd a b ∣ a) ∧ (gcd a b ∣ b) := by
    intro b_arg
    induction b_arg using well_founded_lt.induction
    rename_i b ih
    intro a
    unfold gcd
    by_cases h_b_is_zero : b = 𝟘
    · rw [h_b_is_zero]
      simp
      exact ⟨divides_refl a, divides_zero a⟩
    · simp [if_neg h_b_is_zero]
      have h_mod_lt_b : Lt (a % b) b := mod_lt_divisor a b h_b_is_zero
      let ih_call := ih (a % b) h_mod_lt_b
      let ih_specific := ih_call b
      rcases ih_specific with ⟨h_gcd_div_b, h_gcd_div_mod⟩
      have h_gcd_div_a : gcd b (a % b) ∣ a := by
        have h_div_prod : gcd b (a % b) ∣ mul (a / b) b :=
          divides_mul_left h_gcd_div_b
        have h_div_sum : gcd b (a % b) ∣ add (mul (a / b) b) (a % b) :=
          divides_add h_div_prod h_gcd_div_mod
        unfold div mod at h_div_sum
        rw [← divMod_eq a b h_b_is_zero] at h_div_sum
        exact h_div_sum
      exact ⟨h_gcd_div_a, h_gcd_div_b⟩
  exact (H b a).2

  private theorem gcd_divides_both (a b : ℕ₀) : (gcd a b) ∣ a ∧ (gcd a b) ∣ b := by
    constructor
    · exact gcd_divides_first a b
    · exact gcd_divides_second a b

  /--
    Si c divide a y b, entonces c divide a - b (resta truncada), bajo la condición b < a.
  -/
  theorem divides_sub {a b c : ℕ₀} (h_lt_a_b : Lt b a) (ha : c ∣ a) (hb : c ∣ b) : c ∣ (sub a b) := by
    rcases ha with ⟨ka, hka⟩
    rcases hb with ⟨kb, hkb⟩
    -- c * kb < c * ka (reescribiendo b < a)
    have h_mul_lt : Lt (mul c kb) (mul c ka) := by
      rw [← hkb, ← hka]; exact h_lt_a_b
    -- Derivar Lt kb ka por contradicción
    have h_lt_kb_ka : Lt kb ka := by
      by_cases h_le : Le ka kb
      · -- Si ka ≤ kb, entonces c*ka ≤ c*kb, contradicción con c*kb < c*ka
        have h_le_mul : Le (mul c ka) (mul c kb) := by
          rw [mul_comm c ka, mul_comm c kb]
          exact mul_le_mono_right c h_le
        exact absurd (lt_of_lt_of_le h_mul_lt h_le_mul) (lt_irrefl (mul c kb))
      · exact nle_then_gt_wp h_le
    -- El testigo es sub ka kb
    exact ⟨sub ka kb, by rw [hka, hkb]; exact (mul_sub c ka kb h_lt_kb_ka).symm⟩

  /--
    Si c divide a y b, entonces c divide a % b (resto de la división euclídea).
  -/
  theorem divides_mod {a b c : ℕ₀} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (a % b) := by
    by_cases hb0 : b = 𝟘
    · -- Cuando b = 0, divMod a 0 = (0, 0), luego a % 0 = 0
      subst hb0; simp [mod, divMod]; exact divides_zero c
    · -- Cuando b ≠ 0, a = (a/b)*b + (a%b)
      by_cases hmod : (a % b) = 𝟘
      · rw [hmod]; exact divides_zero c
      · -- a%b ≠ 0, luego (a/b)*b < a
        have h_eq : a = add (mul (a / b) b) (a % b) := divMod_eq a b hb0
        have h1 : c ∣ mul (a / b) b := divides_mul_left hb
        have h_lt : Lt (mul (a / b) b) a := by
          have h_lt' : Lt (mul (a / b) b) (add (mul (a / b) b) (a % b)) :=
            lt_add_of_pos_right (neq_0_then_lt_0 hmod)
          rw [← h_eq] at h_lt'
          exact h_lt'
        have h_mod_eq : (a % b) = sub a (mul (a / b) b) := by
          have key : sub (add (mul (a / b) b) (a % b)) (mul (a / b) b) = a % b :=
            add_k_sub_k (a % b) (mul (a / b) b)
          rw [← h_eq] at key
          exact key.symm
        rw [h_mod_eq]
        exact divides_sub h_lt ha h1

  theorem gcd_greatest (a b c : ℕ₀) :
    (c ∣ a ∧ c ∣ b) → c ∣ (gcd a b)
      := by
    -- Generalizamos sobre ambos argumentos para que la hipótesis de inducción sea suficientemente fuerte
    have H : ∀ (b a : ℕ₀), c ∣ a → c ∣ b → c ∣ gcd a b := by
      intro b_arg
      induction b_arg using well_founded_lt.induction
      rename_i b ih
      intro a h_div_a h_div_b
      unfold gcd
      by_cases h_b_is_zero : b = 𝟘
      · -- gcd a 0 = a
        rw [h_b_is_zero]; simp; exact h_div_a
      · -- gcd a b = gcd b (a%b), inducción sobre (a%b) < b
        simp [if_neg h_b_is_zero]
        have h_mod_lt_b : Lt (a % b) b := mod_lt_divisor a b h_b_is_zero
        exact ih (a % b) h_mod_lt_b b h_div_b (divides_mod h_div_a h_div_b)
    intro ⟨h_a, h_b⟩
    exact H b a h_a h_b

    private theorem gcd_divides_gcd_symm (a b : ℕ₀) : gcd a b ∣ gcd b a :=
      gcd_greatest b a (gcd a b) ⟨gcd_divides_second a b, gcd_divides_first a b⟩

    -- First prove that gcd is commutative
    private theorem gcd_comm (a b : ℕ₀) : gcd a b = gcd b a :=
      antisymm_divides (gcd_divides_gcd_symm a b) (gcd_divides_gcd_symm b a)

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

    -- Lema auxiliar: reducción de gcd cuando b ≠ 0
    private theorem gcd_step (a b : ℕ₀) (hb : b ≠ 𝟘) : gcd a b = gcd b (a % b) := by
      apply antisymm_divides
      · -- gcd a b ∣ gcd b (a%b): usa gcd_greatest b (a%b) (gcd a b)
        apply gcd_greatest
        constructor
        · exact gcd_divides_second a b
        · exact divides_mod (gcd_divides_first a b) (gcd_divides_second a b)
      · -- gcd b (a%b) ∣ gcd a b: usa gcd_greatest a b (gcd b (a%b))
        apply gcd_greatest
        constructor
        · -- gcd b (a%b) ∣ a: reconstruir a desde a = (a/b)*b + (a%b)
          have h1 := gcd_divides_first b (a % b)   -- gcd b (a%b) ∣ b
          have h2 := gcd_divides_second b (a % b)  -- gcd b (a%b) ∣ a%b
          have h3 : gcd b (a % b) ∣ mul (a / b) b :=
            divides_mul_left h1
          have h4 : gcd b (a % b) ∣ add (mul (a / b) b) (a % b) :=
            divides_add h3 h2
          unfold div mod at h4
          rw [← divMod_eq a b hb] at h4
          exact h4
        · exact gcd_divides_first b (a % b)

    -- Lemma 2: Bézout-like form using max and min (natural version)
    -- For any a, b: ∃ n m, gcd(a,b) = n*max(a,b) - m*min(a,b)

    /--
      Forma aditiva de Bézout natural: ∃ n m, gcd(a,b) + n*min(a,b) = m*max(a,b).
      Se demuestra por inducción bien fundada sobre b.
    -/
    private theorem bezout_additive (a b : ℕ₀) :
        ∃ n m : ℕ₀,
          (add (gcd a b) (mul n (min a b)) = mul m (max a b)) ∨
          (add (gcd a b) (mul n (max a b)) = mul m (min a b))
            := by
      suffices H : ∀ (b a : ℕ₀), ∃ n m : ℕ₀,
          (add (gcd a b) (mul n (min a b)) = mul m (max a b)) ∨
          (add (gcd a b) (mul n (max a b)) = mul m (min a b)) by
        exact H b a
      intro b
      induction b using well_founded_lt.induction
      rename_i b ih
      intro a
      by_cases hb0 : b = 𝟘
      · -- b = 0: gcd(a,0) = a, max = a, min = 0, testigos n=0 m=1
        subst hb0
        have h_gcd_a0 : gcd a 𝟘 = a := by unfold gcd; rw [if_pos rfl]
        exact ⟨𝟘, 𝟙, Or.inl (by rw [h_gcd_a0, zero_mul, add_zero, one_mul, max_0_not])⟩
      · -- b ≠ 0: gcd(a,b) = gcd(b, a%b), IH sobre (a%b < b)
        have h_mod_lt : Lt (a % b) b := mod_lt_divisor a b hb0
        -- IH sobre (b, a%b): gcd(b,a%b) + n'*min(b,a%b) = m'*max(b,a%b)
        -- Como a%b < b: max(b,a%b)=b, min(b,a%b)=a%b
        obtain ⟨n', m', ih_eq⟩ := ih (a % b) h_mod_lt b
        have h_max_b : max b (a % b) = b :=
          le_then_max_eq_left b (a % b) (Or.inl h_mod_lt)
        have h_min_b : min b (a % b) = a % b :=
          le_then_min_eq_right b (a % b) (Or.inl h_mod_lt)
        rw [h_max_b, h_min_b] at ih_eq
        -- ih_eq : gcd(b,a%b) + n'*(a%b) = m'*b
        have h_gcd_eq : gcd a b = gcd b (a % b) := gcd_step a b hb0
        rw [h_gcd_eq]
        -- Decidir quién es mayor entre a y b
        rcases le_total a b with h_le_ab | h_le_ba
        · -- a ≤ b: max=b, min=a
          have h_max : max a b = b := le_then_max_eq_right a b h_le_ab
          have h_min : min a b = a := le_then_min_eq_left a b h_le_ab
          rw [h_max, h_min]
          rcases h_le_ab with h_lt_ab | h_eq_ab
          · -- a < b: a%b = a (mod_of_lt)
            have h_mod_a : (a % b) = a := mod_of_lt a b h_lt_ab
            rw [h_mod_a] at ih_eq
            rw [h_mod_a]
            -- ih_eq ya es un Or con el tipo correcto
            exact ⟨n', m', ih_eq⟩
          · -- a = b: gcd(a,a) = a, testigos n=0 m=1
            rw [h_eq_ab]
            have h_mod_zero : (b % b) = 𝟘 := by
              have h_bpos : Lt 𝟘 b := neq_0_then_lt_0 hb0
              have h1 : Le (mul b 𝟙) b := by rw [mul_one]; exact le_refl b
              have h2 : Lt b (mul b (σ 𝟙)) := by
                rw [mul_succ, mul_one]
                exact lt_add_of_pos_right h_bpos
              have := mod_of_lt_nth_interval b b 𝟙 h1 h2
              rw [mul_one, sub_self] at this; exact this
            rw [h_mod_zero]
            have h_gcd_b0 : gcd b 𝟘 = b := by unfold gcd; rw [if_pos rfl]
            rw [h_gcd_b0]
            exact ⟨𝟘, 𝟙, Or.inl (by rw [zero_mul, add_zero, one_mul])⟩
        · -- b ≤ a: max=a, min=b
          have h_max : max a b = a := le_then_max_eq_left a b h_le_ba
          have h_min : min a b = b := le_then_min_eq_right a b h_le_ba
          rw [h_max, h_min]
          -- División: a = q*b + (a%b)
          let q := a / b
          have h_div_eq : a = add (mul q b) (a % b) := divMod_eq a b hb0
          -- q*b ≤ a
          have h_qb_le_a : Le (mul q b) a := by
            rw [h_div_eq]; exact le_self_add (mul q b) (a % b)
          by_cases hmod0 : (a % b) = 𝟘
          · -- a%b = 0: a = q*b, gcd(a,b)=b, testigos n=(q-1), m=1
            have h_a_eq : a = mul q b := by
              rw [hmod0, add_zero] at h_div_eq; exact h_div_eq
            -- q ≠ 0 pues b ≤ a y b ≠ 0
            have hqne : q ≠ 𝟘 := by
              intro hq0
              rw [hq0, zero_mul] at h_a_eq
              rcases h_le_ba with h_lt | h_eq
              · exact absurd (h_a_eq ▸ h_lt) (nlt_n_0 b)
              · exact hb0 (h_eq.trans h_a_eq)
            have hq_pos : Lt 𝟘 q := neq_0_then_lt_0 hqne
            have hq_ge1 : Le 𝟙 q := lt_0n_then_le_1n_wp hq_pos
            -- gcd(b,0) = b
            have h_gcd_b0 : gcd b 𝟘 = b := by unfold gcd; rw [if_pos rfl]
            rw [hmod0, h_gcd_b0]
            -- testigos: n = sub q 𝟙, m = 𝟙, forma Or.inl: G + (q-1)*b = 1*a
            refine ⟨sub q 𝟙, 𝟙, Or.inl ?_⟩
            rw [one_mul, add_comm]
            -- Goal: (sub q 𝟙)*b + b = a
            have h_expand : mul q b = add (mul (sub q 𝟙) b) b := by
              have h3 : add (mul (sub q 𝟙) b) b = add (mul (sub q 𝟙) b) (mul 𝟙 b) :=
                by rw [one_mul]
              rw [h3, ← mul_rdistr (sub q 𝟙) 𝟙 b, sub_k_add_k q 𝟙 hq_ge1]
            exact h_expand.symm.trans h_a_eq.symm
          · -- a%b ≠ 0: IH (Or) da:
            --   Or.inl: G + n'*(a%b) = m'*b  → derivar G + n'*a = (m'+n'*q)*b → Or.inr
            --   Or.inr: G + n'*b = m'*(a%b)  → derivar G + (n'+m'*q)*b = m'*a → Or.inl
            -- Lemas comunes a ambos casos:
            -- q*b < a
            have h_qb_lt_a : Lt (mul q b) a := by
              have : Lt (mul q b) (add (mul q b) (a % b)) :=
                lt_add_of_pos_right (neq_0_then_lt_0 hmod0)
              rw [← h_div_eq] at this; exact this
            have hle_qb : Le (mul q b) a := lt_imp_le _ _ h_qb_lt_a
            -- a%b = a - q*b
            have h_mod_eq : (a % b) = sub a (mul q b) := by
              have key := add_k_sub_k (a % b) (mul q b)
              rw [← h_div_eq] at key; exact key.symm
            -- Lema: para cualquier c, (c*q)*b ≤ c*a
            -- [mul_le_mono_right : Le (n*k) (m*k), luego mul_comm]
            have le_cq_ca : ∀ c : ℕ₀, Le (mul (mul c q) b) (mul c a) := fun c => by
              have h1 := mul_le_mono_right c hle_qb
              rw [mul_comm (mul q b) c, mul_comm a c] at h1
              rwa [← mul_assoc q c b] at h1
            -- Lema: c*(a%b) = c*a - (c*q)*b
            have mul_mod : ∀ c : ℕ₀,
                mul c (a % b) = sub (mul c a) (mul (mul c q) b) := fun c => by
              rw [h_mod_eq, mul_sub c a (mul q b) h_qb_lt_a]
              congr 1; rw [← mul_assoc q c b]
            -- Reescribir ih_eq con h_mul_mod para n'
            rw [mul_mod n'] at ih_eq
            -- ih_eq (Or):
            --   Or.inl: G + (n'*a - (n'*q)*b) = m'*b
            --   Or.inr: G + n'*b = m'*(a%b)  [no tocado por mul_mod n', ya que es mul m' ...]
            rcases ih_eq with ih_eq | ih_eq
            · -- Or.inl: G + (n'*a - (n'*q)*b) = m'*b
              -- Derivar: G + n'*a = (m'+n'*q)*b
              -- Prueba: G + n'*a = G + (n'*a-(n'*q)*b) + (n'*q)*b = m'*b + (n'*q)*b = (m'+n'*q)*b
              have h_le_mul : Le (mul (mul n' q) b) (mul n' a) := le_cq_ca n'
              have h_move : add (gcd b (a % b)) (mul n' a) =
                  mul (add m' (mul n' q)) b := by
                rw [← sub_k_add_k (mul n' a) (mul (mul n' q) b) h_le_mul,
                    add_assoc, ih_eq, ← mul_rdistr]
              exact ⟨n', add m' (mul n' q), Or.inr h_move⟩
            · -- Or.inr: G + n'*b = m'*(a%b)
              -- Reescribir con mul_mod m': m'*(a%b) = m'*a - (m'*q)*b
              rw [mul_mod m'] at ih_eq
              -- ih_eq: G + n'*b = m'*a - (m'*q)*b
              -- Derivar: G + (n'+m'*q)*b = m'*a
              -- Prueba: G + (n'+m'*q)*b = (G + n'*b) + (m'*q)*b = (m'*a-(m'*q)*b) + (m'*q)*b = m'*a
              have h_le_m : Le (mul (mul m' q) b) (mul m' a) := le_cq_ca m'
              have h_move2 : add (gcd b (a % b)) (mul (add n' (mul m' q)) b) =
                  mul m' a := by
                rw [mul_rdistr, add_assoc, ih_eq]
                exact sub_k_add_k (mul m' a) (mul (mul m' q) b) h_le_m
              exact ⟨add n' (mul m' q), m', Or.inl h_move2⟩

    /--
      Lema de Bézout en forma substractiva: el mcd es expresable como diferencia
      n*a - m*b  o bien  n*b - m*a  con coeficientes naturales.
    -/
    theorem bezout_natform (a b : ℕ₀) :
        ∃ n m : ℕ₀,
          (gcd a b = sub (mul n a) (mul m b)) ∨
          (gcd a b = sub (mul n b) (mul m a))
            := by
      obtain ⟨n, m, h⟩ := bezout_additive a b
      -- h : (G + n*min = m*max) ∨ (G + n*max = m*min)
      -- En ambos casos derivamos G = sub(m*max)(n*min) o G = sub(m*min)(n*max)
      -- y según quién sea max/min entre a y b, obtenemos la forma Or adecuada.
      -- Lema auxiliar: de G + k*x = l*y se sigue G = sub (l*y) (k*x)
      have aux : ∀ (x y k l : ℕ₀), add (gcd a b) (mul k x) = mul l y →
          gcd a b = sub (mul l y) (mul k x) := fun x y k l heq => by
        have key := add_k_sub_k (gcd a b) (mul k x)
        rw [add_comm] at key; rw [heq] at key; exact key.symm
      rcases h with h | h
      · -- Or.inl: G + n*min = m*max
        rcases le_total a b with h_le | h_le
        · -- a ≤ b: min=a, max=b  →  G + n*a = m*b  →  G = m*b - n*a
          rw [le_then_min_eq_left a b h_le, le_then_max_eq_right a b h_le] at h
          exact ⟨m, n, Or.inr (aux a b n m h)⟩
        · -- b ≤ a: min=b, max=a  →  G + n*b = m*a  →  G = m*a - n*b
          rw [le_then_min_eq_right a b h_le, le_then_max_eq_left a b h_le] at h
          exact ⟨m, n, Or.inl (aux b a n m h)⟩
      · -- Or.inr: G + n*max = m*min
        rcases le_total a b with h_le | h_le
        · -- a ≤ b: max=b, min=a  →  G + n*b = m*a  →  G = m*a - n*b
          rw [le_then_min_eq_left a b h_le, le_then_max_eq_right a b h_le] at h
          exact ⟨m, n, Or.inl (aux b a n m h)⟩
        · -- b ≤ a: max=a, min=b  →  G + n*a = m*b  →  G = m*b - n*a
          rw [le_then_min_eq_right a b h_le, le_then_max_eq_left a b h_le] at h
          exact ⟨m, n, Or.inr (aux a b n m h)⟩

    -- subₕₖ a b (Lt b a) = sub a b
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

    -- ========================================
    -- Teoremas básicos para ℕ₁
    -- ========================================

    -- Reflexividad de la divisibilidad en ℕ₁
    theorem divides₁_refl (a : ℕ₁) : a ∣₁ a := by
      unfold Divides₁
      exact divides_refl a.val

    -- Transitividad de la divisibilidad en ℕ₁
    theorem divides₁_trans {a b c : ℕ₁} (hab : a ∣₁ b) (hbc : b ∣₁ c) : a ∣₁ c := by
      unfold Divides₁ at *
      exact divides_trans hab hbc

    -- Antisimetría de la divisibilidad en ℕ₁
    theorem divides₁_antisymm {a b : ℕ₁} (hab : a ∣₁ b) (hba : b ∣₁ a) : a = b := by
      apply Subtype.ext
      unfold Divides₁ at *
      exact antisymm_divides hab hba

    -- Lemas auxiliares para gcd₁

    -- Si a % b = 0, entonces b divide a a
    theorem mod_eq_zero_iff_divides {a b : ℕ₁} : (a.val % b.val) = 𝟘 ↔ (b ∣₁ a) := by
      unfold Divides₁
      unfold Divides
      constructor
      · -- Dirección →: a % b = 0 → ∃ k, a = b * k
        intro h_mod
        have h_eq : a.val = add (mul (a.val / b.val) b.val) (a.val % b.val) :=
          divMod_eq a.val b.val b.property
        rw [h_mod, add_zero] at h_eq
        exact ⟨a.val / b.val, h_eq.trans (mul_comm _ _)⟩
      · -- Dirección ←: ∃ k, a = b * k → a % b = 0
        intro ⟨k, hk⟩
        have h_div_a : b.val ∣ a.val := ⟨k, hk⟩
        have h_div_mod : b.val ∣ (a.val % b.val) :=
          divides_mod h_div_a (divides_refl b.val)
        have h_mod_lt : Lt (a.val % b.val) b.val :=
          mod_lt_divisor a.val b.val b.property
        cases Classical.em ((a.val % b.val) = 𝟘) with
        | inl h => exact h
        | inr h => exact absurd h_mod_lt (le_not_lt (divides_le h_div_mod h))

    -- gcd₁ preserva la igualdad en los valores subyacentes
    theorem gcd₁_val_eq (a b : ℕ₁) :
        (gcd₁ a b).val = gcd a.val b.val := by
      suffices H : ∀ (bv : ℕ₀) (a b : ℕ₁), b.val = bv →
          (gcd₁ a b).val = gcd a.val b.val from H b.val a b rfl
      intro bv
      induction bv using well_founded_lt.induction
      rename_i bv ih
      intro a b hb
      by_cases hr : (a.val % b.val) = 𝟘
      · -- gcd₁ a b = b: desplegar y sustituir r := 0
        have hv : (gcd₁ a b).val = b.val := by
          unfold gcd₁; rw [hr]; simp
        rw [hv, gcd_step a.val b.val b.property, hr]
        simp [gcd]
      · -- gcd₁ a b = gcd₁ b ⟨a%b, hr⟩: desplegar y sustituir
        have hv : (gcd₁ a b).val = (gcd₁ b ⟨a.val % b.val, hr⟩).val := by
          have hr' : ¬((a.val % b.val) = 𝟘) := hr
          unfold gcd₁; rw [show (a.val % b.val) ≠ 𝟘 from hr]; simp
        rw [hv]
        have h_r_lt_bv : Lt (a.val % b.val) bv :=
          hb ▸ mod_lt_divisor a.val b.val b.property
        rw [ih (a.val % b.val) h_r_lt_bv b ⟨a.val % b.val, hr⟩ rfl,
            ← gcd_step a.val b.val b.property]

    -- gcd₁ es conmutativo
    theorem gcd₁_comm (a b : ℕ₁) : gcd₁ a b = gcd₁ b a := by
      apply Subtype.ext
      rw [gcd₁_val_eq, gcd₁_val_eq]
      exact gcd_comm a.val b.val
    theorem gcd₁_divides_left (a b : ℕ₁) : gcd₁ a b ∣₁ a := by
      unfold Divides₁
      rw [gcd₁_val_eq]
      exact gcd_divides_left a.val b.val

    theorem gcd₁_divides_right (a b : ℕ₁) : gcd₁ a b ∣₁ b := by
      unfold Divides₁
      rw [gcd₁_val_eq]
      exact gcd_divides_right a.val b.val

    theorem gcd₁_divides_both (a b : ℕ₁) : gcd₁ a b ∣₁ a ∧ gcd₁ a b ∣₁ b := by
      constructor
      · exact gcd₁_divides_left a b
      · exact gcd₁_divides_right a b

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
  divides_sub
  divides_mod
  gcd_greatest
  -- Nuevas definiciones para ℕ₁
  Divides₁
  IsGCD₁
  gcd₁
  Coprime₁
  divides₁_refl
  divides₁_trans
  divides₁_antisymm
  gcd₁_comm
  gcd₁_divides_left
  gcd₁_divides_right
  gcd₁_divides_both
)
