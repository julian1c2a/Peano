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

    -- Lemma 2: Bézout-like form using max and min (natural version)
    -- For any a, b: ∃ n m, gcd(a,b) = n*max(a,b) - m*min(a,b)

    /--
      Forma aditiva de Bézout natural: ∃ n m, gcd(a,b) + n*min(a,b) = m*max(a,b).
      Se demuestra por inducción bien fundada sobre b.
    -/
    private theorem bezout_additive (a b : ℕ₀) :
        ∃ n m : ℕ₀, add (gcd a b) (mul n (min a b)) = mul m (max a b) := by
      suffices H : ∀ (b a : ℕ₀), ∃ n m : ℕ₀,
          add (gcd a b) (mul n (min a b)) = mul m (max a b) by
        exact H b a
      intro b
      induction b using well_founded_lt.induction
      rename_i b ih
      intro a
      by_cases hb0 : b = 𝟘
      · -- b = 0: gcd(a,0) = a, max = a, min = 0, testigos n=0 m=1
        subst hb0
        refine ⟨𝟘, 𝟙, ?_⟩
        rw [mul_zero, add_zero, one_mul, max_0_not]
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
        have h_gcd_eq : gcd a b = gcd b (a % b) := by
          unfold gcd; rw [if_neg hb0]
        rw [h_gcd_eq]
        -- División: a = q*b + (a%b)
        set q := a / b
        have h_div_eq : a = add (mul q b) (a % b) := divMod_eq a b hb0
        -- Decidir quién es mayor entre a y b
        rcases le_total a b with h_le_ab | h_le_ba
        · -- a ≤ b: max=b, min=a
          have h_max : max a b = b := le_then_max_eq_right a b h_le_ab
          have h_min : min a b = a := le_then_min_eq_left a b h_le_ab
          rw [h_max, h_min]
          rcases h_le_ab with h_lt_ab | h_eq_ab
          · -- a < b: a%b = a (mod_of_lt)
            have h_mod_a : a % b = a := mod_of_lt a b h_lt_ab
            rw [h_mod_a] at ih_eq
            -- gcd(b,a) + n'*a = m'*b, y gcd(a,b)=gcd(b,a) por gcd_comm
            exact ⟨n', m', by rw [← gcd_comm b a]; exact ih_eq⟩
          · -- a = b: gcd(a,a) = a, testigos n=0 m=1
            subst h_eq_ab
            have h_mod_zero : b % b = 𝟘 := by
              have := mod_of_lt_nth_interval b b 𝟙
                (by rw [mul_one])
                (by rw [mul_succ, mul_one]; exact lt_self_σ_self b)
              rw [mul_one, sub_self] at this; exact this
            rw [h_mod_zero]
            have h_gcd_b0 : gcd b 𝟘 = b := by unfold gcd; simp
            rw [h_gcd_b0]
            have h_max_bb : max b b = b := le_then_max_eq_right b b (le_refl b)
            have h_min_bb : min b b = b := le_then_min_eq_left b b (le_refl b)
            rw [h_max_bb, h_min_bb]
            exact ⟨𝟘, 𝟙, by rw [mul_zero, add_zero, one_mul]⟩
        · -- b ≤ a: max=a, min=b
          have h_max : max a b = a := le_then_max_eq_left a b h_le_ba
          have h_min : min a b = b := le_then_min_eq_right a b h_le_ba
          rw [h_max, h_min]
          -- q*b ≤ a
          have h_qb_le_a : Le (mul q b) a := by
            rw [h_div_eq]; exact le_self_add (mul q b) (a % b)
          by_cases hmod0 : a % b = 𝟘
          · -- a%b = 0: a = q*b, gcd(a,b)=b, testigos n=(q-1), m=1
            have h_a_eq : a = mul q b := by
              rw [hmod0, add_zero] at h_div_eq; exact h_div_eq
            -- q ≠ 0 pues b ≤ a y b ≠ 0
            have hqne : q ≠ 𝟘 := by
              intro hq0
              rw [hq0, zero_mul] at h_a_eq
              rcases h_le_ba with h_lt | h_eq
              · exact absurd (h_a_eq ▸ h_lt) (nlt_n_0 b)
              · exact hb0 h_eq.symm
            have hq_pos : Lt 𝟘 q := neq_0_then_lt_0 hqne
            have hq_ge1 : Le 𝟙 q := hq_pos
            -- gcd(b,0) = b
            have h_gcd_b0 : gcd b 𝟘 = b := by simp [gcd]
            rw [hmod0, h_gcd_b0]
            -- testigos: n = sub q 𝟙, m = 𝟙
            -- b + (q-1)*b = q*b = a
            refine ⟨sub q 𝟙, 𝟙, ?_⟩
            rw [one_mul]
            have h_sub_mul : mul (sub q 𝟙) b = sub (mul q b) (mul 𝟙 b) := by
              rw [mul_comm (sub q 𝟙) b, mul_comm q b, mul_comm 𝟙 b]
              exact mul_sub b q 𝟙 hq_ge1
            rw [h_sub_mul, mul_one, ← h_a_eq, add_comm]
            exact sub_k_add_k a b h_le_ba
          · -- a%b ≠ 0: derivamos usando mul_sub
            -- q*b < a
            have h_qb_lt_a : Lt (mul q b) a := by
              have : Lt (mul q b) (add (mul q b) (a % b)) :=
                lt_add_of_pos_right (neq_0_then_lt_0 hmod0)
              rw [← h_div_eq] at this; exact this
            -- a%b = a - q*b
            have h_mod_eq : a % b = sub a (mul q b) := by
              have key := add_k_sub_k (a % b) (mul q b)
              rw [← h_div_eq] at key; exact key.symm
            -- n'*(a%b) = n'*(a - q*b) = n'*a - n'*(q*b)
            have h_mul_mod : mul n' (a % b) = sub (mul n' a) (mul (mul n' q) b) := by
              rw [h_mod_eq, mul_sub n' a (mul q b) h_qb_lt_a, mul_assoc n' q b]
            -- Le (n'*(q*b)) (n'*a)
            have h_le_mul : Le (mul (mul n' q) b) (mul n' a) := by
              rw [mul_assoc n' q b]
              exact mul_le_mono_right n' (lt_imp_le _ _ h_qb_lt_a)
            -- ih_eq: gcd + n'*(a%b) = m'*b
            -- rw h_mul_mod: gcd + (n'*a - n'*q*b) = m'*b
            rw [h_mul_mod] at ih_eq
            -- → gcd + n'*a = m'*b + n'*q*b = (m' + n'*q)*b
            have h_move : add (gcd b (a % b)) (mul n' a) =
                mul (add m' (mul n' q)) b := by
              -- usando add_sub_assoc: (X-Y)+Z = (X+Z)-Y  con Y≤X
              -- ih_eq: gcd + (n'a - n'qb) = m'b
              -- ↔ add_comm: (n'a - n'qb) + gcd = m'b
              -- add_sub_assoc (n'a) gcd (n'qb) h_le gives:
              --   (n'a - n'qb) + gcd = (n'a + gcd) - n'qb
              -- so (n'a + gcd) - n'qb = m'b
              -- → n'a + gcd = m'b + n'qb [sub_k_add_k]
              have step1 : add (sub (mul n' a) (mul (mul n' q) b)) (gcd b (a % b)) =
                  sub (add (mul n' a) (gcd b (a % b))) (mul (mul n' q) b) :=
                add_sub_assoc (mul n' a) (gcd b (a % b)) (mul (mul n' q) b) h_le_mul
              have step2 : sub (add (mul n' a) (gcd b (a % b))) (mul (mul n' q) b) = mul m' b := by
                rw [add_comm (sub (mul n' a) (mul (mul n' q) b)) (gcd b (a % b))] at ih_eq
                rw [← step1]; exact ih_eq
              have step3 : add (mul n' a) (gcd b (a % b)) =
                  add (mul m' b) (mul (mul n' q) b) := by
                have := sub_k_add_k (add (mul n' a) (gcd b (a % b))) (mul (mul n' q) b)
                    h_le_mul
                rw [step2] at this
                rw [add_comm (mul m' b) (mul (mul n' q) b)]
                exact this.symm
              have step4 : add (mul m' b) (mul (mul n' q) b) = mul (add m' (mul n' q)) b := by
                rw [mul_rdistr]; rw [mul_assoc]
              rw [add_comm (gcd b (a % b)) (mul n' a)]
              rw [step3, step4]
            exact ⟨n', add m' (mul n' q), h_move⟩

    theorem bezout_natform (a b : ℕ₀) :
        ∃ n m : ℕ₀,
          gcd a b = sub (mul n (max a b)) (mul m (min a b)) := by
      obtain ⟨n, m, h⟩ := bezout_additive a b
      -- h : gcd(a,b) + n*min(a,b) = m*max(a,b)
      -- → gcd(a,b) = m*max(a,b) - n*min(a,b)
      refine ⟨m, n, ?_⟩
      have key := add_k_sub_k (gcd a b) (mul n (min a b))
      -- key : (n*min + gcd) - n*min = gcd
      rw [add_comm] at key
      -- key : (gcd + n*min) - n*min = gcd
      rw [h] at key
      -- key : m*max - n*min = gcd
      exact key.symm

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

    -- Lemas auxiliares para gcd₁

    -- Si a % b = 0, entonces b divide a a
    private theorem mod_eq_zero_iff_divides {a b : ℕ₁} : (a.val % b.val) = 𝟘 ↔ (b ∣₁ a) := by
      unfold Divides₁
      unfold Divides
      constructor
      · intro h_mod
        sorry -- TODO: requiere teorema de división con resto
      · intro h_div
        sorry -- TODO: si b | a entonces a % b = 0

    -- gcd₁ preserva la igualdad en los valores subyacentes
    private theorem gcd₁_val_eq (a b : ℕ₁) :
        (gcd₁ a b).val = gcd a.val b.val := by
      sorry -- TODO: mostrar que gcd₁ y gcd dan el mismo resultado

    -- gcd₁ es conmutativo
    -- Esta es una prueba difícil que requiere varios lemas auxiliares
    theorem gcd₁_comm (a b : ℕ₁) : gcd₁ a b = gcd₁ b a := by
      -- Estrategia general para la prueba completa:
      -- 1. Mostrar que el algoritmo de Euclides preserva el GCD:
      --    gcd₁ a b = gcd₁ b (a % b) cuando a % b ≠ 0
      -- 2. Usar inducción bien fundada sobre el tamaño del segundo argumento
      -- 3. Para el caso base (a % b = 0), necesitamos:
      --    - mod_eq_zero_iff_divides: a % b = 0 ↔ b | a
      --    - Si b | a y a | b, entonces a = b (antisimetría con divisibilidad)
      -- 4. Para el caso recursivo, aplicar HI y la propiedad de Euclides
      --
      -- Lemas necesarios (pendientes):
      -- - mod_eq_zero_iff_divides
      -- - gcd₁_divides_both
      -- - divides_antisymm: (a | b ∧ b | a) → a = b para ℕ₁
      -- - gcd₁_greatest: si c | a y c | b entonces c | gcd₁ a b
      sorry
    theorem gcd₁_divides_left (a b : ℕ₁) : gcd₁ a b ∣₁ a := by
      sorry -- TODO: Requires careful WF induction with proper term recursion

    theorem gcd₁_divides_right (a b : ℕ₁) : gcd₁ a b ∣₁ b := by
      sorry -- TODO: Requires careful WF induction with proper term recursion

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
  gcd₁_comm
  gcd₁_divides_left
  gcd₁_divides_right
  gcd₁_divides_both
)
