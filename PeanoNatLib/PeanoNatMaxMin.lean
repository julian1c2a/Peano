import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import Init.Data.Nat.Lemmas
import Init.Prelude

namespace Peano
    open Peano

    namespace MaxMin
        open Peano.MaxMin
        open Peano.Axioms
        open Peano.StrictOrder
        open Peano.Order

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def max (n m : ℕ₀) : ℕ₀ :=
        match n, m with
        | 𝟘 , m => m
        | n , 𝟘 => n
        | σ n' , σ m' =>
            if n' = m' then
                σ m'
            else if BLt n' m' then
                σ m'
            else
                σ n'

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def min (n m : ℕ₀) : ℕ₀ :=
        match n, m with
        | 𝟘 , _ => 𝟘
        | _ , 𝟘 => 𝟘
        | σ n' , σ m' =>
            if n' = m' then
                σ n'
            else if BLt n' m' then
                σ n'
            else
                σ m'

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def min_max (n m : ℕ₀) : ℕ₀×ℕ₀ :=
        match n, m with
        | 𝟘 , m => (𝟘 , m)
        | n , 𝟘 => (𝟘 , n)
        | σ n' , σ m' =>
            if n' = m' then
                (σ n' , σ n')
            else if BLt n' m' then
                (σ n' , σ m')
            else
                (σ m' , σ n')

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    def max_min (n m : ℕ₀) : ℕ₀×ℕ₀ :=
        match n, m with
        | 𝟘 , m => (m , 𝟘)
        | n , 𝟘 => (n , 𝟘)
        | σ n' , σ m' =>
            if n' = m' then
                (σ n' , σ n')
            else if BLt n' m' then
                (σ m' , σ n')
            else
                (σ n' , σ m')

theorem max_idem(n : ℕ₀) : max n n = n := by
  induction n with
  | zero =>
    simp [max]
  | succ n' n_ih =>
    simp [max]

theorem min_idem(n : ℕ₀) : min n n = n := by
  induction n with
  | zero =>
    simp [min]
  | succ n' n_ih =>
    simp [min]

theorem min_abs_0(n : ℕ₀) : min 𝟘 n = 𝟘 := by
  induction n with
  | zero =>
    simp [min]
  | succ n' n_ih =>
    simp [min]

theorem min_0_abs(n : ℕ₀) : min n 𝟘 = 𝟘 := by
  induction n with
  | zero =>
    rfl
  | succ n' n_ih =>
    simp [min]

theorem max_not_0(n : ℕ₀) : max 𝟘 n = n := by
  induction n with
  | zero =>
    simp [max]
  | succ n' n_ih =>
    simp [max]

theorem max_0_not(n : ℕ₀) : max n 𝟘 = n := by
  induction n with
  | zero =>
    simp [max]
  | succ n' n_ih =>
    simp [max]

theorem eq_max_min_then_eq(n m : ℕ₀) :
    (max n m = min n m) → (n = m)
        := by
    by_cases h_eq_or_neq : (n = m)
    · -- Caso n = m.
      intro h_hyp
      exact h_eq_or_neq
    · -- Caso n ≠ m.
      intro h_max_eq_min_hyp
      exfalso
      cases n with
      | zero =>
        cases m with
        | zero =>
            apply h_eq_or_neq
            rfl
        | succ m' =>
          simp [max, min] at h_max_eq_min_hyp
      | succ n' =>
          cases m with
        | zero =>
          simp [max, min] at h_max_eq_min_hyp
        | succ m' =>
          have h_neq_preds : n' ≠ m' := by
            intro h_preds_eq_contra
            apply h_eq_or_neq
            rw [h_preds_eq_contra]
          simp [max, min, if_neg h_neq_preds] at h_max_eq_min_hyp
          by_cases h_blt_eval : BLt n' m'
          · -- Caso BLt n' m' = true
            simp [h_blt_eval] at h_max_eq_min_hyp
            have h_preds_eq_from_hyp : m' = n' :=
              h_max_eq_min_hyp
            exact h_neq_preds (Eq.symm h_preds_eq_from_hyp)
          · -- Caso BLt n' m' = false
            simp [h_blt_eval] at h_max_eq_min_hyp
            have h_preds_eq_from_sigma_inj : n' = m' :=
              h_max_eq_min_hyp
            exact h_neq_preds h_preds_eq_from_sigma_inj

theorem eq_then_eq_max_min(n m : ℕ₀) :
    (n = m) → (max n m = min n m)
    := by
    intro h_eq_args
    rw [h_eq_args]
    rw [max_idem m]
    rw [min_idem m]

theorem eq_iff_eq_max_min(n m : ℕ₀) :
    n = m ↔ max n m = min n m
        := by
        constructor
        · -- Caso n = m → max n m = min n m
          intro h_eq_args
          exact eq_then_eq_max_min n m h_eq_args
        · -- Caso max n m = min n m → n = m
          intro h_hyp_max_eq_min
          exact eq_max_min_then_eq n m h_hyp_max_eq_min

theorem min_of_min_max(n m : ℕ₀) :
    min n m = min (max n m) (min n m)
      := by
        induction n with
        | zero =>
            induction m with
            | zero =>
                simp [min, max]
            | succ m' =>
                simp [min, max]
        | succ n' n_ih =>
            induction m with
            | zero =>
                simp [min, max]
            | succ m' =>
                by_cases h_eq_preds : (n' = m')
                · -- Caso: n' = m'
                  simp [min, max, h_eq_preds]
                · -- Caso: n' ≠ m'
                  by_cases h_blt_bool : (BLt n' m')
                  · -- Caso: BLt n' m' = true
                    have h_lt_n_prime_m_prime : Lt n' m' := by
                      rw [← BLt_iff_Lt]
                      exact h_blt_bool
                    have h_not_lt_m_prime_n_prime :
                        ¬ (Lt m' n')
                            := by
                              apply lt_asymm
                              exact h_lt_n_prime_m_prime
                    have h_blt_m_prime_n_prime_is_false :
                      BLt m' n' = false
                      := by
                         rw [← Bool.not_eq_true]
                         --   Meta: ¬ (BLt m' n' = true)
                         rw [BLt_iff_Lt]
                         --   Meta: ¬ (Lt m' n')
                         exact h_not_lt_m_prime_n_prime
                    simp [
                          min,
                          max,
                          h_eq_preds,
                          Ne.symm h_eq_preds,
                          h_blt_bool, h_blt_m_prime_n_prime_is_false
                    ]
                  · -- Caso: ¬ (BLt n' m')
                    simp [
                            min,
                            max,
                            h_eq_preds,
                            h_blt_bool
                    ]

theorem max_of_min_max(n m : ℕ₀) :
    max n m = max (min n m) (max n m)
      := by
        induction n with
        | zero =>
            induction m with
            | zero =>
                simp [min, max]
            | succ m' =>
                simp only [min, max]
        | succ n' n_ih =>
            induction m with
            | zero =>
                simp [min, max]
            | succ m' =>
                by_cases h_eq_preds : (n' = m')
                · -- Caso: n' = m'
                  simp [min, max, h_eq_preds]
                · -- Caso: n' ≠ m'
                  by_cases h_blt_bool : (BLt n' m')
                  · -- Caso: BLt n' m' = true
                    have h_lt_n_prime_m_prime : Lt n' m' := by
                      rw [← BLt_iff_Lt]
                      exact h_blt_bool
                    have h_not_lt_m_prime_n_prime :
                        ¬ (Lt m' n')
                            := by
                                apply lt_asymm
                                exact h_lt_n_prime_m_prime
                    have h_blt_m_prime_n_prime_is_false :
                      BLt m' n' = false
                      := by
                         rw [← Bool.not_eq_true]
                         rw [BLt_iff_Lt]
                         exact h_not_lt_m_prime_n_prime
                    simp [
                      min, max, h_eq_preds,
                      Ne.symm h_eq_preds,
                      h_blt_bool,
                      h_blt_m_prime_n_prime_is_false
                    ]
                  · -- Caso: ¬ (BLt n' m')
                    have h_blt_m_n_is_true :
                      BLt m' n' = true
                      := by
                      rcases trichotomy n' m' with
                        h_lt_n_m | h_eq_n_m | h_lt_m_n
                      ·
                        exfalso
                        apply h_blt_bool
                        rw [BLt_iff_Lt]
                        exact h_lt_n_m
                      · -- Caso n' = m', contradice h_eq_preds
                        exfalso
                        exact h_eq_preds h_eq_n_m
                      ·
                        rw [BLt_iff_Lt]
                        exact h_lt_m_n
                    simp [
                      min,
                      max,
                      h_eq_preds,
                      h_blt_bool,
                      h_blt_m_n_is_true
                    ]

theorem max_is_any(n m : ℕ₀) :
    max n m = n ∨ max n m = m
        := by
        cases n with
        | zero =>
          cases m with
          | zero => simp [max]
          | succ m' => simp [max]
        | succ n' =>
          cases m with
          | zero => simp [max]
          | succ m' =>
              dsimp [max]
              by_cases h_eq_cond : (n' = m')
              ·
                rw [if_pos h_eq_cond]
                left
                rw [h_eq_cond]
              ·
                rw [if_neg h_eq_cond]
                by_cases h_blt_cond : (BLt n' m')
                ·
                  rw [if_pos h_blt_cond]
                  right
                  rfl
                ·
                  rw [if_neg h_blt_cond]
                  left -- Revertido a `left`
                  rfl

theorem min_is_any(n m : ℕ₀) :
    min n m = n ∨ min n m = m
        := by
        cases n with
        | zero =>
          cases m with
          | zero => simp [min]
          | succ m' => simp [min]
        | succ n' =>
          cases m with
          | zero => simp [min]
          | succ m' =>
              dsimp [min]
              by_cases h_eq_cond : (n' = m')
              ·
                rw [if_pos h_eq_cond]
                left
                rfl
              ·
                rw [if_neg h_eq_cond]
                by_cases h_blt_cond : (BLt n' m')
                ·
                  rw [if_pos h_blt_cond]
                  left
                  rfl
                ·
                  rw [if_neg h_blt_cond]
                  right
                  rfl

theorem lt_then_min (a b : ℕ₀) :
    Lt a b → min a b = a
    := by
      intro h_lt
      cases a with
      | zero => -- a = 𝟘
        simp [min]
      | succ a' =>
        cases b with
        | zero =>
            exfalso;
            exact nlt_n_0 (σ a') h_lt
        | succ b' =>
          have h_lt_a'_b' : Lt a' b' := by
              simp [Lt] at h_lt; exact h_lt
          have h_a'_ne_b' : a' ≠ b' :=
              lt_then_neq a' b' h_lt_a'_b'
          simp [min, if_neg h_a'_ne_b']
          rw [(BLt_iff_Lt a' b').mpr h_lt_a'_b']
          simp

theorem min_then_le (a b : ℕ₀) :
    min a b = a → Le a b
    := by
      intro h_min_eq
      cases a with
      | zero => -- a = 𝟘
        simp only [min] at h_min_eq
        exact zero_le b
      | succ a' =>
        cases b with
        | zero =>
          exfalso
          simp only [min] at h_min_eq
          exact succ_neq_zero a' h_min_eq.symm
        | succ b' =>
          by_cases h_eq_preds : (a' = b')
          · -- Caso h_eq_preds : a' = b'
            simp only [min, h_eq_preds] at h_min_eq
            rw [h_eq_preds]
            exact Or.inr rfl -- Le X X es X = X, que es rfl.
          · -- Caso ¬ h_eq_preds : a' ≠ b'
            simp only [min, if_neg h_eq_preds] at h_min_eq
            have h_blt_a'_b' : BLt a' b' = true := by
              by_cases h_blt_eval : BLt a' b'
              ·
                exact h_blt_eval
              ·
                simp only [h_blt_eval] at h_min_eq
                have h_b'_eq_a' : b' = a' :=
                    AXIOM_succ_inj b' a' h_min_eq
                exact False.elim (h_eq_preds h_b'_eq_a'.symm)
            have h_lt_a'_b' : Lt a' b' :=
                (BLt_iff_Lt a' b').mp h_blt_a'_b'
            rw [Peano.Order.succ_le_succ_iff]
            exact lt_imp_le a' b' h_lt_a'_b'

theorem min_eq_of_gt {a b : ℕ₀} (h_gt : Lt b a) :
    min a b = b := by
      cases a with
      | zero =>
        exfalso
        exact nlt_n_0 b h_gt
      | succ a' =>
        cases b with
        | zero =>
          simp [min]
        | succ b' =>
          have h_lt_b'_a' : Lt b' a' := by
              simp [Lt] at h_gt; exact h_gt
          have h_b'_ne_a' : b' ≠ a' :=
              lt_then_neq b' a' h_lt_b'_a'
          have h_not_lt_a'_b' :
              ¬(Lt a' b') :=
                  lt_asymm b' a' h_lt_b'_a'
          have h_blt_a'_b'_is_false :
              BLt a' b' = false :=
                  (nBLt_iff_nLt a' b').mpr h_not_lt_a'_b'
          simp only [min, if_neg h_b'_ne_a'.symm]
          rw [h_blt_a'_b'_is_false]
          simp

theorem max_eq_of_lt {a b : ℕ₀} (h_lt : Lt a b) :
    max a b = b := by
      cases a with
      | zero => -- a = 𝟘
        simp [max]
      | succ a' => -- a = σ a'
        cases b with
        | zero => -- b = 𝟘
          exfalso
          exact nlt_n_0 (σ a') h_lt
        | succ b' => -- a = σ a', b = σ b'
          have h_lt_preds : Lt a' b' := by
              simp [Lt] at h_lt; exact h_lt
          have h_a'_ne_b' : a' ≠ b' :=
              lt_then_neq a' b' h_lt_preds
          simp [max, if_neg h_a'_ne_b']
          have h_blt_a'_b'_is_true :
              BLt a' b' = true
                  := (BLt_iff_Lt a' b').mpr h_lt_preds
          rw [h_blt_a'_b'_is_true]
          simp

theorem max_eq_of_gt {a b : ℕ₀} (h_gt : Lt b a) :
    max a b = a := by
      cases a with
      | zero =>
        exfalso
        exact nlt_n_0 b h_gt
      | succ a' =>
        cases b with
        | zero =>
          simp [max]
        | succ b' =>
          have h_lt_b'_a' :
              Lt b' a'
              := (lt_iff_lt_σ_σ b' a').mp h_gt
          have h_b'_ne_a' :
              b' ≠ a'
              := lt_then_neq b' a' h_lt_b'_a'
          have h_not_lt_a'_b' :
              ¬(Lt a' b')
              := lt_asymm b' a' h_lt_b'_a'
          have h_blt_a'_b'_is_false :
              BLt a' b' = false
              := (nBLt_iff_nLt a' b').mpr h_not_lt_a'_b'
          simp only [max, if_neg h_b'_ne_a'.symm]
          rw [h_blt_a'_b'_is_false]
          simp

theorem if_neq_then_max_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((max n m = n) ∧ ¬(max n m = m))
    ∨
    (¬(max n m = n) ∧ (max n m = m))
    := by
      constructor
      ·
        intro h_neq_nm
        by_cases h_eq_nm_case : n = m
        · -- Caso: n = m. Esto contradice h_neq_nm.
          exfalso
          exact h_neq_nm h_eq_nm_case
        ·
          have h_lt_or_gt := neq_then_lt_or_gt n m h_eq_nm_case
          cases h_lt_or_gt with
          | inl h_lt_nm => -- Caso: Lt n m (n < m)
            apply Or.inr
            constructor
            · -- Subobjetivo 1: ¬(max n m = n)
              intro h_max_eq_n_contra
              have h_max_eq_m_true :
                  max n m = m
                      := max_eq_of_lt h_lt_nm
              exact h_eq_nm_case (
                h_max_eq_n_contra.symm.trans h_max_eq_m_true
              )
            · -- Subobjetivo 2: max n m = m
              exact max_eq_of_lt h_lt_nm
          | inr h_lt_mn => -- Caso: Lt m n (m < n)
            apply Or.inl
            constructor
            · -- Subobjetivo 1: max n m = n
              exact max_eq_of_gt h_lt_mn
            · -- Subobjetivo 2: ¬(max n m = m)
              intro h_max_eq_m_contra
              have h_max_eq_n_true :
                  max n m = n
                      := max_eq_of_gt h_lt_mn
              exact h_eq_nm_case (
                h_max_eq_m_contra.symm.trans
                h_max_eq_n_true
              ).symm
      ·
        intro h_disj
        intro h_eq_nm_contra -- h_eq_nm_contra : n = m
        cases h_disj with
        | inl h_and1 =>
          have h_not_max_eq_m : ¬(max n m = m) := h_and1.right
          have h_max_n_m_eq_m_true :
              max n m = m
                  :=
                      by rw [h_eq_nm_contra]
                         exact max_idem m
          exact h_not_max_eq_m h_max_n_m_eq_m_true
        | inr h_and2 =>
          have h_not_max_eq_n :
              ¬(max n m = n)
                  := h_and2.left
          have h_max_n_m_eq_n_true :
              max n m = n
                  := by
                      rw [h_eq_nm_contra]
                      exact max_idem m
          exact h_not_max_eq_n h_max_n_m_eq_n_true

theorem if_neq_then_min_xor(n m : ℕ₀) :
    n ≠ m ↔
    ((min n m = n) ∧ ¬(min n m = m))
    ∨
    (¬(min n m = n) ∧ (min n m = m))
    := by
      constructor
      ·
        intro h_neq_nm
        by_cases h_eq_nm_case : n = m
        · -- Caso: n = m. Esto contradice h_neq_nm.
          exfalso
          exact h_neq_nm h_eq_nm_case
        · -- Caso: n ≠ m
          have h_lt_or_gt := neq_then_lt_or_gt n m h_eq_nm_case
          cases h_lt_or_gt with
          | inl h_lt_nm => -- Caso: Lt n m (n < m)
            apply Or.inl
            constructor
            · -- Subobjetivo 1: min n m = n
              exact lt_then_min n m h_lt_nm
            · -- Subobjetivo 2: ¬(min n m = m)
              intro h_min_eq_m_contra
              have h_min_eq_n_true :
                  min n m = n
                      := lt_then_min n m h_lt_nm
              exact h_eq_nm_case (
                (
                  h_min_eq_m_contra.symm.trans
                      h_min_eq_n_true
                ).symm
              )
          | inr h_lt_mn => -- Caso: Lt m n (m < n)
            apply Or.inr
            constructor
            · -- Subobjetivo 1: ¬(min n m = n)
              intro h_min_eq_n_contra
              have h_min_eq_m_true :
                  min n m = m
                      := min_eq_of_gt h_lt_mn
              exact h_eq_nm_case (
                    h_min_eq_n_contra.symm.trans
                    h_min_eq_m_true
              )
            · -- Subobjetivo 2: min n m = m
              exact min_eq_of_gt h_lt_mn
      ·
        intro h_disj
        intro h_eq_nm_contra -- h_eq_nm_contra : n = m
        cases h_disj with
        | inl h_and1 =>
          have h_not_min_eq_m :
              ¬(min n m = m) := h_and1.right
          have h_min_n_m_eq_m_true :
              min n m = m
                  := by
                      rw [h_eq_nm_contra];
                      exact min_idem m
          exact h_not_min_eq_m h_min_n_m_eq_m_true
        | inr h_and2 =>
          have h_not_min_eq_n :
              ¬(min n m = n) := h_and2.left
          have h_min_n_m_eq_n_true :
              min n m = n :=
                  by
                      rw [h_eq_nm_contra]
                      exact min_idem m
          exact h_not_min_eq_n h_min_n_m_eq_n_true

theorem neq_args_then_lt_min_max(n m : ℕ₀) :
    n ≠ m ↔ Lt (min n m) (max n m)
    := by
      constructor
      · -- Dirección →: n ≠ m → Lt (min n m) (max n m)
        intro h_neq_nm
        have h_lt_or_gt := neq_then_lt_or_gt n m h_neq_nm
        cases h_lt_or_gt with
        | inl h_lt_nm => -- Caso: Lt n m (n < m)
          have h_min_eq_n :
              min n m = n := lt_then_min n m h_lt_nm
          have h_max_eq_m :
              max n m = m := max_eq_of_lt h_lt_nm
          rw [h_min_eq_n, h_max_eq_m]
          exact h_lt_nm
        | inr h_lt_mn => -- Caso: Lt m n (m < n)
          have h_min_eq_m :
              min n m = m := min_eq_of_gt h_lt_mn
          have h_max_eq_n :
              max n m = n := max_eq_of_gt h_lt_mn
          rw [h_min_eq_m, h_max_eq_n]
          exact h_lt_mn
      · -- Dirección ←: Lt (min n m) (max n m) → n ≠ m
        intro h_lt_min_max
        intro h_eq_nm
        have h_min_eq_n :
            min n m = n :=
                by
                    rw [h_eq_nm]
                    exact min_idem m
        have h_max_eq_n :
            max n m = n :=
                by
                    rw [h_eq_nm]
                    exact max_idem m
        rw [h_min_eq_n, h_max_eq_n] at h_lt_min_max
        exact lt_irrefl n h_lt_min_max

theorem max_comm(n m : ℕ₀) :
    max n m = max m n
        := by
          induction n with
          | zero =>
              induction m with
              | zero =>
                  rfl
              | succ m' =>
                  simp [max]
          | succ n' ih_n =>
              induction m with
              | zero =>
                  simp [max]
              | succ m' =>
                  simp only [max]
                  by_cases h_eq_preds : (n' = m')
                  ·
                    simp [h_eq_preds]
                  ·
                    rw [
                      if_neg h_eq_preds,
                      if_neg (Ne.symm h_eq_preds)
                    ]
                    by_cases h_blt_n_m_is_true :
                        (BLt n' m' = true)
                    ·
                      rw [if_pos h_blt_n_m_is_true]
                      have h_lt_n_m :
                          Lt n' m'
                              := (BLt_iff_Lt n' m').mp
                                 h_blt_n_m_is_true
                      have h_not_lt_m_n :
                          ¬ (Lt m' n')
                              := lt_asymm n' m' h_lt_n_m
                      have h_blt_m_n_is_false :
                          BLt m' n' = false
                              := (nBLt_iff_nLt m' n').mpr
                                  h_not_lt_m_n
                      rw [h_blt_m_n_is_false]
                      simp -- Evalúa el if
                    ·
                      rw [if_neg h_blt_n_m_is_true]
                      have h_not_lt_n_m : ¬ (Lt n' m') := by
                        intro h_lt_n_m_contra
                        apply h_blt_n_m_is_true
                        rw [BLt_iff_Lt]
                        exact h_lt_n_m_contra
                      have h_lt_m_n : Lt m' n' := by
                        cases trichotomy n' m' with
                        | inl h_lt_n_m_contra =>
                          exact False.elim (h_not_lt_n_m h_lt_n_m_contra)
                        | inr h_eq_or_gt =>
                          cases h_eq_or_gt with
                          | inl h_eq_n_m_tri =>
                            exact False.elim (
                              h_eq_preds h_eq_n_m_tri
                            )
                          | inr h_lt_m_n_tri =>
                            exact h_lt_m_n_tri
                      have h_blt_m_n_is_true :
                          BLt m' n' = true
                              :=
                              (
                                BLt_iff_Lt m' n'
                              ).mpr h_lt_m_n
                      rw [if_pos h_blt_m_n_is_true]


theorem min_comm(n m : ℕ₀) :
    min n m = min m n
        := by
          induction n with
          | zero =>
              induction m with
              | zero =>
                  simp [min]
              | succ m' =>
                  simp [min]
          | succ n' ih_n =>
              induction m with
              | zero =>
                  simp [min]
              | succ m' =>
                  simp only [min]
                  by_cases h_eq_preds : (n' = m')
                  · -- Case: n' = m'
                    simp [h_eq_preds]
                  · -- Case: n' ≠ m'
                    rw [
                          if_neg h_eq_preds,
                          if_neg (Ne.symm h_eq_preds)
                    ]
                    by_cases h_blt_n_m_is_true :
                        (BLt n' m' = true)
                    · -- Subcase: BLt n' m' = true (i.e., Lt n' m')
                      rw [if_pos h_blt_n_m_is_true]
                      have h_lt_n_m : Lt n' m'
                          := (BLt_iff_Lt n' m').mp h_blt_n_m_is_true
                      have h_not_lt_m_n : ¬ (Lt m' n')
                          := lt_asymm n' m' h_lt_n_m
                      have h_blt_m_n_is_false : BLt m' n' = false
                          := (nBLt_iff_nLt m' n').mpr h_not_lt_m_n
                      rw [h_blt_m_n_is_false]
                      simp
                    ·
                      rw [if_neg h_blt_n_m_is_true]
                      have h_not_lt_n_m : ¬(Lt n' m')
                        :=
                          (nBLt_iff_nLt n' m').mp
                          (eq_false_of_ne_true h_blt_n_m_is_true)
                      have h_lt_m_n : Lt m' n' := by
                        cases trichotomy n' m' with
                        | inl h_lt_n_m_contra => -- Lt n' m'
                          exact False.elim (h_not_lt_n_m h_lt_n_m_contra)
                        | inr h_eq_or_gt =>
                          cases h_eq_or_gt with
                          | inl h_eq_contra => -- n' = m'
                            exact False.elim (h_eq_preds h_eq_contra)
                          | inr h_gt_n_m =>
                            exact h_gt_n_m
                      have h_blt_m_n_is_true :
                          BLt m' n' = true
                              := (BLt_iff_Lt m' n').mpr h_lt_m_n
                      rw [h_blt_m_n_is_true]
                      simp

theorem le_then_max_eq_right (n m : ℕ₀) (h_le : Le n m) :
  max n m = m
  := by
    cases h_le with  -- Le n m es (Lt n m) ∨ (n = m)
    | inl h_lt =>
      exact max_eq_of_lt h_lt --
    | inr h_eq =>
      rw [h_eq];
      exact max_idem m

theorem le_then_max_eq_left (n m : ℕ₀) (h_le : Le m n) :
  max n m = n
  := by
    rw [max_comm n m] -- El objetivo es max m n = n
    exact le_then_max_eq_right m n h_le

theorem Lt_of_not_le {n m : ℕ₀} (h_not_le : ¬ Le n m) :
  Lt m n
  := by
  rcases trichotomy n m with h_lt_n_m | h_eq_n_m | h_lt_m_n
  ·
    exfalso
    apply h_not_le
    exact Or.inl h_lt_n_m
  ·
    exfalso
    apply h_not_le
    exact Or.inr h_eq_n_m
  ·
    exact h_lt_m_n

theorem le_max_left (n m : ℕ₀) :
  Le n (max n m)
  := by
  by_cases h_le_n_m : (Le n m)
  ·
    rw [le_then_max_eq_right n m h_le_n_m]
    exact h_le_n_m
  ·
    have h_lt_m_n : Lt m n := Lt_of_not_le h_le_n_m
    rw [le_then_max_eq_left n m (Or.inl h_lt_m_n)]
    exact le_refl n

theorem le_max_right (n m : ℕ₀) :
  Le m (max n m)
  := by
    rw [max_comm n m]
    exact le_max_left m n

theorem max_le (n m k : ℕ₀)
    (h_n_le_k : Le n k) (h_m_le_k : Le m k) :
    Le (max n m) k
    := by
      obtain h_max_eq_n | h_max_eq_m := max_is_any n m
      · -- Caso: max n m = n
        rw [h_max_eq_n] -- El objetivo es Le n k
        exact h_n_le_k
      · -- Caso: max n m = m
        rw [h_max_eq_m] -- El objetivo es Le m k
        exact h_m_le_k

theorem max_assoc(n m k : ℕ₀) :
    max (max n m) k = max n (max m k)
        := by
          let LHS := max (max n m) k
          let RHS := max n (max m k)
          apply le_antisymm
          · -- Parte 1: Probar Le LHS RHS
            apply max_le (max n m) k RHS
            · -- Subobjetivo 1.1: Le (max n m) RHS
              apply max_le n m RHS
              · -- Subobjetivo 1.1.1: Le n RHS
                exact le_max_left n (max m k)
              · -- Subobjetivo 1.1.2: Le m RHS
                have h_m_le_max_mk :
                    Le m (max m k)
                        := le_max_left m k
                have h_max_mk_le_RHS :
                    Le (max m k) RHS
                        := le_max_right n (max m k)
                exact le_trans m (max m k) RHS
                      h_m_le_max_mk h_max_mk_le_RHS
            · -- Subobjetivo 1.2: Le k RHS
              have h_k_le_max_mk :
                  Le k (max m k)
                      := le_max_right m k
              have h_max_mk_le_RHS :
                  Le (max m k) RHS
                      := le_max_right n (max m k)
              exact le_trans k (max m k) RHS
                    h_k_le_max_mk h_max_mk_le_RHS
          ·
            apply max_le n (max m k) LHS
            · -- Subobjetivo 2.1: Le n LHS
              have h_n_le_max_nm :
                  Le n (max n m) := le_max_left n m
              have h_max_nm_le_LHS :
                  Le (max n m) LHS
                      := le_max_left (max n m) k
              exact le_trans n (max n m)
                    LHS h_n_le_max_nm h_max_nm_le_LHS
            · -- Subobjetivo 2.2: Le (max m k) LHS
              apply max_le m k LHS
              · -- Subobjetivo 2.2.1: Le m LHS
                have h_m_le_max_nm :
                    Le m (max n m)
                        := le_max_right n m
                have h_max_nm_le_LHS :
                    Le (max n m) LHS
                        := le_max_left (max n m) k
                exact
                    le_trans m (max n m) LHS
                        h_m_le_max_nm h_max_nm_le_LHS
              · -- Subobjetivo 2.2.2: Le k LHS
                exact le_max_right (max n m) k

theorem le_then_min_eq_left (n m : ℕ₀) (h_le : Le n m) :
  min n m = n
  := by
  cases h_le with -- Le n m es (Lt n m) ∨ (n = m)
  | inl h_lt =>
    exact lt_then_min n m h_lt --
  | inr h_eq =>
    rw [h_eq];
    exact min_idem m

theorem le_then_min_eq_right (n m : ℕ₀) (h_le : Le m n) :
  min n m = m
  := by
    rw [min_comm n m] -- El objetivo es min m n = m
    exact le_then_min_eq_left m n h_le -- Usamos el lemma anterior

theorem min_le_left (n m : ℕ₀) :
  Le (min n m) n
  := by
  by_cases h_le_n_m : (Le n m)
  ·
    rw [le_then_min_eq_left n m h_le_n_m]
    exact le_refl n
  · -- Caso: ¬ (Le n m)
    have h_lt_m_n : Lt m n
      := Lt_of_not_le h_le_n_m -- Entonces Lt m n
    rw [min_eq_of_gt h_lt_m_n] -- Entonces min n m = m
    exact Or.inl h_lt_m_n

theorem min_le_right (n m : ℕ₀) :
  Le (min n m) m
  := by
    rw [min_comm n m]
    exact min_le_left m n

theorem le_min (k n m : ℕ₀) (h_k_le_n : Le k n) (h_k_le_m : Le k m) : Le k (min n m) := by
  obtain h_min_eq_n | h_min_eq_m := min_is_any n m
  · -- Caso: min n m = n
    rw [h_min_eq_n] -- El objetivo es Le k n
    exact h_k_le_n
  · -- Caso: min n m = m
    rw [h_min_eq_m] -- El objetivo es Le k m
    exact h_k_le_m

theorem min_assoc(n m k : ℕ₀) :
    min (min n m) k = min n (min m k)
        := by
          let LHS := min (min n m) k
          let RHS := min n (min m k)
          apply le_antisymm
          ·
            apply le_min LHS n (min m k)
            ·
              exact le_trans (min (min n m) k) (min n m) n (min_le_left (min n m) k) (min_le_left n m)
            ·
              apply le_min LHS m k
              ·
                exact le_trans (min (min n m) k) (min n m) m (min_le_left (min n m) k) (min_le_right n m)
              ·
                exact min_le_right (min n m) k
          ·
            apply le_min RHS (min n m) k
            ·
              apply le_min RHS n m
              ·
                exact min_le_left n (min m k)
              ·
                exact le_trans
                  (min n (min m k)) (min m k) m
                  (min_le_right n (min m k))
                  (min_le_left m k)
            ·
              exact le_trans (min n (min m k)) (min m k) k (min_le_right n (min m k)) (min_le_right m k)

theorem nexists_max_abs:
    ∀ (k: ℕ₀), ∃ (n: ℕ₀) , max n k = n ∧ n ≠ k
        := by
          intro k
          let n_val : ℕ₀ := σ k
          exists n_val
          have h_max_eq_nval : max n_val k = n_val
            := by
              apply max_eq_of_gt -- Necesita Lt k (σ k)
              exact lt_self_σ_self k -- Provee Lt k (σ k)
          have h_neq_nval_k : n_val ≠ k := by
            intro h_eq_val_k -- Asumimos σ k = k
            exact (neq_succ k) (Eq.symm h_eq_val_k)
          exact ⟨h_max_eq_nval, h_neq_nval_k⟩

  theorem min_eq_right {a b : ℕ₀} (h : b ≤ a) :
      min a b = b
    := by
      cases a with
      | zero =>
        cases b with
        | zero => simp [min]
        | succ b' =>
          -- Caso imposible: σ b' ≤ 𝟘
          exfalso
          cases h with
          | inl h_lt => exfalso; exact nlt_n_0 (σ b') h_lt
          | inr h_eq => exact succ_neq_zero b' h_eq
      | succ a' =>
        cases b with
        | zero => simp [min]
        | succ b' =>
          have h_b'_le_a' : Le b' a' := by
            exact succ_le_succ_then h
          by_cases h_eq : b' = a'
          · -- Caso b' = a'
            simp [min, h_eq]
          · -- Caso b' ≠ a'
            simp [min, if_neg h_eq]
            cases h_b'_le_a' with
            | inl h_lt =>
              have h_blt_true : BLt b' a' = true := by
                rw [BLt_iff_Lt]
                exact h_lt
              -- Necesitamos mostrar que BLt a' b' = false
              have h_not_lt_a'_b' : ¬(Lt a' b') := by
                exact lt_asymm b' a' h_lt
              have h_blt_a'_b'_false : BLt a' b' = false := by
                rw [← Bool.not_eq_true, BLt_iff_Lt]
                exact h_not_lt_a'_b'
              -- Ahora simplificamos la expresión condicional
              simp only [if_neg h_eq, h_blt_a'_b'_false]
              simp
            | inr h_eq_contra =>
              exact False.elim (h_eq h_eq_contra)

  theorem min_eq_left {a b : ℕ₀} (h : a ≤ b) :
      min a b = a
    := by
      cases a with
      | zero =>
        cases b with
        | zero =>
          simp [min]
        | succ b' =>
          simp [min]
      | succ a' =>
        cases b with
        | zero =>
          -- Caso imposible: σ a' ≤ 𝟘
          cases h with
          | inl h_lt =>
            exact False.elim (nlt_n_0 (σ a') h_lt)
          | inr h_eq =>
            exact False.elim (succ_neq_zero a' h_eq)
        | succ b' =>
          have h_a'_le_b' : Le a' b' := by
            exact succ_le_succ_then h
          by_cases h_eq : a' = b'
          · -- Caso a' = b'
            simp [min, h_eq]
          · -- Caso a' ≠ b'
            simp [min, if_neg h_eq]
            cases h_a'_le_b' with
            | inl h_lt =>
              have h_blt_true : BLt a' b' = true := by
                rw [BLt_iff_Lt]
                exact h_lt
              rw [h_blt_true]
              simp
            | inr h_eq_contra =>
              exact False.elim (h_eq h_eq_contra)

  theorem max_eq_right {a b : ℕ₀} (h : a ≤ b) :
      max a b = b
    := by
      cases a with
      | zero =>
        cases b with
        | zero =>
          simp [max]
        | succ b' =>
          simp [max]
      | succ a' =>
        cases b with
        | zero =>
          -- Caso imposible: σ a' ≤ 𝟘
          cases h with
          | inl h_lt =>
            exact False.elim (nlt_n_0 (σ a') h_lt)
          | inr h_eq =>
            exact False.elim (succ_neq_zero a' h_eq)
        | succ b' =>
          have h_a'_le_b' : Le a' b' := by
            exact succ_le_succ_then h
          by_cases h_eq : a' = b'
          · -- Caso a' = b'
            simp [max, h_eq]
          · -- Caso a' ≠ b'
            simp [max, if_neg h_eq]
            cases h_a'_le_b' with
            | inl h_lt =>
              have h_blt_true : BLt a' b' = true := by
                rw [BLt_iff_Lt]
                exact h_lt
              rw [h_blt_true]
              simp
            | inr h_eq_contra =>
              exact False.elim (h_eq h_eq_contra)

theorem max_eq_left {a b : ℕ₀} (h : b ≤ a) :
    max a b = a
  := by
    cases a with
    | zero =>
      cases b with
      | zero =>
        simp [max]
      | succ b' =>
        -- Caso imposible: σ b' ≤ 𝟘
        cases h with
        | inl h_lt =>
          exact False.elim (nlt_n_0 (σ b') h_lt)
        | inr h_eq =>
          exact False.elim (succ_neq_zero b' h_eq)
    | succ a' =>
      cases b with
      | zero =>
        simp [max]
      | succ b' =>
        have h_b'_le_a' : Le b' a' := by
          exact succ_le_succ_then h
        by_cases h_eq : a' = b'
        · -- Caso a' = b'
          simp [max, h_eq]
        · -- Caso a' ≠ b'
          simp [max, if_neg h_eq]
          cases h_b'_le_a' with
          | inl h_lt =>
            -- h_lt : Lt b' a', necesitamos mostrar que BLt a' b' = false
            have h_not_lt_a'_b' : ¬(Lt a' b') := by
              exact lt_asymm b' a' h_lt
            have h_blt_a'_b'_false : BLt a' b' = false := by
              rw [← Bool.not_eq_true, BLt_iff_Lt]
              exact h_not_lt_a'_b'
            rw [h_blt_a'_b'_false]
            simp
          | inr h_eq_contra =>
            exact False.elim (h_eq h_eq_contra.symm)

theorem max_distrib_min(n m k : ℕ₀) :
    max n (min m k) = min (max n m) (max n k)
    := by
  cases le_total m k with
  | inl h_m_le_k => -- Caso 1: Le m k (m ≤ k)
    have min_mk_eq_m : min m k = m
        := le_then_min_eq_left m k h_m_le_k
    rw [min_mk_eq_m]
    have h_le_max_nm_max_nk : Le (max n m) (max n k)
      := by
      apply max_le
      · -- Subobjetivo 1: Le n (max n k)
        exact le_max_left n k
      · -- Subobjetivo 2: Le m (max n k)
        exact le_trans m k (max n k) h_m_le_k (le_max_right n k)
    rw [le_then_min_eq_left (max n m) (max n k) h_le_max_nm_max_nk]
  | inr h_k_le_m => -- Caso 2: Le k m (k ≤ m)
    have min_mk_eq_k : min m k = k
        := le_then_min_eq_right m k h_k_le_m
    rw [min_mk_eq_k] -- LHS se convierte en: max n k
    have h_le_max_nk_max_nm : Le (max n k) (max n m)
      := by
      apply max_le
      · -- Subobjetivo 1: Le n (max n m)
        exact le_max_left n m
      · -- Subobjetivo 2: Le k (max n m)
        exact le_trans k m (max n m) h_k_le_m (le_max_right n m)
    rw [min_eq_right h_le_max_nk_max_nm]

theorem min_distrib_max(n m k : ℕ₀) :
    min n (max m k) = max (min n m) (min n k)
    := by
  cases (le_total m k) with
  | inl h_m_le_k => -- Caso: m ≤ k
    have max_mk_eq_k : max m k = k
        := le_then_max_eq_right m k h_m_le_k
    rw [max_mk_eq_k] -- LHS se convierte en min n k
    by_cases h_n_le_m : Le n m
    · -- Si n ≤ m
      have h_min_nm_eq_n : min n m = n
          := le_then_min_eq_left n m h_n_le_m
      have h_n_le_k : Le n k
          := Order.le_trans n m k h_n_le_m h_m_le_k
      have h_min_nk_eq_n : min n k = n
          := le_then_min_eq_left n k h_n_le_k
      rw [h_min_nm_eq_n, h_min_nk_eq_n]
      rw [max_idem n]
    · -- Si ¬(n ≤ m), entonces m < n
      have h_m_lt_n : Lt m n
          := Lt_of_not_le h_n_le_m
      have h_min_nm_eq_m : min n m = m
          := min_eq_of_gt h_m_lt_n
      by_cases h_n_le_k : Le n k
      · -- Si n ≤ k, entonces min n k = n
        have h_min_nk_eq_n : min n k = n
            := le_then_min_eq_left n k h_n_le_k
        rw [h_min_nm_eq_m, h_min_nk_eq_n]
        have h_m_le_n : Le m n
            := lt_imp_le m n h_m_lt_n
        rw [le_then_max_eq_right m n h_m_le_n]
      · -- Si ¬(n ≤ k), entonces k < n y min n k = k
        have h_k_lt_n : Lt k n
            := Lt_of_not_le h_n_le_k
        have h_min_nk_eq_k : min n k = k
            := min_eq_of_gt h_k_lt_n
        rw [h_min_nm_eq_m, h_min_nk_eq_k]
        -- Goal: k = max m k
        rw [le_then_max_eq_right m k h_m_le_k]
  | inr h_k_le_m => -- Caso 2: Le k m (k ≤ m)
    have max_mk_eq_m : max m k = m
        := le_then_max_eq_left m k h_k_le_m
    rw [max_mk_eq_m] -- LHS se convierte en: min n m
    by_cases h_n_le_k : Le n k
    · -- Si n ≤ k
      have h_n_le_m : Le n m
          := le_trans n k m h_n_le_k h_k_le_m
      have h_min_nm_eq_n : min n m = n
          := le_then_min_eq_left n m h_n_le_m
      have h_min_nk_eq_n : min n k = n
          := le_then_min_eq_left n k h_n_le_k
      rw [h_min_nm_eq_n, h_min_nk_eq_n]
      rw [max_idem n]
    · -- Si ¬(n ≤ k), entonces k < n
      have h_k_lt_n : Lt k n
          := Lt_of_not_le h_n_le_k
      have h_min_nk_eq_k : min n k = k
          := min_eq_of_gt h_k_lt_n
      by_cases h_n_le_m : Le n m
      · -- Si n ≤ m, entonces min n m = n
        have h_min_nm_eq_n : min n m = n
            := le_then_min_eq_left n m h_n_le_m
        rw [h_min_nm_eq_n, h_min_nk_eq_k]
        have h_k_le_n : Le k n
            := lt_imp_le k n h_k_lt_n
        -- Goal: n = max n k
        -- Tenemos h_k_le_n : Le k n, así que max n k = n
        rw [le_then_max_eq_left n k h_k_le_n]
      · -- Si ¬(n ≤ m), entonces m < n y min n m = m
        have h_m_lt_n : Lt m n
            := Lt_of_not_le h_n_le_m
        have h_min_nm_eq_m : min n m = m
            := min_eq_of_gt h_m_lt_n
        rw [h_min_nm_eq_m, h_min_nk_eq_k]
        -- Goal: m = max m k, ya que k ≤ m
        rw [le_then_max_eq_left m k h_k_le_m]

theorem isomorph_Λ_max(n m : Nat) :
    max (Λ n) (Λ m) = Λ (Nat.max n m)
        := by
  rcases Nat.le_total n m with h_n_le_m | h_m_le_n
  ·
    have h_nat_max_simpl :
        Nat.max n m = m
            := by
            exact Nat.max_eq_right h_n_le_m
    rw [h_nat_max_simpl]
    rcases Nat.eq_or_lt_of_le h_n_le_m with
        h_n_eq_m | h_n_lt_m
    · -- Subcaso 1.1: n = m
      rw [h_n_eq_m] at *
      rw [max_idem (Λ m)]
    · -- Subcaso 1.2: n < m
      have h_Λn_lt_Λm :
          Lt (Λ n) (Λ m) :=
          (StrictOrder.isomorph_Λ_lt n m).mp h_n_lt_m
      rw [max_eq_of_lt h_Λn_lt_Λm]
  · -- Caso 2: m ≤ n (para Nat)
    have h_nat_max_simpl : Nat.max n m = n := by
      exact Nat.max_eq_left h_m_le_n
    rw [h_nat_max_simpl]
    rcases Nat.eq_or_lt_of_le h_m_le_n with
        h_m_eq_n | h_m_lt_n
    · -- Subcaso 2.1: m = n
      rw [h_m_eq_n] at *
      rw [max_idem (Λ n)]
    · -- Subcaso 2.2: m < n
      have h_Λm_lt_Λn :
          Lt (Λ m) (Λ n) :=
              (
                  isomorph_Λ_lt m n
              ).mp h_m_lt_n
      rw [max_eq_of_gt h_Λm_lt_Λn]

theorem isomorph_Λ_min(n m : Nat) :
    min (Λ n) (Λ m) = Λ (Nat.min n m)
        := by
  rcases Nat.le_total n m with h_n_le_m | h_m_le_n
  · -- Caso 1: n ≤ m
    have h_nat_min_simpl :
        Nat.min n m = n := by
            exact Nat.min_eq_left h_n_le_m
    rw [h_nat_min_simpl]
    rcases Nat.eq_or_lt_of_le h_n_le_m with
        h_n_eq_m | h_n_lt_m
    · -- Subcaso 1.1: n = m
      rw [h_n_eq_m] at *
      rw [min_idem (Λ m)]
    · -- Subcaso 1.2: n < m
      have h_Λn_lt_Λm :
          Lt (Λ n) (Λ m) :=
              (
                  StrictOrder.isomorph_Λ_lt n m
              ).mp h_n_lt_m
      rw [lt_then_min (Λ n) (Λ m) h_Λn_lt_Λm]
  · -- Caso 2: m ≤ n (en Nat)
    have h_nat_min_simpl : Nat.min n m = m := by
      exact Nat.min_eq_right h_m_le_n
    rw [h_nat_min_simpl]
    rcases Nat.eq_or_lt_of_le h_m_le_n with
        h_m_eq_n | h_m_lt_n
    · -- Subcaso 2.1: m = n
      rw [h_m_eq_n] at *
      rw [min_idem (Λ n)]
    · -- Subcaso 2.2: m < n
      have h_Λm_lt_Λn :
          Lt (Λ m) (Λ n) :=
              (
                  StrictOrder.isomorph_Λ_lt m n
              ).mp h_m_lt_n
      rw [min_eq_of_gt h_Λm_lt_Λn]

theorem isomorph_Ψ_max(n m : ℕ₀) :
    Nat.max (Ψ n) (Ψ m) = Ψ (max n m) := by
  rcases le_total n m with h_le_nm | h_le_mn
  · -- Caso 1: Le n m (para ℕ₀)
    have h_pea_max_simpl : max n m = m := by
      exact le_then_max_eq_right n m h_le_nm
    rw [h_pea_max_simpl]
    have h_nat_le_psi_n_psi_m : Ψ n ≤ Ψ m := by
      exact (isomorph_Ψ_le n m).mpr h_le_nm
    rcases Nat.eq_or_lt_of_le h_nat_le_psi_n_psi_m with h_psi_n_eq_psi_m | h_psi_n_lt_psi_m
    · -- Subcaso 1.1: Ψ n = Ψ m
      rw [h_psi_n_eq_psi_m]
      apply Nat.max_self
    · -- Subcaso 1.2: Ψ n < Ψ m
      have h_le_of_lt :
          Ψ n ≤ Ψ m :=
              Nat.le_of_lt h_psi_n_lt_psi_m
      exact Nat.max_eq_right h_le_of_lt
  · -- Caso 2: Le m n (para ℕ₀)
    have h_pea_max_simpl : max n m = n := by
      exact le_then_max_eq_left n m h_le_mn
    rw [h_pea_max_simpl]
    have h_nat_le_psi_m_psi_n : Ψ m ≤ Ψ n := by
      exact (isomorph_Ψ_le m n).mpr h_le_mn
    rcases Nat.eq_or_lt_of_le h_nat_le_psi_m_psi_n with
        h_psi_m_eq_psi_n | h_psi_m_lt_psi_n
    · -- Subcaso 2.1: Ψ m = Ψ n
      rw [h_psi_m_eq_psi_n]
      apply Nat.max_self
    · -- Subcaso 2.2: Ψ m < Ψ n
      have h_le_of_lt :
          Ψ m ≤ Ψ n :=
              Nat.le_of_lt h_psi_m_lt_psi_n
      exact Nat.max_eq_left h_le_of_lt

theorem isomorph_Ψ_min(n m : ℕ₀) :
    Nat.min (Ψ n) (Ψ m) = Ψ (min n m) := by
  rcases le_total n m with h_le_nm | h_le_mn
  · -- Caso 1: Le n m (para ℕ₀)
    have h_pea_min_simpl : min n m = n := by
      exact le_then_min_eq_left n m h_le_nm
    rw [h_pea_min_simpl]
    have h_nat_le_psi_n_psi_m : Ψ n ≤ Ψ m := by
      exact (isomorph_Ψ_le n m).mpr h_le_nm
    rcases Nat.eq_or_lt_of_le h_nat_le_psi_n_psi_m with
        h_psi_n_eq_psi_m | h_psi_n_lt_psi_m
    · -- Subcaso 1.1: Ψ n = Ψ m
      rw [h_psi_n_eq_psi_m]
      apply Nat.min_self
    · -- Subcaso 1.2: Ψ n < Ψ m
      have h_le_of_lt :
          Ψ n ≤ Ψ m :=
              Nat.le_of_lt h_psi_n_lt_psi_m
      exact Nat.min_eq_left h_le_of_lt
  · -- Caso 2: Le m n (para ℕ₀)
    have h_pea_min_simpl : min n m = m := by
      exact le_then_min_eq_right n m h_le_mn
    rw [h_pea_min_simpl]
    have h_nat_le_psi_m_psi_n : Ψ m ≤ Ψ n := by
      exact (isomorph_Ψ_le m n).mpr h_le_mn
    rcases Nat.eq_or_lt_of_le h_nat_le_psi_m_psi_n with
        h_psi_m_eq_psi_n | h_psi_m_lt_psi_n
    · -- Subcaso 2.1: Ψ m = Ψ n
      rw [h_psi_m_eq_psi_n]
      apply Nat.min_self
    · -- Subcaso 2.2: Ψ m < Ψ n
      have h_le_of_lt :
          Ψ m ≤ Ψ n :=
              Nat.le_of_lt h_psi_m_lt_psi_n
      exact Nat.min_eq_right h_le_of_lt

    end MaxMin

end Peano

export Peano.MaxMin (
  max
  min
  min_max
  max_min
  max_idem
  min_idem
  min_abs_0
  min_0_abs
  max_not_0
  max_0_not
  eq_max_min_then_eq
  eq_then_eq_max_min
  eq_iff_eq_max_min
  min_of_min_max
  max_of_min_max
  max_is_any
  min_is_any
  lt_then_min
  min_then_le
  min_eq_of_gt
  max_eq_of_lt
  if_neq_then_max_xor
  if_neq_then_min_xor
  neq_args_then_lt_min_max
  max_comm
  min_comm
  le_then_max_eq_right
  le_then_max_eq_left
  le_max_left
  le_max_right
  max_le
  max_assoc
  le_then_min_eq_left
  le_then_min_eq_right
  min_le_left
  min_le_right
  le_min
  min_assoc
  nexists_max_abs
  max_distrib_min
  min_distrib_max
  isomorph_Λ_max
  isomorph_Λ_min
  isomorph_Ψ_max
  isomorph_Ψ_min
  max_eq_left
  max_eq_right
  min_eq_left
  min_eq_right
)
