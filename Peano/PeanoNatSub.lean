/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatSub.lean

import Peano.PeanoNat
import Peano.PeanoNatAxioms
import Peano.PeanoNatAdd
import Peano.PeanoNatStrictOrder
import Peano.PeanoNatOrder
import Peano.PeanoNatMaxMin
import Peano.PeanoNatWellFounded
import Peano.PeanoNatAdd

namespace Peano
    open Peano

    namespace Sub
        open Peano.Sub
        open Peano.Axioms
        open Peano.StrictOrder
        open Peano.Order
        open Peano.MaxMin
        open Peano.WellFounded
        open Peano.Add

  def subₕₖ (n m : ℕ₀) (h : Le m n) : ℕ₀ :=
    match n, m with
    | k, 𝟘 => k
    | 𝟘, σ m' =>
      False.elim (
        succ_neq_zero m' (le_zero_eq (σ m') h)
      )
    | σ n', σ m' =>
      subₕₖ n' m' (succ_le_succ_then h)
  termination_by n
  decreasing_by
    simp_wf
    apply Nat.lt_succ_self

  def sub (n m : ℕ₀) : ℕ₀ :=
    if h: Le m n then
      subₕₖ n m h
    else
      𝟘

  infix:65 " - " => sub
  notation:65 n " -( " h " ) " m => subₕₖ n m h

  theorem subₕₖ_zero (n : ℕ₀) :
    subₕₖ n 𝟘 (zero_le n) = n
      := by
    induction n with
    | zero =>
      calc
        subₕₖ 𝟘 𝟘 (zero_le 𝟘) = 𝟘 := by simp [subₕₖ]
        _ = 𝟘 := rfl
    | succ n' ih =>
      calc
        subₕₖ (σ n') 𝟘 (zero_le (σ n')) = σ n'
            := by simp [subₕₖ]
        _ = σ n' := rfl

  theorem zero_subₕₖ (n : ℕ₀) (h : Le n 𝟘) :
    subₕₖ 𝟘 n h = 𝟘
      := by
    cases n with
    | zero =>
      calc
        subₕₖ 𝟘 𝟘 (zero_le 𝟘) = 𝟘 := by simp [subₕₖ]
        _ = 𝟘 := rfl
    | succ n' =>
      exfalso
      have h_succ_le_zero : σ n' <= 𝟘 := h
      exact not_succ_le_zero n' h_succ_le_zero

  theorem sub_zero (n : ℕ₀) :
    sub n 𝟘 = n
      := by
    cases n with
    | zero =>
      calc
        sub 𝟘 𝟘 = subₕₖ 𝟘 𝟘 (zero_le 𝟘) := by rfl
        _ = 𝟘 := by simp [subₕₖ]
    | succ n' =>
      calc
        sub (σ n') 𝟘 = subₕₖ (σ n') 𝟘 (zero_le (σ n'))
            := by rfl
        _ = σ n' := by exact subₕₖ_zero (σ n')

  theorem zero_sub (n : ℕ₀) :
    sub 𝟘 n = 𝟘
      := by
    cases n with
    | zero =>
      calc
        sub 𝟘 𝟘 = subₕₖ 𝟘 𝟘 (zero_le 𝟘) := by rfl
        _ = 𝟘 := by simp [subₕₖ]
    | succ n' =>
      calc
        sub 𝟘 (σ n') = 𝟘
          := by simp [sub, not_succ_le_zero n']

  theorem subₕₖ_eq_zero (n m : ℕ₀) (h : m <= n) :
      subₕₖ n m h = 𝟘 → n = m
          := by
      induction m generalizing n with
      | zero =>
        intro h_eq
        have h_n_eq_0 : n = 𝟘 := by
          calc
            n = subₕₖ n 𝟘 (zero_le n) := by rw [subₕₖ_zero]
            _ = 𝟘 := h_eq
        simp [ h_n_eq_0 ]
      | succ m' ih =>
        intro h_eq
        cases n with
        | zero =>
          exfalso
          have h_succ_le_zero : σ m' <= 𝟘 := h
          exact not_succ_le_zero  m' h_succ_le_zero
        | succ n' =>
          have h_le' : m' <= n' := succ_le_succ_then h
          have h_eq' : subₕₖ n' m' h_le' = 𝟘 := by
            rw [← h_eq]
            simp [subₕₖ]
          have h_n'_eq_m' : n' = m' := ih n' h_le' h_eq'
          rw [h_n'_eq_m']

  theorem sub_eq_zero (n m : ℕ₀) :
      sub n m = 𝟘 → Le n m
          := by
      intro h_eq
      by_cases h : Le m n
      · -- Caso: m ≤ n
        have h_sub_eq : sub n m = subₕₖ n m h := by simp [sub, h]
        rw [h_sub_eq] at h_eq
        have h_n_eq_m : n = m := subₕₖ_eq_zero n m h h_eq
        rw [h_n_eq_m]
        exact le_refl m
      · -- Caso: ¬(m ≤ n)
        have h_sub_eq : sub n m = 𝟘 := by simp [sub, h]
        have h_lt : Lt n m := nle_then_gt m n h
        exact lt_imp_le n m h_lt

  theorem subₕₖ_one (n : ℕ₀) (h: Le 𝟙 n):
    subₕₖ n 𝟙 h = ρ n ( m_neq_0_proved_lt_1_m h )
    := by
      induction n with
      | zero =>
        exfalso
        exact not_succ_le_zero 𝟘 h
      | succ n' => -- Caso n = σ n'
        calc
          subₕₖ (σ n') 𝟙 h = subₕₖ n' 𝟘 (succ_le_succ_then h)
              := by simp only [subₕₖ, one]
          _ = n'
              := by rw [subₕₖ_zero n']
          _ = ρ (σ n') (m_neq_0_proved_lt_1_m h)
              := by simp [ρ]

  theorem sub_one (n : ℕ₀) :
    sub n 𝟙 = τ n
      := by
    by_cases h : Le 𝟙 n
    · -- Caso: 𝟙 ≤ n
      have h_sub_eq : sub n 𝟙 = subₕₖ n 𝟙 h := by simp [sub, h]
      rw [h_sub_eq]
      rw [subₕₖ_one n h]
      cases n with
      | zero =>
        exfalso
        exact not_succ_le_zero 𝟘 h
      | succ n' =>
        simp [ρ, τ]
    · -- Caso: ¬Le 𝟙 n
      have h_n_eq_zero : n = 𝟘 := by
        cases n with
        | zero => rfl
        | succ n' =>
          exfalso
          have h_one_le_succ : Le 𝟙 (σ n') := by
            cases n' with
            | zero => simp [one, Le]
            | succ n'' =>
              simp [one, Le]
              exact zero_lt_succ (σ n'')
          exact h h_one_le_succ
      rw [h_n_eq_zero]
      simp [sub, τ]
      intro h'
      exfalso
      exact not_succ_le_zero 𝟘 h'

  theorem one_sub (m : ℕ₀) :
      sub 𝟙 m = 𝟘 ∨ sub 𝟙 m = 𝟙
          := by
    let h_trichotomy := Peano.StrictOrder.trichotomy 𝟙 m
    rcases h_trichotomy with h_1_lt_m | h_1_eq_m | h_m_lt_1
    · -- Caso 1: h_1_lt_m : 𝟙 < m
      left
      have h_not_le : ¬Le m 𝟙 := gt_then_nle_wp h_1_lt_m
      simp [sub, h_not_le]
    · -- Caso 2: h_1_eq_m : 𝟙 = m
      left
      rw [← h_1_eq_m]
      calc
        sub 𝟙 𝟙 = subₕₖ 𝟙 𝟙 (le_refl 𝟙) := by rfl
        _ = subₕₖ 𝟘 𝟘 (succ_le_succ_then (le_refl 𝟙)) := by simp [subₕₖ, one]
        _ = 𝟘 := by simp [subₕₖ]
    · -- Caso 3: h_m_lt_1 : m < 𝟙
      right
      have h_m_eq_zero : m = 𝟘 := by
        cases m with
        | zero => rfl
        | succ m' =>
          exfalso
          have h_lt_one : σ m' < 𝟙 := h_m_lt_1
          have h_le_zero : Le (σ m') 𝟘 := by
                  have h_lt_zero : Lt (σ m') 𝟘 := by
                    rw [one] at h_lt_one
                    exfalso
                    have h_m_prime_lt_zero : m' < 𝟘 := succ_lt_succ_then m' 𝟘 h_lt_one
                    exact lt_zero m' h_m_prime_lt_zero
                  exact lt_imp_le (σ m') 𝟘 h_lt_zero
          exact not_succ_le_zero m' h_le_zero
      rw [h_m_eq_zero]
      calc
        sub 𝟙 𝟘 = 𝟙 := by rw [sub_zero]

    theorem subₕₖ_succ (n k : ℕ₀) (h_k_le_n : Le k n) :
        subₕₖ (σ n) k (le_k_n_then_le_k_sn_wp h_k_le_n) = σ (subₕₖ n k h_k_le_n)
          := by
      induction k generalizing n with
      | zero =>
        calc
          subₕₖ (σ n) 𝟘 (le_k_n_then_le_k_sn_wp h_k_le_n) = σ n := by simp [subₕₖ]
          _ = σ (subₕₖ n 𝟘 (zero_le n)) := by simp [subₕₖ_zero]
      | succ k' ih =>
        cases n with
        | zero =>
          exfalso
          have h_succ_le_zero : Le (σ k') 𝟘 := h_k_le_n
          exact not_succ_le_zero k' h_succ_le_zero
        | succ n' =>
          have h_k'_le_n' : Le k' n' := succ_le_succ_then h_k_le_n
          calc
            subₕₖ (σ (σ n')) (σ k') (le_k_n_then_le_k_sn_wp h_k_le_n)
                = subₕₖ (σ n') k' (succ_le_succ_then (le_k_n_then_le_k_sn_wp h_k_le_n))
                    := by simp [subₕₖ]
            _ = σ (subₕₖ n' k' h_k'_le_n') := by rw [ih n' h_k'_le_n']
          simp [subₕₖ]

  theorem sub_succ (n k : ℕ₀) (h_k_le_n : Le k n) :
        sub (σ n) k = σ (sub n k)
          := by
    have h_k_le_n' : Le k (σ n) := le_k_n_then_le_k_sn_wp h_k_le_n
    have h_subₕₖ_eq : sub (σ n) k = subₕₖ (σ n) k h_k_le_n' := by simp [sub, h_k_le_n']
    have h_sub_n_k : sub n k = subₕₖ n k h_k_le_n := by simp [sub, h_k_le_n]
    rw [h_subₕₖ_eq, h_sub_n_k]
    rw [subₕₖ_succ n k h_k_le_n]

  theorem subₕₖ_k_add_k (n k : ℕ₀) (h_le: Le k n) :
      add (subₕₖ n k h_le) k = n
      := by
      induction n generalizing k with
      | zero =>
        have h_k_le_zero : Le k 𝟘 := h_le
        have h_k_eq_zero : k = 𝟘 := by
          cases k with
          | zero => rfl
          | succ k' =>
            exfalso
            exact not_succ_le_zero k' h_k_le_zero
        subst h_k_eq_zero
        calc
          add (subₕₖ 𝟘 𝟘 h_le) 𝟘 = add 𝟘 𝟘 := by simp [subₕₖ]
          _ = 𝟘 := by simp [add]
      | succ n' ih =>
        cases k with
        | zero =>
          calc
            add (subₕₖ (σ n') 𝟘 h_le) 𝟘 = add (σ n') 𝟘 := by simp [subₕₖ]
            _ = σ n' := by simp [add]
        | succ k' =>
          have h_k'_le_n' : Le k' n' := succ_le_succ_then h_le
          calc
            add (subₕₖ (σ n') (σ k') h_le) (σ k') = add (subₕₖ n' k' h_k'_le_n') (σ k')
              := by simp [subₕₖ]
            _ = add (add (subₕₖ n' k' h_k'_le_n') k') (σ 𝟘) := by simp [add]
            _ = add n' (σ 𝟘) := by rw [ih k' h_k'_le_n']
            _ = σ n' := by simp [add]

  theorem sub_k_add_k (n k : ℕ₀):
      Le k n → add (sub n k) k = n
      := by
      intro h_le
      have h_subₕₖ_eq : sub n k = subₕₖ n k h_le := by simp [sub, h_le]
      rw [h_subₕₖ_eq]
      exact subₕₖ_k_add_k n k h_le

  theorem subₕₖ_k_add_k_forall (n: ℕ₀):
      ∀ (k : ℕ₀) (h_le : k <= n), add (subₕₖ n k h_le) k = n
          := by
    intro k h_le
    exact subₕₖ_k_add_k n k h_le

  theorem sub_k_add_k_forall (n : ℕ₀):
      ∀ (k : ℕ₀), Le k n → add (sub n k) k = n
      := by
    intro k h_le
    exact sub_k_add_k n k h_le

  theorem add_k_subₕₖ_k (n k : ℕ₀) :
      subₕₖ (add k n) k (le_self_add k n) = n
      := by
    induction n with
    | zero =>
      calc
        subₕₖ (add k 𝟘) k (le_self_add k 𝟘) = subₕₖ k k (le_refl k) := by simp [add]
        _ = 𝟘 := by
          have h_eq : subₕₖ k k (le_refl k) = 𝟘 := by
            induction k with
            | zero => simp [subₕₖ]
            | succ k' ih =>
              calc
                subₕₖ (σ k') (σ k') (le_refl (σ k'))
                    = subₕₖ k' k' (succ_le_succ_then (le_refl (σ k')))
                        := by simp [subₕₖ]
                _ = 𝟘 := ih
          exact h_eq
    | succ n' ih =>
      have h_k_le_add : k <= add k n' := le_self_add k n'
      calc
        subₕₖ (add k (σ n')) k (le_self_add k (σ n')) =
          subₕₖ (σ (add k n')) k (le_self_add k (σ n'))
              := by simp [add]
        _ = σ (subₕₖ (add k n') k h_k_le_add)
              := by rw [subₕₖ_succ (add k n') k h_k_le_add]
        _ = σ n' := by rw [ih]

  theorem add_k_sub_k (n k : ℕ₀) :
      sub (add k n) k = n
          := by
    have h_k_le_add : Le k (add k n) := le_self_add k n
    have h_sub_eq : sub (add k n) k = subₕₖ (add k n) k h_k_le_add
        := by
          simp only [sub, dif_pos h_k_le_add]
    rw [h_sub_eq]
    exact add_k_subₕₖ_k n k

  theorem add_k_sub_k_forall (n : ℕ₀) :
      ∀(k : ℕ₀), sub (add k n) k = n
          := by
      intro k
      exact add_k_sub_k n k

  theorem aux_ge_1 {n m : ℕ₀} (h_le : Le (σ m) n) :
    Le 𝟙 (subₕₖ n m (le_sn_m_then_le_n_m_or_succ_wp h_le))
      := by
    induction n generalizing m with
    | zero =>
      exfalso
      have h_succ_le_zero : Le (σ m) 𝟘 := h_le
      exact not_succ_le_zero m h_succ_le_zero
    | succ n' ih =>
      cases m with
      | zero =>
        simp only [subₕₖ] -- Simplifies subₕₖ (σ n') 𝟘 _ to σ n'
        exact h_le
      | succ m' =>
        have h_le_n' : Le m' n' := succ_le_succ_then (le_sn_m_then_le_n_m_or_succ_wp h_le)
        have h_subₕₖ : subₕₖ (σ n') m' (le_k_n_then_le_k_sn_wp h_le_n') = σ (subₕₖ n' m' h_le_n') := by
          rw [subₕₖ_succ n' m' h_le_n']
        have h_sm'_le_n' : Le (σ m') n' := by
          have h_ssm'_le_sn' : Le (σ (σ m')) (σ n') := h_le
          exact succ_le_succ_then h_ssm'_le_sn'
        have h_aux : Le 𝟙 (subₕₖ n' m' h_le_n') := ih h_sm'_le_n'
        simp only [subₕₖ] at h_aux ⊢
        exact h_aux

  theorem nle_one_zero (h : Le 𝟙 𝟘) : False := by
    have h_1_eq_succ_0 : 𝟙 = σ 𝟘 := rfl
    rw [h_1_eq_succ_0] at h
    exact not_succ_le_zero 𝟘 h

  theorem aux_neq_0 {n m : ℕ₀} (h_le : Le (σ m) n) :
    subₕₖ n m (le_sn_m_then_le_n_m_or_succ_wp h_le) ≠ 𝟘
      := by
    have h_aux : Le 𝟙 (subₕₖ n m (le_sn_m_then_le_n_m_or_succ_wp h_le)) := aux_ge_1 h_le
    intro h_contra
    have h_0_ge_1 : Le 𝟙 𝟘 := by
      rw [← h_contra]
      exact h_aux
    exact nle_one_zero h_0_ge_1


  theorem succ_subₕₖ (n m : ℕ₀) (h_le : Le (σ m) n) :
      subₕₖ n (σ m) h_le =
        ρ (subₕₖ n m (le_sn_m_then_le_n_m_or_succ_wp h_le)) (aux_neq_0 h_le)
          := by
    have h_aux : Le 𝟙 (subₕₖ n m (le_sn_m_then_le_n_m_or_succ_wp h_le))
        := aux_ge_1 h_le
    induction n generalizing m with
    | zero =>
      exfalso
      have h_succ_le_zero : Le (σ m) 𝟘 := h_le
      exact not_succ_le_zero m h_succ_le_zero
    | succ n' ih =>
      cases m with
      | zero =>
        calc
          subₕₖ (σ n') (σ 𝟘) h_le = subₕₖ n' 𝟘 (succ_le_succ_then h_le)
              := by simp [subₕₖ]
          _ = n' := by rw [subₕₖ_zero n']
          _ = ρ (σ n') (succ_neq_zero n') := by rfl
          _ = ρ (subₕₖ (σ n') 𝟘 (le_sn_m_then_le_n_m_or_succ_wp h_le)) (aux_neq_0 h_le)
              := by simp [subₕₖ]
      | succ m' =>
        have h_le' : Le m' n' := succ_le_succ_then (le_sn_m_then_le_n_m_or_succ_wp h_le)
        have h_sm'_le_n' : Le (σ m') n' := succ_le_succ_then h_le
        have h_ge_1 : Le 𝟙 (subₕₖ n' m' h_le') := aux_ge_1 h_sm'_le_n'
        calc
          subₕₖ (σ n') (σ (σ m')) h_le = subₕₖ n' (σ m') (succ_le_succ_then h_le)
              := by simp only [subₕₖ]
          _ = ρ (subₕₖ n' m' h_le') (aux_neq_0 h_sm'_le_n') := by
            rw [ih m' h_sm'_le_n' h_ge_1]
          _ = ρ (subₕₖ (σ n') (σ m') (le_sn_m_then_le_n_m_or_succ_wp h_le)) (aux_neq_0 h_le) := by
            {
              have h_val_eq : subₕₖ n' m' h_le' = subₕₖ (σ n') (σ m') (le_sn_m_then_le_n_m_or_succ_wp h_le) := by
                simp only [subₕₖ]
              simp only [h_val_eq]
            }

  theorem succ_sub (n m : ℕ₀) (h_le : Le (σ m) n) :
      sub n (σ m) = τ (sub n m)
          := by
    calc
      sub n (σ m) = subₕₖ n (σ m) h_le := by
        simp only [sub, dif_pos h_le]
      _ = ρ (subₕₖ n m (le_sn_m_then_le_n_m_or_succ_wp h_le)) (aux_neq_0 h_le)
          := succ_subₕₖ n m h_le
      _ = τ (subₕₖ n m (le_sn_m_then_le_n_m_or_succ_wp h_le))
          := by rw [tau_eq_rho_if_ne_zero _ (aux_neq_0 h_le)]
      _ = τ (sub n m) := by
        apply congrArg τ
        have h_m_le_n_from_sigma_m_le_n : Le m n := le_trans m (σ m) n (le_succ_self m) h_le
        simp only [sub, dif_pos h_m_le_n_from_sigma_m_le_n]

  theorem sub_succ_succ_eq (a b : ℕ₀) :
    sub a b = sub (σ a) (σ b)
      := by
    by_cases h_b_le_a : Le b a
    · -- Caso Le b a
      have h_sb_le_sa : Le (σ b) (σ a) := (succ_le_succ_iff b a).mpr h_b_le_a
      simp only [sub, dif_pos h_b_le_a, dif_pos h_sb_le_sa, subₕₖ]
    · -- Caso ¬(Le b a)
      have h_not_sb_le_sa : ¬(Le (σ b) (σ a)) := by
        intro h_contra_succ_le -- Asumir Le (σ b) (σ a) para contradicción
        exact h_b_le_a ((succ_le_succ_iff b a).mp h_contra_succ_le) -- Deriva Le b a, que contradice h_b_le_a
      simp only [sub, dif_neg h_b_le_a, dif_neg h_not_sb_le_sa]


  theorem isomorph_Λ_sub (n m : Nat) :
    Λ (Nat.sub n m) = sub (Λ n) (Λ m)
      := by
    induction n generalizing m with
    | zero =>
      cases m with
      | zero =>
        calc
          Λ (Nat.sub 0 0) = Λ 0 := by rfl
          _ = 𝟘 := by rfl
          _ = sub 𝟘 𝟘 := by rw [sub_zero]
          _ = sub (Λ 0) (Λ 0) := by rfl
      | succ m' =>
        simp [Nat.sub, Λ, zero_sub]
    | succ n' ih =>
      cases m with
      | zero =>
        simp [Nat.sub, Λ, sub_zero]
      | succ m' =>
        calc
          Λ (Nat.sub (Nat.succ n') (Nat.succ m'))
            = Λ (Nat.sub n' m') := by simp [Nat.succ_sub_succ]
          _ = sub (Λ n') (Λ m') := by rw [ih m']
          _ = sub (σ (Λ n')) (σ (Λ m')) := by rw [←sub_succ_succ_eq (Λ n') (Λ m')]
          _ = sub (Λ (Nat.succ n')) (Λ (Nat.succ m')) := by simp [Λ]

  theorem isomorph_Ψ_sub (n m : ℕ₀) :
      Ψ (sub n m) = Nat.sub (Ψ n) (Ψ m)
        := by
    induction n generalizing m with
    | zero =>
      calc
        Ψ (sub 𝟘 m) = Ψ 𝟘 := by rw [zero_sub]
        _ = 0 := by rfl
        _ = Nat.sub 0 (Ψ m) := by simp
        _ = Nat.sub (Ψ 𝟘) (Ψ m) := by rfl
    | succ n' ih =>
      cases m with
      | zero =>
        calc
          Ψ (sub (σ n') 𝟘) = Ψ (σ n') := by rw [sub_zero]
          _ = Nat.succ (Ψ n') := by rfl
          _ = Nat.sub (Nat.succ (Ψ n')) 0 := by simp [Nat.sub_zero]
          _ = Nat.sub (Ψ (σ n')) (Ψ 𝟘) := by simp [Ψ]
      | succ m' =>
        calc
          Ψ (sub (σ n') (σ m')) = Ψ (sub n' m') := by rw [sub_succ_succ_eq n' m']
          _ = Nat.sub (Ψ n') (Ψ m') := by rw [ih m']
          _ = Nat.sub (Nat.succ (Ψ n')) (Nat.succ (Ψ m')) := by simp [Nat.succ_sub_succ]
          _ = Nat.sub (Ψ (σ n')) (Ψ (σ m')) := by simp [Ψ]

    theorem subₕₖ_self (n : ℕ₀) :
      subₕₖ n n (le_refl n) = 𝟘
        := by
      induction n with
      | zero =>
        simp only [subₕₖ]
      | succ n' ih =>
        simp only [subₕₖ]
        exact ih


  theorem sub_self (n : ℕ₀) :
    sub n n = 𝟘
      := by
    have h_le_refl : Le n n := le_refl n
    simp only [sub, dif_pos h_le_refl]
    induction n with
    | zero =>
      simp only [subₕₖ]
    | succ n' ih =>
      simp only [subₕₖ, ih]

  theorem subₕₖ_le_self (n m : ℕ₀) (h_le : Le m n):
    subₕₖ n m h_le ≤ n
      := by
    induction n generalizing m with
    | zero =>
      cases m with
      | zero =>
        simp only [subₕₖ]
        exact le_refl 𝟘
      | succ m' =>
        exfalso
        have h_succ_le_zero : Le (σ m') 𝟘 := h_le
        exact not_succ_le_zero m' h_succ_le_zero
    | succ n' ih =>
      cases m with
      | zero =>
        simp only [subₕₖ]
        exact le_refl (σ n')
      | succ m' =>
        have h_m'_le_n' : Le m' n' := succ_le_succ_then h_le
        have h_subₕₖ_le_n' : subₕₖ n' m' h_m'_le_n' ≤ n' := ih m' h_m'_le_n'
        simp only [subₕₖ]
        exact le_trans (subₕₖ n' m' h_m'_le_n') n' (σ n') h_subₕₖ_le_n' (le_succ_self n')

  theorem subₕₖ_lt_self (n m : ℕ₀) (h_le : Le m n) (h_m_neq_0 : m ≠ 𝟘) :
    Lt (subₕₖ n m h_le) n
      := by
    induction n generalizing m with
    | zero =>
      cases m with
      | zero =>
        contradiction
      | succ m' =>
        exfalso
        have h_succ_le_zero : Le (σ m') 𝟘 := h_le
        exact not_succ_le_zero m' h_succ_le_zero
    | succ n' ih =>
      cases m with
      | zero =>
        contradiction
      | succ m' =>
        have h_m'_le_n' : Le m' n' := succ_le_succ_then h_le
        by_cases h_m'_zero : m' = 𝟘
        · -- Case: m' = 𝟘
          subst h_m'_zero
          simp only [subₕₖ]
          exact lt_succ_self n'
        · -- Case: m' ≠ 𝟘
          -- ih : ∀ (m' ≠ 𝟘 : ℕ₀) (h_le : Le m' n'), Lt (n' -( h_le ) m') n'
          have h_σm'_le_σn' : Le (σ m') (σ n') := h_le
          have h_lt_n_σn : Lt n' (σ n') := lt_succ_self n'
          have h_subₕₖ_lt_n' : Lt (subₕₖ n' m' h_m'_le_n') n' :=
              ih m' h_m'_le_n' h_m'_zero
          have h_cuasi_finish : Lt (subₕₖ n' m' h_m'_le_n') n' ↔ Lt (subₕₖ (σ n') (σ m') h_le) n'
                  := by simp only [subₕₖ]
          have h_subₕₖ_lt_n' : Lt (subₕₖ (σ n') (σ m') h_σm'_le_σn') n'
                  := by
              rw [h_cuasi_finish] at h_subₕₖ_lt_n'
              exact h_subₕₖ_lt_n'
          have h_finish : Lt (subₕₖ (σ n') (σ m') h_σm'_le_σn') (σ n')
              :=
              lt_trans (subₕₖ (σ n') (σ m') h_σm'_le_σn') n' (σ n') h_subₕₖ_lt_n' (lt_succ_self n')
          exact h_finish

    theorem sub_lt_self (n m : ℕ₀) (h_le : Le m n) (h_m_neq_0 : m ≠ 𝟘) :
        Lt (sub n m) n
            := by
      have h_m_le_n : Le m n := h_le
      have h_subₕₖ_eq : sub n m = subₕₖ n m h_m_le_n := by simp [sub, h_m_le_n]
      rw [h_subₕₖ_eq]
      exact subₕₖ_lt_self n m h_m_le_n h_m_neq_0

    theorem sub_lt_self_wp {n m : ℕ₀} (h_le : Le m n) (h_m_neq_0 : m ≠ 𝟘) :
        Lt (sub n m) n
            := by
      have h_m_le_n : Le m n := h_le
      have h_subₕₖ_eq : sub n m = subₕₖ n m h_m_le_n := by simp [sub, h_m_le_n]
      rw [h_subₕₖ_eq]
      exact subₕₖ_lt_self n m h_m_le_n h_m_neq_0

  theorem sub_le_self (n m : ℕ₀) :
    sub n m ≤ n
      := by
    by_cases h_m_le_n : Le m n
    · -- Caso: m ≤ n
      have h_sub_eq : sub n m = subₕₖ n m h_m_le_n := by simp [sub, h_m_le_n]
      rw [h_sub_eq]
      induction n generalizing m with
      | zero =>
        have h_m_eq_zero : m = 𝟘 := by
          cases m with
          | zero => rfl
          | succ m' =>
            exfalso
            exact not_succ_le_zero m' h_m_le_n
        subst h_m_eq_zero
        simp only [subₕₖ]
        exact le_refl 𝟘
      | succ n' ih =>
        cases m with
        | zero =>
          simp only [subₕₖ]
          exact le_refl (σ n')
        | succ m' =>
          have h_m'_le_n' : Le m' n'
              := succ_le_succ_then h_m_le_n
          have h_sub_eq : sub n' m' = subₕₖ n' m' h_m'_le_n'
              := by simp [sub, h_m'_le_n']
          have h_subₕₖ_le_n' : subₕₖ n' m' h_m'_le_n' ≤ n'
              := ih m' h_m'_le_n' h_sub_eq
          simp only [subₕₖ]
          exact le_trans (subₕₖ n' m' h_m'_le_n') n' (σ n') h_subₕₖ_le_n' (le_succ_self n')
    · -- Caso: ¬(m ≤ n)
      have h_sub_eq : sub n m = 𝟘 := by simp [sub, h_m_le_n]
      rw [h_sub_eq]
      exact zero_le n

  theorem subₕₖ_eq_iff_eq_add_of_le (n m k : ℕ₀) (h_m_le_n : Le m n) :
      subₕₖ n m h_m_le_n = k ↔ n = add k m
          := by
    induction n generalizing m k with
    | zero =>
      cases m with
      | zero =>
        simp only [subₕₖ, add]
      | succ m' =>
        exfalso
        have h_succ_le_zero : Le (σ m') 𝟘 := h_m_le_n
        exact not_succ_le_zero m' h_succ_le_zero
    | succ n' ih =>
      cases m with
      | zero =>
        simp only [subₕₖ, add]
      | succ m' =>
        have h_m'_le_n' : Le m' n' := succ_le_succ_then h_m_le_n
        constructor
        · intro h_eq
          have h_ih : n' = add k m' := (ih m' k h_m'_le_n').mp (by simp only [subₕₖ] at h_eq; exact h_eq)
          simp only [add]
          rw [h_ih]
        · intro h_eq
          simp only [subₕₖ]
          have h_succ_eq : σ n' = σ (add k m') := by simp only [add] at h_eq; exact h_eq
          have h_n'_eq : n' = add k m' := succ_inj n' (add k m') h_succ_eq
          exact (ih m' k h_m'_le_n').mpr h_n'_eq

  theorem subₕₖ_le_subₕₖ_right (a b c : ℕ₀)
    (h_a_le_b : Le a b) (h_c_le_a : Le c a)  (h_c_le_b : Le c b) :
    subₕₖ a c h_c_le_a ≤ subₕₖ b c h_c_le_b
      := by
    induction a generalizing b c with
    | zero =>
      cases c with
      | zero =>
        rw [subₕₖ_zero 𝟘, subₕₖ_zero b]
        exact h_a_le_b
      | succ c' =>
        exfalso
        exact not_succ_le_zero c' h_c_le_a
    | succ a' ih =>
      cases b with
      | zero =>
        exfalso
        exact not_succ_le_zero a' h_a_le_b
      | succ b' =>
        have h_a'_le_b' : Le a' b'
          := succ_le_succ_then h_a_le_b
        cases c with
        | zero =>
          simp only [subₕₖ]
          exact h_a_le_b
        | succ c' =>
          have h_c'_le_a' : Le c' a'
            := succ_le_succ_then h_c_le_a
          have h_c'_le_b' : Le c' b'
            := succ_le_succ_then h_c_le_b
          simp only [subₕₖ]
          exact ih b' c' h_a'_le_b' h_c'_le_a' h_c'_le_b'

  theorem subₕₖ_le_subₕₖ_left (a b c : ℕ₀) (h_b_le_c : Le b c) (h_c_le_a : Le c a) :
      subₕₖ a c h_c_le_a ≤ subₕₖ a b (le_trans b c a h_b_le_c h_c_le_a)
          := by
    induction a generalizing b c with
    | zero =>
      cases c with
      | zero =>
        cases b with
        | zero =>
          simp only [subₕₖ_zero]
          exact le_refl 𝟘
        | succ b' =>
          exfalso
          have h_succ_le_zero : Le (σ b') 𝟘
              := h_b_le_c
          exact not_succ_le_zero b' h_succ_le_zero
      | succ c' =>
        exfalso
        have h_succ_le_zero : Le (σ c') 𝟘
            := h_c_le_a
        exact not_succ_le_zero c' h_succ_le_zero
    | succ a' ih =>
      cases b with
      | zero =>
        cases c with
        | zero =>
          simp only [subₕₖ]
          exact le_refl (σ a')
        | succ c' =>
          simp only [subₕₖ]
          exact le_trans (subₕₖ a' c' (succ_le_succ_then h_c_le_a)) a' (σ a') (subₕₖ_le_self a' c' (succ_le_succ_then h_c_le_a)) (le_succ_self a')
      | succ b' =>
        cases c with
        | zero =>
          exfalso
          have h_succ_le_zero : Le (σ b') 𝟘 := h_b_le_c
          exact not_succ_le_zero b' h_succ_le_zero
        | succ c' =>
          have h_b'_le_c' : Le b' c' := succ_le_succ_then h_b_le_c
          have h_c'_le_a' : Le c' a' := succ_le_succ_then h_c_le_a
          simp only [subₕₖ]
          exact ih b' c' h_b'_le_c' h_c'_le_a'

  theorem add_sub_assoc (n m k : ℕ₀) (h_k_le_n : Le k n) :
      add (sub n k) m = sub (add n m) k
          := by
    induction n generalizing k m with
    | zero =>
      have h_k_eq_zero : k = 𝟘 := by
        cases k with
        | zero => rfl
        | succ k' =>
          exfalso
          exact not_succ_le_zero k' h_k_le_n
      subst h_k_eq_zero
      calc
        add (sub 𝟘 𝟘) m = add 𝟘 m := by simp [sub, subₕₖ]
        _ = m := by rw [zero_add]
        _ = add 𝟘 m := by rw [zero_add]
        _ = sub (add 𝟘 m) 𝟘 := by
          simp [sub, subₕₖ, zero_le]
    | succ n' ih =>
      cases k with
      | zero =>
        have h_zero_le_succ : Le 𝟘 (σ n') := zero_le (σ n')
        have h_zero_le_add : Le 𝟘 (add (σ n') m) := zero_le (add (σ n') m)
        simp [sub, h_zero_le_succ, h_zero_le_add, subₕₖ]
      | succ k' =>
        have h_k'_le_n' : Le k' n' := succ_le_succ_then h_k_le_n
        have h_k'_le_add : Le k' (add n' m) := le_trans k' n' (add n' m) h_k'_le_n' (le_self_add n' m)

        have h_sub_n'_k' : sub n' k' = subₕₖ n' k' h_k'_le_n' := by simp [sub, h_k'_le_n']
        have h_sub_add_k' : sub (add n' m) k' = subₕₖ (add n' m) k' h_k'_le_add := by simp [sub, h_k'_le_add]

        calc
          add (sub (σ n') (σ k')) m = add (sub n' k') m := by rw [← sub_succ_succ_eq n' k']
          _ = add (subₕₖ n' k' h_k'_le_n') m := by rw [h_sub_n'_k']
          _ = add (sub n' k') m := by rw [← h_sub_n'_k']
          _ = sub (add n' m) k' := by rw [ih m k' h_k'_le_n']
          _ = sub (σ (add n' m)) (σ k') := by rw [sub_succ_succ_eq (add n' m) k']
          _ = sub (add (σ n') m) (σ k') := by simp only [succ_add]

  theorem add_le_add_left (a b c : ℕ₀) (h : Le a b) :
    Le (add c a) (add c b)
      := by
    induction c with
    | zero =>
      calc
        add 𝟘 a = a := by rw [zero_add]
        _ ≤ b := h
        _ = add 𝟘 b := by rw [zero_add]
    | succ c' ih =>
      calc
        add (σ c') a = σ (add c' a) := by simp [succ_add]
        _ ≤ σ (add c' b) := (succ_le_succ_iff (add c' a) (add c' b)).mpr ih
        _ = add (σ c') b := by simp [succ_add]

  theorem sub_eq_of_le {n m : ℕ₀} (h : Le m n) :
      sub n m = subₕₖ n m h
          := by
      simp [sub, dif_pos h]

  theorem le_sub_iff_add_le_of_le (n m k : ℕ₀) (h_m_le_n : Le m n) :
    Le k (sub n m) ↔ Le (add m k) n
      := by
    constructor
    · intro h_k_le_sub_nm -- Le k (sub n m)
      induction n generalizing m with
      | zero => -- n = 𝟘
        have h_m_eq_zero : m = 𝟘 := le_zero_eq m h_m_le_n
        rw [h_m_eq_zero] at h_k_le_sub_nm -- Le k (sub 𝟘 𝟘)
        simp [sub_self] at h_k_le_sub_nm -- Le k 𝟘
        have h_k_eq_zero : k = 𝟘 := le_zero_eq k h_k_le_sub_nm
        simp [h_m_eq_zero, h_k_eq_zero, add_zero] -- Le 𝟘 𝟘
        exact le_refl 𝟘
      | succ n' ih_n =>
        cases m with
        | zero => -- m = 𝟘
          simp [sub_zero] at h_k_le_sub_nm -- Le k (σ n')
          simp [zero_add] -- Objetivo: Le k (σ n')
          exact h_k_le_sub_nm
        | succ m' => -- m = σ m'
          have h_m'_le_n' : Le m' n' := (succ_le_succ_iff m' n').mp h_m_le_n
          rw [← sub_succ_succ_eq n' m'] at h_k_le_sub_nm -- h_k_le_sub_nm : Le k (sub n' m')
          rw [succ_add m' k] -- Objetivo: Le (σ (add m' k)) (σ n')
          apply (succ_le_succ_iff (add m' k) n').mpr
          exact ih_n m' h_m'_le_n' h_k_le_sub_nm
    · intro h_add_mk_le_n -- Le (add m k) n
      induction n generalizing m with
      | zero => -- n = 𝟘
        have h_m_eq_zero : m = 𝟘 := le_zero_eq m h_m_le_n
        rw [h_m_eq_zero, zero_add] at h_add_mk_le_n -- Le k 𝟘
        have h_k_eq_zero : k = 𝟘 := le_zero_eq k h_add_mk_le_n
        simp [h_m_eq_zero, h_k_eq_zero, sub_self] -- Le 𝟘 𝟘
        exact le_refl 𝟘
      | succ n' ih_n =>
        cases m with
        | zero => -- m = 𝟘
          simp [zero_add] at h_add_mk_le_n -- Le k (σ n')
          simp [sub_zero] -- Objetivo: Le k (σ n')
          exact h_add_mk_le_n
        | succ m' => -- m = σ m'
          have h_m'_le_n' : Le m' n' := (succ_le_succ_iff m' n').mp h_m_le_n
          have h_add_m'k_le_n' : Le (add m' k) n' := by
            have h_eq : add (σ m') k = σ (add m' k) := by simp [succ_add]
            rw [h_eq] at h_add_mk_le_n -- Le (σ (m' + k)) (σ n')
            exact (succ_le_succ_iff (add m' k) n').mp h_add_mk_le_n
          rw [← sub_succ_succ_eq n' m'] -- Objetivo: Le k (sub n' m')
          exact ih_n m' h_m'_le_n' h_add_m'k_le_n'

  theorem sub_sub (n m k : ℕ₀) (h_m_le_n : Le m n) (h_k_le_sub_nm : Le k (sub n m)) :
      sub (sub n m) k = sub n (add m k)
          := by
    have h_add_mk_le_n : Le (add m k) n := by
      rw [← le_sub_iff_add_le_of_le n m k h_m_le_n]
      exact h_k_le_sub_nm
    have h_k_le_subₕₖ : Le k (subₕₖ n m h_m_le_n) := by
      rw [← sub_eq_of_le h_m_le_n]
      exact h_k_le_sub_nm
    calc
      sub (sub n m) k = sub (subₕₖ n m h_m_le_n) k
          := by simp [sub, h_m_le_n]
      _ = subₕₖ (subₕₖ n m h_m_le_n) k h_k_le_subₕₖ
          := by simp [sub, h_k_le_subₕₖ]
      _ = subₕₖ n (add m k) h_add_mk_le_n
          := by
            have h_eq : add (subₕₖ n m h_m_le_n) m = n := subₕₖ_k_add_k n m h_m_le_n
            have h_eq2 : subₕₖ (subₕₖ n m h_m_le_n) k h_k_le_subₕₖ = subₕₖ n (add m k) h_add_mk_le_n := by
              rw [eq_comm]
              apply (subₕₖ_eq_iff_eq_add_of_le n (add m k) (subₕₖ (subₕₖ n m h_m_le_n) k h_k_le_subₕₖ) h_add_mk_le_n).mpr
              calc
                n = add (subₕₖ n m h_m_le_n) m := by exact (subₕₖ_k_add_k n m h_m_le_n).symm
                _ = add (add (subₕₖ (subₕₖ n m h_m_le_n) k h_k_le_subₕₖ) k) m := by simp [subₕₖ_k_add_k]
                _ = add (subₕₖ (subₕₖ n m h_m_le_n) k h_k_le_subₕₖ) (add k m) := by rw [add_assoc]
                _ = add (subₕₖ (subₕₖ n m h_m_le_n) k h_k_le_subₕₖ) (add m k) := by rw [add_comm k m]
            exact h_eq2
      _ = sub n (add m k)
          := by simp [sub, h_add_mk_le_n]

  theorem sub_lt_iff_lt_add_of_le (n m k : ℕ₀) (h_m_le_n : Le m n) :
      Lt (sub n m) k ↔ Lt n (add k m)
          := by
    constructor
    · intro h_sub_lt_k -- Lt (sub n m) k
      induction n generalizing m with
      | zero => -- n = 𝟘
        have h_m_eq_zero : m = 𝟘 := le_zero_eq m h_m_le_n
        rw [h_m_eq_zero] at h_sub_lt_k -- Lt (sub 𝟘 𝟘) k
        simp [sub_self] at h_sub_lt_k -- Lt 𝟘 k
        rw [h_m_eq_zero, add_comm, zero_add] -- Objetivo: Lt 𝟘 k
        exact h_sub_lt_k
      | succ n' ih_n =>
        cases m with
        | zero => -- m = 𝟘
          simp [sub_zero] at h_sub_lt_k -- Lt (σ n') k
          rw [add_comm k 𝟘, zero_add] -- Objetivo: Lt (σ n') k
          exact h_sub_lt_k
        | succ m' => -- m = σ m'
          have h_m'_le_n' : Le m' n' := (succ_le_succ_iff m' n').mp h_m_le_n
          rw [← sub_succ_succ_eq n' m'] at h_sub_lt_k -- h_sub_lt_k : Lt (sub n' m') k
          rw [add_succ k m'] -- Objetivo: Lt (σ n') (σ (add k m'))
          apply (succ_lt_succ_iff n' (add k m')).mpr
          exact ih_n m' h_m'_le_n' h_sub_lt_k
    · intro h_n_lt_km -- Lt n (add k m)
      induction n generalizing m with
      | zero => -- n = 𝟘
        have h_m_eq_zero : m = 𝟘 := le_zero_eq m h_m_le_n
        rw [h_m_eq_zero] at h_n_lt_km -- Lt 𝟘 (add k 𝟘)
        rw [add_zero] at h_n_lt_km -- Lt 𝟘 k
        rw [h_m_eq_zero, sub_self] -- Objetivo: Lt 𝟘 k
        exact h_n_lt_km
      | succ n' ih_n =>
        cases m with
        | zero => -- m = 𝟘
          rw [add_zero] at h_n_lt_km -- Lt (σ n') k
          simp [sub_zero] -- Objetivo: Lt (σ n') k
          exact h_n_lt_km
        | succ m' => -- m = σ m'
          have h_m'_le_n' : Le m' n' := (succ_le_succ_iff m' n').mp h_m_le_n
          rw [add_succ k m'] at h_n_lt_km -- Lt (σ n') (σ (add k m'))
          have h_n'_lt_km' : Lt n' (add k m') := (succ_lt_succ_iff n' (add k m')).mp h_n_lt_km
          rw [← sub_succ_succ_eq n' m'] -- Objetivo: Lt (sub n' m') k
          exact ih_n m' h_m'_le_n' h_n'_lt_km'

  theorem sub_pos_iff_lt (n m : ℕ₀) :
      Le 𝟙 (sub n m) ↔ Lt m n
          := by
    constructor
    · intro h_le_sub_nm -- Le 𝟙 (sub n m)
      induction n generalizing m with
      | zero => -- n = 𝟘
        simp [zero_sub] at h_le_sub_nm -- Le 𝟙 𝟘
        exfalso
        exact nle_one_zero h_le_sub_nm
      | succ n' ih_n =>
        cases m with
        | zero => -- m = 𝟘
          simp [sub_zero] at h_le_sub_nm -- Le 𝟙 (σ n')
          exact zero_lt_succ n'
        | succ m' => -- m = σ m'
          rw [← sub_succ_succ_eq n' m'] at h_le_sub_nm -- Le 𝟙 (sub n' m')
          have h_m'_lt_n' : Lt m' n' := ih_n m' h_le_sub_nm
          exact (succ_lt_succ_iff m' n').mpr h_m'_lt_n'
    · intro h_lt_mn -- Lt m n
      induction n generalizing m with
      | zero => -- n = 𝟘
        have h_m_eq_zero : m = 𝟘 := le_zero_eq m (lt_imp_le m 𝟘 h_lt_mn)
        rw [h_m_eq_zero] at h_lt_mn -- h_lt_mn becomes Lt 𝟘 𝟘
        exfalso
        exact lt_irrefl 𝟘 h_lt_mn
      | succ n' ih_n =>
        cases m with
        | zero => -- m = 𝟘
          simp [sub_zero] -- Goal becomes Le 𝟙 (σ n').
          change Le (σ 𝟘) (σ n')
          exact ((succ_le_succ_iff 𝟘 n').mpr (zero_le n'))
        | succ m' => -- m = σ m'
          rw [← sub_succ_succ_eq n' m'] -- Goal becomes Le 𝟙 (sub n' m').
          apply ih_n m'
          exact (succ_lt_succ_iff m' n').mp h_lt_mn

  theorem lt_b_a_then_sub_a_b_neq_0 (a b : ℕ₀) (h_lt : Lt b a) :
    sub a b ≠ 𝟘
      := by
    by_cases h_b_le_a : Le b a
    · -- Caso Le b a
      have h_sub_eq : sub a b = subₕₖ a b h_b_le_a := by simp [sub, h_b_le_a]
      rw [h_sub_eq]
      intro h_eq_zero
      have h_a_eq_b : a = b := subₕₖ_eq_zero a b h_b_le_a h_eq_zero
      rw [h_a_eq_b] at h_lt
      exact lt_irrefl b h_lt
    · -- Caso ¬(Le b a)
      exfalso
      exact h_b_le_a (lt_imp_le b a h_lt)

  theorem sub_pos_of_lt {a b : ℕ₀} (h_lt : Lt a b) :
      Lt 𝟘 (sub b a)
          := by
    have h_le : Le a b := lt_imp_le a b h_lt
    have h_neq : a ≠ b := ne_of_lt a b h_lt
    rw [sub]
    simp only [dif_pos h_le]
    induction b generalizing a with
    | zero =>
      exfalso
      exact nlt_n_0 a h_lt
    | succ b' ih =>
      cases a with
      | zero =>
        simp only [subₕₖ]
        exact zero_lt_succ b'
      | succ a' =>
        have h_lt_a'_b' : Lt a' b' := (lt_of_succ_lt_succ a' b').mp h_lt
        have h_le_a'_b' : Le a' b' := lt_imp_le a' b' h_lt_a'_b'
        have h_neq_a'_b' : a' ≠ b' := ne_of_lt a' b' h_lt_a'_b'
        have h_sub_eq : subₕₖ (σ b') (σ a') h_le = subₕₖ b' a' h_le_a'_b' := by
          simp only [subₕₖ]
        rw [h_sub_eq]
        exact ih h_lt_a'_b' h_le_a'_b' h_neq_a'_b'

theorem sub_gt_factor_of_gt_one_and_sufficient_gap {a b : ℕ₀}
  (h_lt : Lt b a) (h_gap : Lt (add b b) a) :
    Lt b (sub a b)
      := by
  have h_le : Le b a := lt_imp_le b a h_lt
  have h_eq : add (sub a b) b = a := sub_k_add_k a b h_le

  -- Usamos tricotomía
  cases trichotomy b (sub a b) with
  | inl h_lt_b_sub => exact h_lt_b_sub
  | inr h_cases =>
    cases h_cases with
    | inl h_eq_b_sub =>
      -- Si b = sub a b, entonces a = 2b, pero tenemos a > 2b
      have h_a_eq_2b : a = add b b := by
        rw [← h_eq, ← h_eq_b_sub, add_comm]
      rw [h_a_eq_2b] at h_gap
      exfalso
      exact lt_irrefl (add b b) h_gap
    | inr h_gt_b_sub =>
      -- Si b > sub a b, llegamos a contradicción con h_gap
      have h_sub_le_b : Le (sub a b) b := lt_imp_le (sub a b) b h_gt_b_sub
      have h_a_le_2b : Le a (add b b) := by
        rw [← h_eq, add_comm (sub a b) b]
        exact add_le_add_left (sub a b) b b h_sub_le_b
      have h_not_gap : ¬Lt (add b b) a := nlt_of_le h_a_le_2b
      exact absurd h_gap h_not_gap
  end Sub


end Peano

export Peano.Sub (
  subₕₖ
  subₕₖ_zero
  subₕₖ_succ
  subₕₖ_k_add_k
  subₕₖ_k_add_k_forall
  sub_k_add_k
  sub_k_add_k_forall
  add_k_sub_k
  add_k_sub_k_forall
  aux_ge_1
  aux_neq_0
  succ_subₕₖ
  succ_sub
  sub_succ_succ_eq
  isomorph_Λ_sub
  isomorph_Ψ_sub
  subₕₖ_self
  sub_self
  subₕₖ_le_self
  sub_le_self
  subₕₖ_eq_iff_eq_add_of_le
  subₕₖ_le_subₕₖ_right
  subₕₖ_le_subₕₖ_left
  add_sub_assoc
  add_le_add_left
  sub_eq_of_le
  le_sub_iff_add_le_of_le
  sub_sub
  sub_lt_iff_lt_add_of_le
  sub_pos_iff_lt
  subₕₖ_lt_self
  sub_lt_self
  lt_b_a_then_sub_a_b_neq_0
  sub_pos_of_lt
  sub_lt_self_wp
  sub_gt_factor_of_gt_one_and_sufficient_gap
)
