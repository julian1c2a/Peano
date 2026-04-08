/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatStrictOrder.lean

import Peano.PeanoNat
import Peano.PeanoNatAxioms
import Init.Prelude
import Init.WF
import Init.Data.Nat.Basic

open Peano
namespace Peano
      --set_option diagnostics true
      --set_option trace.Meta.Tactic.simp true
      open Peano
      open Peano.Axioms

  namespace StrictOrder
    open StrictOrder

    def Lt (n m : ℕ₀) : Prop :=
        match n, m with
        | _       , ℕ₀.zero    => False
        | ℕ₀.zero , σ _        => True
        | σ n'    , σ m'       => Lt n' m'

    theorem lt_then_lt_succ (n m : ℕ₀) :
        Lt n m → Lt n (σ m)
            := by
                intro h_n_lt_m
                induction n generalizing m with
                | zero =>
                  cases m with
                  | zero =>
                      unfold Lt at h_n_lt_m
                      exact False.elim h_n_lt_m
                  | succ m' =>
                      unfold Lt
                      trivial
                | succ n' ih_n' =>
                  cases m with
                  | zero =>
                      unfold Lt at h_n_lt_m
                      exact False.elim h_n_lt_m
                  | succ m' =>
                      unfold Lt at h_n_lt_m
                      exact ih_n' m' h_n_lt_m

    theorem lt_then_lt_succ_wp {n m : ℕ₀} (h_lt : Lt n m):
        Lt n (σ m)
        := by
        exact lt_then_lt_succ n m h_lt


    def BLt (n m : ℕ₀) : Bool :=
        match n, m with
        | _        , ℕ₀.zero   => false
        | ℕ₀.zero  , σ _       => true
        | σ n'     , σ m'      => BLt n' m'

    def Gt (n m : ℕ₀) : Prop :=
        match n, m with
        | ℕ₀.zero , _          => False
        | σ _     , ℕ₀.zero    => True
        | σ n'    , σ m'       => Gt n' m'

    def BGt (n m : ℕ₀) : Bool :=
        match n, m with
        | ℕ₀.zero , _          => false
        | σ _     , ℕ₀.zero    => true
        | σ n'    , σ m'       => BGt n' m'

    theorem lt_iff_lt_σ_σ (n m : ℕ₀) :
        Lt n m ↔ Lt (σ n) (σ m)
            := by
                induction n generalizing m with
                | zero => -- n = 𝟘
                  cases m with
                  | zero =>
                    simp [Lt]
                  | succ m' =>
                    unfold Lt
                    simp [Lt]
                | succ n' ih_n' => -- n = σ n'
                  cases m with
                  | zero =>
                    unfold Lt
                    simp [Lt]
                  | succ m' =>
                    unfold Lt
                    simp [Lt]

    theorem lt_iff_lt_τ_τ
        (n m : ℕ₀)
        (h_n_neq_0 : n ≠ 𝟘)
        (h_m_neq_0 : m ≠ 𝟘):
        Lt n m ↔ Lt (τ n) (τ m)
            := by
        induction m generalizing n with
        | zero =>
            exact False.elim (h_m_neq_0 rfl)
        | succ m' =>
            cases n with
            | zero =>
                exact False.elim (h_n_neq_0 rfl)
            | succ n' =>
                rfl

    theorem nlt_self(n : ℕ₀) :
        ¬(Lt n n)
      := by
          induction n with
          | zero =>
              unfold Lt
              trivial
          | succ n' ih_n' =>
              unfold Lt
              simp [ih_n']

    theorem nlt_0_0:
        ¬(Lt 𝟘 𝟘)
          := by
            exact nlt_self 𝟘

    theorem nlt_n_0(n : ℕ₀) :
        ¬(Lt n 𝟘)
            := by
        induction n with
        | zero =>
            unfold Lt
            trivial
        | succ n' ih_n' =>
            unfold Lt
            trivial

    theorem nlt_n_0_false(n : ℕ₀) :
        Lt n 𝟘 → False
            := by
            induction n with
            | zero =>
                unfold Lt
                trivial
            | succ n' ih_n' =>
                unfold Lt
                trivial

    theorem lt_0_n(n : ℕ₀):
        n ≠ 𝟘 → Lt 𝟘 n
          := by
            intro h_neq
            induction n with
            | zero =>
                unfold Lt
                trivial
            | succ n' ih_n' =>
                unfold Lt
                trivial

    theorem lt_then_neq(n m : ℕ₀) :
        Lt n m → n ≠ m
            := by
                intro h
                induction n with
                | zero =>
                    intro heq
                    rw [Eq.symm heq] at h
                    exact (nlt_0_0 h)
                | succ n' =>
                    intro heq
                    rw [Eq.symm heq] at h
                    exact ((nlt_self (σ n')) h)

    theorem neq_then_lt_or_gt(n m : ℕ₀) :
        n ≠ m → (Lt n m ∨ Lt m n)
            := by
                intro h_neq -- h_neq : n ≠ m
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        exact False.elim (h_neq rfl)
                    | succ m' =>
                        apply Or.inl
                        unfold Lt
                        simp
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        apply Or.inr
                        unfold Lt
                        simp
                    | succ m' =>
                        have h_neq_prime : n' ≠ m' := by
                            apply mt ((congrArg ℕ₀.succ) :
                              n' = m' → σ n' = σ m')
                            exact h_neq
                        let spec_ih := ih_n' m' h_neq_prime
                        dsimp only [Lt]
                        exact spec_ih

    theorem lt_nor_gt_then_eq(n m : ℕ₀) :
        ¬(Lt n m) ∧ ¬(Lt m n) → n = m
            := by
                intro h_conj
                cases h_conj with
                | intro h_not_lt_nm h_not_lt_mn =>
                    induction n generalizing m with
                    | zero =>
                        cases m with
                        | zero =>
                            rfl
                        | succ m' =>
                            apply False.elim
                            apply h_not_lt_nm
                            dsimp [Lt]
                    | succ n' ih_n' => -- n = σ n'
                        cases m with
                        | zero =>
                            apply False.elim
                            apply h_not_lt_mn
                            dsimp [Lt]
                        | succ m' =>
                            have h_not_lt_n_prime_m_prime :
                                ¬(Lt n' m') := by
                                unfold Lt at h_not_lt_nm
                                exact h_not_lt_nm
                            have h_not_lt_m_prime_n_prime :
                                ¬(Lt m' n') := by
                                unfold Lt at h_not_lt_mn
                                exact h_not_lt_mn
                            have h_eq_prime : n' = m' := by
                                apply ih_n' m'
                                . exact h_not_lt_n_prime_m_prime
                                . exact h_not_lt_m_prime_n_prime
                            rw [h_eq_prime]

    theorem lt_succ_self ( n : ℕ₀ ) :
        Lt n (σ n)
            := by
                induction n with
                | zero =>
                    unfold Lt
                    trivial
                | succ n' ih_n' =>
                    unfold Lt
                    trivial

    theorem lt_succ (n m : ℕ₀) :
      Lt n m → Lt n (σ m)
        := by
        intro h_n_lt_m
        induction n generalizing m with
        | zero =>
          cases m with
          | zero =>
            have contradiction : False := by
              unfold Lt at h_n_lt_m
              exact h_n_lt_m
            exact False.elim contradiction
          | succ m' =>
            simp [Lt]
        | succ n' ih_n' =>
          cases m with
          | zero =>
            have contradiction : False := by
              unfold Lt at h_n_lt_m
              exact h_n_lt_m
            exact False.elim contradiction
          | succ m' =>
            simp [Lt] at *
            exact ih_n' m' h_n_lt_m

    theorem lt_succ_then_lt (n m : ℕ₀) :
      Lt (σ n) m → Lt n m
        := by
      intro h_lt_σn_m
      induction n generalizing m with
      | zero =>
        cases m with
        | zero =>
          -- h_lt_σn_m : Lt (σ 𝟘) 𝟘, but Lt (σ 𝟘) 𝟘 = False
          unfold Lt at h_lt_σn_m
          exact False.elim h_lt_σn_m
        | succ m' =>
          unfold Lt
          trivial
      | succ n' ih_n' =>
        cases m with
        | zero =>
            unfold Lt at h_lt_σn_m
            exact False.elim h_lt_σn_m
        | succ m' =>
            unfold Lt at h_lt_σn_m
            exact ih_n' m' h_lt_σn_m

    theorem lt_succ_then_lt_wp {n m : ℕ₀} (h_lt_σn_m : Lt (σ n) m) :
      Lt n m
        := by
      exact lt_succ_then_lt n m h_lt_σn_m

    theorem succ_lt_succ_iff (n m : ℕ₀) :
      Lt (σ n) (σ m) ↔ Lt n m
      := by
      constructor
      · intro h_lt_nm
        induction n generalizing m with
        | zero =>
          cases m with
          | zero =>
            unfold Lt at h_lt_nm
            exact False.elim h_lt_nm
          | succ m' =>
            unfold Lt
            trivial
        | succ n' ih_n' =>
            cases m with
            | zero =>
                unfold Lt at h_lt_nm
                exact False.elim h_lt_nm
            | succ m' =>
                unfold Lt at h_lt_nm
                exact ih_n' m' h_lt_nm
      · intro h_lt_n_m
        induction n generalizing m with
        | zero =>
          cases m with
          | zero =>
            unfold Lt at h_lt_n_m
            exact False.elim h_lt_n_m
          | succ m' =>
            unfold Lt
            trivial
        | succ n' ih_n' =>
          cases m with
          | zero =>
            unfold Lt at h_lt_n_m
            exact False.elim h_lt_n_m
          | succ m' =>
            unfold Lt at h_lt_n_m
            exact ih_n' m' h_lt_n_m

  theorem lt_of_succ_lt_succ (n m : ℕ₀):
      Lt (σ n) (σ m) ↔ Lt n m
      := by
    constructor
    · -- Dirección →: Lt (σ n) (σ m) → Lt n m
      intro h_lt_σn_σm
      unfold Lt at h_lt_σn_σm
      exact h_lt_σn_σm
    · -- Dirección ←: Lt n m → Lt (σ n) (σ m)
      intro h_lt_nm
      unfold Lt
      exact h_lt_nm

    theorem lt_zero (n : ℕ₀) :
        Lt n 𝟘 → False
            := by
                intro h_lt_n_0
                induction n with
                | zero =>
                    unfold Lt at h_lt_n_0
                    exact False.elim h_lt_n_0
                | succ n' ih_n' =>
                    unfold Lt at h_lt_n_0
                    exact False.elim h_lt_n_0

  theorem lt_zero_succ (m: ℕ₀):
      Lt 𝟘 (σ m)
        := by
          unfold Lt;
          exact True.intro

  theorem zero_is_the_minor (n: ℕ₀):
      Lt n 𝟘 → False
          := by
    intro h_n_lt_zero
    cases n with
    | zero =>
      unfold Lt at h_n_lt_zero
      exact h_n_lt_zero
    | succ _ =>
      unfold Lt at h_n_lt_zero;
      exact h_n_lt_zero

    theorem trichotomy (n m : ℕ₀) :
        (Lt n m) ∨ (n = m) ∨ (Lt m n)
            := by
                by_cases h_eq : n = m
                · -- Caso n = m
                  rw [h_eq]
                  apply Or.inr
                  apply Or.inl
                  rfl
                · -- Caso n ≠ m
                  have h_lt_or_gt := neq_then_lt_or_gt n m h_eq
                  cases h_lt_or_gt with
                  | inl h_lt_nm => -- Caso Lt n m
                    apply Or.inl
                    exact h_lt_nm
                  | inr h_lt_mn => -- Caso Lt m n
                    apply Or.inr
                    apply Or.inr
                    exact h_lt_mn

    theorem lt_asymm(n m : ℕ₀) :
        Lt n m → ¬(Lt m n)
            := by
                intro h_lt_nm
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        unfold Lt
                        simp
                | succ n' ih_n' => -- Añadir ih_n' aquí
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        unfold Lt at h_lt_nm
                        exact ih_n' m' h_lt_nm

    theorem lt_asymm_wp {n m : ℕ₀} (h_lt_nm : Lt n m) :
        ¬(Lt m n)
            := by
        induction n generalizing m with
        | zero =>
            cases m with
            | zero =>
                unfold Lt at h_lt_nm
                exact False.elim h_lt_nm
            | succ m' =>
                unfold Lt
                simp
        | succ n' ih_n' =>
            cases m with
            | zero =>
                unfold Lt at h_lt_nm
                exact False.elim h_lt_nm
            | succ m' =>
                unfold Lt at h_lt_nm
                exact ih_n' h_lt_nm

    theorem strong_trichotomy (n m : ℕ₀) :
          ((Lt n m)∧¬(Lt m n)∧(n ≠ m))
        ∨ ((Lt m n)∧¬(Lt n m)∧(n ≠ m))
        ∨ ((n = m)∧¬(Lt n m)∧¬(Lt m n))
            := by
                by_cases h_eq : n = m
                · -- Caso n = m
                  rw [h_eq]
                  apply Or.inr
                  apply Or.inr
                  exact ⟨
                    rfl,
                    nlt_self m,
                    nlt_self m
                  ⟩
                · -- Caso n ≠ m
                  have h_lt_or_gt := neq_then_lt_or_gt n m h_eq
                  cases h_lt_or_gt with
                  | inl h_lt_nm => -- Caso Lt n m
                    apply Or.inl
                    exact ⟨
                        h_lt_nm,
                        lt_asymm n m h_lt_nm,
                        h_eq
                    ⟩
                  | inr h_lt_mn => -- Caso Lt m n
                    apply Or.inr
                    apply Or.inl
                    exact ⟨
                        h_lt_mn,
                        lt_asymm m n h_lt_mn,
                        h_eq
                    ⟩

    theorem lt_irrefl(n : ℕ₀) :
        ¬(Lt n n)
            := by
                induction n with
                | zero =>
                    unfold Lt
                    trivial
                | succ n' ih_n' =>
                    unfold Lt
                    exact ih_n'

    theorem lt_trans(n m k : ℕ₀) :
        Lt n m → Lt m k → Lt n k
            := by
                intro h_lt_nm h_lt_mk
                induction n generalizing m k with
                | zero => -- n = zero
                    cases m with
                    | zero => -- m = zero
                        unfold Lt at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' => -- m = σ m'
                        cases k with
                        | zero => -- k = zero
                            unfold Lt at h_lt_mk
                            exact False.elim h_lt_mk
                        | succ k' => -- k = σ k'
                            unfold Lt
                            trivial
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        cases k with
                        | zero =>
                            unfold Lt at h_lt_mk
                            exact False.elim h_lt_mk
                        | succ k' =>
                            dsimp only [Lt] at *
                            apply ih_n'
                            . exact h_lt_nm
                            . exact h_lt_mk

    theorem lt_trans_wp {n m k : ℕ₀} (h_lt_nm : Lt n m) (h_lt_mk : Lt m k) :
          Lt n k
              := by
        induction n generalizing m k with
        | zero =>
          cases m with
          | zero =>
            unfold Lt at h_lt_nm
            exact False.elim h_lt_nm
          | succ m' =>
            cases k with
            | zero =>
              unfold Lt at h_lt_mk
              exact False.elim h_lt_mk
            | succ k' =>
              unfold Lt
              trivial
        | succ n' ih_n' =>
          cases m with
          | zero =>
            unfold Lt at h_lt_nm
            exact False.elim h_lt_nm
          | succ m' =>
            cases k with
            | zero =>
              unfold Lt
              exact h_lt_mk
            | succ k' =>
              dsimp only [Lt] at *
              apply ih_n'
              . exact h_lt_nm
              . exact h_lt_mk

    theorem lt_equiv_exists_σ (n m : ℕ₀) :
        Lt n m ↔ (m = σ n) ∨ (∃ k : ℕ₀, Lt n k ∧ Lt k m)
        := by
            induction n generalizing m with
            | zero =>
                cases m with
                | zero =>
                    simp [Lt]
                | succ m' =>
                    simp [Lt]
                    cases m' with
                    | zero =>
                        apply Or.inl
                        rfl
                    | succ m_double_prime =>
                        apply Or.inr
                        exists (σ 𝟘)
            | succ n' ih_n' =>
                cases m with
                | zero =>
                    simp [Lt]
                | succ m' =>
                    simp [Lt]
                    rw [ih_n' m']
                    have h_ex_equiv :
                        (∃ k, Lt n' k ∧ Lt k m')
                        ↔
                        (∃ k', Lt (σ n') k' ∧ Lt k' (σ m'))
                            := by
                        constructor
                        · intro h_ex_lhs
                          rcases h_ex_lhs with
                              ⟨
                                k_val,
                                h_lt_nk,
                                h_lt_km
                              ⟩
                          apply Exists.intro (σ k_val)
                          apply And.intro
                          · dsimp only [Lt]
                            exact h_lt_nk
                          · dsimp only [Lt]
                            exact h_lt_km
                        · intro h_ex_rhs
                          rcases h_ex_rhs with
                              ⟨
                                k_prime_val,
                                h_lt_snk_prime,
                                h_lt_k_prime_sm
                              ⟩
                          cases k_prime_val with
                          | zero =>
                            simp only [Lt] at h_lt_snk_prime
                          | succ k_inner =>
                            apply Exists.intro k_inner
                            simp [Lt] at *
                            exact
                                And.intro
                                h_lt_snk_prime h_lt_k_prime_sm
                    apply or_congr
                    · apply Iff.intro
                      · intro h_eq
                        rw [h_eq]
                      · intro h_eq_succ
                        assumption
                    · exact h_ex_equiv

    theorem lt_self_σ_self(n : ℕ₀) :
        Lt n (σ n)
            := by
        induction n with
        | zero =>
          simp [Lt]
        | succ n' ih_n' =>
          simp [Lt]
          exact ih_n'

    theorem exists_greater_nat (n : ℕ₀) :
      ∃ (m : ℕ₀), Lt n m
        := by
          apply Exists.intro (σ n)
          exact lt_self_σ_self n

    theorem nexists_greater_forall :
      ¬∃ (m : ℕ₀), ∀ (n : ℕ₀),  Lt n m
        := by
          intro h_exists -- Supongamos ∃ m, ∀ n, Lt n m
          rcases h_exists with ⟨m, h_forall_n_lt_m⟩
          -- Obtenemos m y la propiedad ∀ n, Lt n m
          -- Para este m, por el teorema exists_greater_nat,
          --   sabemos que existe un k tal que Lt m k
          have h_exists_k_gt_m : ∃ (k : ℕ₀), Lt m k
            := exists_greater_nat m
          rcases h_exists_k_gt_m with ⟨k, h_lt_m_k⟩
          -- Obtenemos ese k y la prueba de Lt m k
          -- Ahora, usando h_forall_n_lt_m con n = k, tenemos Lt k m
          have h_lt_k_m : Lt k m := h_forall_n_lt_m k
          -- Por el teorema lt_asymm, si Lt m k entonces ¬(Lt k m)
          have h_not_lt_k_m : ¬(Lt k m) := lt_asymm m k h_lt_m_k
          -- Tenemos Lt k m y ¬(Lt k m), lo cual es una contradicción.
          exact h_not_lt_k_m h_lt_k_m

    theorem lt_succ_iff_lt_or_eq(n m : ℕ₀) :
      Lt n (σ m) ↔ Lt n m ∨ n = m
        := by
          constructor
          · -- Prueba de: Lt n (σ m) → Lt n m ∨ n = m
            intro h_lt_n_sm -- h_lt_n_sm: Lt n (σ m)
            induction m generalizing n with
            | zero => -- m = 𝟘
              cases n with
              | zero => -- n = 𝟘
                apply Or.inr
                rfl -- Prueba 𝟘 = 𝟘, ahora válido.
              | succ n' => -- n = σ n'
                have h_n'_lt_zero :
                    Lt n' 𝟘
                        := (succ_lt_succ_iff n' 𝟘).mp
                                h_lt_n_sm
                exfalso
                exact (lt_zero n' h_n'_lt_zero)
            | succ m' ih_m' => -- m = σ m'
              cases n with
              | zero => -- n = 𝟘
                exact Or.inl (lt_zero_succ m')
              | succ n' =>
                have h_lt_n'_sm' :
                    Lt n' (σ m')
                        :=
                        (
                          succ_lt_succ_iff n' (σ m')
                        ).mp h_lt_n_sm
                cases ih_m' n' h_lt_n'_sm' with
                | inl h_lt_n'_m' =>
                  have h_lt_sn'_sm' :
                      Lt (σ n') (σ m')
                          :=
                            (
                              succ_lt_succ_iff n' m'
                            ).mpr h_lt_n'_m'
                  exact Or.inl h_lt_sn'_sm'
                | inr h_n'_eq_m' =>
                  have h_sn'_eq_sm' :
                      σ n' = σ m'
                          := by rw [h_n'_eq_m']
                  exact Or.inr h_sn'_eq_sm'
          · intro h
            cases h with
            | inl h_lt =>
                exact lt_trans n m (σ m)
                          h_lt (lt_succ_self m)
            | inr h_eq =>
                rw [h_eq]
                exact lt_succ_self m

    theorem BLt_iff_Lt (n m : ℕ₀) :
        BLt n m = true ↔ Lt n m
        := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [BLt, Lt]
            | succ m' =>
              simp [BLt, Lt]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [BLt, Lt]
            | succ m' =>
              simp [BLt, Lt]
              exact ih_n' m'

    theorem BLt_then_Lt_wp {n m : ℕ₀} (h : BLt n m = true) :
        Lt n m
        := by
          have h_iff := BLt_iff_Lt n m
          rw [h_iff] at h
          exact h

    theorem BGt_iff_Gt (n m : ℕ₀) :
        BGt n m = true ↔ Gt n m
        := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [BGt, Gt]
            | succ m' =>
              simp [BGt, Gt]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [BGt, Gt]
            | succ m' =>
              simp [BGt, Gt]
              exact ih_n' m'


    theorem nBLt_iff_nLt (n m : ℕ₀) :
        BLt n m = false ↔ ¬ (Lt n m)
        := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [BLt, Lt]
            | succ m' =>
              simp [BLt, Lt]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [BLt, Lt]
            | succ m' =>
              simp [BLt, Lt]
              exact ih_n' m'

    theorem nBGt_iff_nGt (n m : ℕ₀) :
        BGt n m = false ↔ ¬ (Gt n m)
        := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [BGt, Gt]
            | succ m' =>
              simp [BGt, Gt]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [BGt, Gt]
            | succ m' =>
              simp [BGt, Gt]
              exact ih_n' m'

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    theorem isomorph_Λ_lt (n m : Nat) :
        (n < m) ↔ (Lt (Λ n) (Λ m))
        := by
        constructor
        · intro h_lt_nm
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              exact (Nat.lt_irrefl 0 h_lt_nm)
            | succ m' =>
              simp only [Λ]
              unfold Lt
              trivial
          | succ n' ih_n' =>
            cases m with
            | zero =>
              unfold Lt -- El objetivo se convierte en False
              exact (Nat.not_lt_zero (Nat.succ n') h_lt_nm).elim
            | succ m' =>
              simp only [Λ] -- Corregido: Ψ eliminado
              rw [← lt_iff_lt_σ_σ]
              apply ih_n'
              exact (Nat.lt_of_succ_lt_succ h_lt_nm)
        · intro h_lt_pn_pm
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              unfold Lt at h_lt_pn_pm
              exact False.elim h_lt_pn_pm
            | succ m' =>
              unfold Λ at h_lt_pn_pm
              apply Nat.zero_lt_succ m'
          | succ n' ih_n' =>
            cases m with
            | zero =>
              unfold Lt at h_lt_pn_pm
              exact (False.elim h_lt_pn_pm)
            | succ m' =>
                apply Nat.succ_lt_succ
                apply ih_n'
                simp only [Lt, Λ] at h_lt_pn_pm
                exact h_lt_pn_pm

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    theorem isomorph_Ψ_lt (n m : ℕ₀) :
        (Lt n m) ↔ (Ψ n < Ψ m)
        := by
                constructor
                · intro h_lt_nm -- h_lt_nm : Lt n m
                  induction n generalizing m with
                  | zero =>
                    cases m with
                    | zero =>
                      exact False.elim h_lt_nm
                    | succ m' =>
                      unfold Ψ
                      apply Nat.zero_lt_succ
                  | succ n' ih_n' =>
                    cases m with
                    | zero =>
                      unfold Lt at h_lt_nm
                      exact (False.elim h_lt_nm)
                    | succ m' =>
                      unfold Ψ
                      apply Nat.succ_lt_succ
                      unfold Lt at h_lt_nm
                      exact ih_n' m' h_lt_nm
                · intro h_psi_n_lt_psi_m
                  induction n generalizing m with
                  | zero =>
                    cases m with
                    | zero =>
                      unfold Ψ at h_psi_n_lt_psi_m
                      exact (Nat.lt_irrefl Nat.zero h_psi_n_lt_psi_m).elim
                    | succ m' =>
                      unfold Lt
                      trivial
                  | succ n' ih_n' =>
                    cases m with
                    | zero =>
                      unfold Lt
                      unfold Ψ at h_psi_n_lt_psi_m
                      exact (
                        Nat.not_lt_zero
                            (Nat.succ (Ψ n'))
                            h_psi_n_lt_psi_m
                      ).elim
                    | succ m' =>
                      unfold Lt
                      unfold Ψ at h_psi_n_lt_psi_m
                      have h_base_lt :
                          Ψ n' < Ψ m'
                              :=
                              Nat.lt_of_succ_lt_succ
                                h_psi_n_lt_psi_m
                      exact ih_n' m' h_base_lt

    instance decidableLt (n m : ℕ₀) :
      Decidable (Lt n m) :=
      if h_blt_is_true : BLt n m then
        isTrue ((BLt_iff_Lt n m).mp h_blt_is_true)
      else
        isFalse (fun h_lt_nm : Lt n m =>
            have proof_blt_should_be_true : BLt n m = true
                := (BLt_iff_Lt n m).mpr h_lt_nm
            h_blt_is_true proof_blt_should_be_true)

    instance : LT ℕ₀ := ⟨Lt⟩

    instance decidableGt (n m : ℕ₀) :
      Decidable (Gt n m) :=
      if h_bgt_is_true : BGt n m then
        isTrue ((BGt_iff_Gt n m).mp h_bgt_is_true)
      else
        isFalse (fun h_gt_nm : Gt n m =>
            have proof_bgt_should_be_true : BGt n m = true
                := (BGt_iff_Gt n m).mpr h_gt_nm
            h_bgt_is_true proof_bgt_should_be_true)

    theorem zero_lt_succ (n : ℕ₀) :
      Lt 𝟘 (σ n)
        := by
          induction n with
          | zero =>
            calc
              Lt 𝟘 𝟙 := lt_succ_self 𝟘
              _ = σ 𝟘 := rfl
          | succ n' ih =>
            calc
              Lt 𝟘 (σ (σ n')) := lt_succ_self 𝟘
              _ = σ (σ n') := rfl

    theorem neq_01_then_gt_1 (n : ℕ₀):
      (n ≠ 𝟘) ∧ (n ≠ 𝟙) → Lt 𝟙 n
        := by
      intro h_all_neq
      have h_n_neq_zero := h_all_neq.left
      have h_n_neq_one := h_all_neq.right
      cases trichotomy n 𝟙 with
      | inl h_n_lt_one =>
        have h_n_eq_zero_from_lt_one : n = 𝟘
          := by
          cases n with
          | zero =>
            rfl
          | succ n_plus =>
            unfold Lt at h_n_lt_one
            exact False.elim (
              zero_is_the_minor n_plus h_n_lt_one
            )
        exact False.elim (
          h_n_neq_zero h_n_eq_zero_from_lt_one
        )
      | inr h_eq_or_gt =>
        cases h_eq_or_gt with
        | inl h_n_eq_one =>
          exact False.elim (h_n_neq_one h_n_eq_one)
        | inr h_one_lt_n =>
          exact h_one_lt_n

    theorem lt_0_succ (n : ℕ₀) :
      Lt 𝟘 (σ n)
        := by
      induction n with
      | zero =>
        unfold Lt
        trivial
      | succ n' ih_n' =>
        unfold Lt
        trivial

    theorem lt_1_succ_succ (n : ℕ₀):
      Lt 𝟙 (σ(σ n))
        := by
      induction n with
      | zero =>
        unfold Lt
        trivial
      | succ n' ih_n' =>
        unfold Lt
        trivial

    theorem nlt_then_ltc_or_eq (n m : ℕ₀) :
        ¬(Lt n m) → (Lt m n ∨ n = m)
            := by
      intro h_not_lt_nm
      induction n generalizing m with
      | zero =>
          cases m with
          | zero =>
              apply Or.inr
              rfl
          | succ m' =>
              -- h_not_lt_nm : ¬Lt 𝟘 (σ m')
              -- Pero Lt 𝟘 (σ m') es verdadero por definición,
              --   contradicción
              apply False.elim
              apply h_not_lt_nm
              unfold Lt
              trivial
      | succ n' ih_n' =>
          cases m with
          | zero =>
              apply Or.inl
              unfold Lt
              trivial
          | succ m' =>
              have h_not_lt_n'_m' : ¬Lt n' m' := by
                  intro h_lt_n'_m'
                  unfold Lt at h_not_lt_nm
                  exact h_not_lt_nm h_lt_n'_m'
              let spec_ih := ih_n' m' h_not_lt_n'_m'
              cases spec_ih with
              | inl h_lt_m'_n' =>
                  apply Or.inl
                  unfold Lt
                  exact h_lt_m'_n'
              | inr h_eq_n'_m' =>
                  apply Or.inr
                  rw [h_eq_n'_m']

    theorem lt_or_eq_then_nltc (n m : ℕ₀) :
          (Lt m n ∨ n = m) → ¬(Lt n m)
              := by
          intro h
          cases h with
          | inl h_lt_m_n =>
              intro h_lt_n_m
              exact (lt_asymm n m h_lt_n_m) h_lt_m_n
          | inr h_eq_n_m =>
              rw [h_eq_n_m]
              exact nlt_self m

    theorem lt_or_eq_iff_nltc (n m : ℕ₀) :
          (Lt m n ∨ n = m) ↔ ¬(Lt n m)
              := by
                  constructor
                  · exact lt_or_eq_then_nltc n m
                  · exact nlt_then_ltc_or_eq n m

    theorem succ_lt_succ_iff_forall :
          ∀ (n m: ℕ₀), Lt (σ n) (σ m) ↔ Lt n m
              := by
                  intro n m
                  constructor
                  · intro h_lt_sn_sm
                    unfold Lt at h_lt_sn_sm
                    exact h_lt_sn_sm
                  · intro h_lt_nm
                    unfold Lt
                    exact h_lt_nm

    theorem lt_then_lt_succ_forall :
          ∀ (n m: ℕ₀), Lt (σ n) (σ m) → Lt n m
              := by
                  intro n m h_lt_sn_sm
                  induction n generalizing m with
                  | zero =>
                      cases m with
                      | zero =>
                          unfold Lt at h_lt_sn_sm
                          exact False.elim h_lt_sn_sm
                      | succ m' =>
                          unfold Lt
                          trivial
                  | succ n' ih_n' =>
                      cases m with
                      | zero =>
                          unfold Lt at h_lt_sn_sm
                          exact False.elim h_lt_sn_sm
                      | succ m' =>
                          unfold Lt at h_lt_sn_sm
                          exact ih_n' m' h_lt_sn_sm

    theorem lt_succ_then_lt_forall :
          ∀ (n m: ℕ₀), Lt n m → Lt (σ n) (σ m)
              := by
                  intro n m h_lt_nm
                  induction n generalizing m with
                  | zero =>
                      cases m with
                      | zero =>
                          unfold Lt at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold Lt
                          trivial
                  | succ n' ih_n' =>
                      cases m with
                      | zero =>
                          unfold Lt at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold Lt at h_lt_nm
                          exact ih_n' m' h_lt_nm

    theorem lt_then_lt_succs (n m : ℕ₀) :
        Lt n m → Lt (σ n) (σ m)
            := by
                intro h_lt_n_sm
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_n_sm
                        exact False.elim h_lt_n_sm
                    | succ m' =>
                        unfold Lt
                        trivial
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_n_sm
                        exact False.elim h_lt_n_sm
                    | succ m' =>
                        unfold Lt at h_lt_n_sm
                        exact ih_n' m' h_lt_n_sm

    theorem succ_lt_succ_then (n m : ℕ₀) :
        Lt (σ n) (σ m) → Lt n m
            := by
                intro h_lt_sn_sm
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_sn_sm
                        exact False.elim h_lt_sn_sm
                    | succ m' =>
                        unfold Lt
                        trivial
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        unfold Lt at h_lt_sn_sm
                        exact False.elim h_lt_sn_sm
                    | succ m' =>
                        unfold Lt at h_lt_sn_sm
                        exact ih_n' m' h_lt_sn_sm

    theorem lt_n_sm_then_lt_n_m_or_eq (n m : ℕ₀) :
      Lt n (σ m) → Lt n m ∨ n = m
        := by
          intro h_lt_n_sm
          exact (lt_succ_iff_lt_or_eq n m).mp h_lt_n_sm

    theorem lt_n_sm_then_lt_n_m_or_eq_wp {n m : ℕ₀} (h_lt : Lt n (σ m)):
      Lt n m ∨ n = m
        := by
          exact lt_n_sm_then_lt_n_m_or_eq n m h_lt

    theorem lt_sn_m_then_lt_n_m (n m : ℕ₀) :
      Lt (σ n) m → Lt n m
        := by
          intro h_lt_sn_m
          induction n generalizing m with
          | zero =>
              cases m with
              | zero =>
                  unfold Lt at h_lt_sn_m
                  exact False.elim h_lt_sn_m
              | succ m' =>
                  unfold Lt
                  trivial
          | succ n' ih_n' =>
              cases m with
              | zero =>
                  unfold Lt at h_lt_sn_m
                  exact False.elim h_lt_sn_m
              | succ m' =>
                  unfold Lt at h_lt_sn_m
                  exact ih_n' m' h_lt_sn_m

    theorem lt_0_1 :
      Lt 𝟘 𝟙
        := by
          unfold Lt
          trivial

    theorem lt_1_b_then_b_neq_1 {b : ℕ₀} (h_lt_1_b : 𝟙 < b) :
      b ≠ 𝟙
        := by
          exact Ne.symm (lt_then_neq 𝟙 b h_lt_1_b)

    theorem lt_sn_m_then_lt_n_m_wp {n m : ℕ₀} (h_lt : Lt (σ n) m):
      Lt n m
        := by
          exact lt_sn_m_then_lt_n_m n m h_lt

    theorem lt_1_b_then_b_neq_0 {b : ℕ₀} (h_lt_1_b : 𝟙 < b) :
          b ≠ 𝟘
          := by
              have h_lt_0_b : Lt 𝟘 b := by exact lt_trans_wp lt_0_1 h_lt_1_b
              exact Ne.symm (lt_then_neq 𝟘 b h_lt_0_b)

    theorem lt_b_1_then_b_eq_0 {b : ℕ₀} (h_lt_b_1 : b < 𝟙) :
          b = 𝟘
              := by
                  cases b with
                  | zero =>
                      rfl
                  | succ b' =>
                      exact False.elim (lt_zero b' h_lt_b_1)

    theorem neq_0_then_lt_0 {n : ℕ₀} (h_neq : n ≠ 𝟘) :
          Lt 𝟘 n
              := by
                  cases n with
                  | zero =>
                      exact False.elim (h_neq rfl)
                  | succ _ =>
                      unfold Lt
                      trivial

    theorem lt_0_then_neq_0 {n : ℕ₀} (h_lt : Lt 𝟘 n) :
          n ≠ 𝟘
              := by
                  cases n with
                  | zero =>
                      exact False.elim h_lt
                  | succ _ =>
                      intro h_eq
                      cases h_eq

    theorem lt_then_lt_σ_σ_wp {n m : ℕ₀} (h_lt_nm : Lt n m) :
          Lt (σ n) (σ m)
              := by
                  induction n generalizing m with
                  | zero =>
                      cases m with
                      | zero =>
                          unfold Lt at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold Lt
                          trivial
                  | succ n' ih_n' =>
                      cases m with
                      | zero =>
                          unfold Lt at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold Lt at h_lt_nm
                          exact ih_n' h_lt_nm

    theorem lt_σ_σ_then_lt_wp {n m : ℕ₀} (h_lt_nm : Lt (σ n) (σ m)) :
          Lt n m
              := by
                  induction n generalizing m with
                  | zero =>
                      cases m with
                      | zero =>
                          unfold Lt at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold Lt
                          trivial
                  | succ n' ih_n' =>
                      cases m with
                      | zero =>
                          unfold Lt at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold Lt at h_lt_nm
                          exact ih_n' h_lt_nm


  end StrictOrder
end Peano

export Peano.StrictOrder (
    Lt
    BLt
    Gt
    BGt
    lt_iff_lt_σ_σ
    nlt_self
    nlt_0_0
    nlt_n_0
    lt_0_n
    lt_then_neq
    neq_then_lt_or_gt
    lt_nor_gt_then_eq
    trichotomy
    lt_asymm
    strong_trichotomy
    lt_irrefl
    lt_trans
    lt_equiv_exists_σ
    lt_self_σ_self
    lt_iff_lt_τ_τ
    BLt_iff_Lt
    BGt_iff_Gt
    nBLt_iff_nLt
    nBGt_iff_nGt
    isomorph_Λ_lt
    isomorph_Ψ_lt
    zero_lt_succ
    zero_is_the_minor
    lt_zero_succ
    lt_succ_iff_lt_or_eq
    lt_succ_self
    lt_succ
    lt_of_succ_lt_succ
    succ_lt_succ_iff
    neq_then_lt_or_gt
    decidableLt
    decidableGt
    neq_01_then_gt_1
    nlt_then_ltc_or_eq
    lt_or_eq_then_nltc
    lt_or_eq_iff_nltc
    succ_lt_succ_iff_forall
    lt_then_lt_succ_forall
    lt_succ_then_lt_forall
    nlt_n_0_false
    BLt_then_Lt_wp
    lt_then_lt_succ
    succ_lt_succ_then
    lt_then_lt_succ
    lt_then_lt_succ_wp
    lt_then_lt_succs
    lt_n_sm_then_lt_n_m_or_eq
    lt_n_sm_then_lt_n_m_or_eq_wp
    lt_sn_m_then_lt_n_m
    lt_sn_m_then_lt_n_m_wp
    lt_0_succ
    lt_1_succ_succ
    lt_1_b_then_b_neq_1
    lt_1_b_then_b_neq_0
    lt_0_1
    lt_trans_wp
    lt_asymm_wp
    lt_b_1_then_b_eq_0
    neq_0_then_lt_0
    lt_0_then_neq_0
    lt_then_lt_σ_σ_wp
    lt_σ_σ_then_lt_wp
    lt_succ_then_lt
    lt_succ_then_lt_wp
)
