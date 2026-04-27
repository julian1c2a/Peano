/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatStrictOrder.lean

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Init.WF
import Init.Data.Nat.Basic

open Peano
namespace Peano
      --set_option diagnostics true
      --set_option trace.Meta.Tactic.simp true
      open Peano
      open Peano.Axioms

  namespace StrictOrder
    open Axioms

    def lt₀ (n m : ℕ₀) : Prop :=
      match n, m with
      | _       , .zero    => False
      | .zero , .succ _        => True
      | .succ n'    , .succ m'       => lt₀ n' m'

    def lt₁ (n m : ℕ₁) : Prop := lt₀ n.val m.val

    def lt₂ (n m : ℕ₂) : Prop := lt₀ n.val.val m.val.val

    theorem lt_then_lt_succ
      (n m : ℕ₀) :
        lt₀ n m → lt₀ n (σ m)
          := by
      intro h_n_lt_m
      induction n generalizing m with
      | zero =>
        cases m with
        | zero =>
            unfold lt₀ at h_n_lt_m
            exact False.elim h_n_lt_m
        | succ m' =>
            unfold lt₀
            trivial
      | succ n' ih_n' =>
        cases m with
        | zero =>
            unfold lt₀ at h_n_lt_m
            exact False.elim h_n_lt_m
        | succ m' =>
            unfold lt₀ at h_n_lt_m
            exact ih_n' m' h_n_lt_m

    theorem lt_then_lt_succ_wp {n m : ℕ₀}
      (h_lt : lt₀ n m) :
        lt₀ n (σ m)
          := by
        exact lt_then_lt_succ n m h_lt


    def blt₀ (n m : ℕ₀) : Bool :=
        match n, m with
        | _        , .zero   => false
        | .zero  , .succ _       => true
        | .succ n'     , .succ m'      => blt₀ n' m'

    def gt₀ (n m : ℕ₀) : Prop :=
        match n, m with
        | .zero , _          => False
        | .succ _     , .zero    => True
        | .succ n'    , .succ m'       => gt₀ n' m'

    def bgt₀ (n m : ℕ₀) : Bool :=
        match n, m with
        | .zero , _          => false
        | .succ _     , .zero    => true
        | .succ n'    , .succ m'       => bgt₀ n' m'

    theorem lt_iff_lt_σ_σ
      (n m : ℕ₀) :
        lt₀ n m ↔ lt₀ (σ n) (σ m)
          := by
      induction n generalizing m with
      | zero => -- n = 𝟘
        cases m with
        | zero =>
          simp [lt₀]
        | succ m' =>
          unfold lt₀
          simp [lt₀]
      | succ n' ih_n' => -- n = σ n'
        cases m with
        | zero =>
          unfold lt₀
          simp [lt₀]
        | succ m' =>
          unfold lt₀
          simp [lt₀]

    theorem lt_iff_lt_τ_τ
      (n m : ℕ₀)
      (h_n_neq_0 : n ≠ 𝟘)
      (h_m_neq_0 : m ≠ 𝟘):
        lt₀ n m ↔ lt₀ (τ n) (τ m)
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

    theorem nlt_self
      (n : ℕ₀) :
        ¬(lt₀ n n)
          := by
      induction n with
      | zero =>
          unfold lt₀
          trivial
      | succ n' ih_n' =>
          unfold lt₀
          simp [ih_n']

  theorem nlt_1_self
    (n : ℕ₁) :
      ¬(lt₁ n n)
        := by
    unfold lt₁
    exact nlt_self n.val

    theorem nlt_2_self
      (n : ℕ₂) :
        ¬(lt₂ n n)
          := by
      unfold lt₂
      exact nlt_self n.val.val

    theorem not_lt_zero:
        ¬(lt₀ 𝟘 𝟘)
          := by
      exact nlt_self 𝟘

    theorem nlt_n_0
      (n : ℕ₀) :
        ¬(lt₀ n 𝟘)
          := by
      induction n with
      | zero =>
          unfold lt₀
          trivial
      | succ n' ih_n' =>
          unfold lt₀
          trivial

    theorem nlt_n_0_false
      (n : ℕ₀) :
        lt₀ n 𝟘 → False
          := by
      induction n with
      | zero =>
          unfold lt₀
          trivial
      | succ n' ih_n' =>
          unfold lt₀
          trivial

    theorem pos_of_ne_zero
      (n : ℕ₀):
        n ≠ 𝟘 → lt₀ 𝟘 n
          := by
      intro h_neq
      induction n with
      | zero =>
          unfold lt₀
          trivial
      | succ n' ih_n' =>
          unfold lt₀
          trivial

    theorem ne_of_lt
      (n m : ℕ₀) :
        lt₀ n m → n ≠ m
          := by
      intro h
      induction n with
      | zero =>
          intro heq
          rw [Eq.symm heq] at h
          exact (not_lt_zero h)
      | succ n' =>
          intro heq
          rw [Eq.symm heq] at h
          exact ((nlt_self (σ n')) h)

    theorem neq_then_lt_or_gt
      (n m : ℕ₀) :
        n ≠ m → (lt₀ n m ∨ lt₀ m n)
          := by
      intro h_neq -- h_neq : n ≠ m
      induction n generalizing m with
      | zero =>
          cases m with
          | zero =>
              exact False.elim (h_neq rfl)
          | succ m' =>
              apply Or.inl
              unfold lt₀
              simp
      | succ n' ih_n' =>
          cases m with
          | zero =>
              apply Or.inr
              unfold lt₀
              simp
          | succ m' =>
              have h_neq_prime : n' ≠ m' := by
                  apply mt ((congrArg ℕ₀.succ) :
                    n' = m' → σ n' = σ m')
                  exact h_neq
              let spec_ih := ih_n' m' h_neq_prime
              dsimp only [lt₀]
              exact spec_ih

    theorem lt_nor_gt_then_eq
      (n m : ℕ₀) :
        ¬(lt₀ n m) ∧ ¬(lt₀ m n) → n = m
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
                  dsimp [lt₀]
          | succ n' ih_n' => -- n = σ n'
              cases m with
              | zero =>
                  apply False.elim
                  apply h_not_lt_mn
                  dsimp [lt₀]
              | succ m' =>
                  have h_not_lt_n_prime_m_prime :
                      ¬(lt₀ n' m') := by
                      unfold lt₀ at h_not_lt_nm
                      exact h_not_lt_nm
                  have h_not_lt_m_prime_n_prime :
                      ¬(lt₀ m' n') := by
                      unfold lt₀ at h_not_lt_mn
                      exact h_not_lt_mn
                  have h_eq_prime : n' = m' := by
                      apply ih_n' m'
                      . exact h_not_lt_n_prime_m_prime
                      . exact h_not_lt_m_prime_n_prime
                  rw [h_eq_prime]

    theorem lt_succ_self
      (n : ℕ₀) :
        lt₀ n (σ n)
          := by
      induction n with
      | zero =>
          unfold lt₀
          trivial
      | succ n' ih_n' =>
          unfold lt₀
          trivial

    theorem lt_succ
      (n m : ℕ₀) :
        lt₀ n m → lt₀ n (σ m)
          := by
      intro h_n_lt_m
      induction n generalizing m with
      | zero =>
        cases m with
        | zero =>
          have contradiction : False := by
            unfold lt₀ at h_n_lt_m
            exact h_n_lt_m
          exact False.elim contradiction
        | succ m' =>
          simp [lt₀]
      | succ n' ih_n' =>
        cases m with
        | zero =>
          have contradiction : False := by
            unfold lt₀ at h_n_lt_m
            exact h_n_lt_m
          exact False.elim contradiction
        | succ m' =>
          simp [lt₀] at *
          exact ih_n' m' h_n_lt_m

    theorem lt_succ_then_lt
      (n m : ℕ₀) :
        lt₀ (σ n) m → lt₀ n m
          := by
      intro h_lt_σn_m
      induction n generalizing m with
      | zero =>
        cases m with
        | zero =>
          -- h_lt_σn_m : lt₀ (σ 𝟘) 𝟘, but lt₀ (σ 𝟘) 𝟘 = False
          unfold lt₀ at h_lt_σn_m
          exact False.elim h_lt_σn_m
        | succ m' =>
          unfold lt₀
          trivial
      | succ n' ih_n' =>
        cases m with
        | zero =>
            unfold lt₀ at h_lt_σn_m
            exact False.elim h_lt_σn_m
        | succ m' =>
            unfold lt₀ at h_lt_σn_m
            exact ih_n' m' h_lt_σn_m

    theorem lt_succ_then_lt_wp {n m : ℕ₀}
      (h_lt_σn_m : lt₀ (σ n) m) :
        lt₀ n m
          := by
      exact lt_succ_then_lt n m h_lt_σn_m

    theorem succ_lt_succ_iff
      (n m : ℕ₀) :
        lt₀ (σ n) (σ m) ↔ lt₀ n m
          := by
      constructor
      · intro h_lt_nm
        induction n generalizing m with
        | zero =>
          cases m with
          | zero =>
            unfold lt₀ at h_lt_nm
            exact False.elim h_lt_nm
          | succ m' =>
            unfold lt₀
            trivial
        | succ n' ih_n' =>
            cases m with
            | zero =>
                unfold lt₀ at h_lt_nm
                exact False.elim h_lt_nm
            | succ m' =>
                unfold lt₀ at h_lt_nm
                exact ih_n' m' h_lt_nm
      · intro h_lt_n_m
        induction n generalizing m with
        | zero =>
          cases m with
          | zero =>
            unfold lt₀ at h_lt_n_m
            exact False.elim h_lt_n_m
          | succ m' =>
            unfold lt₀
            trivial
        | succ n' ih_n' =>
          cases m with
          | zero =>
            unfold lt₀ at h_lt_n_m
            exact False.elim h_lt_n_m
          | succ m' =>
            unfold lt₀ at h_lt_n_m
            exact ih_n' m' h_lt_n_m

  theorem lt_of_succ_lt_succ
    (n m : ℕ₀):
      lt₀ (σ n) (σ m) ↔ lt₀ n m
        := by
    constructor
    · -- Dirección →: lt₀ (σ n) (σ m) → lt₀ n m
      intro h_lt_σn_σm
      unfold lt₀ at h_lt_σn_σm
      exact h_lt_σn_σm
    · -- Dirección ←: lt₀ n m → lt₀ (σ n) (σ m)
      intro h_lt_nm
      unfold lt₀
      exact h_lt_nm

    theorem lt_zero
      (n : ℕ₀) :
        lt₀ n 𝟘 → False
          := by
                intro h_lt_n_0
                induction n with
                | zero =>
                    unfold lt₀ at h_lt_n_0
                    exact False.elim h_lt_n_0
                | succ n' ih_n' =>
                    unfold lt₀ at h_lt_n_0
                    exact False.elim h_lt_n_0

  theorem lt_zero_succ
    (m: ℕ₀):
      lt₀ 𝟘 (σ m)
        := by
          unfold lt₀;
          exact True.intro

  theorem zero_is_the_minor
    (n: ℕ₀) :
      lt₀ n 𝟘 → False
        := by
    intro h_n_lt_zero
    cases n with
    | zero =>
      unfold lt₀ at h_n_lt_zero
      exact h_n_lt_zero
    | succ _ =>
      unfold lt₀ at h_n_lt_zero;
      exact h_n_lt_zero

    theorem trichotomy
      (n m : ℕ₀) :
        (lt₀ n m) ∨ (n = m) ∨ (lt₀ m n)
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
                  | inl h_lt_nm => -- Caso lt₀ n m
                    apply Or.inl
                    exact h_lt_nm
                  | inr h_lt_mn => -- Caso lt₀ m n
                    apply Or.inr
                    apply Or.inr
                    exact h_lt_mn

    theorem lt_asymm
      (n m : ℕ₀) :
        lt₀ n m → ¬(lt₀ m n)
          := by
                intro h_lt_nm
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        unfold lt₀ at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        unfold lt₀
                        simp
                | succ n' ih_n' => -- Añadir ih_n' aquí
                    cases m with
                    | zero =>
                        unfold lt₀ at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        unfold lt₀ at h_lt_nm
                        exact ih_n' m' h_lt_nm

    theorem lt_asymm_wp {n m : ℕ₀}
      (h_lt_nm : lt₀ n m) :
        ¬(lt₀ m n)
          := by
        induction n generalizing m with
        | zero =>
            cases m with
            | zero =>
                unfold lt₀ at h_lt_nm
                exact False.elim h_lt_nm
            | succ m' =>
                unfold lt₀
                simp
        | succ n' ih_n' =>
            cases m with
            | zero =>
                unfold lt₀ at h_lt_nm
                exact False.elim h_lt_nm
            | succ m' =>
                unfold lt₀ at h_lt_nm
                exact ih_n' h_lt_nm

    theorem strong_trichotomy
      (n m : ℕ₀) :
          ((lt₀ n m)∧¬(lt₀ m n)∧(n ≠ m))
        ∨ ((lt₀ m n)∧¬(lt₀ n m)∧(n ≠ m))
        ∨ ((n = m)∧¬(lt₀ n m)∧¬(lt₀ m n))
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
                  | inl h_lt_nm => -- Caso lt₀ n m
                    apply Or.inl
                    exact ⟨
                        h_lt_nm,
                        lt_asymm n m h_lt_nm,
                        h_eq
                    ⟩
                  | inr h_lt_mn => -- Caso lt₀ m n
                    apply Or.inr
                    apply Or.inl
                    exact ⟨
                        h_lt_mn,
                        lt_asymm m n h_lt_mn,
                        h_eq
                    ⟩

    theorem lt_irrefl
      (n : ℕ₀) :
        ¬(lt₀ n n)
          := by
                induction n with
                | zero =>
                    unfold lt₀
                    trivial
                | succ n' ih_n' =>
                    unfold lt₀
                    exact ih_n'

    theorem lt_trans
      (n m k : ℕ₀) :
        lt₀ n m → lt₀ m k → lt₀ n k
          := by
                intro h_lt_nm h_lt_mk
                induction n generalizing m k with
                | zero => -- n = zero
                    cases m with
                    | zero => -- m = zero
                        unfold lt₀ at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' => -- m = σ m'
                        cases k with
                        | zero => -- k = zero
                            unfold lt₀ at h_lt_mk
                            exact False.elim h_lt_mk
                        | succ k' => -- k = σ k'
                            unfold lt₀
                            trivial
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        unfold lt₀ at h_lt_nm
                        exact False.elim h_lt_nm
                    | succ m' =>
                        cases k with
                        | zero =>
                            unfold lt₀ at h_lt_mk
                            exact False.elim h_lt_mk
                        | succ k' =>
                            dsimp only [lt₀] at *
                            apply ih_n'
                            . exact h_lt_nm
                            . exact h_lt_mk

    theorem lt_trans_wp {n m k : ℕ₀}
      (h_lt_nm : lt₀ n m) (h_lt_mk : lt₀ m k) :
        lt₀ n k
          := by
        induction n generalizing m k with
        | zero =>
          cases m with
          | zero =>
            unfold lt₀ at h_lt_nm
            exact False.elim h_lt_nm
          | succ m' =>
            cases k with
            | zero =>
              unfold lt₀ at h_lt_mk
              exact False.elim h_lt_mk
            | succ k' =>
              unfold lt₀
              trivial
        | succ n' ih_n' =>
          cases m with
          | zero =>
            unfold lt₀ at h_lt_nm
            exact False.elim h_lt_nm
          | succ m' =>
            cases k with
            | zero =>
              unfold lt₀
              exact h_lt_mk
            | succ k' =>
              dsimp only [lt₀] at *
              apply ih_n'
              . exact h_lt_nm
              . exact h_lt_mk

    theorem lt_equiv_exists_σ
      (n m : ℕ₀) :
        lt₀ n m ↔ (m = σ n) ∨ (∃ k : ℕ₀, lt₀ n k ∧ lt₀ k m)
          := by
            induction n generalizing m with
            | zero =>
                cases m with
                | zero =>
                    simp [lt₀]
                | succ m' =>
                    simp [lt₀]
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
                    simp [lt₀]
                | succ m' =>
                    simp [lt₀]
                    rw [ih_n' m']
                    have h_ex_equiv :
                        (∃ k, lt₀ n' k ∧ lt₀ k m')
                        ↔
                        (∃ k', lt₀ (σ n') k' ∧ lt₀ k' (σ m'))
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
                          · dsimp only [lt₀]
                            exact h_lt_nk
                          · dsimp only [lt₀]
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
                            simp only [lt₀] at h_lt_snk_prime
                          | succ k_inner =>
                            apply Exists.intro k_inner
                            simp [lt₀] at *
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

    theorem lt_self_σ_self
      (n : ℕ₀) :
        lt₀ n (σ n)
          := by
        induction n with
        | zero =>
          simp [lt₀]
        | succ n' ih_n' =>
          simp [lt₀]
          exact ih_n'

    theorem exists_greater_nat
      (n : ℕ₀) :
        ∃ (m : ℕ₀), lt₀ n m
          := by
          apply Exists.intro (σ n)
          exact lt_self_σ_self n

    theorem nexists_greater_forall :
        ¬∃ (m : ℕ₀), ∀ (n : ℕ₀),  lt₀ n m
          := by
          intro h_exists -- Supongamos ∃ m, ∀ n, lt₀ n m
          rcases h_exists with ⟨m, h_forall_n_lt_m⟩
          -- Obtenemos m y la propiedad ∀ n, lt₀ n m
          -- Para este m, por el teorema exists_greater_nat,
          --   sabemos que existe un k tal que lt₀ m k
          have h_exists_k_gt_m : ∃ (k : ℕ₀), lt₀ m k
            := exists_greater_nat m
          rcases h_exists_k_gt_m with ⟨k, h_lt_m_k⟩
          -- Obtenemos ese k y la prueba de lt₀ m k
          -- Ahora, usando h_forall_n_lt_m con n = k, tenemos lt₀ k m
          have h_lt_k_m : lt₀ k m := h_forall_n_lt_m k
          -- Por el teorema lt_asymm, si lt₀ m k entonces ¬(lt₀ k m)
          have h_not_lt_k_m : ¬(lt₀ k m) := lt_asymm m k h_lt_m_k
          -- Tenemos lt₀ k m y ¬(lt₀ k m), lo cual es una contradicción.
          exact h_not_lt_k_m h_lt_k_m

    theorem lt_succ_iff_lt_or_eq
      (n m : ℕ₀) :
        lt₀ n (σ m) ↔ lt₀ n m ∨ n = m
          := by
          constructor
          · -- Prueba de: lt₀ n (σ m) → lt₀ n m ∨ n = m
            intro h_lt_n_sm -- h_lt_n_sm: lt₀ n (σ m)
            induction m generalizing n with
            | zero => -- m = 𝟘
              cases n with
              | zero => -- n = 𝟘
                apply Or.inr
                rfl -- Prueba 𝟘 = 𝟘, ahora válido.
              | succ n' => -- n = σ n'
                have h_n'_lt_zero :
                    lt₀ n' 𝟘
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
                    lt₀ n' (σ m')
                        :=
                        (
                          succ_lt_succ_iff n' (σ m')
                        ).mp h_lt_n_sm
                cases ih_m' n' h_lt_n'_sm' with
                | inl h_lt_n'_m' =>
                  have h_lt_sn'_sm' :
                      lt₀ (σ n') (σ m')
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

    theorem blt_iff_Lt
      (n m : ℕ₀) :
        blt₀ n m = true ↔ lt₀ n m
          := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [blt₀, lt₀]
            | succ m' =>
              simp [blt₀, lt₀]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [blt₀, lt₀]
            | succ m' =>
              simp [blt₀, lt₀]
              exact ih_n' m'

    theorem blt_then_Lt_wp {n m : ℕ₀}
      (h : blt₀ n m = true) :
        lt₀ n m
          := by
          have h_iff := blt_iff_Lt n m
          rw [h_iff] at h
          exact h

    theorem bgt_iff_Gt
      (n m : ℕ₀) :
        bgt₀ n m = true ↔ gt₀ n m
          := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [bgt₀, gt₀]
            | succ m' =>
              simp [bgt₀, gt₀]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [bgt₀, gt₀]
            | succ m' =>
              simp [bgt₀, gt₀]
              exact ih_n' m'


    theorem nblt_iff_nLt
      (n m : ℕ₀) :
        blt₀ n m = false ↔ ¬ (lt₀ n m)
          := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [blt₀, lt₀]
            | succ m' =>
              simp [blt₀, lt₀]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [blt₀, lt₀]
            | succ m' =>
              simp [blt₀, lt₀]
              exact ih_n' m'

    theorem nbgt_iff_nGt
      (n m : ℕ₀) :
        bgt₀ n m = false ↔ ¬ (gt₀ n m)
          := by
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [bgt₀, gt₀]
            | succ m' =>
              simp [bgt₀, gt₀]
          | succ n' ih_n' =>
            cases m with
            | zero =>
              simp [bgt₀, gt₀]
            | succ m' =>
              simp [bgt₀, gt₀]
              exact ih_n' m'

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    theorem isomorph_Λ_lt
      (n m : Nat) :
        (n < m) ↔ (lt₀ (Λ n) (Λ m))
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
              unfold lt₀
              trivial
          | succ n' ih_n' =>
            cases m with
            | zero =>
              unfold lt₀ -- El objetivo se convierte en False
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
              unfold lt₀ at h_lt_pn_pm
              exact False.elim h_lt_pn_pm
            | succ m' =>
              unfold Λ at h_lt_pn_pm
              apply Nat.zero_lt_succ m'
          | succ n' ih_n' =>
            cases m with
            | zero =>
              unfold lt₀ at h_lt_pn_pm
              exact (False.elim h_lt_pn_pm)
            | succ m' =>
                apply Nat.succ_lt_succ
                apply ih_n'
                simp only [lt₀, Λ] at h_lt_pn_pm
                exact h_lt_pn_pm

    /--! def Λ(n : Nat) : ℕ₀  de_Nat_a_Pea
         def Ψ(n : ℕ₀) : Nat  de_Pea_a_Nat !--/
    theorem isomorph_Ψ_lt
      (n m : ℕ₀) :
        (lt₀ n m) ↔ (Ψ n < Ψ m)
          := by
                constructor
                · intro h_lt_nm -- h_lt_nm : lt₀ n m
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
                      unfold lt₀ at h_lt_nm
                      exact (False.elim h_lt_nm)
                    | succ m' =>
                      unfold Ψ
                      apply Nat.succ_lt_succ
                      unfold lt₀ at h_lt_nm
                      exact ih_n' m' h_lt_nm
                · intro h_psi_n_lt_psi_m
                  induction n generalizing m with
                  | zero =>
                    cases m with
                    | zero =>
                      unfold Ψ at h_psi_n_lt_psi_m
                      exact (Nat.lt_irrefl Nat.zero h_psi_n_lt_psi_m).elim
                    | succ m' =>
                      unfold lt₀
                      trivial
                  | succ n' ih_n' =>
                    cases m with
                    | zero =>
                      unfold lt₀
                      unfold Ψ at h_psi_n_lt_psi_m
                      exact (
                        Nat.not_lt_zero
                            (Nat.succ (Ψ n'))
                            h_psi_n_lt_psi_m
                      ).elim
                    | succ m' =>
                      unfold lt₀
                      unfold Ψ at h_psi_n_lt_psi_m
                      have h_base_lt :
                          Ψ n' < Ψ m'
                              :=
                              Nat.lt_of_succ_lt_succ
                                h_psi_n_lt_psi_m
                      exact ih_n' m' h_base_lt

    instance decidableLt (n m : ℕ₀) :
      Decidable (lt₀ n m) :=
      if h_blt_is_true : blt₀ n m then
        isTrue ((blt_iff_Lt n m).mp h_blt_is_true)
      else
        isFalse (fun h_lt_nm : lt₀ n m =>
            have proof_blt_should_be_true : blt₀ n m = true
                := (blt_iff_Lt n m).mpr h_lt_nm
            h_blt_is_true proof_blt_should_be_true)

    instance : LT ℕ₀ := ⟨lt₀⟩
    instance : LT ℕ₁ := ⟨lt₁⟩
    instance : LT ℕ₂ := ⟨lt₂⟩

    /-- Irreflexividad estándar de `<` en `ℕ₀`, para interoperar con lemmas
        de orden de la stdlib sobre listas lexicográficas. -/
    instance : Std.Irrefl (fun a b : ℕ₀ => a < b) where
      irrefl := lt_irrefl

    /-- Asimetría estándar de `<` en `ℕ₀`. -/
    instance : Std.Asymm (fun a b : ℕ₀ => a < b) where
      asymm := lt_asymm

    /-- Tricotomía estándar de `<` en `ℕ₀` (forma de la stdlib). -/
    instance : Std.Trichotomous (fun a b : ℕ₀ => a < b) where
      trichotomous := fun a b h_ab h_ba =>
        lt_nor_gt_then_eq a b ⟨h_ab, h_ba⟩

    /-- Transitividad de `<` en `ℕ₀` como instancia de typeclass. -/
    instance : Trans (fun a b : ℕ₀ => a < b) (fun a b : ℕ₀ => a < b)
        (fun a b : ℕ₀ => a < b) where
      trans := by
        intro a b c h_ab h_bc
        exact lt_trans a b c h_ab h_bc

    /-- Clase auxiliar: el orden `<` es irreflexivo sobre `α`.
        Requerida por los lemas del Principio del Palomar en FSetFunction. -/
    class IrreflLT (α : Type) [LT α] : Prop where
      lt_irrefl : ∀ x : α, ¬ x < x

    instance : IrreflLT ℕ₀ := ⟨fun n => nlt_self n⟩
    instance : IrreflLT ℕ₁ := ⟨fun n => nlt_self n.val⟩

    /-- Orden lineal estricto decidible sobre `α`.
        Bundlea `DecidableRel (<)`, irreflexividad, transitividad y tricotomía.
        La asimetría se deriva de irrefl + trans. -/
    class StrictLinearOrder (α : Type) [LT α] [DecidableEq α] where
      decLt  : ∀ a b : α, Decidable (a < b)
      irrefl : ∀ a : α, ¬ a < a
      trans  : ∀ {a b c : α}, a < b → b < c → a < c
      trich  : ∀ a b : α, ¬ a < b → ¬ b < a → a = b

    instance instStrictLinearOrderNat0 : StrictLinearOrder ℕ₀ where
      decLt  := fun a b => decidableLt a b
      irrefl := lt_irrefl
      trans  := fun h1 h2 => lt_trans_wp h1 h2
      trich  := fun a b h_nab h_nba => lt_nor_gt_then_eq a b ⟨h_nab, h_nba⟩

    /-- `DecidableRel (<)` derivable de `StrictLinearOrder`.
        Prioridad baja para no competir con instancias más específicas. -/
    instance (priority := 50) instDecidableRelLtOfSLO {α : Type} [LT α] [DecidableEq α]
        [slo : StrictLinearOrder α] : DecidableRel (@LT.lt α _) := slo.decLt

    instance decidableGt (n m : ℕ₀) :
      Decidable (gt₀ n m) :=
      if h_bgt_is_true : bgt₀ n m then
        isTrue ((bgt_iff_Gt n m).mp h_bgt_is_true)
      else
        isFalse (fun h_gt_nm : gt₀ n m =>
            have proof_bgt_should_be_true : bgt₀ n m = true
                := (bgt_iff_Gt n m).mpr h_gt_nm
            h_bgt_is_true proof_bgt_should_be_true)

    theorem zero_lt_succ
      (n : ℕ₀) :
        lt₀ 𝟘 (σ n)
          := by
          induction n with
          | zero =>
            calc
              lt₀ 𝟘 𝟙 := lt_succ_self 𝟘
              _ = σ 𝟘 := rfl
          | succ n' ih =>
            calc
              lt₀ 𝟘 (σ (σ n')) := lt_succ_self 𝟘
              _ = σ (σ n') := rfl

    theorem neq_01_then_gt_1
      (n : ℕ₀) :
        (n ≠ 𝟘) ∧ (n ≠ 𝟙) → lt₀ 𝟙 n
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
            unfold lt₀ at h_n_lt_one
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

    theorem lt_0_succ
      (n : ℕ₀) :
        lt₀ 𝟘 (σ n)
          := by
      induction n with
      | zero =>
        unfold lt₀
        trivial
      | succ n' ih_n' =>
        unfold lt₀
        trivial

    theorem lt_1_succ_succ
      (n : ℕ₀):
        lt₀ 𝟙 (σ(σ n))
          := by
      induction n with
      | zero =>
        unfold lt₀
        trivial
      | succ n' ih_n' =>
        unfold lt₀
        trivial

    theorem nlt_then_ltc_or_eq
      (n m : ℕ₀) :
        ¬(lt₀ n m) → (lt₀ m n ∨ n = m)
          := by
      intro h_not_lt_nm
      induction n generalizing m with
      | zero =>
          cases m with
          | zero =>
              apply Or.inr
              rfl
          | succ m' =>
              -- h_not_lt_nm : ¬lt₀ 𝟘 (σ m')
              -- Pero lt₀ 𝟘 (σ m') es verdadero por definición,
              --   contradicción
              apply False.elim
              apply h_not_lt_nm
              unfold lt₀
              trivial
      | succ n' ih_n' =>
          cases m with
          | zero =>
              apply Or.inl
              unfold lt₀
              trivial
          | succ m' =>
              have h_not_lt_n'_m' : ¬lt₀ n' m' := by
                  intro h_lt_n'_m'
                  unfold lt₀ at h_not_lt_nm
                  exact h_not_lt_nm h_lt_n'_m'
              let spec_ih := ih_n' m' h_not_lt_n'_m'
              cases spec_ih with
              | inl h_lt_m'_n' =>
                  apply Or.inl
                  unfold lt₀
                  exact h_lt_m'_n'
              | inr h_eq_n'_m' =>
                  apply Or.inr
                  rw [h_eq_n'_m']

    theorem lt_or_eq_then_nltc
      (n m : ℕ₀) :
        (lt₀ m n ∨ n = m) → ¬(lt₀ n m)
          := by
          intro h
          cases h with
          | inl h_lt_m_n =>
              intro h_lt_n_m
              exact (lt_asymm n m h_lt_n_m) h_lt_m_n
          | inr h_eq_n_m =>
              rw [h_eq_n_m]
              exact nlt_self m

    theorem lt_or_eq_iff_nltc
      (n m : ℕ₀) :
        (lt₀ m n ∨ n = m) ↔ ¬(lt₀ n m)
          := by
                  constructor
                  · exact lt_or_eq_then_nltc n m
                  · exact nlt_then_ltc_or_eq n m

    theorem succ_lt_succ_iff_forall :
        ∀ (n m: ℕ₀), lt₀ (σ n) (σ m) ↔ lt₀ n m
          := by
                  intro n m
                  constructor
                  · intro h_lt_sn_sm
                    unfold lt₀ at h_lt_sn_sm
                    exact h_lt_sn_sm
                  · intro h_lt_nm
                    unfold lt₀
                    exact h_lt_nm

    theorem lt_then_lt_succ_forall :
        ∀ (n m: ℕ₀), lt₀ (σ n) (σ m) → lt₀ n m
          := by
                  intro n m h_lt_sn_sm
                  induction n generalizing m with
                  | zero =>
                      cases m with
                      | zero =>
                          unfold lt₀ at h_lt_sn_sm
                          exact False.elim h_lt_sn_sm
                      | succ m' =>
                          unfold lt₀
                          trivial
                  | succ n' ih_n' =>
                      cases m with
                      | zero =>
                          unfold lt₀ at h_lt_sn_sm
                          exact False.elim h_lt_sn_sm
                      | succ m' =>
                          unfold lt₀ at h_lt_sn_sm
                          exact ih_n' m' h_lt_sn_sm

    theorem lt_succ_then_lt_forall :
        ∀ (n m: ℕ₀), lt₀ n m → lt₀ (σ n) (σ m)
          := by
                  intro n m h_lt_nm
                  induction n generalizing m with
                  | zero =>
                      cases m with
                      | zero =>
                          unfold lt₀ at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold lt₀
                          trivial
                  | succ n' ih_n' =>
                      cases m with
                      | zero =>
                          unfold lt₀ at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold lt₀ at h_lt_nm
                          exact ih_n' m' h_lt_nm

    theorem lt_then_lt_succs
      (n m : ℕ₀) :
        lt₀ n m → lt₀ (σ n) (σ m)
          := by
                intro h_lt_n_sm
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        unfold lt₀ at h_lt_n_sm
                        exact False.elim h_lt_n_sm
                    | succ m' =>
                        unfold lt₀
                        trivial
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        unfold lt₀ at h_lt_n_sm
                        exact False.elim h_lt_n_sm
                    | succ m' =>
                        unfold lt₀ at h_lt_n_sm
                        exact ih_n' m' h_lt_n_sm

    theorem succ_lt_succ_then
      (n m : ℕ₀) :
        lt₀ (σ n) (σ m) → lt₀ n m
          := by
                intro h_lt_sn_sm
                induction n generalizing m with
                | zero =>
                    cases m with
                    | zero =>
                        unfold lt₀ at h_lt_sn_sm
                        exact False.elim h_lt_sn_sm
                    | succ m' =>
                        unfold lt₀
                        trivial
                | succ n' ih_n' =>
                    cases m with
                    | zero =>
                        unfold lt₀ at h_lt_sn_sm
                        exact False.elim h_lt_sn_sm
                    | succ m' =>
                        unfold lt₀ at h_lt_sn_sm
                        exact ih_n' m' h_lt_sn_sm

    theorem lt_n_sm_then_lt_n_m_or_eq
      (n m : ℕ₀) :
        lt₀ n (σ m) → lt₀ n m ∨ n = m
          := by
          intro h_lt_n_sm
          exact (lt_succ_iff_lt_or_eq n m).mp h_lt_n_sm

    theorem lt_n_sm_then_lt_n_m_or_eq_wp {n m : ℕ₀}
      (h_lt : lt₀ n (σ m)):
        lt₀ n m ∨ n = m
          := by
          exact lt_n_sm_then_lt_n_m_or_eq n m h_lt

    theorem lt_sn_m_then_lt_n_m
      (n m : ℕ₀) :
        lt₀ (σ n) m → lt₀ n m
          := by
          intro h_lt_sn_m
          induction n generalizing m with
          | zero =>
              cases m with
              | zero =>
                  unfold lt₀ at h_lt_sn_m
                  exact False.elim h_lt_sn_m
              | succ m' =>
                  unfold lt₀
                  trivial
          | succ n' ih_n' =>
              cases m with
              | zero =>
                  unfold lt₀ at h_lt_sn_m
                  exact False.elim h_lt_sn_m
              | succ m' =>
                  unfold lt₀ at h_lt_sn_m
                  exact ih_n' m' h_lt_sn_m

    theorem lt_0_1 :
        lt₀ 𝟘 𝟙
          := by
          unfold lt₀
          trivial

    theorem lt_1_b_then_b_neq_1 {b : ℕ₀}
      (h_lt_1_b : 𝟙 < b) :
        b ≠ 𝟙
          := by
          exact Ne.symm (ne_of_lt 𝟙 b h_lt_1_b)

    theorem lt_sn_m_then_lt_n_m_wp {n m : ℕ₀}
      (h_lt : lt₀ (σ n) m):
        lt₀ n m
          := by
          exact lt_sn_m_then_lt_n_m n m h_lt

    theorem lt_1_b_then_b_neq_0 {b : ℕ₀}
      (h_lt_1_b : 𝟙 < b) :
        b ≠ 𝟘
          := by
              have h_lt_0_b : lt₀ 𝟘 b := by exact lt_trans_wp lt_0_1 h_lt_1_b
              exact Ne.symm (ne_of_lt 𝟘 b h_lt_0_b)

    theorem lt_b_1_then_b_eq_0 {b : ℕ₀}
      (h_lt_b_1 : b < 𝟙) :
        b = 𝟘
          := by
                  cases b with
                  | zero =>
                      rfl
                  | succ b' =>
                      exact False.elim (lt_zero b' h_lt_b_1)

    theorem neq_0_then_lt_0 {n : ℕ₀}
      (h_neq : n ≠ 𝟘) :
        lt₀ 𝟘 n
          := by
                  cases n with
                  | zero =>
                      exact False.elim (h_neq rfl)
                  | succ _ =>
                      unfold lt₀
                      trivial

    theorem lt_0_then_neq_0 {n : ℕ₀}
      (h_lt : lt₀ 𝟘 n) :
        n ≠ 𝟘
          := by
                  cases n with
                  | zero =>
                      exact False.elim h_lt
                  | succ _ =>
                      intro h_eq
                      cases h_eq

    theorem lt_then_lt_σ_σ_wp {n m : ℕ₀}
      (h_lt_nm : lt₀ n m) :
        lt₀ (σ n) (σ m)
          := by
                  induction n generalizing m with
                  | zero =>
                      cases m with
                      | zero =>
                          unfold lt₀ at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold lt₀
                          trivial
                  | succ n' ih_n' =>
                      cases m with
                      | zero =>
                          unfold lt₀ at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold lt₀ at h_lt_nm
                          exact ih_n' h_lt_nm

    theorem lt_σ_σ_then_lt_wp {n m : ℕ₀}
      (h_lt_nm : lt₀ (σ n) (σ m)) :
        lt₀ n m
          := by
                  induction n generalizing m with
                  | zero =>
                      cases m with
                      | zero =>
                          unfold lt₀ at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold lt₀
                          trivial
                  | succ n' ih_n' =>
                      cases m with
                      | zero =>
                          unfold lt₀ at h_lt_nm
                          exact False.elim h_lt_nm
                      | succ m' =>
                          unfold lt₀ at h_lt_nm
                          exact ih_n' h_lt_nm


  end StrictOrder
end Peano

export Peano.StrictOrder (
    lt₀
    blt₀
    gt₀
    bgt₀
    lt_iff_lt_σ_σ
    nlt_self
    not_lt_zero
    nlt_n_0
    pos_of_ne_zero
    ne_of_lt
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
    blt_iff_Lt
    bgt_iff_Gt
    nblt_iff_nLt
    nbgt_iff_nGt
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
    blt_then_Lt_wp
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
    StrictLinearOrder
    instStrictLinearOrderNat0
    lt_b_1_then_b_eq_0
    neq_0_then_lt_0
    lt_0_then_neq_0
    lt_then_lt_σ_σ_wp
    lt_σ_σ_then_lt_wp
    lt_succ_then_lt
    lt_succ_then_lt_wp
)
