/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatOrder.lean

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder

namespace Peano
  open Peano

  namespace Order
    open Order
    open Peano.Axioms
    open Peano.StrictOrder

    /-- Definición de "menor o igual que" para ℕ₀. -/
    def le₀ (n m : ℕ₀) : Prop := lt₀ n m ∨ n = m
    def ge₀ (n m : ℕ₀) : Prop := lt₀ m n ∨ n = m

    /--
      Definición de "menor o igual que" para ℕ₀ utilizando
      recursión estructural. Demostraremos que le₀ y le' son
      equivalentes.
    -/
    def le' (n m : ℕ₀) : Prop :=
      match n, m with
      |   .zero    ,     _    =>  True
      | .succ _    ,     .zero    =>  False
      | .succ n'   ,   .succ m'   =>  le' n' m'

    theorem zero_le (n : ℕ₀) :
      le₀ 𝟘 n
      :=
      match n with
      | .zero    => Or.inr rfl
      | .succ n' => Or.inl (pos_of_ne_zero (σ n') (succ_neq_zero n'))

    theorem succ_le_succ_iff (n m : ℕ₀) :
      le₀ (σ n) (σ m) ↔ le₀ n m
      := by
      constructor
      · intro h_le_succ
        unfold le₀ at *
        rcases h_le_succ with h_lt_succ | h_eq_succ
        · -- lt₀ (σ n) (σ m) => lt₀ n m => le₀ n m
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
        · -- σ n = σ m => n = m => le₀ n m
          apply Or.inr
          exact ℕ₀.succ.inj h_eq_succ
      · intro h_le
        unfold le₀ at *
        rcases h_le with h_lt | h_eq
        · -- lt₀ n m => lt₀ (σ n) (σ m) => le₀ (σ n) (σ m)
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mpr h_lt
        · -- n = m => σ n = σ m => le₀ (σ n) (σ m)
          apply Or.inr
          exact h_eq ▸ rfl

    theorem succ_le_succ_iff_wp
           {n m : ℕ₀} (h_le_succ : le₀ (σ n) (σ m)) :
      le₀ n m
      := by
      -- Prueba de le₀ (σ n) (σ m) → le₀ n m
      unfold le₀ at *
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- lt₀ (σ n) (σ m) => lt₀ n m => le₀ n m
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
      · -- σ n = σ m => n = m => le₀ n m
        apply Or.inr
        exact ℕ₀.succ.inj h_eq_succ

    theorem succ_le_succ_then {n m : ℕ₀} :
      le₀ (σ n) (σ m) → le₀ n m
      := by
      intro h_le_succ
      unfold le₀ at *
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- lt₀ (σ n) (σ m) => lt₀ n m => le₀ n m
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
      · -- σ n = σ m => n = m => le₀ n m
        apply Or.inr
        exact ℕ₀.succ.inj h_eq_succ

    theorem succ_le_succ_then_wp {n m : ℕ₀} (h_le_succ : le₀ (σ n) (σ m)) :
      le₀ n m
      := by
      -- Prueba de le₀ (σ n) (σ m) → le₀ n m
      unfold le₀ at *
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- lt₀ (σ n) (σ m) => lt₀ n m => le₀ n m
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
      · -- σ n = σ m => n = m => le₀ n m
        apply Or.inr
        exact ℕ₀.succ.inj h_eq_succ

    theorem succ_le_succ_if {n m : ℕ₀} :
      le₀ n m → le₀ (σ n) (σ m)
        := by
      intro h_le
      unfold le₀ at *
      rcases h_le with h_lt | h_eq
      · -- lt₀ n m => lt₀ (σ n) (σ m) => le₀ (σ n) (σ m)
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt
      · -- n = m => σ n = σ m => le₀ (σ n) (σ m)
        apply Or.inr
        exact h_eq ▸ rfl

    theorem succ_le_succ_if_wp {n m : ℕ₀} (h_le_nm : le₀ n m) :
      le₀ (σ n) (σ m)
        := by
      -- Prueba de le₀ n m → le₀ (σ n) (σ m)
      unfold le₀ at *
      rcases h_le_nm with h_lt | h_eq
      · -- lt₀ n m => lt₀ (σ n) (σ m) => le₀ (σ n) (σ m)
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt
      · -- n = m => σ n = σ m => le₀ (σ n) (σ m)
        apply Or.inr
        exact h_eq ▸ rfl

    theorem succ_le_succ'_then_wp {n m : ℕ₀} (h_le_succ : le₀ (σ n) (σ m)) :
      le₀ n (σ m)
      := by
      -- Prueba de le₀ (σ n) (σ m) → le₀ n (σ m)
      unfold le₀ at *
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- lt₀ (σ n) (σ m) => lt₀ n (σ m) => le₀ n (σ m)
        apply Or.inl
        have h_lt_n_m : lt₀ n m := (lt_iff_lt_σ_σ n m).mpr h_lt_succ
        exact lt_trans n m (σ m) h_lt_n_m (lt_self_σ_self m)
      · -- σ n = σ m => n = m => le₀ n (σ m)
        apply Or.inl
        have h_eq_n_m : n = m := ℕ₀.succ.inj h_eq_succ
        rw [h_eq_n_m]
        exact lt_self_σ_self m

    theorem le_then_le_succ {n m : ℕ₀} :
      le₀ n m → le₀ (σ n) (σ m)
      := by
      intro h_le
      unfold le₀ at *
      rcases h_le with h_lt | h_eq
      · -- lt₀ n m => lt₀ (σ n) (σ m) => le₀ (σ n) (σ m)
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt
      · -- n = m => σ n = σ m => le₀ (σ n) (σ m)
        apply Or.inr
        exact h_eq ▸ rfl

    theorem Le_iff_le' (n m : ℕ₀) :
      le' n m ↔ le₀ n m
      := by
        constructor
        · -- Prueba de le' n m → le₀ n m
          intro h_le'_nm
          induction n generalizing m with
          | zero => -- Caso n = 𝟘
            exact zero_le m
          | succ n' ih_n' => -- Caso n = σ n'
            cases m with
            | zero => -- Caso m = 𝟘
              exfalso; simp [le'] at h_le'_nm
            | succ m' => -- Caso m = σ m'
              have h_le_n'_m' : le₀ n' m' := ih_n' m' h_le'_nm
              exact (succ_le_succ_iff n' m').mpr h_le_n'_m'
        · -- Prueba de le₀ n m → le' n m
          intro h_le_nm
          induction n generalizing m with
          | zero => -- Caso n = 𝟘
            simp [le']
          | succ n' ih_n' => -- Caso n = σ n'
            cases m with
            | zero => -- Caso m = 𝟘
              simp [le'] -- El objetivo se convierte en False.
              rcases h_le_nm with h_lt | h_eq
              · exact (nlt_n_0 (σ n') h_lt).elim
              · exact (succ_neq_zero n' h_eq).elim
            | succ m' => -- Caso m = σ m'
              have h_le_n'_m' :
                  le₀ n' m'
                      :=
                      (
                        succ_le_succ_iff n' m'
                      ).mp h_le_nm
              simp [le']
              exact ih_n' m' h_le_n'_m'

    /--
    Función de ayuda para le₀ con repuesta buleana
    -/
    def ble₀ (n m : ℕ₀) : Bool :=
      match n , m with
      | .zero , _ => true
      | _ , .zero => false
      | .succ n' , .succ m' => ble₀ n' m'

    /--
    Función de ayuda para ge₀ con repuesta buleana
    -/
    def bge₀ (n m : ℕ₀) : Bool :=
      match n , m with
      |   _    ,   .zero  => true
      |   .zero    ,   _  => false
      | .succ n'   , .succ m' => bge₀ n' m'

    theorem le_zero_eq (n : ℕ₀) :
      le₀ n 𝟘 → n = 𝟘
      := by
      intro h_le_n_zero
      unfold le₀ at h_le_n_zero
      rcases h_le_n_zero with h_lt_n_zero | h_eq_n_zero
      · -- lt₀ n 𝟘. Esto solo es posible si n no es sucesor,
        exact (nlt_n_0 n h_lt_n_zero).elim
      · -- n = 𝟘
        exact h_eq_n_zero

    theorem le_zero_eq_wp {n : ℕ₀} (h_le_n_zero : le₀ n 𝟘) :
      n = 𝟘
      := by
      unfold le₀ at h_le_n_zero
      rcases h_le_n_zero with h_lt_n_zero | h_eq_n_zero
      · -- lt₀ n 𝟘. Esto solo es posible si n no es sucesor,
        exact (nlt_n_0 n h_lt_n_zero).elim
      · -- n = 𝟘
        exact h_eq_n_zero

    theorem not_succ_le_zero (n : ℕ₀) :
      ¬le₀ (σ n) 𝟘
      := by
      intro h_contra
      unfold le₀ at h_contra
      cases h_contra with
      | inl h_lt => exact (nlt_n_0 (σ n) h_lt).elim
      | inr h_eq => exact (succ_neq_zero n h_eq).elim


    /--!
    -- El teorema ble_iff_Le se mueve aquí porque se usa
    -- en decidableLe.
    !--/

    theorem ble_iff_Le (n m : ℕ₀) :
      ble₀ n m = true ↔ le₀ n m
      := by
      constructor
      · intro h_ble_true
        induction n generalizing m with
        | zero => -- n = 𝟘. ble₀ 𝟘 m = true. Goal: le₀ 𝟘 m.
          rw [ble₀] at h_ble_true -- Simplifica ble₀ 𝟘 m a true,   h_ble_true : true = true
          exact zero_le m
        | succ n' ih_n' => -- n = σ n'.
          cases m with
          | zero =>
            simp [ble₀] at h_ble_true
          | succ m' =>
            simp [ble₀] at h_ble_true
            have h_le_n'_m' : le₀ n' m' := ih_n' m' h_ble_true
            exact (succ_le_succ_iff n' m').mpr h_le_n'_m'
      · intro h_le_nm
        induction n generalizing m with
        | zero =>
          simp [ble₀]
        | succ n' ih_n' => -- n = σ n'.
          cases m with
          | zero =>
            simp [ble₀] -- El objetivo es ahora `false = true`.
            exact (not_succ_le_zero n' h_le_nm).elim
          | succ m' => -- m = σ m', n = σ n'. h_le_nm: le₀ (σ n')   (σ m').
            -- Goal: ble₀ (σ n') (σ m') = true, que es ble₀ n' m' =   true.
            -- IH: le₀ n' m' → ble₀ n' m' = true.
            simp [ble₀] -- El objetivo es ahora ble₀ n' m' = true.
            apply ih_n'
            exact (succ_le_succ_iff n' m').mp h_le_nm

    instance decidableLe (n m : ℕ₀) :
      Decidable (le₀ n m)
      :=
      match decidableLt n m with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq n m with
        | isTrue h_eq => isTrue (Or.inr h_eq)
        | isFalse h_neq =>
          isFalse (
            fun h_le_contra =>
              match h_le_contra with
              | Or.inl h_lt_ev => h_nlt h_lt_ev
              | Or.inr h_eq_ev => h_neq h_eq_ev
          )

    theorem le_of_eq (n m : ℕ₀) :
      n = m → le₀ n m
        := by
          intro h_eq
          rw [h_eq]
          exact Or.inr rfl

    theorem le_of_eq_wp {n m : ℕ₀} (h_eq : n = m) :
      le₀ n m
        := by
          rw [h_eq]
          exact Or.inr rfl

    theorem le_self_of_eq_self (n : ℕ₀) :
      n = n → le₀ n n
        := by
          intro h_eq
          rw [h_eq]
          exact Or.inr rfl

    theorem le_0_of_eq_0 :
      𝟘 = 𝟘 → le₀ 𝟘 𝟘
      := by
      intro h_eq
      rw [h_eq]
      exact Or.inr rfl

    theorem bge_iff_Ge (n m : ℕ₀) :
        bge₀ n m = true ↔ ge₀ n m
        := by
        constructor
        · -- Dirección →: bge₀ n m = true → ge₀ n m
          intro h_bge_true
          unfold bge₀ at h_bge_true
          cases n with
          | zero =>
            cases m with
            | zero =>
              exact Or.inr rfl
            | succ m' =>
              exfalso
              exact Bool.noConfusion h_bge_true
          | succ n' =>
            cases m with
            | zero =>
              apply Or.inl
              exact pos_of_ne_zero (σ n') (succ_neq_zero n')
            | succ m' =>
              have h_ge_n'_m' :
                  ge₀ n' m' :=
                      (
                        bge_iff_Ge n' m'
                      ).mp h_bge_true
              rcases h_ge_n'_m' with h_lt_m'_n' | h_eq_n'_m'
              · apply Or.inl
                exact (lt_iff_lt_σ_σ m' n').mp h_lt_m'_n'
              · apply Or.inr
                exact h_eq_n'_m' ▸ rfl
        · -- Dirección ←: ge₀ n m → bge₀ n m = true
          intro h_ge_nm
          induction n generalizing m with
          | zero =>
            cases m with
            | zero =>
              simp [bge₀]
            | succ m' =>
              unfold ge₀ at h_ge_nm
              rcases h_ge_nm with h_lt_succ_zero | h_eq_zero_succ
              · exact (nlt_n_0 (σ m') h_lt_succ_zero).elim
              · exact (succ_neq_zero m' h_eq_zero_succ.symm).elim
          | succ n' ih =>
            cases m with
            | zero =>
              simp [bge₀]
            | succ m' =>
              simp [bge₀]
              apply ih
              unfold ge₀ at h_ge_nm ⊢
              rcases h_ge_nm with h_lt_succ_succ | h_eq_succ_succ
              · apply Or.inl
                exact (lt_iff_lt_σ_σ m' n').mpr h_lt_succ_succ
              · apply Or.inr
                exact ℕ₀.succ.inj h_eq_succ_succ

    instance decidableGe (n m : ℕ₀) :
      Decidable (ge₀ n m)
      :=
      match decidableLt m n with
      | isTrue h_lt => isTrue (Or.inl h_lt)
      | isFalse h_nlt =>
        match decEq n m with
        -- decEq proviene de `deriving DecidableEq` para ℕ₀
        | isTrue h_eq => isTrue (Or.inr h_eq)
        | isFalse h_neq =>
          isFalse (fun h_ge_contra =>
            match h_ge_contra with
            | Or.inl h_lt_ev => h_nlt h_lt_ev
            | Or.inr h_eq_ev => h_neq h_eq_ev
          )

    theorem le_refl (n : ℕ₀) :
      le₀ n n
      :=
      Or.inr rfl

    theorem lt_imp_le (n m : ℕ₀) :
      lt₀ n m → le₀ n m
      :=
      fun h_lt => Or.inl h_lt

    theorem lt_imp_le_wp {n m : ℕ₀} (h_lt : lt₀ n m) :
      le₀ n m
        := by exact Or.inl h_lt


    theorem le_trans (n m k : ℕ₀) :
      le₀ n m → le₀ m k → le₀ n k
      :=
      fun h_le_nm h_le_mk =>
      match h_le_nm with
      | Or.inl h_lt_nm => -- Caso n < m
        match h_le_mk with
        | Or.inl h_lt_mk =>
          Or.inl (lt_trans n m k h_lt_nm h_lt_mk)
        | Or.inr h_eq_mk =>
            by rw [h_eq_mk] at h_lt_nm; exact Or.inl h_lt_nm
      | Or.inr h_eq_nm => -- Caso n = m
          by rw [h_eq_nm]; exact h_le_mk -- n = m => (m ≤ k)

    theorem le_antisymm (n m : ℕ₀) :
      le₀ n m → le₀ m n → n = m
      :=
      fun h_le_nm h_le_mn =>
      match h_le_nm with
      | Or.inl h_lt_nm => -- n < m
        match h_le_mn with
        | Or.inl h_lt_mn =>
            (lt_asymm n m h_lt_nm h_lt_mn).elim
        | Or.inr h_eq_mn =>
            h_eq_mn.symm
      | Or.inr h_eq_nm =>
          h_eq_nm

    theorem le_total (n m : ℕ₀) :
      le₀ n m ∨ le₀ m n
      :=
      match trichotomy n m with
      | Or.inl h_lt_nm =>
          Or.inl (lt_imp_le n m h_lt_nm)
      | Or.inr (Or.inl h_eq_nm) =>
          Or.inl (Or.inr h_eq_nm)
      | Or.inr (Or.inr h_lt_mn) =>
          Or.inr (lt_imp_le m n h_lt_mn)

    theorem le_iff_lt_succ (n m : ℕ₀) :
      le₀ n m ↔ lt₀ n (σ m)
      := by
      constructor
      · intro h_le_nm
        rcases h_le_nm with h_lt_nm | h_eq_nm
        · -- Caso lt₀ n m. Queremos lt₀ n (σ m).
          exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
        · -- Caso n = m. Queremos lt₀ m (σ m).
          rw [h_eq_nm]
          exact lt_self_σ_self m
      · intro h_lt_n_succ_m -- lt₀ n (σ m). Queremos le₀ n m.
        revert n h_lt_n_succ_m
        induction m with
        | zero => -- m = 𝟘.
          intro n h_lt_n_succ_zero_case
          cases n with
          | zero =>
            exact Or.inr rfl
          | succ n' =>
            have h_lt_n_prime_zero :
                lt₀ n' 𝟘 :=
                    (
                        lt_iff_lt_σ_σ n' 𝟘
                    ).mp h_lt_n_succ_zero_case
            exact (nlt_n_0 n' h_lt_n_prime_zero).elim
        | succ m' ih_m' => -- m = σ m'.
          intro n h_lt_n_succ_sigma_m_prime_case
          cases n with
          | zero =>
            exact zero_le (σ m')
          | succ n' =>
            have h_lt_n_prime_succ_m_prime : lt₀ n' (σ m') :=
              (lt_iff_lt_σ_σ n' (σ m')).mp h_lt_n_succ_sigma_m_prime_case
            have h_le_n_prime_m_prime : le₀ n' m'
                := ih_m' n' h_lt_n_prime_succ_m_prime
            rcases h_le_n_prime_m_prime with h_lt_n_p_m_p | h_eq_n_p_m_p
            · -- Caso lt₀ n' m'.
              apply Or.inl
              exact (lt_iff_lt_σ_σ n' m').mpr h_lt_n_p_m_p
            · -- Caso n' = m'. Entonces σ n' = σ m'.
              apply Or.inr
              rw [h_eq_n_p_m_p]

    theorem lt_of_le_neq (a b : ℕ₀) :
      le₀ a b → a ≠ b → lt₀ a b
        := by
          intro h_le h_neq
          cases h_le with
          | inl h_lt =>
            exact h_lt
          | inr h_eq =>
            exfalso
            exact h_neq h_eq

    theorem lt_of_le_neq_wp {a b : ℕ₀} (h_le_a_b : le₀ a b) (h_neq_a_b : a ≠ b) :
      lt₀ a b
        := by
        -- Prueba de le₀ a b → a ≠ b → lt₀ a b
        unfold le₀ at h_le_a_b
        rcases h_le_a_b with h_lt_a_b | h_eq_a_b
        · -- Caso lt₀ a b
          exact h_lt_a_b
        · -- Caso a = b
          exfalso
          exact h_neq_a_b h_eq_a_b

    theorem le_succ_self (n : ℕ₀) :
      le₀ n (σ n)
      := by
      unfold le₀
      apply Or.inl
      exact lt_self_σ_self n

    theorem le_succ (n m : ℕ₀) :
        le₀ n m → le₀ n (σ m)
          := by
          intro h_le_nm
          unfold le₀ at *
          rcases h_le_nm with h_lt_nm | h_eq_nm
          · -- Caso lt₀ n m
            apply Or.inl
            exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
          · -- Caso n = m
            apply Or.inl
            rw [h_eq_nm]
            exact lt_self_σ_self m

    theorem le_1_succ (n : ℕ₀) :
      le₀ 𝟙 (σ n)
        := by
        exact le_then_le_succ (zero_le n)

    theorem le_zero_eq_zero (n : ℕ₀) :
      le₀ n 𝟘 ↔ n = 𝟘
        := by
      constructor
      · -- Dirección →: le₀ n 𝟘 → n = 𝟘
        intro h_le_n_zero -- h_le_n_zero : le₀ n 𝟘
        unfold le₀ at h_le_n_zero
        rcases h_le_n_zero with h_lt_n_zero | h_eq_n_zero
        · -- Caso lt₀ n 𝟘.
          exact (nlt_n_0 n h_lt_n_zero).elim
        · -- Caso n = 𝟘.
          exact h_eq_n_zero
      · -- Dirección ←: n = 𝟘 → le₀ n 𝟘
        intro h_eq_n_zero -- h_eq_n_zero : n = 𝟘
        rw [h_eq_n_zero]
        exact zero_le 𝟘

    theorem le_succ_zero_zero (n : ℕ₀) :
      le₀ (σ n) 𝟘 → False
        := by
        intro h_le_succ_n_zero -- h_le_succ_n_zero : le₀ (σ n) 𝟘
        unfold le₀ at h_le_succ_n_zero
        rcases h_le_succ_n_zero with h_lt_succ_n_zero | h_eq_succ_n_zero
        · -- Caso lt₀ (σ n) 𝟘.
            exact (nlt_n_0 (σ n) h_lt_succ_n_zero).elim
        · -- Caso σ n = 𝟘.
            exact (succ_neq_zero n h_eq_succ_n_zero).elim

    theorem  le_succ_0_then_false (n : ℕ₀) :
      le₀ (σ n) 𝟘 → False
        := by
        intro h_le_succ_n_zero -- h_le_succ_n_zero : le₀ (σ n) 𝟘
        unfold le₀ at h_le_succ_n_zero
        rcases h_le_succ_n_zero with h_lt_succ_n_zero | h_eq_succ_n_zero
        · -- Caso lt₀ (σ n) 𝟘.
            exact (nlt_n_0 (σ n) h_lt_succ_n_zero).elim
        · -- Caso σ n = 𝟘.
            exact (succ_neq_zero n h_eq_succ_n_zero).elim

    theorem le_1_0_then_false :
      le₀ 𝟙 𝟘 → False
        := by exact le_succ_0_then_false 𝟘

    theorem le_succ_iff_le_or_eq (a b : ℕ₀) :
      le₀ a (σ b) ↔ le₀ a b ∨ a = σ b
        := by
          constructor
          · intro h_le
            induction b with
            | zero =>
              have equiv_calc : le₀ a (σ 𝟘) ↔ (a = 𝟘 ∨ a = 𝟙) := calc
                le₀ a (σ 𝟘) ↔ le₀ a 𝟙 := by rfl
                _ ↔ lt₀ a 𝟙 ∨ a = 𝟙 := by rfl
                _ ↔ (a = 𝟘 ∨ a = 𝟙) := by
                  constructor
                  · intro h_lt_or_eq_one
                    cases h_lt_or_eq_one with
                    | inl h_a_lt_one =>
                      apply Or.inl
                      cases
                          (
                            lt_succ_iff_lt_or_eq a 𝟘
                          ).mp h_a_lt_one with
                      | inl h_lt_a_zero =>
                        exfalso
                        exact lt_zero a h_lt_a_zero
                      | inr h_a_eq_zero =>
                        exact h_a_eq_zero
                    | inr h_a_eq_one =>
                      exact Or.inr h_a_eq_one
                  · intro h_zero_or_one
                    cases h_zero_or_one with
                    | inl h_a_eq_zero => -- Caso: a = 𝟘
                      rw [h_a_eq_zero] -- Sustituimos a por 𝟘
                      exact Or.inl (lt_succ_self 𝟘)
                    | inr h_a_eq_one => -- Caso: a = 𝟙
                      rw [h_a_eq_one] -- Sustituimos a por 𝟙
                      exact Or.inr (Eq.refl 𝟙)
              cases equiv_calc.mp h_le with
              | inl h_a_eq_zero => -- Caso: a = 𝟘
                rw [h_a_eq_zero]
                -- Sustituimos a por 𝟘 en el objetivo.
                exact Or.inl (le_refl 𝟘)
              | inr h_a_eq_one => -- Caso: a = 𝟙 (que es σ 𝟘)
                rw [h_a_eq_one]
                exact Or.inr (Eq.refl (σ 𝟘))
            | succ b' ih =>
              cases h_le with
              | inl h_lt_a_ssb' =>
                have h_choices
                    :=
                        (
                          lt_succ_iff_lt_or_eq a (σ b')
                        ).mp h_lt_a_ssb'
                cases h_choices with
                | inl h_lt_a_sb' =>
                  exact Or.inl (Or.inl h_lt_a_sb')
                | inr h_a_eq_sb' =>
                  exact Or.inl
                      (h_a_eq_sb' ▸
                          (Or.inr rfl : le₀ (σ b') (σ b'))
                      )
              | inr h_a_eq_ssb' =>
                exact Or.inr h_a_eq_ssb'
          · intro h
            cases h with
            | inl h_a_le_b' =>
              exact le_trans a b (σ b) h_a_le_b' (le_succ_self b)
            | inr h_a_eq_succ_b =>
              rw [h_a_eq_succ_b]
              exact (le_refl (σ b))

    theorem le_succ_then_le_or_eq (a b : ℕ₀) :
      le₀ a (σ b) → le₀ a b ∨ a = σ b
        := by
        intro h_le_succ
        unfold le₀ at h_le_succ
        rcases h_le_succ with h_lt_succ | h_eq_succ
        · -- Caso lt₀ a (σ b).
          apply Or.inl
          exact (le_iff_lt_succ a b).mpr h_lt_succ
        · -- Caso a = σ b.
          apply Or.inr
          exact h_eq_succ ▸ rfl

    theorem le_or_eq_then_le_succ (a b : ℕ₀) :
      le₀ a b ∨ a = σ b → le₀ a (σ b)
        := by
        intro h_le_or_eq
        unfold le₀ at h_le_or_eq
        rcases h_le_or_eq with h_lt_or_eq | h_eq_or_eq
        · -- Caso lt₀ a b ∨ a = b.
          apply Or.inl
          cases h_lt_or_eq with
          | inl h_lt_ab => exact lt_trans a b (σ b) h_lt_ab (lt_self_σ_self b)
          | inr h_eq_ab => rw [h_eq_ab]; exact lt_self_σ_self b
        . -- Caso a = b.
          apply Or.inr
          exact h_eq_or_eq ▸ rfl



    theorem isomorph_Ψ_le (n m : ℕ₀) :
      Ψ n ≤ Ψ m ↔ le₀ n m
      := by
      constructor
      · -- Dirección →: (Ψ n ≤ Ψ m) → le₀ n m
        intro h_psi_le_psi_m -- h_psi_le_psi_m : Ψ n ≤ Ψ m
        rw [Nat.le_iff_lt_or_eq] at h_psi_le_psi_m
        cases h_psi_le_psi_m with
        | inl h_psi_lt_psi_m => -- Caso Ψ n < Ψ m
          apply Or.inl
          exact (isomorph_Ψ_lt n m).mpr h_psi_lt_psi_m
        | inr h_psi_eq_psi_m => -- Caso Ψ n = Ψ m
          apply Or.inr
          exact (Ψ_inj n m h_psi_eq_psi_m)
      · -- Dirección ←: le₀ n m → (Ψ n ≤ Ψ m)
        intro h_le_nm -- h_le_nm : le₀ n m
        cases h_le_nm with
        | inl h_lt_nm => -- Caso lt₀ n m
          have h_psi_lt_psi_m : Ψ n < Ψ m
              := (isomorph_Ψ_lt n m).mp h_lt_nm
          exact Nat.le_of_lt h_psi_lt_psi_m
        | inr h_eq_nm => -- Caso n = m
          rw [h_eq_nm]
          exact Nat.le_refl (Ψ m)

    theorem isomorph_Λ_le (n m : Nat) :
      n ≤ m ↔ le₀ (Λ n) (Λ m)
      := by
      constructor
      · -- Dirección →: n ≤ m → le₀ (Λ n) (Λ m)
        intro h_nat_le -- h_nat_le : n ≤ m
        rw [Nat.le_iff_lt_or_eq] at h_nat_le
        cases h_nat_le with
        | inl h_lt_nm => -- Caso n < m
          apply Or.inl
          exact (
            isomorph_Ψ_lt (Λ n) (Λ m)
          ).mpr (by {
                have h_nat_lt : n < m := h_lt_nm
                have h_psi_eq_n : Ψ (Λ n) = n := ΨΛ n
                have h_psi_eq_m : Ψ (Λ m) = m := ΨΛ m
                rw [h_psi_eq_n, h_psi_eq_m]
                exact h_nat_lt
              }
            )
        | inr h_eq_nm => -- Caso n = m
          apply Or.inr -- El objetivo es ahora Λ n = Λ m.
          rw [h_eq_nm] -- El objetivo se convierte en Λ m = Λ m.
      · -- Dirección ←: le₀ (Λ n) (Λ m) → n ≤ m
        intro h_le_Λn_Λm
        cases h_le_Λn_Λm with
        | inl h_lt_Λn_Λm => -- Caso lt₀ (Λ n) (Λ m)
          have h_psi_lt_psi_m : Ψ (Λ n) < Ψ (Λ m)
              := (isomorph_Ψ_lt (Λ n) (Λ m)).mp h_lt_Λn_Λm
          rw [ΨΛ, ΨΛ] at h_psi_lt_psi_m
          exact Nat.le_of_lt h_psi_lt_psi_m
        | inr h_eq_Λn_Λm => -- Caso Λ n = Λ m
          have h_n_eq_m : n = m := by
            have h_psi_eq :
                Ψ (Λ n) = Ψ (Λ m)
                    := by rw [h_eq_Λn_Λm]
            rwa [ΨΛ, ΨΛ] at h_psi_eq
          rw [h_n_eq_m] -- El objetivo se convierte en m ≤ m.
          exact Nat.le_refl m

    instance : LE ℕ₀ := ⟨le₀⟩

    theorem lt_of_le_of_ne (a b : ℕ₀) :
      le₀ a b → a ≠ b → lt₀ a b
        := by
          intro h_le h_neq
          cases h_le with
          | inl h_lt => exact h_lt
          | inr h_eq => contradiction

    theorem lt_iff_le_not_le (a b : ℕ₀) :
      lt₀ a b ↔ le₀ a b ∧ ¬le₀ b a
        := by
          constructor
          · intro h_lt
            constructor
            · exact lt_imp_le a b h_lt
            · intro h_contra
              have h_eq_or_lt := h_contra
              cases h_eq_or_lt with
              | inl h_lt_ba => exact lt_asymm a b h_lt h_lt_ba
              | inr h_eq_ba =>
                rw [h_eq_ba] at h_lt
                exact lt_irrefl a h_lt
          · intro ⟨h_le_ab, h_not_le_ba⟩
            exact lt_of_le_neq a b h_le_ab (fun h_eq =>
              h_not_le_ba (h_eq ▸ le_refl b))

    theorem lt_succ_iff_lt_or_eq_alt (a b : ℕ₀) :
      lt₀ a (σ b) ↔ le₀ a b
        := by
          constructor
          · intro h_lt_a_ssb
            unfold lt₀ at h_lt_a_ssb
            -- Ahora procedemos por casos en a y b
            cases a with
            | zero =>
              cases b with
              | zero =>
                -- lt₀ 𝟘 (σ 𝟘) → le₀ 𝟘 𝟘
                exact le_refl 𝟘
              | succ b' =>
                -- lt₀ 𝟘 (σ (σ b')) → le₀ 𝟘 (σ b')
                exact zero_le (σ b')
            | succ a' =>
              cases b with
              | zero =>
                -- lt₀ (σ a') (σ 𝟘) → le₀ (σ a') 𝟘
                -- Esto es una contradicción por la definición de lt₀
                simp [lt₀] at h_lt_a_ssb
              | succ b' =>
                -- lt₀ (σ a') (σ (σ b')) → le₀ (σ a') (σ b')
                simp at h_lt_a_ssb
                have h_lt_a'_sb' : lt₀ a' (σ b') := h_lt_a_ssb
                have h_le_a'_b' : le₀ a' b' := (le_iff_lt_succ a' b').mpr h_lt_a'_sb'
                exact (succ_le_succ_iff a' b').mpr h_le_a'_b'
          · intro h_le_ab
            exact (le_iff_lt_succ a b).mp h_le_ab

    theorem le_succ_iff_le_or_eq_alt (n m : ℕ₀) :
      le₀ n (σ m) ↔ le₀ n m ∨ n = σ m
        := by
          constructor
          · intro h_le_n_sm
            cases h_le_n_sm with
            | inl h_lt_nm =>
              have h_le_or_eq := (lt_succ_iff_lt_or_eq_alt n m).mp h_lt_nm
              exact Or.inl h_le_or_eq
            | inr h_eq_nm =>
              exact Or.inr h_eq_nm
          · intro h_or
            cases h_or with
            | inl h_le_nm =>
              exact le_succ n m h_le_nm
            | inr h_a_eq_succ_b =>
              rw [h_a_eq_succ_b]
              exact (le_refl (σ m))

    theorem le_of_succ_le_succ (n m : ℕ₀) :
      le₀ (σ n) (σ m) → le₀ n m
        := by
          intro h_le_ss
          unfold le₀ at *
          rcases h_le_ss with h_lt_ss | h_eq_ss
          · -- Caso lt₀ (σ n) (σ m)
            apply Or.inl
            exact (lt_iff_lt_σ_σ n m).mpr h_lt_ss
          · -- Caso σ n = σ m
            apply Or.inr
            exact ℕ₀.succ.inj h_eq_ss

      theorem nle_iff_gt (n m : ℕ₀) :
        ¬(le₀ n m) ↔ (lt₀ m n)
        := by
        calc
          ¬(le₀ n m) ↔ ¬(lt₀ n m ∨ n = m) := by
            rw [le₀]
          _ ↔ ¬(lt₀ n m) ∧ ¬(n = m) := by
            rw [not_or]
          _ ↔ ((lt₀ m n) ∨ (n = m)) ∧ ¬(n = m) := by
            rw [lt_or_eq_iff_nltc]
          _ ↔ (lt₀ m n ∧ ¬(n = m)) ∨ (n = m ∧ ¬(n = m)) := by
            rw [or_and_right]
          _ ↔ (lt₀ m n) ∧ ¬(n = m) := by
            simp [and_not_self]
          _ ↔ (lt₀ m n) := by
            constructor
            · exact And.left
            · intro h_lt
              exact ⟨h_lt, (ne_of_lt m n h_lt).symm⟩

    theorem nle_then_gt (n m : ℕ₀) :
      ¬(le₀ n m) → lt₀ m n
        := by
          intro h_nle_m
          rw [nle_iff_gt] at h_nle_m
          exact h_nle_m

    theorem nle_then_gt_wp {n m : ℕ₀} (h_nle : ¬(le₀ n m)) :
      lt₀ m n
        := by
          exact nle_then_gt n m h_nle

    theorem gt_then_nle (n m : ℕ₀) :
      lt₀ n m → ¬(le₀ m n)
        := by
          intro h_lt_m
          rw [← nle_iff_gt m n] at h_lt_m
          exact h_lt_m

    theorem gt_then_nle_wp {n m : ℕ₀} (h_nle : lt₀ n m) :
      ¬ le₀ m n
        := by
          exact gt_then_nle n m h_nle

    theorem le_1_m_then_m_neq_0 (m : ℕ₀) :
      le₀ 𝟙 m → m ≠ 𝟘
        := by
          intro h_le_1_m
          unfold le₀ at h_le_1_m
          cases m with
          | zero =>
            rcases h_le_1_m with h_lt_1_0 | h_eq_1_0
            · exact (nlt_n_0 𝟙 h_lt_1_0).elim
            · exact (succ_neq_zero 𝟘 h_eq_1_0).elim
          | succ m' =>
            exact succ_neq_zero m'

    theorem le_1_m_then_m_neq_0_wp {m : ℕ₀} (h_le_1: le₀ 𝟙 m) :
        m ≠ 𝟘
            := by
        exact le_1_m_then_m_neq_0 m h_le_1

    theorem m_neq_0_proved_lt_1_m {m : ℕ₀} (h : le₀ 𝟙 m) :
      m ≠ 𝟘
      := by
          intro h_m_eq_0
          rw [h_m_eq_0] at h
          have h_one_eq_zero : 𝟙 = 𝟘 := le_zero_eq 𝟙 h
          exact absurd h_one_eq_zero (succ_neq_zero 𝟘)

    theorem le_m_1_then_m_eq_0or1_wp {m : ℕ₀} (h : le₀ m 𝟙) :
      m = 𝟘 ∨ m = 𝟙
        := by
          unfold le₀ at h
          cases m with
          | zero =>
            exact Or.inl rfl
          | succ m' =>
            -- le₀ (σ m') 𝟙 implies σ m' = 𝟙 which means m' = 𝟘
            rcases h with h_lt | h_eq
            · -- Case lt₀ (σ m') 𝟙
              -- Since 𝟙 = σ 𝟘, we have lt₀ (σ m') (σ 𝟘)
              -- This implies lt₀ m' 𝟘, which is impossible
              have h_lt_m_zero : lt₀ m' 𝟘 := (lt_iff_lt_σ_σ m' 𝟘).mpr h_lt
              exact (nlt_n_0 m' h_lt_m_zero).elim
            · -- Case σ m' = 𝟙
              -- Since 𝟙 = σ 𝟘, we have σ m' = σ 𝟘, so m' = 𝟘
              have h_m_eq_zero : m' = 𝟘 := ℕ₀.succ.inj h_eq
              exact Or.inr (h_m_eq_zero ▸ rfl)

    theorem le_n_m_then_m_neq_0 (n m : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) :
      (le₀ n m) → (m ≠ 𝟘)
        := by
          intro h_le_n_m
          rcases h_le_n_m with h_lt_nm | h_eq_nm
          · -- Caso lt₀ n m
            unfold lt₀ at h_lt_nm
            cases n with
            | zero =>
              -- lt₀ 𝟘 m es válido cuando m ≠ 𝟘, no es contradicción
              cases m with
              | zero => exact (nlt_n_0 𝟘 h_lt_nm).elim
              | succ m' => exact succ_neq_zero m'
            | succ n' =>
              cases m with
              | zero => exact (nlt_n_0 (σ n') h_lt_nm).elim
              | succ m' => exact succ_neq_zero m'
          · -- Caso n = m
            exact (h_eq_nm.symm ▸ h_n_neq_0)

    theorem le_n_m_n_neq_0_then_m_neq_0 (n m : ℕ₀) :
      (le₀ n m)∧(n ≠ 𝟘) → (m ≠ 𝟘)
        := by
          intro h_le_n_m_and_n_neq_0
          rcases h_le_n_m_and_n_neq_0 with ⟨h_le_n_m, h_n_neq_0⟩
          exact le_n_m_then_m_neq_0 n m h_n_neq_0 h_le_n_m

    theorem m_neq_0_proved_lt_1_m_wp {m : ℕ₀} (h : le₀ 𝟙 m) :
      m ≠ 𝟘
      := by
          intro h_m_eq_0
          rw [h_m_eq_0] at h
          have h_one_eq_zero : 𝟙 = 𝟘 := le_zero_eq 𝟙 h
          exact absurd h_one_eq_zero (succ_neq_zero 𝟘)

    theorem le_0_succ_then_lt_0_succ (n : ℕ₀) :
      le₀ 𝟘 (σ n) → lt₀ 𝟘 (σ n)
        := by
          intro h_le_0_sn
          unfold le₀ at h_le_0_sn
          cases h_le_0_sn with
          | inl h_lt_0_sn =>
            exact h_lt_0_sn
          | inr h_eq_0_sn =>
            exfalso
            exact succ_neq_zero n h_eq_0_sn.symm

    theorem le_0_succ_then_lt_0_succ_wp {n : ℕ₀} (h_le : le₀ 𝟘 (σ n)) :
      lt₀ 𝟘 (σ n)
        := by
          exact le_0_succ_then_lt_0_succ n h_le

    theorem lt_0_succ_then_le_0_succ (n : ℕ₀) :
      lt₀ 𝟘 (σ n) → le₀ 𝟘 (σ n)
        := by
          intro h_lt_0_sn
          unfold le₀
          exact Or.inl h_lt_0_sn

    theorem lt_0_succ_then_le_0_succ_wp {n : ℕ₀} (h_lt : lt₀ 𝟘 (σ n)) :
      le₀ 𝟘 (σ n)
        := by
          exact lt_0_succ_then_le_0_succ n h_lt

    theorem le_0_succ_iff_lt_0_succ (n : ℕ₀) :
      le₀ 𝟘 (σ n) ↔ lt₀ 𝟘 (σ n)
        := by
          constructor
          · intro h_le_0_sn
            cases h_le_0_sn with
            | inl h_lt_0_sn =>
              exact h_lt_0_sn
            | inr h_eq_0_sn =>
              exfalso
              exact succ_neq_zero n h_eq_0_sn.symm
          · intro h_lt_0_succ_n
            exact lt_imp_le 𝟘 (σ n) h_lt_0_succ_n

    theorem le_then_lt_succ (n m : ℕ₀) :
      le₀ n m → lt₀ n (σ m)
        := by
          intro h_le_nm
          unfold le₀ at h_le_nm
          rcases h_le_nm with h_lt_nm | h_eq_nm
          · -- Caso lt₀ n m
            exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
          · -- Caso n = m
            rw [h_eq_nm]
            exact lt_self_σ_self m

    theorem le_then_lt_succ_wp {n m : ℕ₀} (h_le : le₀ n m) :
      lt₀ n (σ m)
        := by
          exact le_then_lt_succ n m h_le


    theorem le_succ_then_le_or_eq_wp {n m : ℕ₀} (h_le : le₀ n (σ m)) :
      le₀ n m ∨ n = σ m
        := by
          exact le_succ_then_le_or_eq n m h_le

    theorem le_or_eq_then_le_succ_wp {n m : ℕ₀}
        (h_le_or_eq_succ : le₀ n m ∨ n = σ m) :
      le₀ n (σ m)
        := by
          exact le_or_eq_then_le_succ n m h_le_or_eq_succ

    theorem le_succ_k_n_then_le_k_n {n k : ℕ₀} :
      le₀ (σ k) n → le₀ k n
        := by
          intro h_le_ssn
          unfold le₀ at h_le_ssn
          rcases h_le_ssn with h_lt_ssn | h_eq_ssn
          · -- Caso lt₀ (σ k) n
            apply Or.inl
            cases n with
            | zero => exfalso; exact (nlt_n_0 (σ k) h_lt_ssn).elim
            | succ m => -- n = σ m. h_lt_ssn becomes lt₀ (σ k) (σ m)
              -- Goal: lt₀ k (σ m)
              have h_lt_k_m : lt₀ k m := (lt_iff_lt_σ_σ k m).mpr h_lt_ssn
              exact lt_trans k m (σ m) h_lt_k_m (lt_self_σ_self m)
          · -- Caso σ k = n. Here h_eq_ssn : σ k = n.
            apply Or.inl
            rw [← h_eq_ssn]
            exact lt_self_σ_self k

    theorem lt_k_succ_n_then_le_k_n {n k : ℕ₀} :
      lt₀ k (σ n) → le₀ k n
        := by
          intro h_lt_k_sn
          unfold lt₀ at h_lt_k_sn
          cases k with
          | zero =>
            cases n with
            | zero => exact le_refl 𝟘
            | succ n' => exact zero_le (σ n')
          | succ k' =>
            cases n with
            | zero =>
              simp [lt₀] at h_lt_k_sn
            | succ n' =>
              have h_lt_k'_sn' : lt₀ k' (σ n') := h_lt_k_sn
              have h_le_k'_n' : le₀ k' n' := (le_iff_lt_succ k' n').mpr h_lt_k'_sn'
              rcases h_le_k'_n' with h_lt_k'_n' | h_eq_k'_n'
              · -- Caso lt₀ k' n'
                apply Or.inl
                exact (lt_iff_lt_σ_σ k' n').mpr h_lt_k'_n'
              · -- Caso k' = n'. Entonces σ k' = σ n'.
                apply Or.inr
                rw [h_eq_k'_n']

    theorem lt_k_succ_n_then_le_k_n_wp {n k : ℕ₀} (h_lt_k_sn : lt₀ k (σ n)):
      le₀ k n
        := by
          exact lt_k_succ_n_then_le_k_n h_lt_k_sn

    theorem le_succ_k_n_then_lt_k_n {n k : ℕ₀} :
      le₀ (σ k) n → lt₀ k n
        := by
          intro h_le_ssn
          unfold le₀ at h_le_ssn
          rcases h_le_ssn with h_lt_ssn | h_eq_ssn
          · -- Caso lt₀ (σ k) n
            cases n with
            | zero => exfalso; exact (nlt_n_0 (σ k) h_lt_ssn).elim
            | succ m => -- n = σ m. h_lt_ssn becomes lt₀ (σ k) (σ m)
              -- Goal: lt₀ k (σ m)
              have h_lt_k_m : lt₀ k m := (lt_iff_lt_σ_σ k m).mpr h_lt_ssn
              exact lt_trans k m (σ m) h_lt_k_m (lt_self_σ_self m)
          · -- Caso σ k = n. Here h_eq_ssn : σ k = n.
            rw [← h_eq_ssn]
            exact lt_self_σ_self k

    theorem le_succ_k_n_then_lt_k_n_wp {n k : ℕ₀} (h_le_sk_n: le₀ (σ k) n):
      lt₀ k n
        := by
          exact le_succ_k_n_then_lt_k_n h_le_sk_n

    theorem le_succ_then_le {n k : ℕ₀} :
      le₀ (σ k) n → le₀ k n
        := by
          intro h_le_ssn
          unfold le₀ at h_le_ssn
          rcases h_le_ssn with h_lt_ssn | h_eq_ssn
          · -- Caso lt₀ (σ k) n
            apply Or.inl
            cases n with
            | zero => exfalso; exact (nlt_n_0 (σ k) h_lt_ssn).elim
            | succ m => -- n = σ m. h_lt_ssn becomes lt₀ (σ k) (σ m)
              -- Goal: lt₀ k (σ m)
              have h_lt_k_m : lt₀ k m := (lt_iff_lt_σ_σ k m).mpr h_lt_ssn
              exact lt_trans k m (σ m) h_lt_k_m (lt_self_σ_self m)
          · -- Caso σ k = n. Here h_eq_ssn : σ k = n.
            apply Or.inl
            rw [← h_eq_ssn]
            exact lt_self_σ_self k

    theorem le_succ_then_le_wp {n k : ℕ₀} (le_sk_n: le₀ (σ k) n) :
      le₀ k n
        := by
      exact le_succ_then_le le_sk_n

    theorem le_k_n_then_le_k_sn_wp {n k : ℕ₀} (h_le_k_n : le₀ k n):
      le₀ k (σ n)
        := by
          exact le_succ k n h_le_k_n

    theorem le_n_m_then_le_n_sm (n m : ℕ₀) :
      le₀ n m → le₀ n (σ m)
        := by
          intro h_le_nm
          unfold le₀ at h_le_nm
          rcases h_le_nm with h_lt_nm | h_eq_nm
          · -- Caso lt₀ n m
            apply Or.inl
            have h_lt_n_m : lt₀ n m := (lt_iff_lt_σ_σ n m).mpr h_lt_nm
            exact lt_trans n m (σ m) h_lt_n_m (lt_self_σ_self m)
          · -- Caso n = m
            apply Or.inl
            rw [h_eq_nm]
            exact lt_self_σ_self m

    theorem le_n_m_then_le_n_sm_wp  {n m : ℕ₀} (h_le_nm : le₀ n m) :
      le₀ n (σ m)
        := by
          exact le_n_m_then_le_n_sm n m h_le_nm

    theorem le_sn_m_then_le_n_m_or_succ (n m : ℕ₀) :
      le₀ (σ n) m → le₀ n m
        := by
          intro h_le_sn_m
          unfold le₀ at h_le_sn_m
          rcases h_le_sn_m with h_lt_sn_m | h_eq_sn_m
          · -- Caso lt₀ (σ n) m
            apply Or.inl
            cases m with
            | zero => exfalso; exact (nlt_n_0 (σ n) h_lt_sn_m).elim
            | succ m' =>
              have h_lt_n_m' : lt₀ n m' := (lt_iff_lt_σ_σ n m').mpr h_lt_sn_m
              exact lt_trans n m' (σ m') h_lt_n_m' (lt_self_σ_self m')
          · -- Caso σ n = m
            apply Or.inl
            rw [← h_eq_sn_m]
            exact lt_self_σ_self n

    theorem le_sn_m_then_le_n_m_or_succ_wp {n m : ℕ₀} (h_le_sn_m : le₀ (σ n) m) :
      le₀ n m
        := by
          exact le_sn_m_then_le_n_m_or_succ n m h_le_sn_m

    theorem le_then_lt_or_eq (n m : ℕ₀) :
      n ≤ m → (lt₀ n m) ∨ (n = m)
        := by
          intro h_le_nm
          exact h_le_nm

    theorem le_not_lt {a b : ℕ₀} (h_le : le₀ a b) :
      ¬(lt₀ b a)
      := by
        intro h_lt_ba
        have h_not_le_ab : ¬le₀ a b := gt_then_nle b a h_lt_ba
        exact h_not_le_ab h_le


    theorem nle_σn_n (n : ℕ₀) :
      ¬(le₀ (σ n) n)
        := by
        intro h_le_sn_n
        unfold le₀ at h_le_sn_n
        rcases h_le_sn_n with h_lt_sn_n | h_eq_sn_n
        · exact (lt_asymm n (σ n) (lt_self_σ_self n) h_lt_sn_n)
        · exact (lt_irrefl n (cast (congrArg (lt₀ n) h_eq_sn_n) (lt_self_σ_self n)))

    theorem le_σn_n_then_false (n : ℕ₀) :
      le₀ (σ n) n → False
        := by
        intro h_le_sn_n
        have h_nle_sn_n : ¬(le₀ (σ n) n) := nle_σn_n n
        exact h_nle_sn_n h_le_sn_n

    theorem lt_0n_then_le_1n (n : ℕ₀) :
      lt₀ 𝟘 n → le₀ 𝟙 n
        := by
          intro h_lt_0n
          unfold lt₀ at h_lt_0n
          cases n with
          | zero =>
            exact (nlt_n_0 𝟘 h_lt_0n).elim
          | succ n' =>
            rw [one]
            exact (succ_le_succ_iff 𝟘 n').mpr (zero_le n')

    theorem lt_0n_then_le_1n_wp {n : ℕ₀} (h_lt_0n : lt₀ 𝟘 n):
      le₀ 𝟙 n
        := by
          exact lt_0n_then_le_1n n h_lt_0n

    theorem lt_nm_then_le_nm (n m: ℕ₀):
      lt₀ n m → le₀ (σ n) m
        := by
          intro h_lt_nm
          cases n with
          | zero =>
            cases m with
            | zero => contradiction
            | succ m' => exact succ_le_succ_if (zero_le m')
          | succ n' =>
            cases m with
            | zero => contradiction
            | succ m' =>
              have h_le_sn'_m' : le₀ (σ n') m' := (lt_succ_iff_lt_or_eq_alt (σ n') m').mp h_lt_nm
              exact succ_le_succ_if h_le_sn'_m'

    theorem lt_nm_then_le_nm_wp {n m: ℕ₀} (h_lt_nm : lt₀ n m) :
      le₀ (σ n) m
        := by
          exact lt_nm_then_le_nm n m h_lt_nm

    theorem le_then_ngt (n m : ℕ₀) :
      le₀ n m → ¬(lt₀ m n)
        := by
        intro h_le_nm
        intro h_lt_mn
        have h_nle_m : ¬(le₀ n m) := gt_then_nle m n h_lt_mn
        exact h_nle_m h_le_nm

    theorem le_then_ngt_wp {n m : ℕ₀} (h_le_nm : le₀ n m) :
      ¬(lt₀ m n)
        := by
      exact le_then_ngt n m h_le_nm

    theorem ngt_then_le (n m : ℕ₀) :
      ¬ le₀ n m → lt₀ m n
        := by
        intro h_nle_nm
        exact nle_then_gt n m h_nle_nm

    theorem ngt_then_le_wp {n m : ℕ₀} (h_ngt_nm : ¬(le₀ n m)) :
      lt₀ m n
        := by
      exact ngt_then_le n m h_ngt_nm

    theorem le_succ_then_lt (n m : ℕ₀) :
      le₀ (σ n) m → lt₀ n m
        := by
          intro h_le_sn_m
          unfold le₀ at h_le_sn_m
          rcases h_le_sn_m with h_lt_sn_m | h_eq_sn_m
          · -- Caso lt₀ (σ n) m
            cases m with
            | zero =>
              exfalso
              exact (nlt_n_0 (σ n) h_lt_sn_m).elim
            | succ m' =>
              have h_lt_n_m' : lt₀ n m' := (lt_iff_lt_σ_σ n m').mp h_lt_sn_m
              exact lt_trans n m' (σ m') h_lt_n_m' (lt_self_σ_self m')
          · -- Caso σ n = m
            rw [← h_eq_sn_m]
            exact lt_self_σ_self n

    theorem le_succ_then_lt_wp {n m : ℕ₀} (h_le_sn_m : le₀ (σ n) m) :
      lt₀ n m
        := by
          exact le_succ_then_lt n m h_le_sn_m

    theorem lt_then_le_succ_wp {n m : ℕ₀} (h_lt_nm : lt₀ n (σ m)) :
      le₀ n m
        := by
          unfold lt₀ at h_lt_nm
          cases n with
          | zero =>
            cases m with
            | zero => exact le_refl 𝟘
            | succ m' => exact zero_le (σ m')
          | succ n' =>
            cases m with
            | zero => exact (nlt_n_0 n' h_lt_nm).elim
            | succ m' =>
              have h_le_n'_m' : le₀ n' m' := (le_iff_lt_succ n' m').mpr h_lt_nm
              exact (succ_le_succ_iff n' m').mpr h_le_n'_m'

    theorem lt_then_le_succ (n m : ℕ₀):
      lt₀ n (σ m) → le₀ n m
        := by
          intro h_lt_nm
          unfold lt₀ at h_lt_nm
          cases n with
          | zero =>
            cases m with
            | zero => exact le_refl 𝟘
            | succ m' => exact zero_le (σ m')
          | succ n'  =>
            cases m with
            | zero => exact (nlt_n_0 n' h_lt_nm).elim
            | succ m' =>
              have h_le_n'_m' : le₀ n' m' := (le_iff_lt_succ n' m').mpr h_lt_nm
              exact (succ_le_succ_iff n' m').mpr h_le_n'_m'


    theorem well_ordering_principle {P : ℕ₀ → Prop}
      (h_nonempty : ∃ n, P n) :
        ∃ n, P n ∧ ∀ m, lt₀ m n → ¬ P m
          := by
      let Q := fun (n : ℕ₀) => (∃ k, le₀ k n ∧ P k) → (∃ k, P k ∧ ∀ m, lt₀ m k → ¬ P m)
      have h_Q_n : ∀ n, Q n := by
        intro n
        induction n with
        | zero =>
          intro h_exists_le_zero
          cases h_exists_le_zero with | intro k hk =>
          have h_k_eq_zero : k = 𝟘 := le_zero_eq_wp hk.left
          exists 𝟘
          constructor
          · rw [←h_k_eq_zero]; exact hk.right
          · intro m hm_lt_zero
            exfalso
            exact lt_zero m hm_lt_zero
        | succ n' ih =>
          intro h_exists_le_succ
          cases h_exists_le_succ with
          | intro k hk =>
            cases hk.left with
            | inl h_k_lt_succ_n' =>
              have h_k_le_n' : le₀ k n' := lt_then_le_succ_wp h_k_lt_succ_n'
              apply ih
              exists k; exact ⟨h_k_le_n', hk.right⟩
            | inr h_k_eq_succ_n' =>
              by_cases h_exists_le_n' : (∃ k', le₀ k' n' ∧ P k')
              · exact ih h_exists_le_n'
              · exists (σ n')
                constructor
                · rw [←h_k_eq_succ_n']; exact hk.right
                · intro m hm_lt_succ_n'
                  have h_m_le_n' : le₀ m n' := lt_then_le_succ_wp hm_lt_succ_n'
                  intro h_P_m
                  exact h_exists_le_n' ⟨m, ⟨h_m_le_n', h_P_m⟩⟩
      cases h_nonempty with
      | intro j h_P_j =>
        have h_exists_le_j : ∃ k, le₀ k j ∧ P k := by
          exists j; exact ⟨le_refl j, h_P_j⟩
        exact (h_Q_n j) h_exists_le_j


    theorem ngt_iff_le {n m : ℕ₀} :
      ¬(lt₀ n m) ↔ le₀ m n
        := by
          constructor
          · intro h_nlt_nm
            -- We use trichotomy: either n < m, n = m, or m < n
            cases trichotomy n m with
            | inl h_lt_nm =>
                contradiction
            | inr h_cases =>
                cases h_cases with
                | inl h_eq_nm =>
                    rw [h_eq_nm]
                    exact le_refl m
                | inr h_lt_mn =>
                    exact Or.inl h_lt_mn
          · intro h_le_mn
            intro h_lt_nm
            have h_not_le_mn := gt_then_nle n m h_lt_nm
            contradiction

    theorem ngt_iff_le_wp {n m : ℕ₀} (h_ngt : ¬(lt₀ n m)) :
      le₀ m n
        := by
          exact ngt_iff_le.mp h_ngt

    theorem le_succ_trans {k l' : ℕ₀} (h : le₀ k l') :
        le₀ (σ k) (σ l')
            := by
      cases h with
      | inl h_lt =>
        -- Si k < l', entonces σ k < σ l'
        exact lt_imp_le (σ k) (σ l') ((lt_iff_lt_σ_σ k l').mp h_lt)
      | inr h_eq =>
        -- Si k = l', entonces σ k = σ l'
        rw [h_eq]
        exact le_refl (σ l')

    theorem le_iff_lt_or_eq (a b : ℕ₀) : le₀ a b ↔ (lt₀ a b ∨ a = b) := by
      unfold le₀
      rfl

    theorem lt_pred_of_lt_succ {a b : ℕ₀} (h : lt₀ a (σ b)) : (le₀ a b) := by
      exact (le_iff_lt_succ a b).mpr h

    theorem lt_succ_iff_le (n m : ℕ₀) :
      lt₀ n (σ m) ↔ le₀ n m
      := by
        exact (le_iff_lt_succ n m).symm

    theorem nlt_of_le {a b : ℕ₀} (h : le₀ a b) :
      ¬lt₀ b a
        := by
          intro h_contra
          exact gt_then_nle_wp h_contra h

    theorem not_lt_and_not_eq_implies_gt (a b : ℕ₀) (h_not_lt : ¬ lt₀ a b) (h_not_eq : ¬ a = b) :
      lt₀ b a
        := by
      rcases trichotomy a b with hlt | heq | hgt
      · contradiction -- hlt contradicts h_not_lt
      · contradiction -- heq contradicts h_not_eq
      · exact hgt

    /-- Boolean bounded existential search: does `P k` hold for some `k ≤ n`? -/
    def bexLe (P : ℕ₀ → Bool) : ℕ₀ → Bool
      | .zero    => P 𝟘
      | .succ n' => P (σ n') || bexLe P n'

    /-- Helper: witness extraction from `bexLe`. -/
    theorem bexLe_true_imp_exists (P : ℕ₀ → Prop) (Pb : ℕ₀ → Bool)
        (h_iff : ∀ k, Pb k = true ↔ P k) :
        (n : ℕ₀) → bexLe Pb n = true → ∃ k, le₀ k n ∧ P k
      | .zero, h => ⟨𝟘, le_refl 𝟘, (h_iff 𝟘).mp h⟩
      | .succ n', h => by
        simp [bexLe, Bool.or_eq_true] at h
        rcases h with hp | hr
        · exact ⟨σ n', le_refl (σ n'), (h_iff (σ n')).mp hp⟩
        · obtain ⟨k, hk, hpk⟩ := bexLe_true_imp_exists P Pb h_iff n' hr
          exact ⟨k, le_k_n_then_le_k_sn_wp hk, hpk⟩

    /-- Helper: negation from `bexLe = false`. -/
    theorem bexLe_false_imp_not_exists (P : ℕ₀ → Prop) (Pb : ℕ₀ → Bool)
        (h_iff : ∀ k, Pb k = true ↔ P k) :
        (n : ℕ₀) → bexLe Pb n = false → ¬ ∃ k, le₀ k n ∧ P k
      | .zero, h, ⟨k, hle, hpk⟩ => by
        have hk0 := le_zero_eq_wp hle
        rw [hk0] at hpk
        exact Bool.false_ne_true (h ▸ (h_iff 𝟘).mpr hpk)
      | .succ n', h, ⟨k, hle, hpk⟩ => by
        have hbex : bexLe Pb (σ n') = false := h
        simp [bexLe] at hbex
        have ⟨h1, h2⟩ := hbex
        exact hle.elim
          (fun h_lt =>
            bexLe_false_imp_not_exists P Pb h_iff n' h2
              ⟨k, lt_then_le_succ_wp h_lt, hpk⟩)
          (fun h_eq => Bool.false_ne_true (h1 ▸ (h_iff (σ n')).mpr (h_eq ▸ hpk)))

    /-- Decidability of bounded existential: `∃ k, le₀ k n ∧ P k`,
        given a boolean decision function for `P`. -/
    def decidableBExLe_of_bool (P : ℕ₀ → Prop) (Pb : ℕ₀ → Bool)
        (h_iff : ∀ k, Pb k = true ↔ P k) (n : ℕ₀) :
        Decidable (∃ k, le₀ k n ∧ P k) :=
      if h : bexLe Pb n = true then
        isTrue (bexLe_true_imp_exists P Pb h_iff n h)
      else
        isFalse (bexLe_false_imp_not_exists P Pb h_iff n (Bool.eq_false_iff.mpr h))


    -- ══════════════════════════════════════════════════════════════════
    -- § lt_or_ge / le_or_lt
    -- ══════════════════════════════════════════════════════════════════

    theorem lt_or_ge (a b : ℕ₀) : lt₀ a b ∨ le₀ b a :=
      match trichotomy a b with
      | Or.inl h_lt => Or.inl h_lt
      | Or.inr (Or.inl h_eq) => Or.inr (Or.inr h_eq.symm)
      | Or.inr (Or.inr h_gt) => Or.inr (Or.inl h_gt)

    theorem le_or_lt (a b : ℕ₀) : le₀ a b ∨ lt₀ b a :=
      match trichotomy a b with
      | Or.inl h_lt => Or.inl (Or.inl h_lt)
      | Or.inr (Or.inl h_eq) => Or.inl (Or.inr h_eq)
      | Or.inr (Or.inr h_gt) => Or.inr h_gt

  end Order
end Peano

export Peano.Order (
  le₀ ge₀ le' ble₀ bge₀
  zero_le
  succ_le_succ_iff
  succ_le_succ_then
  Le_iff_le'
  bge_iff_Ge
  le_of_eq
  decidableLe decidableGe
  le_refl
  lt_imp_le
  le_trans
  le_antisymm
  le_total
  le_iff_lt_succ
  not_succ_le_zero
  lt_of_le_neq
  lt_of_le_neq_wp
  le_zero_eq
  isomorph_Ψ_le
  isomorph_Λ_le
  lt_of_le_of_ne
  le_succ_iff_le_or_eq
  lt_iff_le_not_le
  le_succ_iff_le_or_eq_alt
  le_of_succ_le_succ
  lt_succ_iff_lt_or_eq_alt
  nle_iff_gt
  nle_then_gt
  le_not_lt
  gt_then_nle
  gt_then_nle_wp
  le_1_m_then_m_neq_0
  le_n_m_then_m_neq_0
  le_n_m_n_neq_0_then_m_neq_0
  m_neq_0_proved_lt_1_m_wp
  m_neq_0_proved_lt_1_m
  nle_then_gt_wp
  le_then_le_succ
  le_0_succ_then_lt_0_succ_wp
  lt_0_succ_then_le_0_succ_wp
  le_0_succ_iff_lt_0_succ
  lt_0_succ_then_le_0_succ
  le_0_succ_then_lt_0_succ
  le_self_of_eq_self
  le_0_of_eq_0
  le_then_lt_succ
  le_then_lt_succ_wp
  succ_le_succ_iff_wp
  le_succ_then_le_or_eq
  le_or_eq_then_le_succ
  le_succ_then_le_or_eq_wp
  le_or_eq_then_le_succ_wp
  le_succ_k_n_then_le_k_n
  lt_k_succ_n_then_le_k_n
  lt_k_succ_n_then_le_k_n_wp
  le_k_n_then_le_k_sn_wp
  succ_le_succ_then_wp
  succ_le_succ'_then_wp
  le_n_m_then_le_n_sm
  le_n_m_then_le_n_sm_wp
  le_sn_m_then_le_n_m_or_succ
  le_sn_m_then_le_n_m_or_succ_wp
  le_then_lt_or_eq
  le_zero_eq_zero
  le_succ_zero_zero
  le_succ_0_then_false
  le_1_0_then_false
  le_1_succ
  le_of_eq_wp
  le_zero_eq_wp
  nle_σn_n
  le_σn_n_then_false
  succ_le_succ_if
  succ_le_succ_if_wp
  le_succ_k_n_then_lt_k_n
  le_succ_k_n_then_lt_k_n_wp
  lt_imp_le_wp
  le_succ_then_le
  le_succ_then_le_wp
  lt_0n_then_le_1n
  lt_0n_then_le_1n_wp
  lt_nm_then_le_nm
  lt_nm_then_le_nm_wp
  le_then_ngt
  le_then_ngt_wp
  ngt_then_le
  ngt_then_le_wp
  le_succ_then_lt
  le_succ_then_lt_wp
  lt_then_le_succ
  lt_then_le_succ_wp
  well_ordering_principle
  ngt_iff_le
  ngt_iff_le_wp
  le_succ_trans
  le_1_m_then_m_neq_0_wp
  le_iff_lt_or_eq
  lt_pred_of_lt_succ
  lt_succ_iff_le
  nlt_of_le
  not_lt_and_not_eq_implies_gt
  bexLe
  decidableBExLe_of_bool
  lt_or_ge
  le_or_lt
)
