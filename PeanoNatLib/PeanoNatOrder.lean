import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import Init.Prelude

namespace Peano
  open Peano

  namespace Order
      open Order
      open Peano.Axioms
      open Peano.StrictOrder
    /-- Definición de "menor o igual que" para ℕ₀. -/
    def Le (n m : ℕ₀) : Prop := Lt n m ∨ n = m
    def Ge (n m : ℕ₀) : Prop := Lt m n ∨ n = m

    /--
      Definición de "menor o igual que" para ℕ₀ utilizando
      recursión estructural. Demostraremos que Le y Le' son
      equivalentes.
    -/
    def Le' (n m : ℕ₀) : Prop :=
      match n, m with
      |   𝟘  ,   _  =>  True
      | σ _  ,   𝟘  =>  False
      | σ n' , σ m' =>  Le' n' m'

    theorem zero_le (n : ℕ₀) :
      Le 𝟘 n
      :=
      match n with
      | 𝟘    => Or.inr rfl
      | σ n' => Or.inl (lt_0_n (σ n') (succ_neq_zero n'))

    theorem succ_le_succ_iff (n m : ℕ₀) :
      Le (σ n) (σ m) ↔ Le n m
      := by
      constructor
      · intro h_le_succ
        unfold Le at *
        rcases h_le_succ with h_lt_succ | h_eq_succ
        · -- Lt (σ n) (σ m) => Lt n m => Le n m
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
        · -- σ n = σ m => n = m => Le n m
          apply Or.inr
          exact ℕ₀.succ.inj h_eq_succ
      · intro h_le
        unfold Le at *
        rcases h_le with h_lt | h_eq
        · -- Lt n m => Lt (σ n) (σ m) => Le (σ n) (σ m)
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mp h_lt
        · -- n = m => σ n = σ m => Le (σ n) (σ m)
          apply Or.inr
          exact h_eq ▸ rfl

    theorem succ_le_succ_iff_wp
           {n m : ℕ₀} (h_le_succ : Le (σ n) (σ m)) :
      Le n m
      := by
      -- Prueba de Le (σ n) (σ m) → Le n m
      unfold Le at *
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- Lt (σ n) (σ m) => Lt n m => Le n m
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
      · -- σ n = σ m => n = m => Le n m
        apply Or.inr
        exact ℕ₀.succ.inj h_eq_succ

    theorem succ_le_succ_then {n m : ℕ₀} :
      Le (σ n) (σ m) → Le n m
      := by
      intro h_le_succ
      unfold Le at *
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- Lt (σ n) (σ m) => Lt n m => Le n m
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
      · -- σ n = σ m => n = m => Le n m
        apply Or.inr
        exact ℕ₀.succ.inj h_eq_succ

    theorem succ_le_succ_then_wp {n m : ℕ₀} (h_le_succ : Le (σ n) (σ m)) :
      Le n m
      := by
      -- Prueba de Le (σ n) (σ m) → Le n m
      unfold Le at *
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- Lt (σ n) (σ m) => Lt n m => Le n m
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt_succ
      · -- σ n = σ m => n = m => Le n m
        apply Or.inr
        exact ℕ₀.succ.inj h_eq_succ

    theorem succ_le_succ'_then_wp {n m : ℕ₀} (h_le_succ : Le (σ n) (σ m)) :
      Le n (σ m)
      := by
      -- Prueba de Le (σ n) (σ m) → Le n (σ m)
      unfold Le at *
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- Lt (σ n) (σ m) => Lt n (σ m) => Le n (σ m)
        apply Or.inl
        have h_lt_n_m : Lt n m := (lt_iff_lt_σ_σ n m).mpr h_lt_succ
        exact lt_trans n m (σ m) h_lt_n_m (lt_self_σ_self m)
      · -- σ n = σ m => n = m => Le n (σ m)
        apply Or.inl
        have h_eq_n_m : n = m := ℕ₀.succ.inj h_eq_succ
        rw [h_eq_n_m]
        exact lt_self_σ_self m

    theorem le_then_le_succ {n m : ℕ₀} :
      Le n m → Le (σ n) (σ m)
      := by
      intro h_le
      unfold Le at *
      rcases h_le with h_lt | h_eq
      · -- Lt n m => Lt (σ n) (σ m) => Le (σ n) (σ m)
        apply Or.inl
        exact (lt_iff_lt_σ_σ n m).mpr h_lt
      · -- n = m => σ n = σ m => Le (σ n) (σ m)
        apply Or.inr
        exact h_eq ▸ rfl

    theorem Le_iff_Le' (n m : ℕ₀) :
      Le' n m ↔ Le n m
      := by
        constructor
        · -- Prueba de Le' n m → Le n m
          intro h_le'_nm
          induction n generalizing m with
          | zero => -- Caso n = 𝟘
            exact zero_le m
          | succ n' ih_n' => -- Caso n = σ n'
            cases m with
            | zero => -- Caso m = 𝟘
              exfalso; simp [Le'] at h_le'_nm
            | succ m' => -- Caso m = σ m'
              have h_le_n'_m' : Le n' m' := ih_n' m' h_le'_nm
              exact (succ_le_succ_iff n' m').mpr h_le_n'_m'
        · -- Prueba de Le n m → Le' n m
          intro h_le_nm
          induction n generalizing m with
          | zero => -- Caso n = 𝟘
            simp [Le']
          | succ n' ih_n' => -- Caso n = σ n'
            cases m with
            | zero => -- Caso m = 𝟘
              simp [Le'] -- El objetivo se convierte en False.
              rcases h_le_nm with h_lt | h_eq
              · exact (nlt_n_0 (σ n') h_lt).elim
              · exact (succ_neq_zero n' h_eq).elim
            | succ m' => -- Caso m = σ m'
              have h_le_n'_m' :
                  Le n' m'
                      :=
                      (
                        succ_le_succ_iff n' m'
                      ).mp h_le_nm
              simp [Le']
              exact ih_n' m' h_le_n'_m'

    /--
    Función de ayuda para Le con repuesta buleana
    -/
    def BLe (n m : ℕ₀) : Bool :=
      match n , m with
      | 𝟘 , _ => true
      | _ , 𝟘 => false
      | σ n' , σ m' => BLe n' m'

    /--
    Función de ayuda para Ge con repuesta buleana
    -/
    def BGe (n m : ℕ₀) : Bool :=
      match n , m with
      |   _    ,   𝟘  => true
      |   𝟘    ,   _  => false
      | σ n'   , σ m' => BGe n' m'

    theorem le_zero_eq (n : ℕ₀) :
      Le n 𝟘 → n = 𝟘
      := by
      intro h_le_n_zero
      unfold Le at h_le_n_zero
      rcases h_le_n_zero with h_lt_n_zero | h_eq_n_zero
      · -- Lt n 𝟘. Esto solo es posible si n no es sucesor,
        exact (nlt_n_0 n h_lt_n_zero).elim
      · -- n = 𝟘
        exact h_eq_n_zero

    theorem le_zero_eq_wp {n : ℕ₀} (h_le_n_zero : Le n 𝟘) :
      n = 𝟘
      := by
      unfold Le at h_le_n_zero
      rcases h_le_n_zero with h_lt_n_zero | h_eq_n_zero
      · -- Lt n 𝟘. Esto solo es posible si n no es sucesor,
        exact (nlt_n_0 n h_lt_n_zero).elim
      · -- n = 𝟘
        exact h_eq_n_zero

    theorem not_succ_le_zero (n : ℕ₀) :
      ¬Le (σ n) 𝟘
      := by
      intro h_contra
      unfold Le at h_contra
      cases h_contra with
      | inl h_lt => exact (nlt_n_0 (σ n) h_lt).elim
      | inr h_eq => exact (succ_neq_zero n h_eq).elim


    /--!
    -- El teorema BLe_iff_Le se mueve aquí porque se usa
    -- en decidableLe.
    !--/

  theorem BLe_iff_Le (n m : ℕ₀) :
    BLe n m = true ↔ Le n m
    := by
    constructor
    · intro h_ble_true
      induction n generalizing m with
      | zero => -- n = 𝟘. BLe 𝟘 m = true. Goal: Le 𝟘 m.
        rw [BLe] at h_ble_true -- Simplifica BLe 𝟘 m a true,   h_ble_true : true = true
        exact zero_le m
      | succ n' ih_n' => -- n = σ n'.
        cases m with
        | zero =>
          simp [BLe] at h_ble_true
        | succ m' =>
          simp [BLe] at h_ble_true
          have h_le_n'_m' : Le n' m' := ih_n' m' h_ble_true
          exact (succ_le_succ_iff n' m').mpr h_le_n'_m'
    · intro h_le_nm
      induction n generalizing m with
      | zero =>
        simp [BLe]
      | succ n' ih_n' => -- n = σ n'.
        cases m with
        | zero =>
          simp [BLe] -- El objetivo es ahora `false = true`.
          exact (not_succ_le_zero n' h_le_nm).elim
        | succ m' => -- m = σ m', n = σ n'. h_le_nm: Le (σ n')   (σ m').
          -- Goal: BLe (σ n') (σ m') = true, que es BLe n' m' =   true.
          -- IH: Le n' m' → BLe n' m' = true.
          simp [BLe] -- El objetivo es ahora BLe n' m' = true.
          apply ih_n'
          exact (succ_le_succ_iff n' m').mp h_le_nm

  instance decidableLe (n m : ℕ₀) :
    Decidable (Le n m)
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
    n = m → Le n m
      := by
        intro h_eq
        rw [h_eq]
        exact Or.inr rfl

  theorem le_of_eq_wp {n m : ℕ₀} (h_eq : n = m) :
    Le n m
      := by
        rw [h_eq]
        exact Or.inr rfl

  theorem le_self_of_eq_self (n : ℕ₀) :
    n = n → Le n n
      := by
        intro h_eq
        rw [h_eq]
        exact Or.inr rfl

  theorem le_0_of_eq_0 :
    𝟘 = 𝟘 → Le 𝟘 𝟘
    := by
    intro h_eq
    rw [h_eq]
    exact Or.inr rfl

theorem BGe_iff_Ge (n m : ℕ₀) :
    BGe n m = true ↔ Ge n m
    := by
    constructor
    · -- Dirección →: BGe n m = true → Ge n m
      intro h_bge_true
      unfold BGe at h_bge_true
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
          exact lt_0_n (σ n') (succ_neq_zero n')
        | succ m' =>
          have h_ge_n'_m' :
              Ge n' m' :=
                  (
                    BGe_iff_Ge n' m'
                  ).mp h_bge_true
          rcases h_ge_n'_m' with h_lt_m'_n' | h_eq_n'_m'
          · apply Or.inl
            exact (lt_iff_lt_σ_σ m' n').mp h_lt_m'_n'
          · apply Or.inr
            exact h_eq_n'_m' ▸ rfl
    · -- Dirección ←: Ge n m → BGe n m = true
      intro h_ge_nm
      induction n generalizing m with
      | zero =>
        cases m with
        | zero =>
          simp [BGe]
        | succ m' =>
          unfold Ge at h_ge_nm
          rcases h_ge_nm with h_lt_succ_zero | h_eq_zero_succ
          · exact (nlt_n_0 (σ m') h_lt_succ_zero).elim
          · exact (succ_neq_zero m' h_eq_zero_succ.symm).elim
      | succ n' ih =>
        cases m with
        | zero =>
          simp [BGe]
        | succ m' =>
          simp [BGe]
          apply ih
          unfold Ge at h_ge_nm ⊢
          rcases h_ge_nm with h_lt_succ_succ | h_eq_succ_succ
          · apply Or.inl
            exact (lt_iff_lt_σ_σ m' n').mpr h_lt_succ_succ
          · apply Or.inr
            exact ℕ₀.succ.inj h_eq_succ_succ

    instance decidableGe (n m : ℕ₀) :
      Decidable (Ge n m)
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
      Le n n
      :=
      Or.inr rfl

    theorem lt_imp_le (n m : ℕ₀) :
      Lt n m → Le n m
      :=
      fun h_lt => Or.inl h_lt

    theorem le_trans (n m k : ℕ₀) :
      Le n m → Le m k → Le n k
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
      Le n m → Le m n → n = m
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
      Le n m ∨ Le m n
      :=
      match trichotomy n m with
      | Or.inl h_lt_nm =>
          Or.inl (lt_imp_le n m h_lt_nm)
      | Or.inr (Or.inl h_eq_nm) =>
          Or.inl (Or.inr h_eq_nm)
      | Or.inr (Or.inr h_lt_mn) =>
          Or.inr (lt_imp_le m n h_lt_mn)

    theorem le_iff_lt_succ (n m : ℕ₀) :
      Le n m ↔ Lt n (σ m)
      := by
      constructor
      · intro h_le_nm
        rcases h_le_nm with h_lt_nm | h_eq_nm
        · -- Caso Lt n m. Queremos Lt n (σ m).
          exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
        · -- Caso n = m. Queremos Lt m (σ m).
          rw [h_eq_nm]
          exact lt_self_σ_self m
      · intro h_lt_n_succ_m -- Lt n (σ m). Queremos Le n m.
        revert n h_lt_n_succ_m
        induction m with
        | zero => -- m = 𝟘.
          intro n h_lt_n_succ_zero_case
          cases n with
          | zero =>
            exact Or.inr rfl
          | succ n' =>
            have h_lt_n_prime_zero :
                Lt n' 𝟘 :=
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
            have h_lt_n_prime_succ_m_prime : Lt n' (σ m') :=
              (lt_iff_lt_σ_σ n' (σ m')).mp h_lt_n_succ_sigma_m_prime_case
            have h_le_n_prime_m_prime : Le n' m'
                := ih_m' n' h_lt_n_prime_succ_m_prime
            rcases h_le_n_prime_m_prime with h_lt_n_p_m_p | h_eq_n_p_m_p
            · -- Caso Lt n' m'.
              apply Or.inl
              exact (lt_iff_lt_σ_σ n' m').mpr h_lt_n_p_m_p
            · -- Caso n' = m'. Entonces σ n' = σ m'.
              apply Or.inr
              rw [h_eq_n_p_m_p]

  theorem lt_of_le_neq (a b : ℕ₀) :
    Le a b → a ≠ b → Lt a b
      := by
        intro h_le h_neq
        cases h_le with
        | inl h_lt =>
          exact h_lt
        | inr h_eq =>
          exfalso
          exact h_neq h_eq

  theorem lt_of_le_neq_wp {a b : ℕ₀} (h_le_a_b : Le a b) (h_neq_a_b : a ≠ b) :
    Lt a b
      := by
      -- Prueba de Le a b → a ≠ b → Lt a b
      unfold Le at h_le_a_b
      rcases h_le_a_b with h_lt_a_b | h_eq_a_b
      · -- Caso Lt a b
        exact h_lt_a_b
      · -- Caso a = b
        exfalso
        exact h_neq_a_b h_eq_a_b

  theorem le_succ_self (n : ℕ₀) :
    Le n (σ n)
    := by
    unfold Le
    apply Or.inl
    exact lt_self_σ_self n

  theorem le_succ (n m : ℕ₀) :
      Le n m → Le n (σ m)
        := by
        intro h_le_nm
        unfold Le at *
        rcases h_le_nm with h_lt_nm | h_eq_nm
        · -- Caso Lt n m
          apply Or.inl
          exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
        · -- Caso n = m
          apply Or.inl
          rw [h_eq_nm]
          exact lt_self_σ_self m

  theorem le_1_succ (n : ℕ₀) :
    Le 𝟙 (σ n)
      := by
      exact le_then_le_succ (zero_le n)

  theorem le_zero_eq_zero (n : ℕ₀) :
    Le n 𝟘 ↔ n = 𝟘
      := by
    constructor
    · -- Dirección →: Le n 𝟘 → n = 𝟘
      intro h_le_n_zero -- h_le_n_zero : Le n 𝟘
      unfold Le at h_le_n_zero
      rcases h_le_n_zero with h_lt_n_zero | h_eq_n_zero
      · -- Caso Lt n 𝟘.
        exact (nlt_n_0 n h_lt_n_zero).elim
      · -- Caso n = 𝟘.
        exact h_eq_n_zero
    · -- Dirección ←: n = 𝟘 → Le n 𝟘
      intro h_eq_n_zero -- h_eq_n_zero : n = 𝟘
      rw [h_eq_n_zero]
      exact zero_le 𝟘

  theorem le_succ_zero_zero (n : ℕ₀) :
    Le (σ n) 𝟘 → False
      := by
      intro h_le_succ_n_zero -- h_le_succ_n_zero : Le (σ n) 𝟘
      unfold Le at h_le_succ_n_zero
      rcases h_le_succ_n_zero with h_lt_succ_n_zero | h_eq_succ_n_zero
      · -- Caso Lt (σ n) 𝟘.
          exact (nlt_n_0 (σ n) h_lt_succ_n_zero).elim
      · -- Caso σ n = 𝟘.
          exact (succ_neq_zero n h_eq_succ_n_zero).elim

  theorem  le_succ_0_then_false (n : ℕ₀) :
    Le (σ n) 𝟘 → False
      := by
      intro h_le_succ_n_zero -- h_le_succ_n_zero : Le (σ n) 𝟘
      unfold Le at h_le_succ_n_zero
      rcases h_le_succ_n_zero with h_lt_succ_n_zero | h_eq_succ_n_zero
      · -- Caso Lt (σ n) 𝟘.
          exact (nlt_n_0 (σ n) h_lt_succ_n_zero).elim
      · -- Caso σ n = 𝟘.
          exact (succ_neq_zero n h_eq_succ_n_zero).elim

  theorem le_1_0_then_false :
    Le 𝟙 𝟘 → False
      := by exact le_succ_0_then_false 𝟘

  theorem le_succ_iff_le_or_eq (a b : ℕ₀) :
    Le a (σ b) ↔ Le a b ∨ a = σ b
      := by
        constructor
        · intro h_le
          induction b with
          | zero =>
            have equiv_calc : Le a (σ 𝟘) ↔ (a = 𝟘 ∨ a = 𝟙) := calc
              Le a (σ 𝟘) ↔ Le a 𝟙 := by simp [one]
              _ ↔ Lt a 𝟙 ∨ a = 𝟙 := by rfl
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
                        (Or.inr rfl : Le (σ b') (σ b'))
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
    Le a (σ b) → Le a b ∨ a = σ b
      := by
      intro h_le_succ
      unfold Le at h_le_succ
      rcases h_le_succ with h_lt_succ | h_eq_succ
      · -- Caso Lt a (σ b).
        apply Or.inl
        exact (le_iff_lt_succ a b).mpr h_lt_succ
      · -- Caso a = σ b.
        apply Or.inr
        exact h_eq_succ ▸ rfl

  theorem le_or_eq_then_le_succ (a b : ℕ₀) :
    Le a b ∨ a = σ b → Le a (σ b)
      := by
      intro h_le_or_eq
      unfold Le at h_le_or_eq
      rcases h_le_or_eq with h_lt_or_eq | h_eq_or_eq
      · -- Caso Lt a b ∨ a = b.
        apply Or.inl
        cases h_lt_or_eq with
        | inl h_lt_ab => exact lt_trans a b (σ b) h_lt_ab (lt_self_σ_self b)
        | inr h_eq_ab => rw [h_eq_ab]; exact lt_self_σ_self b
      . -- Caso a = b.
        apply Or.inr
        exact h_eq_or_eq ▸ rfl



  theorem isomorph_Ψ_le (n m : ℕ₀) :
    Ψ n ≤ Ψ m ↔ Le n m
    := by
    constructor
    · -- Dirección →: (Ψ n ≤ Ψ m) → Le n m
      intro h_psi_le_psi_m -- h_psi_le_psi_m : Ψ n ≤ Ψ m
      rw [Nat.le_iff_lt_or_eq] at h_psi_le_psi_m
      cases h_psi_le_psi_m with
      | inl h_psi_lt_psi_m => -- Caso Ψ n < Ψ m
        apply Or.inl
        exact (isomorph_Ψ_lt n m).mpr h_psi_lt_psi_m
      | inr h_psi_eq_psi_m => -- Caso Ψ n = Ψ m
        apply Or.inr
        exact (Ψ_inj n m h_psi_eq_psi_m)
    · -- Dirección ←: Le n m → (Ψ n ≤ Ψ m)
      intro h_le_nm -- h_le_nm : Le n m
      cases h_le_nm with
      | inl h_lt_nm => -- Caso Lt n m
        have h_psi_lt_psi_m : Ψ n < Ψ m
            := (isomorph_Ψ_lt n m).mp h_lt_nm
        exact Nat.le_of_lt h_psi_lt_psi_m
      | inr h_eq_nm => -- Caso n = m
        rw [h_eq_nm]
        exact Nat.le_refl (Ψ m)

  theorem isomorph_Λ_le (n m : Nat) :
    n ≤ m ↔ Le (Λ n) (Λ m)
    := by
    constructor
    · -- Dirección →: n ≤ m → Le (Λ n) (Λ m)
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
    · -- Dirección ←: Le (Λ n) (Λ m) → n ≤ m
      intro h_le_Λn_Λm
      cases h_le_Λn_Λm with
      | inl h_lt_Λn_Λm => -- Caso Lt (Λ n) (Λ m)
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

  instance : LE ℕ₀ := ⟨Le⟩

  theorem lt_of_le_of_ne (a b : ℕ₀) :
    Le a b → a ≠ b → Lt a b
      := by
        intro h_le h_neq
        cases h_le with
        | inl h_lt => exact h_lt
        | inr h_eq => contradiction

  theorem lt_iff_le_not_le (a b : ℕ₀) :
    Lt a b ↔ Le a b ∧ ¬Le b a
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
    Lt a (σ b) ↔ Le a b
      := by
        constructor
        · intro h_lt_a_ssb
          unfold Lt at h_lt_a_ssb
          -- Ahora procedemos por casos en a y b
          cases a with
          | zero =>
            cases b with
            | zero =>
              -- Lt 𝟘 (σ 𝟘) → Le 𝟘 𝟘
              exact le_refl 𝟘
            | succ b' =>
              -- Lt 𝟘 (σ (σ b')) → Le 𝟘 (σ b')
              exact zero_le (σ b')
          | succ a' =>
            cases b with
            | zero =>
              -- Lt (σ a') (σ 𝟘) → Le (σ a') 𝟘
              -- Esto es una contradicción por la definición de Lt
              simp [Lt] at h_lt_a_ssb
            | succ b' =>
              -- Lt (σ a') (σ (σ b')) → Le (σ a') (σ b')
              simp [Lt] at h_lt_a_ssb
              have h_lt_a'_sb' : Lt a' (σ b') := h_lt_a_ssb
              have h_le_a'_b' : Le a' b' := (le_iff_lt_succ a' b').mpr h_lt_a'_sb'
              exact (succ_le_succ_iff a' b').mpr h_le_a'_b'
        · intro h_le_ab
          exact (le_iff_lt_succ a b).mp h_le_ab

  theorem le_succ_iff_le_or_eq_alt (n m : ℕ₀) :
    Le n (σ m) ↔ Le n m ∨ n = σ m
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
          | inr h_eq_nsm =>
            rw [h_eq_nsm]
            exact le_refl (σ m)

  theorem le_of_succ_le_succ (n m : ℕ₀) :
    Le (σ n) (σ m) → Le n m
      := by
        intro h_le_ss
        unfold Le at *
        rcases h_le_ss with h_lt_ss | h_eq_ss
        · -- Caso Lt (σ n) (σ m)
          apply Or.inl
          exact (lt_iff_lt_σ_σ n m).mpr h_lt_ss
        · -- Caso σ n = σ m
          apply Or.inr
          exact ℕ₀.succ.inj h_eq_ss

    theorem nle_iff_gt (n m : ℕ₀) :
      ¬(Le n m) ↔ (Lt m n)
      := by
      calc
        ¬(Le n m) ↔ ¬(Lt n m ∨ n = m) := by
          rw [Le]
        _ ↔ ¬(Lt n m) ∧ ¬(n = m) := by
          rw [not_or]
        _ ↔ ((Lt m n) ∨ (n = m)) ∧ ¬(n = m) := by
          rw [lt_or_eq_iff_nltc]
        _ ↔ (Lt m n ∧ ¬(n = m)) ∨ (n = m ∧ ¬(n = m)) := by
          rw [or_and_right]
        _ ↔ (Lt m n) ∧ ¬(n = m) := by
          simp [and_not_self]
        _ ↔ (Lt m n) := by
          constructor
          · exact And.left
          · intro h_lt
            exact ⟨h_lt, (lt_then_neq m n h_lt).symm⟩

  theorem nle_then_gt (n m : ℕ₀) :
    ¬(Le n m) → Lt m n
      := by
        intro h_nle_m
        rw [nle_iff_gt] at h_nle_m
        exact h_nle_m

  theorem nle_then_gt_wp {n m : ℕ₀} (h_nle : ¬(Le n m)) :
    Lt m n
      := by
        exact nle_then_gt n m h_nle

  theorem gt_then_nle (n m : ℕ₀) :
    Lt n m → ¬(Le m n)
      := by
        intro h_lt_m
        rw [← nle_iff_gt m n] at h_lt_m
        exact h_lt_m

  theorem gt_then_nle_wp {n m : ℕ₀} (h_nle : Lt n m) :
    ¬ Le m n
      := by
        exact gt_then_nle n m h_nle

  theorem le_1_m_then_m_neq_0 (m : ℕ₀) :
    Le 𝟙 m → m ≠ 𝟘
      := by
        intro h_le_1_m
        unfold Le at h_le_1_m
        cases m with
        | zero =>
          rcases h_le_1_m with h_lt_1_0 | h_eq_1_0
          · exact (nlt_n_0 𝟙 h_lt_1_0).elim
          · exact (succ_neq_zero 𝟘 h_eq_1_0).elim
        | succ m' =>
          exact succ_neq_zero m'

  theorem m_neq_0_proved_lt_1_m {m : ℕ₀} (h : Le 𝟙 m) :
    m ≠ 𝟘
    := by
        intro h_m_eq_0
        rw [h_m_eq_0] at h
        have h_one_eq_zero : 𝟙 = 𝟘 := le_zero_eq 𝟙 h
        exact absurd h_one_eq_zero (succ_neq_zero 𝟘)

  theorem le_m_1_then_m_eq_0or1_wp {m : ℕ₀} (h : Le m 𝟙) :
    m = 𝟘 ∨ m = 𝟙
      := by
        unfold Le at h
        cases m with
        | zero =>
          exact Or.inl rfl
        | succ m' =>
          -- Le (σ m') 𝟙 implies σ m' = 𝟙 which means m' = 𝟘
          rcases h with h_lt | h_eq
          · -- Case Lt (σ m') 𝟙
            -- Since 𝟙 = σ 𝟘, we have Lt (σ m') (σ 𝟘)
            -- This implies Lt m' 𝟘, which is impossible
            have h_lt_m_zero : Lt m' 𝟘 := (lt_iff_lt_σ_σ m' 𝟘).mpr h_lt
            exact (nlt_n_0 m' h_lt_m_zero).elim
          · -- Case σ m' = 𝟙
            -- Since 𝟙 = σ 𝟘, we have σ m' = σ 𝟘, so m' = 𝟘
            have h_m_eq_zero : m' = 𝟘 := ℕ₀.succ.inj h_eq
            exact Or.inr (h_m_eq_zero ▸ rfl)

  theorem le_n_m_then_m_neq_0 (n m : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) :
    (Le n m) → (m ≠ 𝟘)
      := by
        intro h_le_n_m
        rcases h_le_n_m with h_lt_nm | h_eq_nm
        · -- Caso Lt n m
          unfold Lt at h_lt_nm
          cases n with
          | zero =>
            -- Lt 𝟘 m es válido cuando m ≠ 𝟘, no es contradicción
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
    (Le n m)∧(n ≠ 𝟘) → (m ≠ 𝟘)
      := by
        intro h_le_n_m_and_n_neq_0
        rcases h_le_n_m_and_n_neq_0 with ⟨h_le_n_m, h_n_neq_0⟩
        exact le_n_m_then_m_neq_0 n m h_n_neq_0 h_le_n_m

  theorem m_neq_0_proved_lt_1_m_wp {m : ℕ₀} (h : Le 𝟙 m) :
    m ≠ 𝟘
    := by
        intro h_m_eq_0
        rw [h_m_eq_0] at h
        have h_one_eq_zero : 𝟙 = 𝟘 := le_zero_eq 𝟙 h
        exact absurd h_one_eq_zero (succ_neq_zero 𝟘)

  theorem le_0_succ_then_lt_0_succ (n : ℕ₀) :
    Le 𝟘 (σ n) → Lt 𝟘 (σ n)
      := by
        intro h_le_0_sn
        unfold Le at h_le_0_sn
        cases h_le_0_sn with
        | inl h_lt_0_sn =>
          exact h_lt_0_sn
        | inr h_eq_0_sn =>
          exfalso
          exact succ_neq_zero n h_eq_0_sn.symm

  theorem le_0_succ_then_lt_0_succ_wp {n : ℕ₀} (h_le : Le 𝟘 (σ n)) :
    Lt 𝟘 (σ n)
      := by
        exact le_0_succ_then_lt_0_succ n h_le

  theorem lt_0_succ_then_le_0_succ (n : ℕ₀) :
    Lt 𝟘 (σ n) → Le 𝟘 (σ n)
      := by
        intro h_lt_0_sn
        unfold Le
        exact Or.inl h_lt_0_sn

  theorem lt_0_succ_then_le_0_succ_wp {n : ℕ₀} (h_lt : Lt 𝟘 (σ n)) :
    Le 𝟘 (σ n)
      := by
        exact lt_0_succ_then_le_0_succ n h_lt

  theorem le_0_succ_iff_lt_0_succ (n : ℕ₀) :
    Le 𝟘 (σ n) ↔ Lt 𝟘 (σ n)
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
    Le n m → Lt n (σ m)
      := by
        intro h_le_nm
        unfold Le at h_le_nm
        rcases h_le_nm with h_lt_nm | h_eq_nm
        · -- Caso Lt n m
          exact lt_trans n m (σ m) h_lt_nm (lt_self_σ_self m)
        · -- Caso n = m
          rw [h_eq_nm]
          exact lt_self_σ_self m

  theorem le_then_lt_succ_wp {n m : ℕ₀} (h_le : Le n m) :
    Lt n (σ m)
      := by
        exact le_then_lt_succ n m h_le


  theorem le_succ_then_le_or_eq_wp {n m : ℕ₀} (h_le : Le n (σ m)) :
    Le n m ∨ n = σ m
      := by
        exact le_succ_then_le_or_eq n m h_le

  theorem le_or_eq_then_le_succ_wp {n m : ℕ₀}
      (h_le_or_eq_succ : Le n m ∨ n = σ m) :
    Le n (σ m)
      := by
        exact le_or_eq_then_le_succ n m h_le_or_eq_succ

  theorem le_succ_k_n_then_le_k_n {n k : ℕ₀} :
    Le (σ k) n → Le k n
      := by
        intro h_le_ssn
        unfold Le at h_le_ssn
        rcases h_le_ssn with h_lt_ssn | h_eq_ssn
        · -- Caso Lt (σ k) n
          apply Or.inl
          cases n with
          | zero => exfalso; exact (nlt_n_0 (σ k) h_lt_ssn).elim
          | succ m => -- n = σ m. h_lt_ssn becomes Lt (σ k) (σ m)
            -- Goal: Lt k (σ m)
            have h_lt_k_m : Lt k m := (lt_iff_lt_σ_σ k m).mpr h_lt_ssn
            exact lt_trans k m (σ m) h_lt_k_m (lt_self_σ_self m)
        · -- Caso σ k = n. Here h_eq_ssn : σ k = n.
          apply Or.inl
          rw [← h_eq_ssn]
          exact lt_self_σ_self k

  theorem lt_k_succ_n_then_le_k_n {n k : ℕ₀} :
    Lt k (σ n) → Le k n
      := by
        intro h_lt_k_sn
        unfold Lt at h_lt_k_sn
        cases k with
        | zero =>
          cases n with
          | zero => exact le_refl 𝟘
          | succ n' => exact zero_le (σ n')
        | succ k' =>
          cases n with
          | zero =>
            simp [Lt] at h_lt_k_sn
          | succ n' =>
            have h_lt_k'_sn' : Lt k' (σ n') := h_lt_k_sn
            have h_le_k'_n' : Le k' n' := (le_iff_lt_succ k' n').mpr h_lt_k'_sn'
            rcases h_le_k'_n' with h_lt_k'_n' | h_eq_k'_n'
            · -- Caso Lt k' n'
              apply Or.inl
              exact (lt_iff_lt_σ_σ k' n').mpr h_lt_k'_n'
            · -- Caso k' = n'. Entonces σ k' = σ n'.
              apply Or.inr
              rw [h_eq_k'_n']

  theorem lt_k_succ_n_then_le_k_n_wp {n k : ℕ₀} (h_lt_k_sn : Lt k (σ n)):
    Le k n
      := by
        exact lt_k_succ_n_then_le_k_n h_lt_k_sn

  theorem le_k_n_then_le_k_sn_wp {n k : ℕ₀} (h_le_k_n : Le k n):
    Le k (σ n)
      := by
        exact le_succ k n h_le_k_n

  theorem le_n_m_then_le_n_sm (n m : ℕ₀) :
    Le n m → Le n (σ m)
      := by
        intro h_le_nm
        unfold Le at h_le_nm
        rcases h_le_nm with h_lt_nm | h_eq_nm
        · -- Caso Lt n m
          apply Or.inl
          have h_lt_n_m : Lt n m := (lt_iff_lt_σ_σ n m).mpr h_lt_nm
          exact lt_trans n m (σ m) h_lt_n_m (lt_self_σ_self m)
        · -- Caso n = m
          apply Or.inl
          rw [h_eq_nm]
          exact lt_self_σ_self m

  theorem le_n_m_then_le_n_sm_wp  {n m : ℕ₀} (h_le_nm : Le n m) :
    Le n (σ m)
      := by
        exact le_n_m_then_le_n_sm n m h_le_nm

  theorem le_sn_m_then_le_n_m_or_succ (n m : ℕ₀) :
    Le (σ n) m → Le n m
      := by
        intro h_le_sn_m
        unfold Le at h_le_sn_m
        rcases h_le_sn_m with h_lt_sn_m | h_eq_sn_m
        · -- Caso Lt (σ n) m
          apply Or.inl
          cases m with
          | zero => exfalso; exact (nlt_n_0 (σ n) h_lt_sn_m).elim
          | succ m' =>
            have h_lt_n_m' : Lt n m' := (lt_iff_lt_σ_σ n m').mpr h_lt_sn_m
            exact lt_trans n m' (σ m') h_lt_n_m' (lt_self_σ_self m')
        · -- Caso σ n = m
          apply Or.inl
          rw [← h_eq_sn_m]
          exact lt_self_σ_self n

  theorem le_sn_m_then_le_n_m_or_succ_wp {n m : ℕ₀} (h_le_sn_m : Le (σ n) m) :
    Le n m
      := by
        exact le_sn_m_then_le_n_m_or_succ n m h_le_sn_m

  theorem le_then_lt_or_eq (n m : ℕ₀) :
    n ≤ m → (Lt n m) ∨ (n = m)
      := by
        intro h_le_nm
        exact h_le_nm

  theorem le_not_lt {a b : ℕ₀} (h_le : Le a b) :
    ¬(Lt b a)
    := by
      intro h_lt_ba
      have h_not_le_ab : ¬Le a b := gt_then_nle b a h_lt_ba
      exact h_not_le_ab h_le


  theorem nle_σn_n (n : ℕ₀) :
    ¬(Le (σ n) n)
      := by
      intro h_le_sn_n
      unfold Le at h_le_sn_n
      rcases h_le_sn_n with h_lt_sn_n | h_eq_sn_n
      · exact (lt_asymm n (σ n) (lt_self_σ_self n) h_lt_sn_n)
      · exact (lt_irrefl n (cast (congrArg (Lt n) h_eq_sn_n) (lt_self_σ_self n)))

  theorem le_σn_n_then_false (n : ℕ₀) :
    Le (σ n) n → False
      := by
      intro h_le_sn_n
      have h_nle_sn_n : ¬(Le (σ n) n) := nle_σn_n n
      exact h_nle_sn_n h_le_sn_n

  end Order
end Peano

export Peano.Order (
  Le Ge Le' BLe BGe
  zero_le
  succ_le_succ_iff
  succ_le_succ_then
  Le_iff_Le'
  BGe_iff_Ge
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
  le_1_m_then_m_neq_0
  le_n_m_then_m_neq_0
  le_n_m_n_neq_0_then_m_neq_0
  m_neq_0_proved_lt_1_m_wp
  m_neq_0_proved_lt_1_m
  nle_then_gt_wp
  gt_then_nle_wp
  le_then_le_succ
  succ_le_succ_iff
  succ_le_succ_then
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
)
