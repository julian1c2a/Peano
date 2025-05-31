import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import Init.Prelude

namespace Peano
  open Peano
  open Peano.Axioms
  open Peano.StrictOrder
    -- Definiciones y teoremas para Le (menor o igual)
  namespace Order
      open Order
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

    -- El teorema zero_le se mueve aquí porque se usa en Le'_iff_Le.
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

/--!
    FALTA ESTE TEOREMA POR COMPLETITUD
    -- El teorema BGe_iff_Ge se mueve aquí porque se usa
    -- en decidableGe.
    theorem BGe_iff_Ge (n m : ℕ₀) :
    BGe n m = true ↔ Ge n m
--/

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

   /-- Instancia Decidable para Ge n m.
        Se construye a partir de las instancias
        Decidable para Lt m n y n = m.
    -/
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

  theorem le_succ_iff_le_or_eq (a b : ℕ₀) :
    Le a (σ b) ↔ Le a b ∨ a = σ b
      := by
        constructor
        · intro h_le
          induction b with
          | zero =>
            have equiv_calc : Le a (σ 𝟘) ↔ (a = 𝟘 ∨ a = 𝟙) := calc
              Le a (σ 𝟘) ↔ Le a 𝟙 := by simp [Peano.one]
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
      intro h_n_le_m -- h_n_le_m : n ≤ m
      rw [Nat.le_iff_lt_or_eq] at h_n_le_m
      cases h_n_le_m with
      | inl h_lt_nm => -- Caso n < m
        apply Or.inl
        exact (
          isomorph_Ψ_lt (Λ n) (Λ m)
        ).mpr (by {
              rw [ΨΛ, ΨΛ]
              exact h_lt_nm
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
            := (
                  isomorph_Ψ_lt (Λ n) (Λ m)
            ).mp h_lt_Λn_Λm
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
        intro h_le h_ne
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

--    theorem lt_then_neq (n m : ℕ₀) :
--      Lt n m → n ≠ m
--      := by
--      intros h_lt_nm h_eq_nm
--      rw [h_eq_nm] at h_lt_nm
--      exact lt_irrefl m h_lt_nm

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
  gt_then_nle
  le_1_m_then_m_neq_0
  le_n_m_then_m_neq_0
  le_n_m_n_neq_0_then_m_neq_0
  m_neq_0_proved_lt_1_m
  nle_then_gt_wp
  le_then_le_succ
)
