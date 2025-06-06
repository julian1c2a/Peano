import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub


namespace Peano
    open Peano

  namespace Mul
      open Axioms
      open StrictOrder
      open Order
      open MaxMin
      open Add
      open Sub

  def mul (n m : ℕ₀) : ℕ₀ :=
    match m with
    | 𝟘 => 𝟘
    | σ m' => add (mul n m') n

  infix:70 "*" => mul

  theorem mul_zero (n : ℕ₀) :
    mul n 𝟘 = 𝟘
      := by simp [mul]

  theorem zero_mul (n : ℕ₀) :
    mul 𝟘 n = 𝟘
      := by
    induction n with
    | zero => simp [mul]
    | succ n' ih => simp [mul, ih, add_zero]

  theorem succ_mul (n m : ℕ₀) :
    mul (σ n) m = add (mul n m) m
      := by
    induction m with
    | zero => rw [mul_zero, mul_zero, add_zero]
    | succ m' ih =>
      simp [mul]
      rw [ih]
      rw [←add_assoc (mul n m') m' (σ n) ]
      rw [←add_assoc (mul n m') n (σ m')]
      apply congrArg (add (mul n m'))
      rw [add_succ m' n, add_succ n m']
      apply congrArg
      exact add_comm m' n

  theorem mul_succ (n m : ℕ₀) :
    mul n (σ m) = add (mul n m) n
      := by rfl

  theorem mul_one (n : ℕ₀) :
    mul n 𝟙 = n
      := by
    induction n with
    | zero => rfl
    | succ n' ih => rw [succ_mul, ih, add_one]

  theorem one_mul (m : ℕ₀) :
    mul 𝟙 m = m
      := by
    induction m with
    | zero => rfl
    | succ m' ih => rw [mul_succ, ih, add_one]

  theorem mul_two (n : ℕ₀):
    mul n 𝟚 = add n n
      := by
    have h_two_eq_succ_one : 𝟚 = σ 𝟙 := by rfl
    calc
      mul n 𝟚 = mul n (σ 𝟙) := by rfl
      _ = add (mul n 𝟙) n := by rfl
      _ = add n n := by rw [mul_one]

  theorem two_mul (n : ℕ₀):
    mul 𝟚 n = add n n
      := by
    have h_two_eq_succ_one : 𝟚 = σ 𝟙 := by rfl
    induction n with
    | zero =>
      calc
        mul 𝟚 𝟘 = 𝟘 := by rw [mul_zero]
        _ = add 𝟘 𝟘 := by rw [add_zero]
    | succ n' _ =>
      calc
        mul 𝟚 (σ n') = mul (σ 𝟙) (σ n') := by rfl
        _ = add (mul 𝟙 (σ n')) (σ n') := by rw [succ_mul]
        _ = add (σ n') (σ n') := by rw [one_mul]

  theorem mul_comm (n m : ℕ₀) :
    mul n m = mul m n
      := by
    induction m with
    | zero => rw [mul_zero, zero_mul]
    | succ m' ih => simp [mul]; rw [ih]; rw [succ_mul m' n]

  theorem mul_ldistr (m n k : ℕ₀) :
    mul m (add n k) = add (mul m n) (mul m k)
      := by
    induction k with
    | zero =>
      rw [add_zero, mul_zero, add_zero]
    | succ k' ih =>
      rw [add_succ, mul_succ, ih, mul_succ, add_assoc (mul m n) (mul m k') m]

  theorem mul_rdistr (m n k : ℕ₀) :
    mul (add m n) k = add (mul m k) (mul n k)
      := by
    induction k with
    | zero =>
      rw [mul_zero, mul_zero, mul_zero, add_zero]
    | succ k' _ =>
      calc
        mul (add m n) (σ k')
          = mul (σ k') (add m n) := by rw [mul_comm]
        _ = add (mul (σ k') m) (mul (σ k') n) := by rw [mul_ldistr]
        _ = add (mul m (σ k')) (mul n (σ k')) := by rw [mul_comm (σ k') m, mul_comm (σ k') n]

  theorem mul_cancelation_left (n m k : ℕ₀) :
    n ≠ 𝟘 → (mul n m = mul n k → m = k)
      := by
    intro h_n_neq_zero h_mul_eq_nk
    induction m generalizing k with
    | zero =>
      rw [mul_zero] at h_mul_eq_nk
      cases k with
      | zero => rfl
      | succ k' =>
        rw [mul_succ] at h_mul_eq_nk
        cases n with
        | zero => exact False.elim (h_n_neq_zero rfl)
        | succ n_val =>
          have : add (mul (σ n_val) k') (σ n_val) ≠ 𝟘
            := by
            intro h
            exact succ_neq_zero n_val ((add_eq_zero_iff _ _).mp h).2
          exact False.elim (this h_mul_eq_nk.symm)
    | succ m' ih =>
      cases k with
      | zero =>
        rw [mul_zero] at h_mul_eq_nk
        cases n with
        | zero => exact False.elim (h_n_neq_zero rfl)
        | succ n_val =>
          rw [mul_succ] at h_mul_eq_nk
          have : add (mul (σ n_val) m') (σ n_val) ≠ 𝟘 := by
            intro h
            exact succ_neq_zero n_val ((add_eq_zero_iff _ _).mp h).right
          exact False.elim (this h_mul_eq_nk)
      | succ k' =>
        rw [mul_succ, mul_succ] at h_mul_eq_nk
        have h_eq : mul n m' = mul n k' := cancelation_add n (mul n m') (mul n k') h_mul_eq_nk
        have h_m'_eq_k' : m' = k' := ih k' h_eq
        exact congrArg (fun x => σ x) h_m'_eq_k'

  theorem mul_cancelation_right (n m k : ℕ₀) :
    k ≠ 𝟘 → (mul n k = mul m k → n = m)
      := by
    intro h_k_neq_zero h_mul_eq_nk
    rw [mul_comm n k, mul_comm m k] at h_mul_eq_nk
    exact mul_cancelation_left k n m h_k_neq_zero h_mul_eq_nk

  theorem mul_assoc (n m k : ℕ₀) :
    mul (mul m n) k = mul m (mul n k)
      := by
    induction n with
    | zero =>
      rw [mul_zero, zero_mul]
      rw [mul_zero]
    | succ n' ih =>
      rw [succ_mul]
      rw [mul_succ]
      rw [mul_rdistr]
      rw [ih]
      rw [mul_ldistr]

  theorem mul_eq_zero (n m : ℕ₀) :
    mul n m = 𝟘 ↔ n = 𝟘 ∨ m = 𝟘
      := by
    induction m with
    | zero =>
      rw [mul_zero]
      simp
    | succ m' ih =>
      rw [mul_succ]
      rw [add_eq_zero_iff]
      rw [ih]
      constructor
      · intro h
        cases h with
        | intro h_left h_right =>
          cases h_left with
          | inl h_n_zero => exact Or.inl h_n_zero
          | inr h_m'_zero => exact Or.inl h_right
      · intro h
        cases h with
        | inl h_n_zero => exact ⟨Or.inl h_n_zero, h_n_zero⟩
        | inr h_succ_zero => exact False.elim (succ_neq_zero m' h_succ_zero)

  theorem mul_eq_zero_wp {n m : ℕ₀} (h_n_neq_0 : n ≠ 𝟘) (h_m_neq_0 : m ≠ 𝟘) :
      mul n m ≠ 𝟘
          := by
    intro h_mul_eq_zero
    have h_mul_eq_zero' : mul n m = 𝟘 := h_mul_eq_zero
    have h_n_or_m_zero : n = 𝟘 ∨ m = 𝟘 := (mul_eq_zero n m).mp h_mul_eq_zero'
    exact h_n_or_m_zero.elim
      (fun h_n_zero => h_n_neq_0 h_n_zero)
      (fun h_m_zero => h_m_neq_0 h_m_zero)

/--!
  Los siguientes lemas relacionan la multiplicación con el predecesor: ρ (chequeado) y τ (isomorfo)
!--/
  theorem obvio (n : ℕ₀) :
    Le n (mul n 𝟙)
      := by
    rw [mul_one n]
    exact le_refl n

  theorem mul_pred (n m : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) (h_m_neq_0 : m ≠ 𝟘):
    mul n (ρ m h_m_neq_0) = sub (mul n m) n
      := by
    induction m with
    | zero =>
      exact False.elim (h_m_neq_0 rfl)
    | succ m' ih =>
      cases m' with
      | zero =>
        calc
          mul n (ρ (σ 𝟘) h_m_neq_0)
            = mul n 𝟘 := by rfl
          _ = 𝟘 := by rw [mul_zero]
          _ = subₕₖ n n (le_refl n) := by rw [subₕₖ_self n]
          _ = subₕₖ (mul n 𝟙) n (obvio n) := by simp [mul_one]
          _ = subₕₖ (mul n (σ 𝟘)) n (obvio n) := by rfl
          _ = sub (mul n (σ 𝟘)) n := by
            simp [sub]
            have h_le : Le n (mul n 𝟙) := by
              rw [mul_one]
              exact le_refl n
            have h_le_succ : Le n (mul n (σ 𝟘)) := by
              rw [←mul_one n]
              rw [←mul_one n] at h_le
              exact h_le
            simp [h_le_succ]
      | succ m'' =>
        have h_succ_m''_neq_0 : σ m'' ≠ 𝟘 := succ_neq_zero m''
        rw [ρ_succ, mul_succ]
        rw [ih h_succ_m''_neq_0]
        rw [mul_succ, add_assoc]
      rw [add_succ n (mul n m')]
      rw [add_assoc (mul n m') n (σ n)]
      apply congrArg (add (mul n m'))
      rw [add_succ m' n, add_succ n m']

  end Mul

end Peano
