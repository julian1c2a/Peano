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

  theorem mul_three (n : ℕ₀):
    mul n 𝟛 = add (add n n) n
      := by
    have h_three_eq_succ_two : 𝟛 = σ 𝟚 := by rfl
    calc
      mul n 𝟛 = mul n (σ 𝟚) := by rfl
      _ = add (mul n 𝟚) n := by rw [mul_succ]
      _ = add (add n n) n := by rw [mul_two]

  theorem three_mul (n : ℕ₀):
    mul 𝟛 n = add (add n n) n
      := by
    have h_three_eq_succ_two : 𝟛 = σ 𝟚 := by rfl
    induction n with
    | zero =>
      calc
        mul 𝟛 𝟘 = 𝟘 := by rw [mul_zero]
        _ = add (add 𝟘 𝟘) 𝟘 := by rw [add_zero, add_zero]
    | succ n' ih =>
      calc
        mul 𝟛 (σ n') = mul (σ 𝟚) (σ n') := by rfl
        _ = add (mul 𝟚 (σ n')) (σ n') := by rw [succ_mul]
        _ = add (add (σ n') (σ n')) (σ n') := by rw [two_mul]
        _ = add (add (σ n') (σ n')) (σ n') := by rfl

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
  theorem obvio_1 (n : ℕ₀) :
    Le n (mul n 𝟙)
      := by
    rw [mul_one n]
    exact le_refl n

  theorem obvio_2 (n m : ℕ₀):
    Le n (mul n (σ m))
      := by
    induction m generalizing n with
    | zero =>
      rw [mul_succ n 𝟘]
      rw [mul_zero n]
      rw [zero_add n]
      exact le_refl n
    | succ m' ih =>
      have h_le : Le n (mul n (σ m')) := ih n
      rw [mul_succ n (σ m')]
      exact add_le n (mul n (σ m')) n h_le

  theorem mul_le_right (n m : ℕ₀) (h_neq_0 : m ≠ 𝟘) :
    Le n (mul n m)
      := by
    induction m with
    | zero =>
      exact False.elim (h_neq_0 rfl)
    | succ m' ih =>
      exact obvio_2 n m'

  theorem mul_le_left (n m : ℕ₀) (h_neq_0 : m ≠ 𝟘) :
    Le n (mul m n)
      := by
    have mul_le_left_reverse : Le n (mul n m)
      := mul_le_right n m h_neq_0
    rw [mul_comm n m] at mul_le_left_reverse
    exact mul_le_left_reverse

  theorem mul_le_full_right (k n m : ℕ₀):
    Le (mul k n) (mul k (add n m))
      := by
    induction m with
    | zero =>
      rw [add_zero]
      exact le_refl (mul k n)
    | succ m' ih =>
      rw [add_succ, mul_succ]
      exact le_trans (mul k n) (mul k (add n m')) (mul k (add n (σ m'))) ih (add_le (mul k (add n m')) (mul k (add n m')) k (le_refl (mul k (add n m'))))

  theorem mul_le_full_left (k n m : ℕ₀):
    Le (mul n k) (mul (add n m) k)
      := by
    induction m with
    | zero =>
      rw [add_zero]
      exact le_refl (mul n k)
    | succ m' ih =>
      rw [add_succ, succ_mul]
      exact le_trans (mul n k) (mul (add n m') k) (add (mul (add n m') k) k) ih (add_le (mul (add n m') k) (mul (add n m') k) k (le_refl (mul (add n m') k)))

  theorem mul_lt_left (n m : ℕ₀) (h_neq_0 : n ≠ 𝟘) (h_lt_1 : Lt 𝟙 m):
    Lt n (mul n m)
      := by
    induction m with
    | zero =>
      have h_not_lt : ¬Lt 𝟙 𝟘 := by simp [Lt]
      exact False.elim (h_not_lt h_lt_1)
    | succ m' ih =>
      cases m' with
      | zero =>
        -- m = σ 𝟘 = 𝟙, so h_lt_1 : Lt 𝟙 𝟙 which is false
        have h_sigma_zero_eq_one : σ 𝟘 = 𝟙 := by rfl
        rw [←h_sigma_zero_eq_one] at h_lt_1
        have h_not_lt_self : ¬Lt 𝟙 𝟙 := lt_irrefl 𝟙
        exact False.elim (h_not_lt_self h_lt_1)
      | succ m'' =>
        induction m'' with
        | zero =>
          -- m = σ (σ 𝟘) = σ 𝟙 = 𝟚, so h_lt_1 : Lt 𝟙 𝟚 which is true
          induction n with
          | zero =>
            -- n = 𝟘, so mul n m = 𝟘
            exact False.elim (h_neq_0 rfl)
          | succ n' =>
            -- n = σ n', so mul n m = σ n' + σ 𝟘 = σ (n' + 𝟘) = σ n'
            have h_mul_succ : mul (σ n') (σ (σ 𝟘)) = add (σ n') (σ n') := by
              rw [mul_succ]
              rw [mul_succ]
              rw [mul_zero]
              rw [zero_add]
            have h_le : Le (σ n') (mul (σ n') 𝟙) := obvio_1 (σ n')
            rw [mul_one] at h_le
            have h_lt : Lt (σ n') (add (σ n') (σ n')) := by
              exact lt_add_succ (σ n') n'
            rw [←h_mul_succ] at h_lt
            exact h_lt
        | succ m''' ih' =>
          induction n with
          | zero =>
            -- n = 𝟘, so mul n m = 𝟘
            exact False.elim (h_neq_0 rfl)
          | succ n' ih_n => -- n is σ n', m is σ (σ (σ m'''))
                            -- h_neq_0 is (σ n') ≠ 𝟘
                            -- h_lt_1 is Lt 𝟙 (σ (σ (σ m''')))
                            -- ih is the main induction hypothesis from `induction m`
                            -- ih: (h_lt_1_arg : Lt 𝟙 (σ (σ m'''))) → Lt (σ n') (mul (σ n') (σ (σ m''')))
            -- Goal: Lt (σ n') (mul (σ n') (σ (σ (σ m'''))))
            rw [mul_succ] -- Goal: Lt (σ n') (add (mul (σ n') (σ (σ m'''))) (σ n'))

            have h_inductive_call_m_prev : Lt (σ n') (mul (σ n') (σ (σ m'''))) := by
              apply ih -- ih is m_ih from the outer `induction m`
                       -- n argument for ih is σ n' (current n)
                       -- m_val for ih is σ (σ m''')
              exact lt_1_succ_succ m''' -- Proves Lt 𝟙 (σ (σ m'''))

            have h_lt_add_term : Lt (mul (σ n') (σ (σ m'''))) (add (mul (σ n') (σ (σ m'''))) (σ n')) := by
              apply lt_add_succ -- lt_add_succ (mul (σ n') (σ (σ m'''))) n'

            exact StrictOrder.lt_trans (σ n') (mul (σ n') (σ (σ m'''))) (add (mul (σ n') (σ (σ m'''))) (σ n')) h_inductive_call_m_prev h_lt_add_term

  theorem mul_lt_right (n m : ℕ₀) (h_neq_0 : n ≠ 𝟘) (h_lt_1 : Lt 𝟙 m):
    Lt n (mul m n)
      := by
    have mul_lt_left_reverse : Lt n (mul n m)
      := mul_lt_left n m h_neq_0 h_lt_1
    rw [mul_comm n m] at mul_lt_left_reverse
    exact mul_lt_left_reverse

  theorem mul_lt_full_left (k n m : ℕ₀) (h_le_1_m : Le 𝟙 m) (h_le_1_k : Le 𝟙 k):
    Lt (mul n k) (mul (add n m) k)
      := by
    induction m with
    | zero =>
      rw [add_zero] -- Goal is now `Lt (mul n k) (mul n k)`
      -- The hypothesis `h_le_1_m` becomes `Le 𝟙 𝟘` in this case.
      -- `Le 𝟙 𝟘` (i.e. `Le (σ 𝟘) 𝟘`) is false.
      have h_one_not_le_zero : ¬ (Le 𝟙 𝟘) := le_succ_0_then_false 𝟘
      exact False.elim (h_one_not_le_zero h_le_1_m)
    | succ m' ih => -- m = σ m'
      rw [add_succ, succ_mul] -- Goal: Lt (mul n k) (add (mul (add n m') k) k)
      -- Let A = mul n k
      -- Let B = mul (add n m') k
      -- Let C = add B k = add (mul (add n m') k) k
      -- We want to prove Lt A C.

      -- First, establish B < C: Lt (mul (add n m') k) (add (mul (add n m') k) k)
      -- This holds because k ≥ 1 (from h_le_1_k), so k is a successor.
      have h_lt_b_c : Lt (mul (add n m') k) (add (mul (add n m') k) k) := by
        have h_k_ne_zero : k ≠ 𝟘 := by {
          intro h_k_eq_zero;
          rw [h_k_eq_zero] at h_le_1_k;
          exact (le_succ_0_then_false 𝟘) h_le_1_k;
        }
        conv =>
          rhs;
          arg 2; -- Focus on the second `k` in `add _ k`
          rw [(σ_τ_eq_id_pos_forall h_k_ne_zero).symm];
          -- RHS is now `add (mul (add n m') k) (σ (τ k))`
          -- which is definitionally `σ (add (mul (add n m') k) (τ k))`
        apply lt_add_succ; -- Goal is `Lt X (σ (X + τ k))`, matches `lt_add_succ X (τ k)`

      -- Next, establish A < B or A = B, by cases on m'
      cases m' with
      | zero => -- m' = 𝟘. So m = σ 𝟘 = 𝟙.
        rw [add_zero] -- Goal becomes Lt (mul n k) (add (mul n k) k)
        -- This is Lt A (add A k), which is h_lt_b_c with m' = 0.
        -- h_lt_b_c is Lt (mul (add n 𝟘) k) (add (mul (add n 𝟘) k) k)
        rw [add_zero] at h_lt_b_c -- Now h_lt_b_c is Lt (mul n k) (add (mul n k) k)
        exact h_lt_b_c
      | succ m'' => -- m' = σ m''. So m = σ (σ m'').
        -- The induction hypothesis ih is: (h_le_1_m_prime : Le 𝟙 m') → Lt (mul n k) (mul (add n m') k)
        -- We need a proof for `Le 𝟙 m'`, where m' = σ m''.
        -- `Le 𝟙 (σ m'')` is equivalent to `Lt 𝟘 (σ m'')` (since 𝟙 = σ 𝟘).
        -- `Lt 𝟘 (σ m'')` is true because σ m'' is a successor.
        have h_le_1_m_prime_proof : Le 𝟙 (σ m'') := by
          exact le_1_succ m'' -- Use le_succ_all to show 1 ≤ σ m''

        -- Use ih to get A < B: Lt (mul n k) (mul (add n m') k)
        have h_lt_a_b_from_ih : Lt (mul n k) (mul (add n (σ m'')) k) := ih h_le_1_m_prime_proof

        -- Combine A < B and B < C using lt_trans
        exact lt_trans (mul n k) (mul (add n (σ m'')) k) (add (mul (add n (σ m'')) k) k) h_lt_a_b_from_ih h_lt_b_c

  theorem mul_lt_full_right (k n m : ℕ₀) (h_le_1_m : Le 𝟙 m) (h_le_1_k : Le 𝟙 k):
    Lt (mul k n) (mul k (add n m))
      := by
    induction m with
    | zero =>
      rw [add_zero] -- Goal is now `Lt (mul k n) (mul k n)`
      -- The hypothesis `h_le_1_m` becomes `Le 𝟙 𝟘` in this case.
      -- `Le 𝟙 𝟘` (i.e. `Le (σ 𝟘) 𝟘`) is false.
      have h_one_not_le_zero : ¬ (Le 𝟙 𝟘) := le_succ_0_then_false 𝟘
      exact False.elim (h_one_not_le_zero h_le_1_m)
    | succ m' ih => -- m = σ m'
      rw [add_succ n m', mul_succ] -- Goal: Lt (mul k n) (add (mul k (add n m')) k)
      -- Let A = mul k n
      -- Let B = mul k (add n m')
      -- Let C = add B k = add (mul k (add n m')) k
      -- We want to prove Lt A C.

      -- First, establish B < C: Lt (mul k (add n m')) (add (mul k (add n m')) k)
      -- This holds because k ≥ 1 (from h_le_1_k), so k is a successor.
      have h_lt_b_c : Lt (mul k (add n m')) (add (mul k (add n m')) k) := by
        have h_k_ne_zero : k ≠ 𝟘 := by {
          intro h_k_eq_zero;
          rw [h_k_eq_zero] at h_le_1_k;
          exact (le_succ_0_then_false 𝟘) h_le_1_k;
        }
        conv =>
          rhs;
          arg 2; -- Focus on the second `k` in `add _ k`
          rw [(σ_τ_eq_id_pos_forall h_k_ne_zero).symm];
          -- RHS is now `add (mul k (add n m')) (σ (τ k))`
          -- which is definitionally `σ (add (mul k (add n m')) (τ k))`
        apply lt_add_succ; -- Goal is `Lt X (σ (X + τ k))`, matches `lt_add_succ X (τ k)`

      -- Next, establish A < B or A = B, by cases on m'
      cases m' with
      | zero => -- m' = 𝟘. So m = σ 𝟘 = 𝟙.
        rw [add_zero] -- Goal becomes Lt (mul k n) (add (mul k n) k)
        -- This is Lt A (add A k), which is h_lt_b_c with m' = 0.
        -- h_lt_b_c is Lt (mul k 𝟘) (add (mul k 𝟘) k)
        -- (mul k n) (add (mul k n) k)
        exact h_lt_b_c
      | succ m'' => -- m' = σ m''. So m = σ (σ m'').
        -- The induction hypothesis ih is: (h_le_1_m_prime : Le 𝟙 m') → Lt (mul k n) (mul k (add n m'))
        -- We need a proof for `Le 𝟙 m'`, where m' = σ m''.
        -- `Le 𝟙 (σ m'')` is equivalent to `Lt 𝟘 (σ m'')` (since 𝟙 = σ 𝟘).
        -- `Lt 𝟘 (σ m'')` is true because σ m'' is a successor.
        have h_le_1_m_prime_proof : Le 𝟙 (σ m'') := by
          exact le_1_succ m'' -- Use le_succ_all to show 1 ≤ σ m''

        -- Use ih to get A < B: Lt (mul k n) (mul k (add n m'))
        have h_lt_a_b_from_ih : Lt (mul k n) (mul k (add n (σ m''))) := ih h_le_1_m_prime_proof

        -- Combine A < B and B < C using lt_trans
        exact lt_trans (mul k n) (mul k (add n (σ m''))) (add (mul k (add n (σ m''))) k) h_lt_a_b_from_ih h_lt_b_c

  theorem τ_0_eq_0 :
    τ 𝟘 = 𝟘
      := by rfl

  theorem τ_succ (n : ℕ₀) :
    τ (σ n) = n
      := by
    induction n with
    | zero => rfl
    | succ n' ih =>
      calc
        τ (σ (σ n')) = σ n' := by rfl
        _ = add n' 𝟙 := by rfl

  -- theorem τ_add_n_σm_eq_add_n_m (n m : ℕ₀) :
  --   τ (add n (σ m)) = add n m
  --     := by
  --   induction m with
  --   | zero =>
  --     have h_m_eq_1 : σ 𝟘 = 𝟙 := by rfl
  --     have h_add_n_1_eq_σ_n : add n 𝟙 = σ n := by rfl
  --     have h_τ_add_n_1_eq_τ_σ_n : τ (add n 𝟙) = τ (σ n) := by rfl
  --     have h_τ_add_n_1_eq_n : τ (add n 𝟙) = n := by
  --       rw [h_add_n_1_eq_σ_n]
  --       exact τ_succ n
  --   | succ m' ih =>
  --     by sorry

  -- theorem mul_pred (n m : ℕ₀):
  --   mul n (τ m) = sub (mul n m) n
  --     := by
  --   induction m with
  --   | zero =>
  --     have h_mul_n_tau_0_eq_0 : mul n (τ 𝟘) = 𝟘 := by
  --       calc
  --         mul n (τ 𝟘) = mul n 𝟘 := by rfl
  --         _ = 𝟘 := by rw [mul_zero n]
  --     have h_suv_mul_n_0_sub_n_eq_0 : sub (mul n 𝟘) n = 𝟘 := by
  --       calc
  --         sub (mul n 𝟘) n = sub 𝟘 n := by rw [mul_zero n]
  --         _ = 𝟘 := by exact zero_sub n
  --     rw [h_mul_n_tau_0_eq_0, h_suv_mul_n_0_sub_n_eq_0]
  --   | succ m' ih =>
  --     calc
  --       mul n (τ (σ m')) = mul n (τ (add m' 𝟙)):= by rfl
  --       _ = sub (mul n (σ m')) n := by
  --         rw [succ_mul]
  --         rw [sub_add_cancel (mul n m') n]
  --     by sorry

  end Mul

end Peano

export Peano.Mul(
  mul
  mul_zero
  zero_mul
  succ_mul
  mul_succ
  mul_one
  one_mul
  mul_two
  two_mul
  mul_three
  three_mul
  mul_comm
  mul_ldistr
  mul_rdistr
  mul_cancelation_left
  mul_cancelation_right
  mul_assoc
  mul_eq_zero
  mul_eq_zero_wp
  mul_le_right
  mul_le_left
  mul_le_full_right
  mul_le_full_left
)
