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

  theorem obvio_1 (n : ℕ₀) :
    Le n (mul n 𝟙)
      := by
    rw [mul_one n]
    exact le_refl n

  theorem le_n_mul_n_σn (n m : ℕ₀):
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
      exact le_n_mul_n_σn n m'

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
      have h_one_not_le_zero : ¬ (Le 𝟙 𝟘) := le_succ_0_then_false 𝟘
      exact False.elim (h_one_not_le_zero h_le_1_m)
    | succ m' ih => -- m = σ m'
      rw [add_succ n m', mul_succ] -- Goal: Lt (mul k n) (add (mul k (add n m')) k)
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
        apply lt_add_succ; -- Goal is `Lt X (σ (X + τ k))`, matches `lt_add_succ X (τ k)`
      cases m' with
      | zero => -- m' = 𝟘. So m = σ 𝟘 = 𝟙.
        rw [add_zero] -- Goal becomes Lt (mul k n) (add (mul k n) k)
        exact h_lt_b_c
      | succ m'' => -- m' = σ m''. So m = σ (σ m'').
        have h_le_1_m_prime_proof : Le 𝟙 (σ m'') := by
          exact le_1_succ m'' -- Use le_succ_all to show 1 ≤ σ m''
        have h_lt_a_b_from_ih : Lt (mul k n) (mul k (add n (σ m''))) := ih h_le_1_m_prime_proof
        exact lt_trans (mul k n) (mul k (add n (σ m''))) (add (mul k (add n (σ m''))) k) h_lt_a_b_from_ih h_lt_b_c

  theorem mul_le_mono_right (k : ℕ₀) {n m : ℕ₀} (h_le : Le n m) :
    Le (mul n k) (mul m k)
      := by
    cases (le_iff_exists_add n m).mp h_le with | intro d hd =>
    rw [hd, mul_rdistr]
    exact add_le (mul n k) (mul n k) (mul d k) (le_refl (mul n k))

  theorem lt_σn_mul_σn_σσm (n m : ℕ₀):
    Lt (σ n) (mul (σ n) (σ (σ m)))
      := by
    have h_neq_0 : σ n ≠ 𝟘 := succ_neq_zero n
    have h_lt_1 : Lt 𝟙 (σ (σ m)) := lt_1_succ_succ m
    exact mul_lt_left (σ n) (σ (σ m)) h_neq_0 h_lt_1

  theorem τ0_eq_0 :
    τ 𝟘 = 𝟘
      := by rfl

  theorem τn_eq_m {n : ℕ₀} (h_n_neq_zero : Le n 𝟘) :
    τ n = 𝟘
      := by
    induction n with
    | zero => rfl
    | succ n' ih =>
      exfalso
      exact le_succ_0_then_false n' h_n_neq_zero

  theorem τ_σ (n : ℕ₀) :
    τ (σ n) = n
      := by
    induction n with
    | zero => rfl
    | succ n' ih =>
      calc
        τ (σ (σ n')) = σ n' := by rfl
        _ = add n' 𝟙 := by rfl

  theorem σ_τ (n : ℕ₀):
    σ (τ (σ n)) = σ n ∨ σ (τ 𝟘) = 𝟙
      := by
    induction n with
    | zero =>
      have h_τ_0_eq_0 : τ 𝟘 = 𝟘 := by rfl
      have h_sigma_τ_0_eq_one : σ (τ 𝟘) = σ 𝟘 := by rfl
      exact Or.inr h_sigma_τ_0_eq_one
    | succ n' ih =>
      have h_τ_σ_σ_n'_eq_σ_n' : τ (σ (σ n')) = σ n' := by rfl
      have h_σ_τ_σ_σ_n'_eq_σ_σ_n' : σ (τ (σ (σ n'))) = σ (σ n') := by rw [h_τ_σ_σ_n'_eq_σ_n']
      exact Or.inl h_σ_τ_σ_σ_n'_eq_σ_σ_n'

  theorem σ_τ_0 :
    σ (τ 𝟘) = 𝟙
      := by
    have h_τ_0_eq_0 : τ 𝟘 = 𝟘 := by rfl
    have h_sigma_τ_0_eq_one : σ (τ 𝟘) = σ 𝟘 := by rfl
    exact h_sigma_τ_0_eq_one

  theorem σ_τ_eq_id_pos_forall (n : ℕ₀) (h_neq_0 : n ≠ 𝟘) :
    σ (τ n) = n
      := by
    cases n with
    | zero => exact False.elim (h_neq_0 rfl)
    | succ n' =>
      rw [τ_σ]

  theorem mul_n_τm (n m : ℕ₀) (h_m_neq_0 : m ≠ 𝟘) :
    mul n (τ m) = sub (mul n m) n
      := by
    have h_sigma_τ_eq_id_pos : σ (τ m) = m := σ_τ_eq_id_pos_forall m h_m_neq_0
    have h_mul_succ : mul n (σ (τ m)) = add (mul n (τ m)) n := mul_succ n (τ m)
    have h_mul_n_m : mul n m = add (mul n (τ m)) n := by
      rw [←h_sigma_τ_eq_id_pos]
      exact h_mul_succ
    have h_sub_add : sub (add (mul n (τ m)) n) n = mul n (τ m) := by
      rw [add_comm (mul n (τ m)) n, add_k_sub_k_forall]
    rw [←h_mul_n_m] at h_sub_add
    exact h_sub_add.symm

  theorem mul_τn_m (n m : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) :
    mul (τ n) m = sub (mul n m) m
      := by
    have h_sigma_τ_eq_id_pos : σ (τ n) = n := σ_τ_eq_id_pos_forall n h_n_neq_0
    have h_mul_succ : mul (σ (τ n)) m = add (mul (τ n) m) m := succ_mul (τ n) m
    have h_mul_n_m : mul n m = add (mul (τ n) m) m := by
      rw [←h_sigma_τ_eq_id_pos]
      exact h_mul_succ
    have h_sub_add : sub (add (mul (τ n) m) m) m = mul (τ n) m := by
      rw [add_comm (mul (τ n) m) m, add_k_sub_k_forall]
    rw [←h_mul_n_m] at h_sub_add
    exact h_sub_add.symm

  theorem lt_of_lt_of_le {a b c : ℕ₀} (h_lt_ab : Lt a b) (h_le_bc : Le b c) :
    Lt a c
      := by
    cases h_le_bc with
    | inl h_lt_bc => exact lt_trans a b c h_lt_ab h_lt_bc
    | inr h_eq_bc =>
      rw [←h_eq_bc]
      exact h_lt_ab

  theorem archimedean_property {n m : ℕ₀} (h_n_pos : Lt 𝟘 n) :
    ∃ j, Lt m (mul j n)
      := by
    -- Un candidato simple es j = σ m.
    exists (σ m)
    -- Queremos probar: m < (σ m) * n
    have h_mul_ge_self : Le (σ m) (mul (σ m) n) := by
      -- Esto es porque n ≥ 1 (ya que n > 0)
      have h_n_ge_1 : Le 𝟙 n := by
        exact lt_0n_then_le_1n_wp h_n_pos
      -- Si n = 1, (σ m) * 1 = σ m. Si n > 1, (σ m) * n > σ m.
      -- Un lema general sería: Le a (mul a b) si Le 𝟙 b
      exact mul_le_right (σ m) n (le_1_m_then_m_neq_0 n h_n_ge_1)
    -- Como m < σ m y σ m ≤ (σ m) * n, por transitividad m < (σ m) * n
    exact lt_of_lt_of_le (lt_self_σ_self m) h_mul_ge_self

  theorem exists_unique_mul_le_and_lt_succ_mul (n m : ℕ₀) (h_n_pos : Lt 𝟘 n) :
    -- Consideramos el conjunto de múltiplos de n que son mayores que m.
    let S := { j : ℕ₀ // Lt m (mul j n) }

    -- 1. Este conjunto S no es vacío, por la propiedad de Arquímedes.

    -- ======= PARTE 1: EXISTENCIA ========
    -- Usaremos el principio del buen orden.
    -- Consideramos el conjunto de múltiplos de n que son mayores que m.
    let S := { j : ℕ₀ // Lt m (mul j n) }

    -- 1. Este conjunto S no es vacío, por la propiedad de Arquímedes.
    have h_S_nonempty : ∃ j, j ∈ S := by
      -- Desplegamos la definición de S para h_j_is_in_S
      -- h_j_is_in_S : Lt m (mul j n)
      let j := Nat.find h_S_nonempty
      have h_j_is_in_S : j ∈ S := Nat.find_spec h_S_nonempty
      have h_j_is_minimal : ∀ j' < j, j' ∉ S := Nat.find_min h_S_nonempty

    -- Desplegamos la definición de S para h_j_is_in_S
    unfold S at h_j_is_in_S
    -- h_j_is_in_S : Lt m (mul j n)

    -- 3. Este j no puede ser 0, porque m < 0 * n (m < 0) es falso.
    have h_j_neq_zero : j ≠ 𝟘 := by
      intro h_j_zero
      rw [h_j_zero] at h_j_is_in_S
      rw [mul_zero] at h_j_is_in_S -- Ahora h_j_is_in_S : Lt m 𝟘, lo cual es imposible.
      exact lt_zero m h_j_is_in_S

    -- 4. Como j ≠ 0, j debe ser el sucesor de algún número. Llamémoslo k.
    -- k es el predecesor de j.
    let k := τ j
    have h_j_eq_succ_k : j = σ k := by
      -- Usamos el teorema que tienes en Axioms: σ (τ n) = n si n ≠ 𝟘
      rw [← σ_τ_eq_id_pos_forall j h_j_neq_zero] -- Reemplaza con el nombre de tu lema si es diferente
      rfl

    -- 5. Demostramos que este k es el que buscamos.
    -- Proponemos k como nuestro candidato.
    exists k

    -- Debemos probar P(k), es decir, las dos partes del ∧.
      -- Si k ∉ S, entonces ¬(Lt m (mul k n)).
      -- Por tricotomía, si no es 'menor que', tiene que ser 'menor o igual que'.
    · -- Como k < j y j es el elemento MÍNIMO de S, k no puede estar en S.
      have h_k_lt_j : Lt k j := by rw [h_j_eq_succ_k]; exact lt_self_σ_self k
      have h_k_not_in_S : k ∉ S := h_j_is_minimal k h_k_lt_j
      -- Si k ∉ S, entonces ¬(Lt m (mul k n)).
      unfold S at h_k_not_in_S
      -- Por tricotomía, si no es 'menor que', tiene que ser 'menor o igual que'.
      rcases (trichotomy m (mul k n)) with h_lt | h_eq | h_gt
      · exfalso; exact h_k_not_in_S h_lt -- Contradicción con k ∉ S
      · exact le_of_eq_wp h_eq
      · exact lt_imp_le_wp h_gt

    -- Segunda parte de P(k): Lt m (mul (σ k) n)
    · -- Esto es exactamente la propiedad de j, ya que j = σ k
      rw [← h_j_eq_succ_k]
      exact h_j_is_in_S

    -- ======= PARTE 2: UNICIDAD ========
    -- Ahora probamos que si k₁ y k₂ cumplen P, entonces k₁ = k₂.
    · intros k₁ h_P_k₁
      intros k₂ h_P_k₂

      -- Usamos la antisimetría de Le: si k₁ ≤ k₂ y k₂ ≤ k₁, entonces k₁ = k₂.
      apply le_antisymm

      -- Sub-objetivo 1: Probar Le k₁ k₂
      · -- Suponemos por contradicción que no es así, es decir, Lt k₂ k₁.
        by_contradiction h_not_le
        have h_k2_lt_k1 : Lt k₂ k₁ := nle_then_gt k₁ k₂ h_not_le

        -- De P(k₂), sabemos que m < mul (σ k₂) n
        have h_m_lt_succ : Lt m (mul (σ k₂) n) := h_P_k₂.right

        have h_mul_le : Le (mul (σ k₂) n) (mul k₁ n) :=
            mul_le_mono_right n h_succ_k2_le_k1
        -- Como la multiplicación por n > 0 preserva el orden (necesitarás este lema):
        -- σ k₂ ≤ k₁  =>  (σ k₂) * n ≤ k₁ * n
        have h_mul_le : Le (mul (σ k₂) n) (mul k₁ n) := by
            -- Este es un lema importante: le_then_le_add (o similar para mul)
            exact le_then_le_add_r_add_r_then_le (σ k₂) k₁ n h_succ_k2_le_k1 -- ajusta el nombre

        -- De P(k₁), sabemos que mul k₁ n ≤ m.
        have h_k1_mul_le_m : Le (mul k₁ n) m := h_P_k₁.left

        -- Ahora encadenamos las desigualdades:
        -- m < (σ k₂) * n  y  (σ k₂) * n ≤ k₁ * n  y  k₁ * n ≤ m
        -- Esto implica m < m, lo cual es una contradicción.
        have h_m_lt_m : Lt m m := lt_trans m (mul (σ k₂) n) m h_m_lt_succ (le_trans (mul (σ k₂) n) (mul k₁ n) m h_mul_le h_k1_mul_le_m)

        -- Usamos el lema de que un número no puede ser menor que sí mismo.
        exact lt_irrefl m h_m_lt_m

      -- Sub-objetivo 2: Probar Le k₂ k₁
      · -- La prueba es simétrica a la anterior.
        by_contradiction h_not_le
        have h_mul_le : Le (mul (σ k₁) n) (mul k₂ n) := mul_le_mono_right n h_succ_k1_le_k2

        have h_m_lt_succ : Lt m (mul (σ k₁) n) := h_P_k₁.right
        have h_succ_k1_le_k2 : Le (σ k₁) k₂ := (lt_succ_iff_lt_or_eq_alt k₁ k₂).mp h_k1_lt_k2
        have h_mul_le : Le (mul (σ k₁) n) (mul k₂ n) := le_then_le_add_r_add_r_then_le (σ k₁) k₂ n h_succ_k1_le_k2
        have h_k2_mul_le_m : Le (mul k₂ n) m := h_P_k₂.left

        have h_m_lt_m : Lt m m := lt_trans m (mul (σ k₁) n) m h_m_lt_succ (le_trans (mul (σ k₁) n) (mul k₂ n) m h_mul_le h_k2_mul_le_m)
        exact lt_irrefl m h_m_lt_m

  theorem mul_le_then_exists_max_factor {n m : ℕ₀} (h_le : Le n m) (h_neq_0 : n ≠ 𝟘):
    ∃ (k : ℕ₀), Le (mul k n) m ∧ ∀ (k' : ℕ₀), Le (mul k' n) m → Le k' k
      := by
    induction m with
    | zero =>
      have h_n_neq_zero : n ≠ 𝟘 := h_neq_0
      have h_n_eq_zero : n = 𝟘 := le_zero_eq_wp h_le
      exact False.elim (h_n_neq_zero h_n_eq_zero)
    | succ m' ih =>
      cases n with
      | zero =>
        have h_n_neq_zero : 𝟘 ≠ 𝟘 := h_neq_0
        exact False.elim (h_n_neq_zero rfl)
      | succ n' =>
        -- n = σ n', m = σ m'
        -- n' ≤ m' by h_le
        -- ih : Le n m' → ∃ k, Le (k*n) m' ∧ ∀ (k' : ℕ₀), Le (k'*n) m' → Le k' k
        -- ih : Le σn' m' → ∃ k, Le (k*σn') m' ∧ ∀ (k' : ℕ₀), Le (k'*σn') m' → Le k' k
        -- go : Le σn' σm' → ∃ k, Le (k*σn') σm' ∧ ∀ (k' : ℕ₀), Le (k'*σn') σm' → Le k' k
        have h_le_n_m' : Le (σ n') m' := by
          cases h_le with
          | inl h_lt =>
            -- h_lt : Lt (σ n') (σ m'), so n' < m'
            have h_lt_n_m' : Lt n' m' := succ_lt_succ_inv h_lt
            exact lt_imp_le h_lt_n_m'
          | inr h_eq => exact Or.inr h_lt
        have ⟨k, h_le_k_n, h_max⟩ := ih h_le_n_m' (succ_neq_zero n')
        exact
          ⟨   k,
              le_refl (mul k.val n'), fun k' h_le_k'_n =>
              have h_le_k'_n' : Le (mul k'.val n) m' := by
                rw [mul_comm k'.val n]
                exact h_le_k'_n
              have h_k'_le_k : Le k'.val k.val := h_max k' h_le_k'_n'
              h_k'_le_k
          ⟩

  -- theorem le_le_mul_le_compat {n m k l: ℕ₀} (h_le_n_m : Le n m) (h_le_k_l : Le k l) :
  --   Le (mul n k) (mul m l)
  --     := by
  --   induction l generalizing k with
  --   | zero =>
  --     rw [mul_zero]
  --     have h_k_eq_zero : k = 𝟘 := by
  --       cases k with
  --       | zero => rfl
  --       | succ k' =>
  --         have h_succ_le_zero : Le (σ k') 𝟘 := h_le_k_l
  --         exact False.elim (le_succ_0_then_false k' h_succ_le_zero)
  --     rw [h_k_eq_zero, mul_zero]
  --     exact le_refl 𝟘
  --   | succ l' ih =>
  --     rw [mul_succ]
  --     have h_le_k_l' : Le k l' := by
  --       cases k with
  --       | zero => exact zero_le l'
  --       | succ k' =>
  --         have h_succ_le_succ : Le (σ k') (σ l') := h_le_k_l
  --         have h_le_k'_l' : Le k' l' := by
  --           cases h_succ_le_succ with
  --           | inl h_eq =>
  --             have h_k'_eq_l' : k' = l' := succ_inj h_eq
  --             rw [h_k'_eq_l']
  --             exact le_refl l'
  --           | inr h_lt =>
  --             have h_lt_k'_l' : Lt k' l' := succ_lt_succ_inv h_lt
  --             exact lt_imp_le h_lt_k'_l'
  --         exact le_succ_trans h_le_k'_l'
  --     have h_le_mul : Le (mul n k) (mul m l') := ih h_le_k_l'
  --     exact le_trans (mul n k) (mul m l') (add (mul m l') m) h_le_mul (add_le (mul m l') (mul m l') m (le_refl (mul m l')))

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
  mul_n_τm
  mul_τn_m
  le_n_mul_n_σn
  lt_σn_mul_σn_σσm
)
