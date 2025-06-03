import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin

namespace Peano
    open Peano

    namespace Sub
        open Peano.Sub
        open Peano.Axioms
        open Peano.StrictOrder
        open Peano.Order
        open Peano.MaxMin
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
        simp [ h_n_eq_0 , h_eq ]
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
        -- Si ¬(m ≤ n), entonces n < m, lo cual implica n ≤ m
        have h_lt : Lt n m := nle_then_gt m n h
        exact lt_imp_le n m h_lt

  theorem subₕₖ_one (n : ℕ₀) (h: Le 𝟙 n):
    subₕₖ n 𝟙 h = ρ n ( m_neq_0_proved_lt_1_m h )
    := by
      induction n with
      | zero =>
        -- Caso imposible: 𝟙 ≤ 𝟘 es falso
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
      -- Mostrar que ρ n (m_neq_0_proved_lt_1_m h) = τ n
      cases n with
      | zero =>
        exfalso
        exact not_succ_le_zero 𝟘 h
      | succ n' =>
        simp [ρ, τ]
    · -- Caso: ¬Le 𝟙 n
      -- Si ¬Le 𝟙 n, entonces n = 𝟘
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
      simp [sub, τ, h]
      intro h'
      exfalso
      exact not_succ_le_zero 𝟘 h'


  -- theorem one_subₕₖ {m : ℕ₀} (h: Eq 𝟙 m):
  --  subₕₖ 𝟙 m h = ρ m (h_neq_0: ¬ Eq 𝟘 m)
  -- Este teorema no tiene sentido poque m solo puede ser 𝟘 o 𝟙
  -- Y aún en este caso, m = 𝟘 no puede ser porque no le puede sustraer 𝟙
  -- ya que 𝟘 < 𝟙. m tiene que ser 𝟙.

    theorem one_sub (m : ℕ₀) :
        sub 𝟙 m = 𝟘 ∨ sub 𝟙 m = 𝟙
            := by
      let h_trichotomy := Peano.StrictOrder.trichotomy 𝟙 m -- Esto da (𝟙 < m) ∨ (𝟙 = m) ∨ (m < 𝟙)
      --intro h_trichotomy
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
        -- Si m < 𝟙, entonces m = 𝟘
        have h_m_eq_zero : m = 𝟘 := by
          cases m with
          | zero => rfl
          | succ m' =>
            exfalso
            -- Since m < 𝟙 and m = σ m', we have σ m' < σ 𝟘, which is impossible
            have h_lt_one : σ m' < 𝟙 := h_m_lt_1
            have h_le_zero : Le (σ m') 𝟘 := by
                    have h_lt_zero : Lt (σ m') 𝟘 := by
                      rw [one] at h_lt_one
                      -- Now h_lt_one has type σ m' < σ 𝟘, which is Lt (σ m') (σ 𝟘)
                      -- We need Lt (σ m') 𝟘, but this is impossible since σ m' cannot be less than 𝟘
                      -- Let's use the fact that no successor is less than zero
                      exfalso
                      -- h_lt_one has type σ m' < σ 𝟘 (from rw [one] at h_lt_one earlier)
                      -- This implies m' < 𝟘 by succ_lt_succ_then
                      have h_m_prime_lt_zero : m' < 𝟘 := succ_lt_succ_then m' 𝟘 h_lt_one
                      -- This contradicts that m' (a natural number) cannot be less than 𝟘
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
        -- Caso k = 𝟘
        calc
          subₕₖ (σ n) 𝟘 (le_k_n_then_le_k_sn_wp h_k_le_n) = σ n := by simp [subₕₖ]
          _ = σ (subₕₖ n 𝟘 (zero_le n)) := by simp [subₕₖ_zero]
      | succ k' ih =>
        -- Caso k = σ k'
        cases n with
        | zero =>
          -- Caso n = 𝟘, pero σ k' ≤ 𝟘 es imposible
          exfalso
          have h_succ_le_zero : Le (σ k') 𝟘 := h_k_le_n
          exact not_succ_le_zero k' h_succ_le_zero
        | succ n' =>
          -- Caso n = σ n' y k = σ k'
          have h_k'_le_n' : Le k' n' := succ_le_succ_then h_k_le_n
          calc
            subₕₖ (σ (σ n')) (σ k') (le_k_n_then_le_k_sn_wp h_k_le_n)
                = subₕₖ (σ n') k' (succ_le_succ_then (le_k_n_then_le_k_sn_wp h_k_le_n))
                    := by simp [subₕₖ]
            _ = σ (subₕₖ n' k' h_k'_le_n') := by rw [ih n' h_k'_le_n']
          simp [subₕₖ, subₕₖ_zero]

  -- s(n) - k = s(n - k)
  -- Caso k = s(n) => 0 = s(n - k) = s(n - p(n)) = s0 = 1 !!!
  -- Caso k < s(n) <=> Le k n => s(n) - k = s(n - k)
  -- Caso k > s(n) => s(n) - k = 0; s(n - k) = s0 = 1 !!!
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
        -- Caso n = 𝟘
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
        -- Caso n = σ n'
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
            _ = σ n' := by simp [add, one]

  theorem subₕₖ_k_add_k_forall (n: ℕ₀):
      ∀ (k : ℕ₀) (h_le : k <= n), add (subₕₖ n k h_le) k = n
          := by
      intro k h_le
      exact subₕₖ_k_add_k n k h_le

  theorem add_k_subₕₖ_k (n k : ℕ₀) :
      subₕₖ (add k n) k (le_self_add k n) = n
      := by
    induction n with
    | zero =>
      -- Caso n = 𝟘
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
      -- Caso n = σ n'
      have h_k_le_add : k <= add k n' := le_self_add k n'
      calc
        subₕₖ (add k (σ n')) k (Peano.Add.le_self_add k (σ n')) =
          subₕₖ (σ (add k n')) k (Peano.Add.le_self_add k (σ n'))
              := by simp [add]
        _ = σ (subₕₖ (add k n') k h_k_le_add)
              := by rw [subₕₖ_succ (add k n') k h_k_le_add]
        _ = σ n' := by rw [ih]

  -- theorem add_k_sub_k (n k : ℕ₀) :
  --     sub (add k n) k = n
  --     := by
  --   have h_k_le_add : k <= add k n := le_self_add k n
  --   have h_sub_eq : sub (add k n) k = subₕₖ (add k n) k h_k_le_add
  --       := by
  --         simp only [sub, dif_pos h_k_le_add]
  --   rw [h_sub_eq]
  --   exact add_k_subₕₖ_k n k



        -- Ahora tenemos que demostrar que σ n' = n'
        -- Esto es cierto porque:
        -- σ n' = n' si n' = 𝟘


        -- Ahora tenemos que demostrar que σ (sub n' k) + k = σ n'
        -- Esto es cierto porque:
        -- σ (sub n' k) + k = σ n' si k < n'
        -- σ (sub n' k) + k = σ n' si k = n'
        -- σ (sub n' k) + k = σ n' si k > n'



        -- Ahora tenemos que demostrar que σ (subₕₖ n' k h_k_le_n') + k = σ n'
        -- Esto es cierto porque:
        -- σ (subₕₖ n' k h_k_le_n') + k = σ n' si k < n'
        -- σ (subₕₖ n' k h_k_le_n') + k = σ n' si k = n'
        -- σ (subₕₖ n' k h_k_le_n') + k = σ n' si k > n'
      -- En resumen, tenemos que demostrar que:
        -- add (subₕₖ n' k h_k_le_n') k = n'
  -- substract_k_add_k (n: ℕ₀):


  -- substract_k_add_k (n: ℕ₀):
  --     ∀ (k : ℕ₀) (h_le : k <= n),
  --        add (substract n k h_le) k = n
  --     := by
  --     intro k h_le
  --     induction n with
  --     | zero =>
  --       -- Caso n = truck 𝟘
  --       have h_k_le_zero : k <= 𝟘 := h_le
  --       have h_k_eq_zero : k = 𝟘 := by
  --         have h_k_lt_zero : k < 𝟘 := le_then_lt k 𝟘 h_k_le_zero
  --         exact not_succ_le_zero k h_k_lt_zero
  --       rw [h_k_eq_zero]
  --       calc
  --         add (substract 𝟘 𝟘 (zero_le 𝟘)) 𝟘 = add 𝟘 𝟘 := by simp [substract]
  --         _ = 𝟘 := by simp [add]
  --     | succ n' ih =>
  --       -- Caso n = σ n'
  --       have h_k_le_n' : k <= n' := succ_le_succ_then h_le
  --       have h_sub_eq : substract (σ n') k h_k_le_n' = subₕₖ (σ n') k h_k_le_n' := by simp [substract, h_k_le_n']
  --       rw [h_sub_eq]
  --       calc
  --         add (subₕₖ (σ n') k h_k_le_n') k = add (σ (subₕₖ n' k h_k_le_n')) k
  --           := by rw [subₕₖ_succ n' k h_k_le_n']
  --         _ = σ (subₕₖ n' k h_k_le_n') + k := by simp [add]
  --         _ = σ (substract n' k h_k_le_n') + k := by rw [ih n' h_k_le_n']
        -- Ahora tenemos que demostrar que σ (substract n' k h_k_le_n') + k = σ n'
  --       -- Esto es cierto porque:

--  k ≤ n → σ n - k = n + 1 - k
-- substract_k_add_k (n: ℕ₀):
--     ∀ (k : ℕ₀) (h_le : k <= n),
--        add (substract n k h_le) k = n
--     := by sorry


    end Sub


end Peano
