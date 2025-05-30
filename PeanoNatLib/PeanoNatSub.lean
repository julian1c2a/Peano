import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatAdd

namespace Peano
    open Peano
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order hiding lt_then_neq
    open Peano.Add
    open Peano.MaxMin

    namespace Sub
        open Peano.Sub

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
        subₕₖ 𝟘 𝟘 (zero_le 𝟘) = 𝟘 := by rw [subₕₖ]
        _ = 𝟘 := rfl
    | succ n' ih =>
      calc
        subₕₖ (σ n') 𝟘 (zero_le (σ n')) = σ n'
            := by rw [subₕₖ]
        _ = σ n' := rfl

  theorem zero_subₕₖ (n : ℕ₀) (h : Le n 𝟘) :
    subₕₖ 𝟘 n h = 𝟘
      := by
    cases n with
    | zero =>
      calc
        subₕₖ 𝟘 𝟘 (zero_le 𝟘) = 𝟘 := by rw [subₕₖ]
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
        _ = 𝟘 := by rw [subₕₖ]
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
        _ = 𝟘 := by rw [subₕₖ]
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
      match h_eq_nm : n = m with
      | True =>
        exact le_refl n
      | False =>
        exact not_le_zero m h_eq_nm

    theorem subₕₖ_one (n : ℕ₀) (h: Le 𝟙 n):
      subₕₖ n 𝟙 h = ρ n h
        := by
      induction n with
      | zero =>
        simp [subₕₖ, ρ]
      | succ n' =>
        simp [subₕₖ, ρ]
        exact succ_le_succ h

  theorem sub_one (n : ℕ₀) :
    sub n 𝟙 = τ n
      := by
    cases n with
    | zero =>
      calc
        sub 𝟘 𝟙 = subₕₖ 𝟘 𝟙 (zero_le 𝟘) := by rfl
        _ = 𝟘 := by rw [subₕₖ_one]
    | succ n' =>
      calc
        sub (σ n') 𝟙 = subₕₖ (σ n') 𝟙 (zero_le (σ n'))
            := by rfl
        _ = ρ (σ n') := by rw [subₕₖ_one]

--    theorem one_subₕₖ (m : ℕ₀) (h: Le m 𝟙):
--      subₕₖ 𝟙 m h = ρ m h
--        := by

--  theorem sub_succ (n k : ℕ₀) :
--     sub (σ n) k = σ (sub n k)
--      := by
--       match k with
--        | 𝟘 =>
--          calc
--            sub (σ n) 𝟘 = σ n := by rw [sub_zero]
--            _ = σ (sub n 𝟘) := rfl
--        | σ k' =>
--          calc
--            sub (σ n) k' = σ (sub n k') := by rw [sub_succ]
--            _ = σ (sub n (σ k')) := rfl
--        termination_by n k
--
--  k ≤ n → σ n - k = n + 1 - k
--

--  theorem substract_k_add_k (n: ℕ₀): ∀ (k : ℕ₀) (h_le : k <= n), add (substract n k h_le) k = n := by
--    sorry


end Sub
end Peano
