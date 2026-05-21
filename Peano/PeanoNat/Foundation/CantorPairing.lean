/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Foundation/CantorPairing.lean
--
-- Enuncia y bosqueja la prueba de que ℕ₀ × ℕ₀ ≅ ℕ₀ (apareamiento de Cantor).
-- Las pruebas aritméticas quedan pendientes de completar.
--
-- NOTAS PARA COMPLETAR:
--  · triag_succ : requiere  div_add_exact  y  two_dvd_mul_succ
--  · antidiag_exists : el caso succ necesita T estrictamente creciente
--  · antidiag_unique : el caso lt/gt por tricotomía de lt₀
--  · fst_pair : requiere  sub_add_left : a + b - a = b
--  · snd_pair : requiere  add_sub_cancel_left : (m + n) - m = n
--  · pair_surj : combina los anteriores con antidiag_spec

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Sqrt

namespace Peano
  open Peano

  namespace Foundation
    open Foundation
    open Peano.Sub
    open Peano.Sqrt

  -- ─────────────────────────────────────────────────────────────────────────
  -- 1. Número triangular T(n) = n*(n+1)/2
  -- ─────────────────────────────────────────────────────────────────────────

  /-- T(n) = n*(n+1)/2. La división es exacta (uno de n, n+1 es par). -/
  def triag (n : ℕ₀) : ℕ₀ := mul n (σ n) / 𝟚

  -- ── auxiliares privados ──────────────────────────────────────────────────

  /-- 2 ∣ n·(n+1) para todo n : por inducción. -/
  private theorem two_dvd_mul_succ (n : ℕ₀) : 𝟚 ∣ mul n (σ n) := by
    induction n with
    | zero => exact ⟨𝟘, by rw [zero_mul, mul_zero]⟩
    | succ n' ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨add k (σ n'), ?_⟩
      -- goal: mul (σ n') (σ (σ n')) = mul 𝟚 (add k (σ n'))
      calc mul (σ n') (σ (σ n'))
          = add (mul (σ n') (σ n')) (σ n')        := by rw [mul_succ]
        _ = add (add (mul n' (σ n')) (σ n')) (σ n') := by rw [succ_mul]
        _ = add (add (mul 𝟚 k) (σ n')) (σ n')      := by rw [hk]
        _ = add (mul 𝟚 k) (add (σ n') (σ n'))      := by rw [add_assoc]
        _ = add (mul 𝟚 k) (mul 𝟚 (σ n'))           := by rw [← two_mul]
        _ = mul 𝟚 (add k (σ n'))                   := by rw [← mul_add]

  /-- (2·m)/2 = m. -/
  private theorem mul_two_div_two (m : ℕ₀) : mul 𝟚 m / 𝟚 = m := by
    have h2ne : 𝟚 ≠ 𝟘 := (zero_ne_succ _).symm
    have h_dvd : 𝟚 ∣ mul 𝟚 m := divides_mul_right (divides_refl 𝟚)
    have h_eq  : mul (mul 𝟚 m / 𝟚) 𝟚 = mul 𝟚 m := div_mul_cancel h2ne h_dvd
    exact mul_cancelation_right _ m 𝟚 h2ne (h_eq.trans (mul_comm 𝟚 m))

  -- ── teoremas principales ─────────────────────────────────────────────────

  theorem triag_zero : triag 𝟘 = 𝟘 := by
    show mul 𝟘 (σ 𝟘) / 𝟚 = 𝟘
    rw [zero_mul]
    exact div_of_lt 𝟘 𝟚 (lt_zero_succ 𝟙)

  theorem triag_succ (n : ℕ₀) : triag (σ n) = add (triag n) (σ n) := by
    obtain ⟨k, hk⟩ := two_dvd_mul_succ n
    have htn : triag n = k := by
      show mul n (σ n) / 𝟚 = k
      rw [hk]; exact mul_two_div_two k
    have hmain : mul (σ n) (σ (σ n)) = mul 𝟚 (add k (σ n)) := by
      calc mul (σ n) (σ (σ n))
          = add (mul (σ n) (σ n)) (σ n)          := by rw [mul_succ]
        _ = add (add (mul n (σ n)) (σ n)) (σ n)  := by rw [succ_mul]
        _ = add (add (mul 𝟚 k) (σ n)) (σ n)      := by rw [hk]
        _ = add (mul 𝟚 k) (add (σ n) (σ n))      := by rw [add_assoc]
        _ = add (mul 𝟚 k) (mul 𝟚 (σ n))          := by rw [← two_mul]
        _ = mul 𝟚 (add k (σ n))                   := by rw [← mul_add]
    show mul (σ n) (σ (σ n)) / 𝟚 = add (triag n) (σ n)
    rw [hmain, mul_two_div_two, htn]

  theorem triag_strict_mono {m n : ℕ₀} (h : Peano.StrictOrder.lt₀ m n) :
      Peano.StrictOrder.lt₀ (triag m) (triag n) := by
    induction n with
    | zero => exact absurd h (nlt_n_0 m)
    | succ n' ih =>
      have h_le := (lt_succ_iff_le m n').mp h
      rcases (le_iff_lt_or_eq m n').mp h_le with h_lt | h_eq
      · exact lt_trans _ _ _
            (ih h_lt)
            (by rw [triag_succ]; exact lt_add_of_pos_right (lt_zero_succ n'))
      · subst h_eq
        rw [triag_succ]
        exact lt_add_of_pos_right (lt_zero_succ m)

  theorem triag_le_of_le {m n : ℕ₀} (h : Peano.Order.le₀ m n) :
      Peano.Order.le₀ (triag m) (triag n) := by
    rcases (le_iff_lt_or_eq m n).mp h with h_lt | h_eq
    · exact (le_iff_lt_or_eq _ _).mpr (Or.inl (triag_strict_mono h_lt))
    · subst h_eq; exact le_refl _

  -- ─────────────────────────────────────────────────────────────────────────
  -- 2. Función de apareamiento de Cantor
  -- ─────────────────────────────────────────────────────────────────────────

  /-- pair(m,n) = T(m+n) + m. -/
  def pair (m n : ℕ₀) : ℕ₀ := add (triag (add m n)) m

  theorem triag_le_pair (m n : ℕ₀) :
      Peano.Order.le₀ (triag (add m n)) (pair m n) := by
    unfold pair
    exact le_self_add _ _

  theorem pair_lt_triag_succ (m n : ℕ₀) :
      Peano.StrictOrder.lt₀ (pair m n) (triag (σ (add m n))) := by
    unfold pair
    rw [triag_succ]
    exact (add_lt_add_left_iff (triag (add m n)) m (σ (add m n))).mpr (lt_add_succ m n)

  -- ─────────────────────────────────────────────────────────────────────────
  -- 3. Anti-diagonal
  -- ─────────────────────────────────────────────────────────────────────────

  theorem antidiag_exists (z : ℕ₀) :
      ∃ w : ℕ₀,
        Peano.Order.le₀ (triag w) z ∧
        Peano.StrictOrder.lt₀ z (triag (σ w)) := by
    induction z with
    | zero =>
      exact ⟨𝟘,
        by rw [triag_zero]; exact le_refl _,
        by rw [triag_succ, triag_zero, zero_add]; exact lt_zero_succ _⟩
    | succ z' ih =>
      obtain ⟨w, h_le, h_lt⟩ := ih
      rcases trichotomy (σ z') (triag (σ w)) with h1 | h2 | h3
      · exact ⟨w, le_trans _ _ _ h_le (le_n_m_then_le_n_sm z' z' (le_refl z')), h1⟩
      · exact ⟨σ w,
          by rw [← h2]; exact le_refl _,
          by rw [h2]; exact triag_strict_mono (lt_succ_self (σ w))⟩
      · exfalso
        exact absurd
          ((lt_succ_iff_le (triag (σ w)) z').mp h3)
          (gt_then_nle z' (triag (σ w)) h_lt)

  theorem antidiag_unique (z : ℕ₀) :
      ExistsUnique (fun w =>
        Peano.Order.le₀ (triag w) z ∧
        Peano.StrictOrder.lt₀ z (triag (σ w))) := by
    obtain ⟨w, h_le, h_lt⟩ := antidiag_exists z
    refine ⟨w, ⟨h_le, h_lt⟩, ?_⟩
    intro w' h_w'
    have h_le' := h_w'.1
    have h_lt' := h_w'.2
    rcases trichotomy w' w with h1 | h2 | h3
    · exfalso
      have h_sw'_le_w : le₀ (σ w') w := by
        cases w with
        | zero => exact absurd h1 (nlt_n_0 w')
        | succ w'' =>
          exact (succ_le_succ_iff w' w'').mpr ((lt_succ_iff_le w' w'').mp h1)
      exact absurd
        (le_trans _ _ _ (triag_le_of_le h_sw'_le_w) h_le)
        (gt_then_nle z (triag (σ w')) h_lt')
    · exact h2
    · exfalso
      have h_sw_le_w' : le₀ (σ w) w' := by
        cases w' with
        | zero => exact absurd h3 (nlt_n_0 w)
        | succ w'' =>
          exact (succ_le_succ_iff w w'').mpr ((lt_succ_iff_le w w'').mp h3)
      exact absurd
        (le_trans _ _ _ (triag_le_of_le h_sw_le_w') h_le')
        (gt_then_nle z (triag (σ w)) h_lt)

  -- ─────────────────────────────────────────────────────────────────────────
  -- Auxiliares para antidiag computable
  -- ─────────────────────────────────────────────────────────────────────────

  -- 2·triag(s) = s·(s+1)
  private theorem two_mul_triag (s : ℕ₀) : mul 𝟚 (triag s) = mul s (σ s) := by
    unfold triag
    have h_dvd := two_dvd_mul_succ s
    obtain ⟨k, hk⟩ := h_dvd
    -- hk : mul s (σ s) = mul 𝟚 k
    -- triag s = mul s (σ s) / 𝟚 = mul 𝟚 k / 𝟚 = k
    have htn : mul s (σ s) / 𝟚 = k := by rw [hk]; exact mul_two_div_two k
    rw [htn, hk]

  /-- La anti-diagonal de z: único w con T(w) ≤ z < T(w+1).
      Definición computable: s = ⌊√(2z)⌋; si T(s) ≤ z entonces s, sino s-1. -/
  def antidiag (z : ℕ₀) : ℕ₀ :=
    let s := sqrt (mul 𝟚 z)
    if Peano.Order.le₀ (triag s) z then s else sub s 𝟙

  -- Helper: 2·a ≤ 2·b → a ≤ b
  private theorem le_of_two_mul_le {a b : ℕ₀} (h : Peano.Order.le₀ (mul 𝟚 a) (mul 𝟚 b)) :
      Peano.Order.le₀ a b := by
    rcases trichotomy a b with h1 | h1 | h1
    · exact lt_imp_le _ _ h1
    · exact h1 ▸ le_self_of_eq_self _ rfl
    · exfalso
      -- b < a → mul 𝟚 b < mul 𝟚 a  (strict) → combined with h gives irrefl
      have hba : Peano.Order.le₀ (mul 𝟚 b) (mul 𝟚 a) := by
        rw [mul_comm 𝟚 b, mul_comm 𝟚 a]
        exact mul_le_mono_right 𝟚 (lt_imp_le _ _ h1)
      have hne : b ≠ a := ne_of_lt b a h1
      have hne2 : mul 𝟚 b ≠ mul 𝟚 a := fun heq =>
        absurd (mul_cancelation_left 𝟚 b a (by decide) heq) hne
      exact lt_irrefl (mul 𝟚 b)
        (lt_of_lt_of_le (lt_of_le_of_ne _ _ hba hne2) h)

  -- Helper: σ(s-1) = s when s ≠ 0
  private theorem succ_sub_one {s : ℕ₀} (hs : s ≠ 𝟘) : σ (sub s 𝟙) = s := by
    cases s with
    | zero => exact absurd rfl hs
    | succ s' =>
      have h_1_le : Peano.Order.le₀ 𝟙 (σ s') := by
        cases s' with
        | zero => simp [one, le₀, zero]
        | succ s'' => simp [one, le₀, zero]; exact zero_lt_succ (σ s'')
      -- sub_k_add_k (σ s') 𝟙 h_1_le : add (sub (σ s') 𝟙) 𝟙 = σ s'
      have h := sub_k_add_k (σ s') 𝟙 h_1_le
      -- h : add (sub (σ s') 𝟙) 𝟙 = σ s'
      -- want : σ (sub (σ s') 𝟙) = σ s'
      -- add n 𝟙 = σ n by add_one, so sub (σ s') 𝟙 + 1 = σ s' means σ(sub (σ s') 𝟙) = σ s'
      rw [← add_one (sub (σ s') 𝟙)]; exact h

  theorem antidiag_spec (z : ℕ₀) :
      Peano.Order.le₀ (triag (antidiag z)) z ∧
      Peano.StrictOrder.lt₀ z (triag (σ (antidiag z))) := by
    let s := sqrt (mul 𝟚 z)
    -- (A) s·s ≤ 2z  (from sqrtMod_spec)
    have h_sq_le : Peano.Order.le₀ (mul s s) (mul 𝟚 z) := by
      have h := sqrtMod_spec (mul 𝟚 z)
      rw [Peano.Pow.pow_two] at h; rw [h]; exact le_self_add _ _
    -- (B) 2z < (σ s)·(σ s)  (from sqrt_upper_bound)
    have h_lt_sq : Peano.StrictOrder.lt₀ (mul 𝟚 z) (mul (σ s) (σ s)) := by
      have h := sqrt_upper_bound (mul 𝟚 z)
      rwa [Peano.Pow.pow_two] at h
    -- (C) (σ s)·(σ s) ≤ (σ s)·(σ(σ s))  (since σ s ≤ σ(σ s))
    have h_ss_le : Peano.Order.le₀ (mul (σ s) (σ s)) (mul (σ s) (σ (σ s))) := by
      rw [mul_comm (σ s) (σ s), mul_comm (σ s) (σ (σ s))]
      exact mul_le_mono_right (σ s) (lt_imp_le _ _ (lt_succ_self (σ s)))
    -- (D) 2·triag(σ s) = (σ s)·(σ(σ s))
    have h_2tss : mul 𝟚 (triag (σ s)) = mul (σ s) (σ (σ s)) := two_mul_triag (σ s)
    -- Therefore: 2z < 2·triag(σ s)
    have h_2z_lt_tss : Peano.StrictOrder.lt₀ (mul 𝟚 z) (mul 𝟚 (triag (σ s))) := by
      rw [h_2tss]; exact lt_of_lt_of_le h_lt_sq h_ss_le
    -- Therefore: z < triag(σ s)  (cancel 2 from left)
    have h_z_lt_tss : Peano.StrictOrder.lt₀ z (triag (σ s)) := by
      rcases trichotomy z (triag (σ s)) with h | h | h
      · exact h
      · exfalso; rw [h] at h_2z_lt_tss; exact lt_irrefl _ h_2z_lt_tss
      · exfalso
        have hmono : Peano.Order.le₀ (mul 𝟚 (triag (σ s))) (mul 𝟚 z) := by
          rw [mul_comm 𝟚 _, mul_comm 𝟚 z]
          exact mul_le_mono_right 𝟚 (lt_imp_le _ _ h)
        exact lt_irrefl _ (lt_of_lt_of_le h_2z_lt_tss hmono)
    -- Now case-split on antidiag definition
    unfold antidiag
    rcases trichotomy (triag s) z with h_lt | h_eq | h_gt
    · -- triag s < z
      have h_le : Peano.Order.le₀ (triag s) z := lt_imp_le _ _ h_lt
      rw [if_pos h_le]; exact ⟨h_le, h_z_lt_tss⟩
    · -- triag s = z
      have h_le : Peano.Order.le₀ (triag s) z := h_eq ▸ le_self_of_eq_self _ rfl
      rw [if_pos h_le]; exact ⟨h_le, h_z_lt_tss⟩
    · -- z < triag s → s ≠ 0, result is sub s 1
      have h_nle : ¬ Peano.Order.le₀ (triag s) z := gt_then_nle _ _ h_gt
      rw [if_neg h_nle]
      have hs_ne : s ≠ 𝟘 := by
        intro h; rw [h, triag_zero] at h_gt; exact absurd h_gt (nlt_n_0 z)
      have h_ss : σ (sub s 𝟙) = s := succ_sub_one hs_ne
      -- triag(s-1) ≤ z:  2·triag(s-1) = (s-1)·s ≤ s·s ≤ 2z
      have h_part1 : Peano.Order.le₀ (triag (sub s 𝟙)) z := by
        apply le_of_two_mul_le
        rw [two_mul_triag (sub s 𝟙), h_ss]
        exact le_trans _ _ _ (mul_le_mono_right s (sub_le_self s 𝟙)) h_sq_le
      -- z < triag(σ(s-1)) = triag s
      have h_part2 : Peano.StrictOrder.lt₀ z (triag (σ (sub s 𝟙))) := by
        show lt₀ z (triag (σ (sub s 𝟙)))
        rw [h_ss]; exact h_gt
      exact ⟨h_part1, h_part2⟩

  theorem antidiag_pair (m n : ℕ₀) : antidiag (pair m n) = add m n := by
    have h_spec := antidiag_spec (pair m n)
    -- Both antidiag(pair m n) and add m n satisfy the spec; use uniqueness.
    have h_mn_spec : Peano.Order.le₀ (triag (add m n)) (pair m n) ∧
        Peano.StrictOrder.lt₀ (pair m n) (triag (σ (add m n))) :=
      ⟨triag_le_pair m n, pair_lt_triag_succ m n⟩
    -- antidiag_unique says the satisfier is unique
    have huniq := antidiag_unique (pair m n)
    obtain ⟨w, _hw, hw_uniq⟩ := huniq
    have ha := hw_uniq (antidiag (pair m n)) h_spec
    have hb := hw_uniq (add m n) h_mn_spec
    rw [← hb] at ha
    exact ha

  -- ─────────────────────────────────────────────────────────────────────────
  -- 4. Proyecciones y biyectividad
  -- ─────────────────────────────────────────────────────────────────────────

  /-- Primera proyección (columna). -/
  def fst (z : ℕ₀) : ℕ₀ := sub z (triag (antidiag z))

  /-- Segunda proyección (fila - columna). -/
  def snd (z : ℕ₀) : ℕ₀ := sub (antidiag z) (fst z)

  /-- fst(pair m n) = m. -/
  theorem pair_fst (m n : ℕ₀) : fst (pair m n) = m := by
    show sub (pair m n) (triag (antidiag (pair m n))) = m
    rw [antidiag_pair]
    unfold pair
    exact add_k_sub_k m (triag (add m n))

  /-- snd(pair m n) = n. -/
  theorem pair_snd (m n : ℕ₀) : snd (pair m n) = n := by
    show sub (antidiag (pair m n)) (fst (pair m n)) = n
    rw [antidiag_pair, pair_fst]
    exact add_k_sub_k n m

  /-- pair(fst z, snd z) = z  (sobreyectividad). -/
  theorem pair_surj (z : ℕ₀) : pair (fst z) (snd z) = z := by
    have h_spec := antidiag_spec z
    have h_le  : le₀ (triag (antidiag z)) z              := h_spec.1
    have h_lt  : lt₀ z (triag (σ (antidiag z)))          := h_spec.2
    -- fst z ≤ antidiag z
    have h_fst_le : le₀ (fst z) (antidiag z) := by
      show le₀ (sub z (triag (antidiag z))) (antidiag z)
      apply (lt_succ_iff_le _ _).mp
      apply (sub_lt_iff_lt_add_of_le z (triag (antidiag z)) (σ (antidiag z)) h_le).mpr
      calc z < triag (σ (antidiag z))
                := h_lt
        _ = add (triag (antidiag z)) (σ (antidiag z))
                := triag_succ _
        _ = add (σ (antidiag z)) (triag (antidiag z))
                := add_comm _ _
    -- fst z + snd z = antidiag z
    have h_sum : add (fst z) (snd z) = antidiag z := by
      show add (sub z (triag (antidiag z))) (sub (antidiag z) (sub z (triag (antidiag z)))) = antidiag z
      rw [add_comm]
      exact sub_k_add_k (antidiag z) (sub z (triag (antidiag z))) h_fst_le
    -- pair (fst z) (snd z) = z
    show add (triag (add (fst z) (snd z))) (fst z) = z
    rw [h_sum]
    show add (triag (antidiag z)) (sub z (triag (antidiag z))) = z
    rw [add_comm]
    exact sub_k_add_k z (triag (antidiag z)) h_le

  end Foundation

end Peano
