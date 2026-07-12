/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/NumberTheory/ChineseRemainder.lean
--
-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: ModEq, Arith (Coprime, bezout_natform), Primes (gcd_eq_one_iff_coprime)
-- @axiom_system: Peano
-- @importance: high

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes
import Peano.PeanoNat.NumberTheory.ModEq

set_option autoImplicit false

namespace Peano
  open Peano

  namespace CRT
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.Add
    open Peano.Sub
    open Peano.Mul
    open Peano.Div
    open Peano.Arith
    open Peano.ModEq

    /-!
    ## § 1. Helper lemmas
    !-/

    /-- If `c ≠ 𝟘` then `le₀ 𝟙 c`. -/
    private theorem le_one_of_ne_zero {c : ℕ₀} (hc : c ≠ 𝟘) : le₀ 𝟙 c := by
      cases c with
      | zero => exact absurd rfl hc
      | succ c' => exact (succ_le_succ_iff 𝟘 c').mpr (zero_le c')

    /-- If `sub a b = c` and `c ≠ 𝟘`, then `a = add b c`. -/
    private theorem sub_eq_imp_add {a b c : ℕ₀}
        (h : sub a b = c) (hc : c ≠ 𝟘) : a = add b c := by
      have h_lt : lt₀ b a := (sub_pos_iff_lt a b).mp (h ▸ le_one_of_ne_zero hc)
      have h_le : le₀ b a := lt_imp_le_wp h_lt
      have h2 := sub_k_add_k a b h_le
      rw [h] at h2
      rw [add_comm] at h2
      exact h2.symm

    /-- `mod (mul k m) m = 𝟘` when `m ≠ 𝟘`. -/
    private theorem mod_mul_self_right (k m : ℕ₀) (hm : m ≠ 𝟘) :
        mod (mul k m) m = 𝟘 :=
      (mod_eq_zero_iff_dvd hm).mpr ⟨k, mul_comm k m⟩

    /-!
    ## § 2. Modular inverse from Bézout
    !-/

    /-- From `𝟙 = sub (mul s m) (mul t n)` derive `mod (mul s m) n = mod 𝟙 n`.
    That is, `mul s m` is a modular inverse of `m` modulo `n`. -/
    private theorem bezout_mod_one {s t m n : ℕ₀}
        (hn : n ≠ 𝟘)
        (h_bez : 𝟙 = sub (mul s m) (mul t n)) :
        mod (mul s m) n = mod 𝟙 n := by
      have h_ne : mul s m ≠ 𝟘 := by
        intro h_eq
        rw [h_eq, zero_sub] at h_bez
        exact absurd h_bez.symm (zero_ne_succ 𝟘)
      have h_add := sub_eq_imp_add h_bez.symm (Ne.symm (zero_ne_succ 𝟘))
      -- h_add : mul s m = add (mul t n) 𝟙
      calc mod (mul s m) n
          = mod (add (mul t n) 𝟙) n := by rw [h_add]
        _ = mod (add (mod (mul t n) n) (mod 𝟙 n)) n := by rw [add_mod]
        _ = mod (add 𝟘 (mod 𝟙 n)) n := by rw [mod_mul_self_right t n hn]
        _ = mod (mod 𝟙 n) n := by rw [zero_add]
        _ = mod 𝟙 n := mod_mod 𝟙 n

    /-- If `mul s m` is a modular inverse of `m` modulo `n`, then
    `mod (mul (mul r s) m) n = mod r n` for any `r`. -/
    private theorem mod_mul_inv {s m n : ℕ₀}
        (h_inv : mod (mul s m) n = mod 𝟙 n) (r : ℕ₀) :
        mod (mul (mul r s) m) n = mod r n := by
      calc mod (mul (mul r s) m) n
          = mod (mul r (mul s m)) n := by rw [mul_assoc]
        _ = mod (mul (mod r n) (mod (mul s m) n)) n := by rw [mul_mod]
        _ = mod (mul (mod r n) (mod 𝟙 n)) n := by rw [h_inv]
        _ = mod (mul r 𝟙) n := by rw [← mul_mod]
        _ = mod r n := by rw [mul_one]

    /-!
    ## § 3. CRT construction from modular inverse
    !-/

    /-- Given a modular inverse `h_inv : mod (mul s m) n = mod 𝟙 n`,
    construct a simultaneous solution to `x ≡ a [MOD m]` and `x ≡ b [MOD n]`.
    The witness is `x = add a (mul (mul c s) m)` where
    `c = sub (add b n) (mod a n)`. -/
    private theorem crt_from_inverse {m n s : ℕ₀}
        (hm : m ≠ 𝟘) (hn : n ≠ 𝟘)
        (h_inv : mod (mul s m) n = mod 𝟙 n)
        (a b : ℕ₀) :
        ∃ x : ℕ₀, ModEq m x a ∧ ModEq n x b := by
      let c := sub (add b n) (mod a n)
      refine ⟨add a (mul (mul c s) m), ?_, ?_⟩
      · -- Congruence 1: x ≡ a [MOD m]
        -- mul (mul c s) m is a multiple of m, so mod cancels it.
        show mod (add a (mul (mul c s) m)) m = mod a m
        rw [add_mod, mod_mul_self_right _ m hm, add_zero, mod_mod]
      · -- Congruence 2: x ≡ b [MOD n]
        -- Uses the modular inverse to reduce c·s·m to c (mod n),
        -- then the choice of c ensures add (mod a n) c = add b n.
        show mod (add a (mul (mul c s) m)) n = mod b n
        rw [add_mod, mod_mul_inv h_inv]
        -- Goal: mod (add (mod a n) (mod c n)) n = mod b n
        have h_le : le₀ (mod a n) (add b n) :=
          le_trans (mod a n) n (add b n)
            (lt_imp_le_wp (mod_lt a n hn))
            (add_comm b n ▸ le_self_add n b)
        have h_cancel_raw := sub_k_add_k (add b n) (mod a n) h_le
        -- h_cancel_raw : add c (mod a n) = add b n
        have h_cancel : add (mod a n) c = add b n := by
          rw [add_comm]; exact h_cancel_raw
        have h_reduce : mod (add (mod a n) (mod c n)) n
            = mod (add (mod a n) c) n := by
          have h := add_mod (mod a n) c n
          rw [mod_mod a n] at h
          exact h.symm
        rw [h_reduce, h_cancel]
        exact (modEq_add_right b n).symm

    /-!
    ## § 4. Chinese Remainder Theorem
    !-/

    /-- **Chinese Remainder Theorem (existence)**.
    If `m` and `n` are coprime, then for any `a` and `b` there exists `x`
    with `x ≡ a [MOD m]` and `x ≡ b [MOD n]`. -/
    theorem chinese_remainder {m n : ℕ₀} (hcop : Coprime m n) (a b : ℕ₀) :
        ∃ x : ℕ₀, ModEq m x a ∧ ModEq n x b := by
      -- Edge case: m = 0 implies n = 1
      by_cases hm : m = 𝟘
      · subst hm
        have h_n1 : n = 𝟙 := by
          rw [← Peano.Primes.gcd_eq_one_iff_coprime] at hcop
          rwa [gcd_zero_left] at hcop
        refine ⟨b, ?_, h_n1 ▸ modEq_one b b⟩
        show mod b 𝟘 = mod a 𝟘
        rw [mod_zero_right, mod_zero_right]
      -- Edge case: n = 0 implies m = 1
      · by_cases hn : n = 𝟘
        · subst hn
          have h_m1 : m = 𝟙 := by
            rw [← Peano.Primes.gcd_eq_one_iff_coprime] at hcop
            rwa [gcd_zero_right] at hcop
          refine ⟨a, h_m1 ▸ modEq_one a a, ?_⟩
          show mod a 𝟘 = mod b 𝟘
          rw [mod_zero_right, mod_zero_right]
        -- Main case: m ≠ 0, n ≠ 0 — use Bézout identity
        · obtain ⟨s, t, h_bez⟩ := bezout_natform m n
          rw [← Peano.Primes.gcd_eq_one_iff_coprime] at hcop
          rw [hcop] at h_bez
          rcases h_bez with h_L | h_R
          · -- 𝟙 = sub (mul s m) (mul t n) → inverse of m mod n
            exact crt_from_inverse hm hn (bezout_mod_one hn h_L) a b
          · -- 𝟙 = sub (mul s n) (mul t m) → inverse of n mod m → swap
            obtain ⟨x, hx_n, hx_m⟩ := crt_from_inverse hn hm (bezout_mod_one hm h_R) b a
            exact ⟨x, hx_m, hx_n⟩

  end CRT
end Peano

-- ============================================================
-- Exports (AI-GUIDE.md §17)
-- ============================================================
export Peano.CRT (
  chinese_remainder
)
