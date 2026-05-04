/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/NumberTheory/Wilson.lean
-- Wilson's theorem: for every prime p, p ∣ (p−1)! + 1.
--
-- Strategy:
--   1. Define modular inverse modInv p a = a^(p−2) mod p.
--   2. Prove pow a (p−1) ≡ 1 [MOD p] (from Fermat + cancellation).
--   3. Prove modInv_mul: a * modInv p a ≡ 1 [MOD p].
--   4. Prove modInv is an involution on {1,…,p−1}.
--   5. Pair-up {2,…,p−2} via modInv (no fixed points), each pair ≡ 1.
--   6. Conclude (p−2)! ≡ 1 [MOD p], then (p−1)! ≡ p−1 [MOD p].
--   7. p | (p−1)! + 1.

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Combinatorics.Factorial
import Peano.PeanoNat.NumberTheory.ModEq
import Peano.PeanoNat.NumberTheory.Fermat
import Peano.PeanoNat.Primes

set_option autoImplicit false

namespace Peano
  open Peano
  open Peano.Sub
  open Peano.Axioms
  open Peano.StrictOrder
  open Peano.Order
  open Peano.Add
  open Peano.Mul
  open Peano.Div
  open Peano.Arith
  open Peano.Pow
  open Peano.Factorial
  open Peano.ModEq
  open Peano.Primes hiding Prime
  open Peano.Fermat

  private abbrev Prime := Peano.Arith.Prime

  namespace Wilson

    /-! ## § 1. Arithmetic helpers -/

    /-- `σ (n − 1) = n` for `n ≠ 0`. -/
    private theorem succ_sub_one {n : ℕ₀} (h : n ≠ 𝟘) : σ (sub n 𝟙) = n := by
      rw [sub_one]
      cases n with
      | zero  => exact absurd rfl h
      | succ n' => rfl   -- τ(σ n') = n'

    private theorem succ_one_eq_one_plus_one  :
        (σ 𝟙) = (add 𝟙 𝟙)
          := by
      calc
        σ 𝟙 = σ (σ 𝟘) := by rfl
          _ = add (σ 𝟘) (σ 𝟘) := by rfl
          _ = add 𝟙 𝟙 := by rfl

    /-- `sub (sub p 𝟙) 𝟙 = sub p (𝟙 + 𝟙)` — i.e. `(p−1)−1 = p−2`. -/
    private theorem sub_sub_one_one
      (p : ℕ₀) :
        sub (sub p 𝟙) 𝟙 = sub p (add 𝟙 𝟙)
          := by
      apply Ψ_inj
      simp only [isomorph_Ψ_sub, isomorph_Ψ_add]
      exact Nat.sub_sub (Ψ p) (Ψ 𝟙) (Ψ 𝟙)

    /-- For prime `p`, `σ (sub p (𝟙 + 𝟙)) = sub p 𝟙`, i.e. `(p−2)+1 = p−1`. -/
    private theorem succ_p_sub_two_eq {p : ℕ₀}
      (hp : Prime p) :
        σ (sub p (add 𝟙 𝟙)) = sub p 𝟙
          := by
      rw [← sub_sub_one_one]
      apply succ_sub_one
      -- Need: sub p 𝟙 ≠ 𝟘, i.e. p ≥ 2
      intro h
      have h_lt : lt₀ 𝟙 p := one_lt_prime hp
      have h_le : le₀ p 𝟙 := by
        exact sub_eq_zero p 𝟙 h
      exact absurd h_lt (le_not_lt h_le)

    /-- `pow a p = mul (pow a (sub p 𝟙)) a` for prime `p`. -/
    private theorem pow_eq_pow_pred_mul {p a : ℕ₀}
      (hp : Prime p) :
        pow a p = mul (pow a (sub p 𝟙)) a
          := by
      rw [← pow_succ, succ_sub_one (prime_ne_zero hp)]

    /-- For prime `p` and `1 < a < p`, `a` does not divide `p`. -/
    private theorem prime_ndvd_lt {a p : ℕ₀}
      (hp : Prime p) (ha_pos : lt₀ 𝟙 a) (ha_lt : lt₀ a p) :
        ¬ (a ∣ p)
          := by
      intro h_dvd
      obtain ⟨k, hk⟩ := h_dvd
      rcases (prime_imp_irreducible hp).2 a k hk.symm with h_a1 | h_k1
      · rw [h_a1] at ha_pos
        exact absurd ha_pos (lt_irrefl 𝟙)
      · rw [h_k1, mul_one] at hk
        rw [← hk] at ha_lt
        exact absurd ha_lt (lt_irrefl p)

    /-- For `a < p`, `mod a p = a`. -/
    private theorem mod_small {p a : ℕ₀} (ha_lt : lt₀ a p) : mod a p = a :=
      mod_of_lt a p ha_lt

    /-! ## § 2. Key cancellation lemma -/

    /-- If `mod (add a Y) p = a` with `a < p` and `Y < p` and `p ≠ 0`, then `Y = 0`. -/
    private theorem add_mod_cancel {p a Y : ℕ₀}
        (ha_lt : lt₀ a p) (hY_lt : lt₀ Y p) (hp_ne : p ≠ 𝟘)
        (h : mod (add a Y) p = a) : Y = 𝟘 := by
      -- Work entirely at ℕ₀ level.  Two cases: add a Y < p  or  p ≤ add a Y.
      rcases le_or_lt p (add a Y) with hge | hlt
      · -- Case p ≤ add a Y.  Since a < p and Y < p we have add a Y < add p p.
        have h_bound : lt₀ (add a Y) (add p p) :=
          lt_le_then_lt_add_compat a p Y p ha_lt (lt_imp_le_wp hY_lt)
        -- mod (add a Y) p = sub (add a Y) p  (first interval)
        have h_mod_eq : mod (add a Y) p = sub (add a Y) p := by
          have := mod_of_lt_fst_interval (add a Y) p hge h_bound
          simp only [mod_def] at this; exact this
        rw [h_mod_eq] at h
        -- sub_k_add_k: add (sub (add a Y) p) p = add a Y
        have h_restore : add (sub (add a Y) p) p = add a Y := sub_k_add_k (add a Y) p hge
        -- h says sub (add a Y) p = a, so  add a p = add a Y
        rw [h] at h_restore
        -- cancel a: p = Y, contradicts Y < p
        have hYp : p = Y := add_cancel a p Y h_restore
        exact absurd (hYp ▸ hY_lt) (lt_irrefl Y)
      · -- Case add a Y < p.  mod (add a Y) p = add a Y  (by mod_of_lt)
        have h_mod_eq : mod (add a Y) p = add a Y := by
          have := mod_of_lt (add a Y) p hlt
          simp only [mod_def] at this; exact this
        rw [h_mod_eq] at h
        -- h : add a Y = a = add a 𝟘, cancel a: Y = 𝟘
        have : add a Y = add a 𝟘 := by rw [h, add_zero]
        exact add_cancel a Y 𝟘 this

    /-! ## § 3. Fermat implies `a^(p−1) ≡ 1 [MOD p]` -/

    /-- For prime `p` and `0 < a < p`:  `pow a (sub p 𝟙) ≡ 𝟙 [MOD p]`. -/
    private theorem pow_pred_one {p a : ℕ₀} (hp : Prime p) (ha_pos : 𝟘 < a)
        (ha_lt : lt₀ a p) : pow a (sub p 𝟙) ≡ 𝟙 [MOD p] := by
      have hp_ne : p ≠ 𝟘 := prime_ne_zero hp
      -- X = mod (pow a (sub p 𝟙)) p  (introduce without set tactic)
      let X := mod (pow a (sub p 𝟙)) p
      have hX_def : X = mod (pow a (sub p 𝟙)) p := rfl
      -- Fermat: mod (pow a p) p = a
      have h_fermat : mod (pow a p) p = a := by
        rw [fermat_little_theorem a p hp, mod_small ha_lt]
      -- pow a p = mul (pow a (sub p 𝟙)) a
      rw [pow_eq_pow_pred_mul hp] at h_fermat
      -- mod (mul X a) p = a, using mul_mod to substitute X
      have h_Xa : mod (mul X a) p = a := by
        rw [mul_mod X a p, hX_def, mod_mod, ← mul_mod]
        exact h_fermat
      -- X ≠ 0: otherwise mod(0*a)p = 0 ≠ a
      have hX_ne : X ≠ 𝟘 := by
        intro hX0
        rw [hX0, zero_mul] at h_Xa
        simp [mod_zero_left] at h_Xa
        exact absurd (h_Xa ▸ ha_pos) (lt_irrefl 𝟘)
      -- X ≥ 1
      have hX_pos : 𝟘 < X := pos_of_ne_zero X hX_ne
      -- Decompose: mul X a = add a (mul (sub X 𝟙) a)
      have h_expand : mul X a = add a (mul (sub X 𝟙) a) :=
        calc mul X a = mul (σ (sub X 𝟙)) a := by rw [succ_sub_one hX_ne]
          _ = add (mul (sub X 𝟙) a) a := succ_mul (sub X 𝟙) a
          _ = add a (mul (sub X 𝟙) a) := add_comm _ _
      -- Y := mod (mul (sub X 𝟙) a) p; then mod (add a Y) p = a
      let Y := mod (mul (sub X 𝟙) a) p
      have hY_def : Y = mod (mul (sub X 𝟙) a) p := rfl
      have hY_lt : lt₀ Y p := mod_lt (mul (sub X 𝟙) a) p hp_ne
      -- mod (add a Y) p = a  (via add_mod + mod_mod)
      have h_add_mod : mod (add a Y) p = a := by
        rw [add_mod, hY_def, mod_mod, ← add_mod, ← h_expand]
        exact h_Xa
      -- By add_mod_cancel: Y = 0
      have hY0 : Y = 𝟘 := add_mod_cancel ha_lt hY_lt hp_ne h_add_mod
      -- p | mul (sub X 𝟙) a
      have hpY : p ∣ mul (sub X 𝟙) a := by
        rw [← mod_eq_zero_iff_dvd hp_ne, ← hY_def, hY0]
      -- ¬ (p ∣ a): since 0 < a < p, any multiple of p ≥ p
      have h_ndvd : ¬ (p ∣ a) := by
        intro ⟨k, hk⟩
        cases k with
        | zero =>
          have : a = 𝟘 := by rw [mul_zero] at hk; exact hk
          exact absurd (this ▸ ha_pos) (lt_irrefl 𝟘)
        | succ k' =>
          have hle : le₀ p a := by
            rw [hk]; exact mul_le_right p (σ k') (zero_ne_succ k').symm
          exact absurd ha_lt (le_not_lt hle)
      -- Coprime p a
      have hcop : Coprime p a := (gcd_eq_one_iff_coprime p a).mp (prime_not_dvd_imp_coprime hp h_ndvd)
      -- By Gauss: p | sub X 𝟙
      have hp_sub : p ∣ sub X 𝟙 := by
        rw [mul_comm] at hpY
        exact coprime_dvd_of_dvd_mul hcop hpY
      -- sub X 𝟙 < p  (since X < p and X ≥ 1)
      have hX_lt : lt₀ X p := mod_lt (pow a (sub p 𝟙)) p hp_ne
      have hsub_lt : lt₀ (sub X 𝟙) p :=
        lt_trans (sub X 𝟙) X p
          (sub_lt_self_wp (lt_0n_then_le_1n_wp hX_pos) (zero_ne_succ 𝟘).symm)
          hX_lt
      -- sub X 𝟙 = 0
      have hsub0 : sub X 𝟙 = 𝟘 := by
        rcases hp_sub with ⟨k, hk⟩
        cases k with
        | zero => rw [mul_zero] at hk; exact hk
        | succ k' =>
          exfalso
          have hle_p : le₀ p (mul p (σ k')) :=
            mul_le_right p (σ k') (zero_ne_succ k').symm
          rw [hk] at hsub_lt
          exact absurd hsub_lt (le_not_lt hle_p)
      -- X = 1
      have hX1 : X = 𝟙 := by
        have hle : le₀ X 𝟙 := sub_eq_zero X 𝟙 hsub0
        have hge : le₀ 𝟙 X := lt_0n_then_le_1n_wp hX_pos
        exact le_antisymm X 𝟙 hle hge
      -- Show ModEq: mod (pow a (sub p 𝟙)) p = 𝟙 = mod 𝟙 p
      unfold ModEq
      rw [← hX_def, hX1]
      exact (mod_small (one_lt_prime hp)).symm

    /-! ## § 4. Modular inverse -/

    /-- `modInv p a := a^(p−2) mod p` (the modular inverse of `a` mod `p`). -/
    private def modInv (p a : ℕ₀) : ℕ₀ :=
      mod (pow a (sub p (add 𝟙 𝟙))) p

    /-- `modInv p a < p`. -/
    private theorem modInv_lt {p a : ℕ₀} (hp : Prime p) :
        lt₀ (modInv p a) p :=
      mod_lt (pow a (sub p (add 𝟙 𝟙))) p (prime_ne_zero hp)

    /-- `mul a (modInv p a) ≡ 𝟙 [MOD p]` for `0 < a < p`. -/
    private theorem modInv_mul {p a : ℕ₀} (hp : Prime p) (ha_pos : 𝟘 < a)
        (ha_lt : lt₀ a p) : mul a (modInv p a) ≡ 𝟙 [MOD p] := by
      -- pow a (sub p 𝟙) = mul (pow a (sub p (𝟙+𝟙))) a   [by pow_succ + succ_p_sub_two_eq]
      have h_pow_eq : pow a (sub p 𝟙) = mul (pow a (sub p (add 𝟙 𝟙))) a := by
        rw [← pow_succ, succ_p_sub_two_eq hp]
      -- pow a (sub p 𝟙) ≡ 𝟙 [MOD p]
      have h_pred : pow a (sub p 𝟙) ≡ 𝟙 [MOD p] := pow_pred_one hp ha_pos ha_lt
      -- mul (pow a (sub p (𝟙+𝟙))) a ≡ 𝟙 [MOD p]
      rw [h_pow_eq] at h_pred
      -- modInv p a ≡ pow a (sub p (𝟙+𝟙)) [MOD p]
      have h_inv_eq : modInv p a ≡ pow a (sub p (add 𝟙 𝟙)) [MOD p] :=
        modEq_symm (modEq_mod (pow a (sub p (add 𝟙 𝟙))) p)
      -- mul a (modInv p a) ≡ mul a (pow a (sub p (𝟙+𝟙))) [MOD p]
      have h1 : mul a (modInv p a) ≡ mul a (pow a (sub p (add 𝟙 𝟙))) [MOD p] :=
        modEq_mul (modEq_refl p a) h_inv_eq
      -- mul a (pow a (sub p (𝟙+𝟙))) = mul (pow a (sub p (𝟙+𝟙))) a  [comm]
      have h2 : mul a (pow a (sub p (add 𝟙 𝟙))) = mul (pow a (sub p (add 𝟙 𝟙))) a :=
        mul_comm a _
      rw [h2] at h1
      exact modEq_trans h1 h_pred

    /-- `0 < modInv p a` for `0 < a < p`. -/
    private theorem modInv_pos {p a : ℕ₀}
      (hp : Prime p) (ha_pos : 𝟘 < a) (ha_lt : lt₀ a p) :
        𝟘 < modInv p a
          := by
      apply pos_of_ne_zero
      intro h0
      have h_inv := @modInv_mul p a hp ha_pos ha_lt
      rw [h0, mul_zero] at h_inv
      unfold ModEq at h_inv
      rw [mod_zero_left, mod_small (one_lt_prime hp)] at h_inv
      exact absurd h_inv (zero_ne_succ 𝟘)

    /-! ## § 5. Involution of modInv -/

    /-- `modInv p (modInv p a) = a` for `0 < a < p`. -/
    private theorem modInv_invol {p a : ℕ₀}
      (hp : Prime p) (ha_pos : 𝟘 < a) (ha_lt : lt₀ a p) :
        modInv p (modInv p a) = a
          := by
      have hp_ne  : p ≠ 𝟘        := prime_ne_zero hp
      let b := modInv p a
      have hb_pos : 𝟘 < b        := modInv_pos hp ha_pos ha_lt
      have hb_lt  : lt₀ b p      := modInv_lt hp
      -- mul a b ≡ 1 [MOD p]
      have h_ab : mul a b ≡ 𝟙 [MOD p] := modInv_mul hp ha_pos ha_lt
      -- mul b (modInv p b) ≡ 1 [MOD p]
      have h_b_inv : mul b (modInv p b) ≡ 𝟙 [MOD p] := modInv_mul hp hb_pos hb_lt
      -- Derive: a ≡ modInv p b [MOD p]
      -- a = a*1 ≡ a*(b*(modInv p b)) = (a*b)*(modInv p b) ≡ 1*(modInv p b) = modInv p b
      have h_equiv : a ≡ modInv p b [MOD p] := by
        have s1 : a ≡ mul a 𝟙 [MOD p] := by unfold ModEq; rw [mul_one]
        have s2 : mul a 𝟙 ≡ mul a (mul b (modInv p b)) [MOD p] :=
          modEq_mul (modEq_refl p a) (modEq_symm h_b_inv)
        have s3 : mul a (mul b (modInv p b)) ≡ mul (mul a b) (modInv p b) [MOD p] := by
          unfold ModEq; rw [← mul_assoc b a (modInv p b)]
        have s4 : mul (mul a b) (modInv p b) ≡ mul 𝟙 (modInv p b) [MOD p] :=
          modEq_mul h_ab (modEq_refl p _)
        have s5 : mul 𝟙 (modInv p b) ≡ modInv p b [MOD p] := by
          unfold ModEq; rw [one_mul]
        exact modEq_trans s1 (modEq_trans s2 (modEq_trans s3 (modEq_trans s4 s5)))
      -- a < p and modInv p b < p, so from a ≡ modInv p b [MOD p]: a = modInv p b
      have ha_mod : mod a p = a := mod_small ha_lt
      have hb_inv_lt : lt₀ (modInv p b) p := modInv_lt hp
      have hb_inv_mod : mod (modInv p b) p = modInv p b := mod_small hb_inv_lt
      unfold ModEq at h_equiv
      rw [ha_mod, hb_inv_mod] at h_equiv
      exact h_equiv.symm

    /-- `modInv p a = a ↔ a = 𝟙 ∨ a = sub p 𝟙` for `0 < a < p`. -/
    private theorem modInv_self_iff {p a : ℕ₀}
      (hp : Prime p) (ha_pos : 𝟘 < a) (ha_lt : lt₀ a p) :
        modInv p a = a ↔ a = 𝟙 ∨ a = sub p 𝟙
          := by
      have hp_ne  : p ≠ 𝟘 := prime_ne_zero hp
      have h_a_eq_1 : a = 𝟙 → modInv p a = a := by
        intro h
        rw [h]
        unfold modInv
        rw [one_pow]
        exact mod_small (one_lt_prime hp)
      have h_a_eq_sub : a = sub p 𝟙 → modInv p a = a := by
        intro h
        rw [h]
        unfold modInv
        have hp1_pos : 𝟘 < sub p 𝟙 := by
          apply pos_of_ne_zero; intro hz
          exact absurd (one_lt_prime hp) (le_not_lt (sub_eq_zero p 𝟙 hz))
        have hp1_lt : lt₀ (sub p 𝟙) p :=
          sub_lt_self_wp (lt_imp_le_wp (one_lt_prime hp)) (succ_neq_zero 𝟘)
        -- 1. Demostrar que (p-1)*(p-1) ≡ 1 [MOD p] bajando a Nat
        have h_sq_one : mul (sub p 𝟙) (sub p 𝟙) ≡ 𝟙 [MOD p] := by
          -- Queremos demostrar p ∣ (mul (sub p 𝟙) (sub p 𝟙) - 𝟙)
          -- (p-1)*(p-1) - 1 = (p^2 - 2p + 1) - 1 = p^2 - 2p = p * (p-2)
          have h_p_ge_2 : le₀ 𝟚 p := prime_ge_two hp
          have h_p_ne_0 : p ≠ 𝟘 := prime_ne_zero hp
          have h_p_ne_1 : p ≠ 𝟙 := prime_ne_one hp
          have h_diff_eq : sub (mul (sub p 𝟙) (sub p 𝟙)) 𝟙 = mul p (sub p 𝟚) := by
            let k := sub p 𝟚
            have hp_eq : p = add (add k 𝟙) 𝟙 := by
              calc p = add k 𝟚 := (sub_k_add_k p 𝟚 h_p_ge_2).symm
                   _ = add (add k 𝟙) 𝟙 := rfl
            have hp1_eq : sub p 𝟙 = add k 𝟙 := by
              calc sub p 𝟙 = sub (add (add k 𝟙) 𝟙) 𝟙 := by rw [hp_eq]
                   _ = sub (add 𝟙 (add k 𝟙)) 𝟙 := by rw [add_comm (add k 𝟙) 𝟙]
                   _ = add k 𝟙 := add_k_sub_k (add k 𝟙) 𝟙
            have h_sq : mul (sub p 𝟙) (sub p 𝟙) = add (mul p k) 𝟙 := by
              calc mul (sub p 𝟙) (sub p 𝟙)
                  = mul (add k 𝟙) (add k 𝟙) := by rw [hp1_eq]
                _ = add (mul (add k 𝟙) k) (mul (add k 𝟙) 𝟙) := mul_add (add k 𝟙) k 𝟙
                _ = add (mul (add k 𝟙) k) (add k 𝟙) := by rw [mul_one]
                _ = add (add (mul k k) (mul 𝟙 k)) (add k 𝟙) := by rw [add_mul k 𝟙 k]
                _ = add (add (mul k k) k) (add k 𝟙) := by rw [one_mul]
                _ = add (mul k k) (add k (add k 𝟙)) := by rw [← add_assoc (mul k k) k (add k 𝟙)]
                _ = add (mul k k) (add (add k k) 𝟙) := by rw [add_assoc k k 𝟙]
                _ = add (add (mul k k) (add k k)) 𝟙 := by rw [add_assoc (mul k k) (add k k) 𝟙]
                _ = add (add (mul k k) (mul 𝟚 k)) 𝟙 := by
                      have h2 : mul 𝟚 k = add k k := by
                        calc
                          mul 𝟚 k = mul (σ 𝟙) k := by rfl
                                _ = add (mul 𝟙 k) k := by rw [succ_mul 𝟙 k]
                                _ = add k k := by rw [one_mul]
                      rw [← h2]
                _ = add (mul (add k 𝟚) k) 𝟙 := by rw [← add_mul k 𝟚 k]
                _ = add (mul p k) 𝟙 := by
                      have hp_k2 : add k 𝟚 = p := sub_k_add_k p 𝟚 h_p_ge_2
                      rw [hp_k2]
            calc sub (mul (sub p 𝟙) (sub p 𝟙)) 𝟙
                = sub (add (mul p k) 𝟙) 𝟙 := by rw [h_sq]
              _ = sub (add 𝟙 (mul p k)) 𝟙 := by rw [add_comm (mul p k) 𝟙]
              _ = mul p k := add_k_sub_k (mul p k) 𝟙
          have hA_pos : 𝟙 ≤ (mul (sub p 𝟙) (sub p 𝟙)) := by
            exact lt_0n_then_le_1n_wp (mul_pos hp1_pos hp1_pos)
          have heq : (mul (sub p 𝟙) (sub p 𝟙)) = (add 𝟙 (mul p (sub p 𝟚))) := by
            calc mul (sub p 𝟙) (sub p 𝟙)
               = add (sub (mul (sub p 𝟙) (sub p 𝟙)) 𝟙) 𝟙 := (sub_k_add_k _ 𝟙 hA_pos).symm
             _ = add (mul p (sub p 𝟚)) 𝟙 := by rw [h_diff_eq]
             _ = add 𝟙 (mul p (sub p 𝟚)) := add_comm _ _
          have h_mul_zero : mul p (sub p 𝟚) ≡ 𝟘 [MOD p] := by
            apply (modEq_zero_iff_dvd h_p_ne_0).mpr
            exact ⟨sub p 𝟚, rfl⟩
          have h_add_equiv : add 𝟙 (mul p (sub p 𝟚)) ≡ add 𝟙 𝟘 [MOD p] :=
            modEq_add (modEq_refl p 𝟙) h_mul_zero
          unfold ModEq at h_add_equiv ⊢
          rw [add_zero] at h_add_equiv
          rw [heq]
          exact h_add_equiv
        -- 2. Usar que (p-1) * modInv p (p-1) ≡ 1 [MOD p]
        have h_inv : mul (sub p 𝟙) (modInv p (sub p 𝟙)) ≡ 𝟙 [MOD p] :=
          modInv_mul hp hp1_pos hp1_lt

        -- 3. Multiplicar para concluir que modInv p (p-1) ≡ p-1 [MOD p]
        let Z := modInv p (sub p 𝟙)
        have hZ_lt : lt₀ Z p := modInv_lt hp

        have h_equiv : Z ≡ sub p 𝟙 [MOD p] := by
          have s1 : Z ≡ mul Z 𝟙 [MOD p] := by unfold ModEq; rw [mul_one]
          have s2 : mul Z 𝟙 ≡ mul Z (mul (sub p 𝟙) (sub p 𝟙)) [MOD p] :=
            modEq_mul (modEq_refl p Z) (modEq_symm h_sq_one)
          have s3 : mul Z (mul (sub p 𝟙) (sub p 𝟙)) ≡ mul (mul Z (sub p 𝟙)) (sub p 𝟙) [MOD p] := by
            unfold ModEq; rw [← mul_assoc (sub p 𝟙) Z (sub p 𝟙)]
          have s4 : mul (mul Z (sub p 𝟙)) (sub p 𝟙) ≡ mul 𝟙 (sub p 𝟙) [MOD p] := by
            have h_comm : mul Z (sub p 𝟙) = mul (sub p 𝟙) Z := mul_comm Z _
            rw [h_comm]
            exact modEq_mul h_inv (modEq_refl p _)
          have s5 : mul 𝟙 (sub p 𝟙) ≡ sub p 𝟙 [MOD p] := by
            unfold ModEq; rw [one_mul]
          exact modEq_trans s1 (modEq_trans s2 (modEq_trans s3 (modEq_trans s4 s5)))

        -- 4. Como Z < p y p-1 < p, la congruencia implica igualdad
        unfold ModEq at h_equiv
        rw [mod_small hZ_lt, mod_small hp1_lt] at h_equiv
        exact h_equiv

      constructor
      · -- Forward direction: modInv p a = a → a = 𝟙 ∨ a = sub p 𝟙
        intro h_self
        have h_sq : mul a a ≡ 𝟙 [MOD p] := by
          have := modInv_mul hp ha_pos ha_lt; rw [h_self] at this; exact this
        have ha_nat : 𝟘 < a := ha_pos
        have hge2 : 𝟚 ≤ p := prime_ge_two hp
        have h_sq_nat : mod (mul a a) p = 𝟙 := by
          unfold ModEq at h_sq
          rw [mod_small (one_lt_prime hp)] at h_sq
          exact h_sq
        have hsq_pos : 𝟘 < mul a a := mul_pos ha_nat ha_nat
        have h_dvd_N0 : p ∣ mul (sub a 𝟙) (add a 𝟙) := by
          have hfact : sub (mul a a) 𝟙 = mul (sub a 𝟙) (add a 𝟙) := by
            cases h_a : a with
            | zero => exact absurd (h_a ▸ ha_nat) (lt_irrefl 𝟘)
            | succ k =>
              rw [← add_one k]
              have hk_sub : sub (add k 𝟙) 𝟙 = k := by
                rw [add_comm k 𝟙]; exact add_k_sub_k k 𝟙
              have hk_add : add (add k 𝟙) 𝟙 = add k 𝟚 := by rfl
              rw [hk_sub, hk_add]
              have h2k : mul 𝟚 k = add k k := by
                have h : mul 𝟚 k = mul (σ 𝟙) k := rfl
                rw [h, succ_mul 𝟙 k, one_mul]
              have h_expand : mul k (add k 𝟚) = add (mul k k) (add k k) :=
                calc mul k (add k 𝟚)
                    = add (mul k k) (mul k 𝟚) := mul_add k k 𝟚
                  _ = add (mul k k) (mul 𝟚 k) := by rw [mul_comm k 𝟚]
                  _ = add (mul k k) (add k k)  := by rw [h2k]
              have h_sq2 : mul (add k 𝟙) (add k 𝟙) = add (mul k (add k 𝟚)) 𝟙 :=
                calc mul (add k 𝟙) (add k 𝟙)
                    = add (mul k (add k 𝟙)) (mul 𝟙 (add k 𝟙)) := add_mul k 𝟙 (add k 𝟙)
                  _ = add (mul k (add k 𝟙)) (add k 𝟙) := by rw [one_mul]
                  _ = add (add (mul k k) (mul k 𝟙)) (add k 𝟙) := by rw [mul_add k k 𝟙]
                  _ = add (add (mul k k) k) (add k 𝟙) := by rw [mul_one]
                  _ = add (mul k k) (add k (add k 𝟙)) := by
                        rw [← add_assoc (mul k k) k (add k 𝟙)]
                  _ = add (mul k k) (add (add k k) 𝟙) := by rw [add_assoc k k 𝟙]
                  _ = add (add (mul k k) (add k k)) 𝟙 := by
                        rw [add_assoc (mul k k) (add k k) 𝟙]
                  _ = add (mul k (add k 𝟚)) 𝟙 := by rw [h_expand]
              calc sub (mul (add k 𝟙) (add k 𝟙)) 𝟙
                  = sub (add (mul k (add k 𝟚)) 𝟙) 𝟙 := by rw [h_sq2]
                _ = sub (add 𝟙 (mul k (add k 𝟚))) 𝟙 := by
                      rw [add_comm (mul k (add k 𝟚)) 𝟙]
                _ = mul k (add k 𝟚) := add_k_sub_k (mul k (add k 𝟚)) 𝟙
          rw [← hfact]
          let Y := mod (sub (mul a a) 𝟙) p
          have hY_def : Y = mod (sub (mul a a) 𝟙) p := rfl
          have hY_lt : lt₀ Y p := mod_lt (sub (mul a a) 𝟙) p hp_ne
          have h1_lt : lt₀ 𝟙 p := one_lt_prime hp
          have hdm : mul a a = add (sub (mul a a) 𝟙) 𝟙 := by
            have h1 : le₀ 𝟙 (mul a a) := lt_0n_then_le_1n_wp hsq_pos
            exact (sub_k_add_k (mul a a) 𝟙 h1).symm
          have h_mod_add : mod (add 𝟙 Y) p = 𝟙 := by
            have h_expand : add 𝟙 (sub (mul a a) 𝟙) = mul a a := by
              rw [add_comm 𝟙 (sub (mul a a) 𝟙)]
              exact hdm.symm
            rw [add_mod, hY_def, mod_mod, ← add_mod, h_expand]
            exact h_sq_nat
          have hY_zero : Y = 𝟘 := add_mod_cancel h1_lt hY_lt hp_ne h_mod_add
          have h_zero_mod : sub (mul a a) 𝟙 ≡ 𝟘 [MOD p] := by
            unfold ModEq
            rw [mod_zero_left p]
            exact hY_zero
          exact (modEq_zero_iff_dvd hp_ne).mp h_zero_mod
        rcases hp.2.2 (sub a 𝟙) (add a 𝟙) h_dvd_N0
            with ⟨j1, hj1⟩ | ⟨j2, hj2⟩
        · have h_dvd_u : sub a 𝟙 = mul p j1 := hj1
          by_cases h0 : sub a 𝟙 = 𝟘
          · left
            have h1 : le₀ a 𝟙 := sub_eq_zero a 𝟙 h0
            have h2 : le₀ 𝟙 a := lt_0n_then_le_1n_wp ha_pos
            exact le_antisymm a 𝟙 h1 h2
          · exact absurd (divides_le ⟨j1, h_dvd_u⟩ h0) (by
              intro hle
              have h1 : lt₀ (sub a 𝟙) a := sub_lt_self a 𝟙 (lt_0n_then_le_1n_wp ha_pos) (succ_neq_zero 𝟘)
              have h2 : lt₀ (sub a 𝟙) p := lt_trans (sub a 𝟙) a p h1 ha_lt
              exact absurd h2 (le_not_lt hle))
        · have h_dvd_v : add a 𝟙 = mul p j2 := by exact hj2
          have h_add_le : le₀ (add a 𝟙) p := by
            have h1 : le₀ (σ a) p := lt_then_le_succ (σ a) p ((lt_iff_lt_σ_σ a p).mp ha_lt)
            rw [← add_one a] at h1
            exact h1
          have h_add_ne_zero : add a 𝟙 ≠ 𝟘 := by
            intro h
            rw [add_one] at h
            exact succ_neq_zero a h
          have h_p_le : le₀ p (add a 𝟙) := divides_le ⟨j2, h_dvd_v⟩ h_add_ne_zero
          have h_eq : add a 𝟙 = p := le_antisymm (add a 𝟙) p h_add_le h_p_le
          right
          calc a = sub (add a 𝟙) 𝟙 := by rw [add_comm a 𝟙]; exact (add_k_sub_k a 𝟙).symm
            _ = sub p 𝟙 := by rw [h_eq]
      · -- Backward direction: a = 𝟙 ∨ a = sub p 𝟙 → modInv p a = a
        intro h
        rcases h with rfl | rfl
        · -- Case a = 𝟙: modInv p 𝟙 = 𝟙
          unfold modInv; rw [one_pow, mod_small (one_lt_prime hp)]
        · -- Case a = sub p 𝟙: modInv p (sub p 𝟙) = sub p 𝟙
          exact h_a_eq_sub rfl

    /-! ## § 6. List product and the pairing argument -/

    /-- Product of a list of `ℕ₀` elements. -/
    private def listProd : List ℕ₀ → ℕ₀
      | []       => 𝟙
      | a :: rest => mul a (listProd rest)

    /-- `listProd [] = 𝟙`. -/
    private theorem listProd_nil : listProd [] = 𝟙 := rfl

    /-- `listProd (a :: l) = mul a (listProd l)`. -/
    private theorem listProd_cons (a : ℕ₀) (l : List ℕ₀) :
        listProd (a :: l) = mul a (listProd l) := rfl

    /-- `listProd (l₁ ++ l₂) = mul (listProd l₁) (listProd l₂)`. -/
    private theorem listProd_append (l₁ l₂ : List ℕ₀) :
        listProd (l₁ ++ l₂) = mul (listProd l₁) (listProd l₂) := by
      induction l₁ with
      | nil        => simp [listProd, one_mul]
      | cons a rest ih =>
        simp [listProd, ih]
        rw [mul_assoc]

    /-- `factorial n = listProd (range_from_one n)`. -/
    private theorem factorial_eq_listProd (n : ℕ₀) :
        factorial n = listProd (range_from_one n) := by
      induction n with
      | zero      => rfl
      | succ n' ih =>
        rw [factorial_succ, range_from_one, listProd_append]
        rw [← ih]
        simp [listProd, mul_comm (factorial n') (σ n'), mul_one]

    /-- If `b ∈ L`, then `listProd L = mul b (listProd (L.erase b))`. -/
    private theorem listProd_erase {b : ℕ₀} {L : List ℕ₀}
        (hb : b ∈ L) : listProd L = mul b (listProd (L.erase b)) := by
      induction L with
      | nil        => exact absurd hb List.not_mem_nil
      | cons a rest ih =>
        simp only [listProd_cons]
        by_cases h : a = b
        · -- a = b: L.erase b = rest
          subst h
          rw [List.erase_cons_head]
        · -- a ≠ b: b ∈ rest, L.erase b = a :: rest.erase b
          have hb_rest : b ∈ rest := by
            rcases List.mem_cons.mp hb with h_eq | h_mem
            · exact absurd h_eq.symm h
            · exact h_mem
          have herase : (a :: rest).erase b = a :: rest.erase b := by
            apply List.erase_cons_tail; simp [beq_iff_eq, h]
          rw [herase, listProd_cons, ih hb_rest]
          -- mul a (mul b (listProd (rest.erase b))) = mul b (mul a (listProd (rest.erase b)))
          rw [← mul_assoc, mul_comm a b, mul_assoc]

    /-- **Pairing lemma**: If every element of `L` pairs with a distinct partner
        under `modInv`, then `listProd L ≡ 𝟙 [MOD p]`. -/
    private theorem prod_pairs {p : ℕ₀} (hp : Prime p) (L : List ℕ₀)
        (hnd     : L.Nodup)
        (hrange  : ∀ x ∈ L, 𝟘 < x ∧ lt₀ x p)
        (hclosed : ∀ x ∈ L, modInv p x ∈ L)
        (hnf     : ∀ x ∈ L, modInv p x ≠ x) :
        listProd L ≡ 𝟙 [MOD p] := by
      -- Prove by induction on bound n ≥ L.length
      suffices key : ∀ (n : Nat) (M : List ℕ₀), M.length ≤ n →
          M.Nodup →
          (∀ x ∈ M, 𝟘 < x ∧ lt₀ x p) →
          (∀ x ∈ M, modInv p x ∈ M) →
          (∀ x ∈ M, modInv p x ≠ x) →
          listProd M ≡ 𝟙 [MOD p] from
        key L.length L (Nat.le_refl _) hnd hrange hclosed hnf
      intro n
      induction n with
      | zero =>
        intro M hlen _ _ _ _
        have hM_empty : M = [] := by cases M with | nil => rfl | cons a l => simp at hlen
        subst hM_empty
        exact modEq_refl p 𝟙
      | succ n' ih =>
        intro M hlen hnd_M hrange_M hclosed_M hnf_M
        match M with
        | []        => exact modEq_refl p 𝟙
        | a :: rest =>
          have ha_in  : a ∈ (a :: rest) := List.mem_cons_self
          let b := modInv p a
          have hb_def : b = modInv p a := rfl
          have hb_in  : b ∈ (a :: rest) := hclosed_M a ha_in
          have hb_ne  : b ≠ a := hnf_M a ha_in
          have hb_rest : b ∈ rest := by
            rcases List.mem_cons.mp hb_in with h | h
            · exact absurd h hb_ne
            · exact h
          -- rest' = rest with b removed
          let rest' := rest.erase b
          have hrest_len : rest.length ≤ n' :=
            Nat.le_of_succ_le_succ hlen
          have hrest'_len : rest'.length ≤ n' := by
            show (rest.erase b).length ≤ n'
            have h1 : (rest.erase b).length = Nat.sub rest.length 1 :=
              List.length_erase_of_mem hb_rest
            exact Nat.le_trans (h1 ▸ Nat.sub_le rest.length 1) hrest_len
          -- rest'.Nodup
          have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd_M).2
          have hnd_rest' : rest'.Nodup := hnd_rest.erase b
          -- rest' ⊆ rest ⊆ a :: rest
          have hmem_rest' : ∀ x ∈ rest', x ∈ (a :: rest) := by
            intro x hx
            exact List.mem_cons_of_mem a (List.erase_subset hx)
          -- range condition for rest'
          have hrange_rest' : ∀ x ∈ rest', 𝟘 < x ∧ lt₀ x p := fun x hx =>
            hrange_M x (hmem_rest' x hx)
          -- no fixed points for rest'
          have hnf_rest' : ∀ x ∈ rest', modInv p x ≠ x := fun x hx =>
            hnf_M x (hmem_rest' x hx)
          -- closure under modInv for rest'
          have ha_not_rest : a ∉ rest := (List.nodup_cons.mp hnd_M).1
          have hclosed_rest' : ∀ x ∈ rest', modInv p x ∈ rest' := by
            intro x hx
            have hx_in_L : x ∈ (a :: rest) := hmem_rest' x hx
            have hx_ne_a  : x ≠ a := by
              intro h
              rw [h] at hx
              exact absurd (List.erase_subset hx) ha_not_rest
            have hmodx_in_L : modInv p x ∈ (a :: rest) := hclosed_M x hx_in_L
            -- modInv p x ≠ a (using involution: if modInv x = a then x = modInv a = b, but x ≠ b)
            have hx_ne_b : x ≠ b := fun h => by
              rw [h] at hx
              exact absurd hx (List.Nodup.not_mem_erase hnd_rest)
            have hmodx_ne_a : modInv p x ≠ a := by
              intro h_eq
              -- modInv x = a → x = modInv a = b (by involution)
              have hx_pos := (hrange_M x hx_in_L).1
              have hx_lt  := (hrange_M x hx_in_L).2
              have h_invol := modInv_invol hp hx_pos hx_lt
              rw [h_eq] at h_invol
              -- h_invol : modInv p a = x, i.e. b = x
              exact hx_ne_b h_invol.symm
            -- modInv p x ≠ b (by injectivity: if modInv x = b = modInv a then x = a)
            have hmodx_ne_b : modInv p x ≠ b := by
              intro h_eq
              -- modInv x = b = modInv a → apply involution to a: modInv(modInv a) = a
              -- and modInv x = modInv a → by involution x = a. But x ≠ a.
              have ha_pos := (hrange_M a ha_in).1
              have ha_lt  := (hrange_M a ha_in).2
              have hx_pos := (hrange_M x hx_in_L).1
              have hx_lt  := (hrange_M x hx_in_L).2
              -- modInv p a = b and modInv p x = b → modInv p a = modInv p x
              -- Apply modInv_invol to a: modInv p (modInv p a) = a
              -- modInv p (modInv p x) = x (involution)
              -- modInv p a = modInv p x → modInv p (modInv p a) = modInv p (modInv p x) → a = x
              have hinv_a := modInv_invol hp ha_pos ha_lt
              have hinv_x := modInv_invol hp hx_pos hx_lt
              -- h_eq: modInv p x = b = modInv p a
              have h_eq' : modInv p x = modInv p a := h_eq.trans hb_def
              -- modInv p x = modInv p a
              -- Apply involution: x = modInv p (modInv p x) = modInv p (modInv p a) = a
              rw [h_eq'] at hinv_x
              exact hx_ne_a (hinv_a.symm.trans hinv_x).symm
            -- modInv p x ∈ rest (since it's in a :: rest and ≠ a)
            have hmodx_in_rest : modInv p x ∈ rest := by
              rcases List.mem_cons.mp hmodx_in_L with h | h
              · exact absurd h hmodx_ne_a
              · exact h
            -- modInv p x ∈ rest and ≠ b → ∈ rest.erase b = rest'
            rwa [List.mem_erase_of_ne hmodx_ne_b]
          -- IH for rest'
          have ih_rest' : listProd rest' ≡ 𝟙 [MOD p] :=
            ih rest' hrest'_len hnd_rest' hrange_rest' hclosed_rest' hnf_rest'
          -- Expand listProd using erase
          have h_prod_rest : listProd rest = mul b (listProd rest') :=
            listProd_erase hb_rest
          have h_prod_L : listProd (a :: rest) = mul a (mul b (listProd rest')) := by
            rw [listProd_cons, h_prod_rest]
          -- a * b ≡ 1 [MOD p]
          have h_ab : mul a b ≡ 𝟙 [MOD p] := by
            rw [hb_def]; exact modInv_mul hp (hrange_M a ha_in).1 (hrange_M a ha_in).2
          -- Conclude
          rw [h_prod_L]
          exact modEq_trans
            (modEq_mul (modEq_refl p a) (modEq_mul (modEq_refl p b) ih_rest'))
            (by rw [mul_one]; exact h_ab)

    /-! ## § 7. The inner range {2, …, p−2} -/

    /-- `range_from_one n = 𝟙 :: (range_from_one n).tail` for `n ≠ 0`
        and the head is `𝟙`. -/
    private theorem range_from_one_head_one : ∀ (n : ℕ₀), n ≠ 𝟘 →
        ∃ t, range_from_one n = 𝟙 :: t := by
      intro n
      induction n with
      | zero => intro h; exact absurd rfl h
      | succ n' ih =>
        intro _
        cases n' with
        | zero => exact ⟨[], rfl⟩
        | succ n'' =>
          obtain ⟨t, ht⟩ := ih (succ_neq_zero n'')
          exact ⟨t ++ [σ (σ n'')], by rw [range_from_one, ht]; rfl⟩

    /-- `range_from_one n` is nodup. -/
    private theorem range_from_one_nodup : ∀ n : ℕ₀, (range_from_one n).Nodup := by
      intro n
      induction n with
      | zero => simp [range_from_one]
      | succ n' ih =>
        rw [range_from_one, List.nodup_append]
        refine ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro x hx y hy
        simp at hy; subst hy
        have hx_le := mem_range_from_one_le hx
        intro h
        rw [h] at hx_le
        exact absurd (lt_succ_self n') (le_not_lt hx_le)

    /-- `∀ x ∈ range_from_one n, 0 < x ∧ x ≤ n`. -/
    private theorem range_from_one_range (n : ℕ₀) :
        ∀ x ∈ range_from_one n, 𝟘 < x ∧ le₀ x n := by
      intro x hx
      exact ⟨pos_of_ne_zero x (mem_range_from_one_pos hx), mem_range_from_one_le hx⟩

    /-- `factorial (sub p (𝟙 + 𝟙)) ≡ 𝟙 [MOD p]` for prime `p`. -/
    private theorem factorial_pred_pred_one {p : ℕ₀} (hp : Prime p) :
        factorial (sub p (add 𝟙 𝟙)) ≡ 𝟙 [MOD p] := by
      -- p = 2: factorial 0 = 1 ≡ 1 [MOD 2]
      -- p = 3: factorial 1 = 1 ≡ 1 [MOD 3]
      -- p ≥ 5: pairing argument
      -- Cases on p
      cases p with
      | zero => exact absurd rfl (prime_ne_zero hp)
      | succ p' =>
        cases p' with
        | zero => exact absurd rfl (prime_ne_one hp)
        | succ p'' =>
          -- p = σ(σ p'') ≥ 2
          -- sub p (𝟙+𝟙) = p''
          have h_sub : sub (σ (σ p'')) (add 𝟙 𝟙) = p'' := by
            rw [show add 𝟙 𝟙 = σ (σ 𝟘) from rfl, ← sub_succ_succ_eq, ← sub_succ_succ_eq, sub_zero]
          rw [h_sub]
          -- factorial p'' = listProd (range_from_one p'')
          rw [factorial_eq_listProd]
          -- Case split: p'' = 0 (p=2) or p'' = σ 0 = 1 (p=3) or p'' ≥ 2 (p ≥ 4)
          cases p'' with
          | zero =>
            -- p=2: range_from_one 0 = [], listProd [] = 1 ≡ 1 [MOD 2]
            simp [range_from_one, listProd]
            exact modEq_refl _ 𝟙
          | succ p''' =>
            cases p''' with
            | zero =>
              -- p=3: range_from_one 1 = [1], listProd [1] = 1 ≡ 1 [MOD 3]
              native_decide
            | succ p'''' =>
              -- p ≥ 5 (since p = σ(σ(σ(σ p''''))); actually p'' = σ(σ p''''), p = σ(σ(σ(σ p''''))))
              -- σ(σ p'''') ≥ 2
              -- range_from_one (σ(σ p'''')) = [1, 2, ..., p''+1]
              -- = 𝟙 :: inner_range where inner_range = (range_from_one (σ(σ p''''))).tail
              -- listProd (𝟙 :: inner_range) = mul 𝟙 (listProd inner_range) = listProd inner_range
              -- We need: listProd inner_range ≡ 1 [MOD p]
              -- Apply prod_pairs to inner_range = [2,...,p-2]
              let n := σ (σ p'''')
              -- range_from_one n has head 𝟙
              obtain ⟨inner, hinner⟩ := range_from_one_head_one n (succ_neq_zero _)
              rw [hinner, listProd_cons, one_mul]
              have hp_eq : p = σ (σ n) := rfl
              have hp1 : sub p 𝟙 = σ n := by
                calc sub p 𝟙 = sub (σ (σ n)) 𝟙 := by rw [hp_eq]
                  _ = τ (σ (σ n)) := sub_one (σ (σ n))
                  _ = σ n := τ_σ_eq_self (σ n)
              have h_inner_props : ∀ x ∈ inner, x ≠ 𝟙 ∧ le₀ x n := by
                intro x hx
                have hx_L : x ∈ range_from_one n := by rw [hinner]; exact List.mem_cons.mpr (Or.inr hx)
                have h_le : le₀ x n := mem_range_from_one_le hx_L
                have h_neq_1 : x ≠ 𝟙 := by
                  intro h1
                  have h_nd : (range_from_one n).Nodup := range_from_one_nodup n
                  rw [hinner] at h_nd
                  have h_not_in : 𝟙 ∉ inner := (List.nodup_cons.mp h_nd).1
                  rw [h1] at hx
                  exact absurd hx h_not_in
                exact ⟨h_neq_1, h_le⟩
              have h_mem_range : ∀ m y, 𝟘 < y → le₀ y m → y ∈ range_from_one m := by
                intro m
                induction m with
                | zero =>
                  intro y hy_pos hy_le
                  have hy0 : y = 𝟘 := le_zero_eq y hy_le
                  rw [hy0] at hy_pos
                  exact absurd hy_pos (lt_irrefl 𝟘)
                | succ m' ih =>
                  intro y hy_pos hy_le
                  rcases (le_succ_iff_le_or_eq y m').mp hy_le with h_le | h_eq
                  · have hy_in : y ∈ range_from_one m' := ih y hy_pos h_le
                    rw [range_from_one]
                    exact List.mem_append.mpr (Or.inl hy_in)
                  · rw [h_eq, range_from_one]
                    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

              apply prod_pairs hp
              · -- inner.Nodup: it's the tail of range_from_one n which is nodup
                have hnd := range_from_one_nodup n
                rw [hinner] at hnd
                exact (List.nodup_cons.mp hnd).2
              · -- range: every x in inner satisfies 0 < x < p
                intro x hx
                have hx_in_L : x ∈ range_from_one n := by
                  rw [hinner]; exact List.mem_cons.mpr (Or.inr hx)
                have hx_range := range_from_one_range n x hx_in_L
                constructor
                · exact hx_range.1
                · -- x ≤ n = p-2 < p-1 < p
                have hy_lt_p : lt₀ y p := modInv_lt hp hx_pos hx_lt_p
                have hy_pos : 𝟘 < y := modInv_pos hp hx_pos hx_lt_p
                have hy_ne_1 : y ≠ 𝟙 := by
                  intro hy1
                  have h_inv_inv := modInv_invol hp hx_pos hx_lt_p
                  rw [hy1] at h_inv_inv
                  have h1_pos : 𝟘 < 𝟙 := lt_zero_succ 𝟘
                  have h1_lt_p : lt₀ 𝟙 p := one_lt_prime hp
                  have h_inv1 : modInv p 𝟙 = 𝟙 := (modInv_self_iff hp h1_pos h1_lt_p).mpr (Or.inl rfl)
                  rw [h_inv1] at h_inv_inv
                  exact absurd h_inv_inv.symm h_props.1
                have hy_ne_sub : y ≠ sub p 𝟙 := by
                  intro hy_sub
                  have h_inv_inv := modInv_invol hp hx_pos hx_lt_p
                  rw [hy_sub] at h_inv_inv
                  have hp1_pos : 𝟘 < sub p 𝟙 := sub_pos_of_lt (one_lt_prime hp)
                  have hp1_lt : lt₀ (sub p 𝟙) p := sub_lt_self_wp (lt_imp_le_wp (one_lt_prime hp)) (succ_neq_zero 𝟘)
                  have h_invp1 : modInv p (sub p 𝟙) = sub p 𝟙 := (modInv_self_iff hp hp1_pos hp1_lt).mpr (Or.inr rfl)
                  rw [h_invp1] at h_inv_inv
                  have hx_eq_sn : x = σ n := (h_inv_inv.symm.trans h_invp1).trans hp1
                  have hx_le_n : le₀ x n := h_props.2
                  rw [hx_eq_sn] at hx_le_n
                  exact absurd hx_le_n (nle_σn_n n)
                have hy_le_n : le₀ y n := by
                  have hy_le_sn : le₀ y (σ n) := (lt_succ_iff_le y (σ n)).mp (hp_eq ▸ hy_lt_p)
                  rcases (le_succ_iff_le_or_eq y n).mp hy_le_sn with hy_le | hy_eq
                  · exact hy_le
                  · exact absurd (hy_eq.trans hp1.symm) hy_ne_sub
                have hy_in_range : y ∈ range_from_one n := h_mem_range n y hy_pos hy_le_n
                rw [hinner] at hy_in_range
                rcases List.mem_cons.mp hy_in_range with hy1 | hy_inner
                · exact absurd hy1 hy_ne_1
                · exact hy_inner
              · -- no fixed points: ∀ x ∈ inner, modInv p x ≠ x
                intro x hx
                have h_props := h_inner_props x hx
                have hx_L : x ∈ range_from_one n := by rw [hinner]; exact List.mem_cons.mpr (Or.inr hx)
                have hx_range := range_from_one_range n x hx_L
                have hx_pos : 𝟘 < x := hx_range.1
                have hn_lt_p : lt₀ n p := by
                  rw [hp_eq]; exact lt_trans n (σ n) (σ (σ n)) (lt_succ_self n) (lt_succ_self (σ n))
                have hx_lt_p : lt₀ x p := lt_of_le_of_lt hx_range.2 hn_lt_p
                intro h_fix
                have h_self := (modInv_self_iff hp hx_pos hx_lt_p).mp h_fix
                rcases h_self with h1 | hp1_eq_x
                · exact absurd h1 h_props.1
                · have h_le_n := h_props.2
                  rw [hp1] at hp1_eq_x
                  rw [hp1_eq_x] at h_le_n
                  exact absurd h_le_n (nle_σn_n n)

    /-! ## § 8. Wilson's theorem -/

    /-- **Wilson's theorem**: for every prime `p`, `p ∣ (p−1)! + 1`. -/
    theorem wilson {p : ℕ₀} (hp : Prime p) : p ∣ add (factorial (sub p 𝟙)) 𝟙 := by
      -- (p-1)! = factorial(p-2) * (p-1)  [by factorial_succ]
      -- factorial(p-2) ≡ 1 [MOD p]         [by factorial_pred_pred_one]
      -- (p-1)! ≡ 1*(p-1) = p-1 [MOD p]
      -- (p-1)! + 1 ≡ p-1 + 1 = p ≡ 0 [MOD p]
      -- So p | (p-1)! + 1
      have hp_ne : p ≠ 𝟘 := prime_ne_zero hp
      -- p ≥ 2
      have hp2 : le₀ 𝟚 p := prime_ge_two hp
      -- sub p 𝟙 ≠ 0  (p - 1 ≥ 1)
      have hp1_ne : sub p 𝟙 ≠ 𝟘 := by
        intro h
        exact absurd (sub_eq_zero p 𝟙 h) (le_not_lt (one_lt_prime hp))
      -- σ (sub p (𝟙+𝟙)) = sub p 𝟙
      have h_succ_p2 := succ_p_sub_two_eq hp
      -- factorial (sub p 𝟙) = mul (factorial (sub p (𝟙+𝟙))) (sub p 𝟙)
      have h_fact_eq : factorial (sub p 𝟙) =
          mul (factorial (sub p (𝟙 + 𝟙))) (sub p 𝟙) := by
        rw [← h_succ_p2, factorial_succ]
      -- factorial (sub p (𝟙+𝟙)) ≡ 𝟙 [MOD p]
      have h_pred : factorial (sub p (𝟙 + 𝟙)) ≡ 𝟙 [MOD p] :=
        factorial_pred_pred_one hp
      -- factorial (sub p 𝟙) ≡ sub p 𝟙 [MOD p]
      have h_fact_mod : factorial (sub p 𝟙) ≡ sub p 𝟙 [MOD p] := by
        rw [h_fact_eq]
        have h1 : mul (factorial (sub p (𝟙 + 𝟙))) (sub p 𝟙) ≡
            mul 𝟙 (sub p 𝟙) [MOD p] :=
          modEq_mul h_pred (modEq_refl p _)
        simp [one_mul] at h1
        exact h1
      -- add (factorial (sub p 𝟙)) 𝟙 ≡ add (sub p 𝟙) 𝟙 [MOD p]
      have h_add_mod : add (factorial (sub p 𝟙)) 𝟙 ≡ add (sub p 𝟙) 𝟙 [MOD p] :=
        modEq_add h_fact_mod (modEq_refl p 𝟙)
      -- add (sub p 𝟙) 𝟙 = p  (since sub p 𝟙 = p - 1, adding 1 gives p)
      have h_p1_add : add (sub p 𝟙) 𝟙 = p := by
        rw [← succ_sub_one hp_ne, add_one]
      -- add (factorial (sub p 𝟙)) 𝟙 ≡ p ≡ 0 [MOD p]
      have h_zero_mod : add (factorial (sub p 𝟙)) 𝟙 ≡ 𝟘 [MOD p] := by
        rw [← h_p1_add] at h_add_mod ⊢
        calc add (factorial (sub p 𝟙)) 𝟙
            ≡ add (sub p 𝟙) 𝟙 [MOD p] := h_add_mod
          _ = add (sub p 𝟙) 𝟙 := rfl
          _ ≡ 𝟘 [MOD p] := by
              rw [h_p1_add]
              exact modEq_symm (modEq_zero_of_dvd hp_ne ⟨𝟙, mul_one p⟩)
      -- p | add (factorial (sub p 𝟙)) 𝟙
      exact (modEq_zero_iff_dvd hp_ne).mp h_zero_mod

  end Wilson

end Peano

export Peano.Wilson (wilson)
