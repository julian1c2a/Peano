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

    /-- `sub (sub p 𝟙) 𝟙 = sub p (𝟙 + 𝟙)` — i.e. `(p−1)−1 = p−2`. -/
    private theorem sub_sub_one_one (p : ℕ₀) : sub (sub p 𝟙) 𝟙 = sub p (𝟙 + 𝟙) := by
      rw [sub_sub]

    /-- For prime `p`, `σ (sub p (𝟙 + 𝟙)) = sub p 𝟙`, i.e. `(p−2)+1 = p−1`. -/
    private theorem succ_p_sub_two_eq {p : ℕ₀} (hp : Prime p) :
        σ (sub p (𝟙 + 𝟙)) = sub p 𝟙 := by
      rw [← sub_sub_one_one]
      apply succ_sub_one
      -- Need: sub p 𝟙 ≠ 𝟘, i.e. p ≥ 2
      intro h
      have h_lt : lt₀ 𝟙 p := one_lt_prime hp
      have h_le : le₀ p 𝟙 := by
        exact sub_eq_zero p 𝟙 h
      exact absurd h_lt (le_not_lt h_le)

    /-- `pow a p = mul (pow a (sub p 𝟙)) a` for prime `p`. -/
    private theorem pow_eq_pow_pred_mul {p a : ℕ₀} (hp : Prime p) :
        pow a p = mul (pow a (sub p 𝟙)) a := by
      rw [← pow_succ, succ_sub_one (prime_ne_zero hp)]

    /-- For prime `p` and `0 < a < p`, `p` does not divide `a`. -/
    private theorem prime_ndvd_lt {p a : ℕ₀} (hp : Prime p) (ha_pos : 𝟘 < a)
        (ha_lt : lt₀ a p) : ¬ p ∣ a := fun h_dvd =>
      absurd ha_lt (le_not_lt (divides_le h_dvd (pos_ne_zero ha_pos)))

    /-- For `a < p`, `mod a p = a`. -/
    private theorem mod_small {p a : ℕ₀} (ha_lt : lt₀ a p) : mod a p = a :=
      mod_of_lt a p ha_lt

    /-! ## § 2. Key cancellation lemma -/

    /-- If `mod (add a Y) p = a` with `a < p` and `Y < p` and `p ≠ 0`, then `Y = 0`. -/
    private theorem add_mod_cancel {p a Y : ℕ₀}
        (ha_lt : lt₀ a p) (hY_lt : lt₀ Y p) (hp_ne : p ≠ 𝟘)
        (h : mod (add a Y) p = a) : Y = 𝟘 := by
      -- Transfer to Nat level
      have h_ψp : Ψ p ≠ 0 := by rwa [Ne, ← isomorph_0_Ψ, Ψ_inj_iff]
      have h_ψ : (Ψ a + Ψ Y) % Ψ p = Ψ a := by
        have h1 := isomorph_Ψ_mod (add a Y) p hp_ne
        rw [isomorph_Ψ_add] at h1
        rw [← h1, h]
        rw [isomorph_Ψ_mod a p hp_ne, mod_small ha_lt]
      have ha_nat : Ψ a < Ψ p := isomorph_Ψ_lt.mpr ha_lt
      have hY_nat : Ψ Y < Ψ p := isomorph_Ψ_lt.mpr hY_lt
      by_cases hlt : Ψ a + Ψ Y < Ψ p
      · -- Case a + Y < p: mod is identity, so Y = 0
        rw [Nat.mod_eq_of_lt hlt] at h_ψ
        have hY0 : Ψ Y = 0 := by omega
        exact (Ψ_eq_zero_iff_eq_zero Y).mp hY0
      · -- Case a + Y ≥ p; since a + Y < 2p, mod = a + Y - p
        have h_bound : Ψ a + Ψ Y < 2 * Ψ p := by omega
        have h_eq : (Ψ a + Ψ Y) % Ψ p = Ψ a + Ψ Y - Ψ p := by
          have hge : Ψ p ≤ Ψ a + Ψ Y := Nat.le_of_not_lt hlt
          rw [Nat.mod_eq_sub_mod hge]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h_eq] at h_ψ
        -- Ψa + ΨY - Ψp = Ψa → ΨY = Ψp → ΨY ≥ Ψp, contradicts hY_nat
        have : Ψ Y = Ψ p := by omega
        exact absurd (this ▸ hY_nat) (Nat.lt_irrefl _)

    /-! ## § 3. Fermat implies `a^(p−1) ≡ 1 [MOD p]` -/

    /-- For prime `p` and `0 < a < p`:  `pow a (sub p 𝟙) ≡ 𝟙 [MOD p]`. -/
    private theorem pow_pred_one {p a : ℕ₀} (hp : Prime p) (ha_pos : 𝟘 < a)
        (ha_lt : lt₀ a p) : pow a (sub p 𝟙) ≡ 𝟙 [MOD p] := by
      have hp_ne : p ≠ 𝟘 := prime_ne_zero hp
      -- X = mod (pow a (sub p 𝟙)) p
      set X := mod (pow a (sub p 𝟙)) p with hX_def
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
      have h_expand : mul X a = add a (mul (sub X 𝟙) a) := by
        conv_lhs =>
          rw [← succ_sub_one hX_ne, add_mul, one_mul]
        rw [add_comm]
      -- Let Y := mod (mul (sub X 𝟙) a) p; then mod (add a Y) p = a
      set Y := mod (mul (sub X 𝟙) a) p with hY_def
      have hY_lt : lt₀ Y p := mod_lt (mul (sub X 𝟙) a) p hp_ne
      have ha_lt_for_cancel := ha_lt
      have h_add_mod : mod (add a Y) p = a := by
        rw [add_mod, mod_small ha_lt, hY_def, ← add_mod]
        rw [← h_expand]
        exact h_Xa
      -- By add_mod_cancel: Y = 0
      have hY0 : Y = 𝟘 := add_mod_cancel ha_lt hY_lt hp_ne h_add_mod
      -- p | mul (sub X 𝟙) a
      have hpY : p ∣ mul (sub X 𝟙) a := by
        rw [← mod_eq_zero_iff_dvd hp_ne, ← hY_def, hY0]
      -- Coprime p a
      have hcop : gcd p a = 𝟙 :=
        prime_not_dvd_imp_coprime hp (prime_ndvd_lt hp ha_pos ha_lt)
      -- By Gauss: p | sub X 𝟙
      have hp_sub : p ∣ sub X 𝟙 := by
        have hcop' : Coprime p a := (gcd_eq_one_iff_coprime p a).mp hcop
        rw [mul_comm] at hpY
        exact coprime_dvd_of_dvd_mul hcop' hpY
      -- sub X 𝟙 < p (since X < p and X ≥ 1 → sub X 𝟙 ≤ X - 1 < p - 1 < p)
      have hX_lt : lt₀ X p := mod_lt (pow a (sub p 𝟙)) p hp_ne
      have hsub_lt : lt₀ (sub X 𝟙) p := by
        calc lt₀ (sub X 𝟙) X := sub_lt_self_wp (lt_imp_le_wp hX_pos) hX_ne
          _ < p := hX_lt
      -- sub X 𝟙 = 0
      have hsub0 : sub X 𝟙 = 𝟘 := by
        rcases hp_sub with ⟨k, hk⟩
        cases k with
        | zero => rw [mul_zero] at hk; exact hk.symm
        | succ k' =>
          exfalso
          have : le₀ p (mul p (σ k')) := ⟨σ k', (mul_comm p _).symm⟩
          have : lt₀ (sub X 𝟙) p := hsub_lt
          rw [← hk] at this
          exact absurd ‹le₀ p (mul p (σ k'))› (lt_not_le this)
      -- X = 1
      have hX1 : X = 𝟙 := by
        have hle : le₀ X 𝟙 := sub_eq_zero X 𝟙 hsub0
        have hge : le₀ 𝟙 X := hX_pos
        exact antisymm_le hle hge
      -- Show ModEq: mod (pow a (sub p 𝟙)) p = mod 𝟙 p = 1
      unfold ModEq
      rw [← hX_def, hX1, mod_small ha_lt |>.symm, mod_small (one_lt_prime hp)]
      rfl

    /-! ## § 4. Modular inverse -/

    /-- `modInv p a := a^(p−2) mod p` (the modular inverse of `a` mod `p`). -/
    private def modInv (p a : ℕ₀) : ℕ₀ :=
      mod (pow a (sub p (𝟙 + 𝟙))) p

    /-- `modInv p a < p`. -/
    private theorem modInv_lt {p a : ℕ₀} (hp : Prime p) (ha_lt : lt₀ a p) :
        lt₀ (modInv p a) p :=
      mod_lt (pow a (sub p (𝟙 + 𝟙))) p (prime_ne_zero hp)

    /-- `mul a (modInv p a) ≡ 𝟙 [MOD p]` for `0 < a < p`. -/
    private theorem modInv_mul {p a : ℕ₀} (hp : Prime p) (ha_pos : 𝟘 < a)
        (ha_lt : lt₀ a p) : mul a (modInv p a) ≡ 𝟙 [MOD p] := by
      -- pow a (sub p 𝟙) = mul (pow a (sub p (𝟙+𝟙))) a   [by pow_succ + succ_p_sub_two_eq]
      have h_pow_eq : pow a (sub p 𝟙) = mul (pow a (sub p (𝟙 + 𝟙))) a := by
        rw [← pow_succ, succ_p_sub_two_eq hp]
      -- pow a (sub p 𝟙) ≡ 𝟙 [MOD p]
      have h_pred : pow a (sub p 𝟙) ≡ 𝟙 [MOD p] := pow_pred_one hp ha_pos ha_lt
      -- mul (pow a (sub p (𝟙+𝟙))) a ≡ 𝟙 [MOD p]
      rw [← h_pow_eq] at h_pred
      -- modInv p a ≡ pow a (sub p (𝟙+𝟙)) [MOD p]
      have h_inv_eq : modInv p a ≡ pow a (sub p (𝟙 + 𝟙)) [MOD p] :=
        modEq_symm (modEq_mod (pow a (sub p (𝟙 + 𝟙))) p)
      -- mul a (modInv p a) ≡ mul a (pow a (sub p (𝟙+𝟙))) [MOD p]
      have h1 : mul a (modInv p a) ≡ mul a (pow a (sub p (𝟙 + 𝟙))) [MOD p] :=
        modEq_mul (modEq_refl p a) h_inv_eq
      -- mul a (pow a (sub p (𝟙+𝟙))) = mul (pow a (sub p (𝟙+𝟙))) a  [comm]
      have h2 : mul a (pow a (sub p (𝟙 + 𝟙))) = mul (pow a (sub p (𝟙 + 𝟙))) a :=
        mul_comm a _
      rw [h2] at h1
      exact modEq_trans h1 h_pred

    /-- `0 < modInv p a` for `0 < a < p`. -/
    private theorem modInv_pos {p a : ℕ₀} (hp : Prime p) (ha_pos : 𝟘 < a)
        (ha_lt : lt₀ a p) : 𝟘 < modInv p a := by
      by_contra h
      push_neg at h
      have h0 : modInv p a = 𝟘 := antisymm_le h (zero_le _)
      -- mul a 0 ≡ 1 [MOD p], but mul a 0 = 0 and 0 ≡ 1 [MOD p] means p | 1
      rw [h0, mul_zero] at modInv_mul
      have h_dvd : p ∣ 𝟙 := by
        have := @modInv_mul p a hp ha_pos ha_lt
        rw [h0, mul_zero] at this
        unfold ModEq at this
        rw [mod_zero_left, mod_small (one_lt_prime hp)] at this
        exact (mod_eq_zero_iff_dvd (prime_ne_zero hp)).mp this.symm
      have := divides_le h_dvd (succ_neq_zero 𝟘)
      exact absurd (one_lt_prime hp) (le_not_lt this)

    /-! ## § 5. Involution of modInv -/

    /-- `modInv p (modInv p a) = a` for `0 < a < p`. -/
    private theorem modInv_invol {p a : ℕ₀} (hp : Prime p) (ha_pos : 𝟘 < a)
        (ha_lt : lt₀ a p) : modInv p (modInv p a) = a := by
      have hp_ne  : p ≠ 𝟘        := prime_ne_zero hp
      set b := modInv p a with hb_def
      have hb_pos : 𝟘 < b        := modInv_pos hp ha_pos ha_lt
      have hb_lt  : lt₀ b p      := modInv_lt hp ha_lt
      -- mul a b ≡ 1 [MOD p]
      have h_ab : mul a b ≡ 𝟙 [MOD p] := modInv_mul hp ha_pos ha_lt
      -- mul b (modInv p b) ≡ 1 [MOD p]
      have h_b_inv : mul b (modInv p b) ≡ 𝟙 [MOD p] := modInv_mul hp hb_pos hb_lt
      -- Derive: a ≡ modInv p b [MOD p]
      -- a = a*1 ≡ a*(b*(modInv p b)) = (a*b)*(modInv p b) ≡ 1*(modInv p b) = modInv p b
      have h_equiv : a ≡ modInv p b [MOD p] := by
        calc a = mul a 𝟙                           := (mul_one a).symm
          _ ≡ mul a (mul b (modInv p b)) [MOD p]  := modEq_mul (modEq_refl p a) (modEq_symm h_b_inv)
          _ = mul (mul a b) (modInv p b)           := by rw [mul_assoc b a (modInv p b)]
          _ ≡ mul 𝟙 (modInv p b) [MOD p]          := modEq_mul h_ab (modEq_refl p _)
          _ = modInv p b                           := one_mul _
      -- a < p and modInv p b < p, so from a ≡ modInv p b [MOD p]: a = modInv p b
      have ha_mod : mod a p = a := mod_small ha_lt
      have hb_inv_lt : lt₀ (modInv p b) p := modInv_lt hp hb_lt
      have hb_inv_mod : mod (modInv p b) p = modInv p b := mod_small hb_inv_lt
      unfold ModEq at h_equiv
      rw [ha_mod, hb_inv_mod] at h_equiv
      exact h_equiv

    /-- `modInv p a = a ↔ a = 𝟙 ∨ a = sub p 𝟙` for `0 < a < p`. -/
    private theorem modInv_self_iff {p a : ℕ₀} (hp : Prime p) (ha_pos : 𝟘 < a)
        (ha_lt : lt₀ a p) : modInv p a = a ↔ a = 𝟙 ∨ a = sub p 𝟙 := by
      have hp_ne  : p ≠ 𝟘 := prime_ne_zero hp
      constructor
      · intro h_self
        -- modInv p a = a → a * a ≡ 1 [MOD p]
        have h_sq : mul a a ≡ 𝟙 [MOD p] := by
          have := modInv_mul hp ha_pos ha_lt
          rw [h_self] at this
          exact this
        -- p | a^2 - 1 = (a-1)*(a+1)  [using Nat transfer]
        -- At Nat level: (Ψa)^2 % Ψp = 1
        -- Then Ψp | (Ψa)^2 - 1 = (Ψa-1)*(Ψa+1)
        -- By primality: Ψp | Ψa-1 or Ψp | Ψa+1
        -- ⟹ a ≡ 1 (mod p) or a ≡ p-1 (mod p)
        -- Since 0 < a < p: a = 1 or a = p-1
        have h_ψp_ne : Ψ p ≠ 0 := by rwa [Ne, ← isomorph_0_Ψ, Ψ_inj_iff]
        have h_sq_nat : Ψ a ^ 2 % Ψ p = 1 := by
          have h1 := isomorph_Ψ_mod (mul a a) p hp_ne
          rw [isomorph_Ψ_mul] at h1
          unfold ModEq at h_sq
          rw [← h1, h_sq, isomorph_Ψ_mod 𝟙 p hp_ne]
          rw [mod_small (one_lt_prime hp)]
          simp [isomorph_0_Ψ, Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
        -- Ψp | (Ψa)^2 - 1 = (Ψa - 1) * (Ψa + 1)
        have ha_pos_nat : 0 < Ψ a := by
          have := isomorph_Ψ_lt.mpr ha_pos
          simp [isomorph_0_Ψ] at this
          exact this
        have ha_lt_nat : Ψ a < Ψ p := isomorph_Ψ_lt.mpr ha_lt
        have h_sq_dvd : Ψ p ∣ Ψ a ^ 2 - 1 := by
          have : Ψ a ^ 2 % Ψ p = 1 % Ψ p := by
            rw [h_sq_nat, Nat.mod_eq_of_lt (Nat.one_lt_iff_ne_one.mp (Nat.lt_of_lt_pred
              (by omega)) |>.symm ▸ (by omega))]
            omega
          exact Nat.dvd_of_mod_eq_zero (by
            have := Nat.sub_mod (Ψ a ^ 2) 1 (Ψ p)
            rw [h_sq_nat] at this
            simp at this
            exact Nat.mod_eq_zero_of_dvd ⟨_, this.symm⟩)
        -- (Ψa)^2 - 1 = (Ψa - 1) * (Ψa + 1)
        have h_factor : Ψ a ^ 2 - 1 = (Ψ a - 1) * (Ψ a + 1) := by
          have : 1 ≤ Ψ a := ha_pos_nat
          nlinarith [Nat.sub_add_cancel this]
        rw [h_factor] at h_sq_dvd
        -- By primality of Ψp: Ψp | Ψa-1 or Ψp | Ψa+1
        have h_prime_nat : Nat.Prime (Ψ p) := by
          rwa [← isPrimeb_iff] at hp
          done
        rcases h_prime_nat.dvd_mul.mp h_sq_dvd with h1 | h2
        · -- Ψp | Ψa - 1, and 0 < Ψa - 1 < Ψp (since 1 ≤ Ψa ≤ Ψp-1)
          -- So Ψa - 1 = 0, Ψa = 1, a = 1
          have : Ψ a - 1 < Ψ p := by omega
          have h_zero : Ψ a - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h1 this
          have : Ψ a = 1 := by omega
          left
          exact Ψ_inj a 𝟙 (by rw [this, isomorph_0_Ψ]; rfl)
        · -- Ψp | Ψa + 1, and Ψa + 1 ≤ Ψp (since Ψa ≤ Ψp - 1)
          -- So Ψa + 1 = Ψp, a = p-1
          have h_le : Ψ a + 1 ≤ Ψ p := by omega
          have h_dvd_le := Nat.le_of_dvd (by omega) h2
          have : Ψ a + 1 = Ψ p := Nat.le_antisymm h_dvd_le h_le
          right
          apply Ψ_inj
          rw [isomorph_Ψ_sub, isomorph_0_Ψ]
          · simp; omega
          · simp [isomorph_0_Ψ]
      · intro h
        rcases h with rfl | rfl
        · -- modInv p 𝟙 = 𝟙
          simp [modInv]
          rw [pow_one_base, mod_small (one_lt_prime hp)]
        · -- modInv p (p-1) = p-1
          -- (p-1)^(p-2) ≡ p-1 [MOD p]
          -- From (p-1) ≡ -1 [MOD p] and (-1)^(p-2) = -1 (p odd or p=2)
          -- We use: modInv p (sub p 𝟙) = sub p 𝟙 iff (p-1)*(p-1) ≡ 1 [MOD p]
          -- (p-1)^2 = p^2 - 2p + 1 ≡ 1 [MOD p]. ✓
          -- So modInv_mul applied to (sub p 𝟙) gives (p-1)*modInv p (p-1) ≡ 1
          -- Also (p-1)*(p-1) ≡ 1. By uniqueness: modInv p (p-1) = p-1.
          have hp1_pos : 𝟘 < sub p 𝟙 := by
            apply pos_of_ne_zero
            intro h
            have := sub_eq_zero p 𝟙 h
            exact absurd (one_lt_prime hp) (le_not_lt this)
          have hp1_lt : lt₀ (sub p 𝟙) p := by
            apply sub_lt_self_wp (lt_imp_le_wp hp1_pos)
            exact succ_neq_zero 𝟘
          -- (p-1)*(p-1) ≡ 1 [MOD p]
          have h_sq_one : mul (sub p 𝟙) (sub p 𝟙) ≡ 𝟙 [MOD p] := by
            -- Transfer to Nat: (Ψp - 1)^2 % Ψp = 1
            unfold ModEq
            have hp_ne := prime_ne_zero hp
            have h := isomorph_Ψ_mod (mul (sub p 𝟙) (sub p 𝟙)) p hp_ne
            rw [isomorph_Ψ_mul, isomorph_Ψ_sub, isomorph_0_Ψ] at h
            have h1 : (Ψ p - 1) * (Ψ p - 1) % Ψ p = 1 := by
              have hge : 1 ≤ Ψ p := by
                have := isomorph_Ψ_lt.mpr (one_lt_prime hp); simp [isomorph_0_Ψ] at this; omega
              have : (Ψ p - 1) * (Ψ p - 1) = Ψ p * Ψ p - 2 * Ψ p + 1 := by nlinarith
              rw [this, show Ψ p * Ψ p - 2 * Ψ p + 1 = Ψ p * (Ψ p - 2) + 1 by nlinarith]
              rw [Nat.add_mul_mod_self_left]
              exact Nat.mod_eq_of_lt (by
                have := isomorph_Ψ_lt.mpr (one_lt_prime hp); simp [isomorph_0_Ψ] at this; omega)
            rw [← h, h1]
            rw [isomorph_Ψ_mod 𝟙 p hp_ne, mod_small (one_lt_prime hp)]
          -- By involution: modInv p (sub p 𝟙) = modInv p (modInv p (sub p 𝟙))?
          -- Instead: use that (p-1)*modInv p (p-1) ≡ 1 and (p-1)*(p-1) ≡ 1, so modInv = p-1
          have h_inv := modInv_mul hp hp1_pos hp1_lt
          -- (p-1)*(modInv p (p-1)) ≡ 1 [MOD p]
          -- (p-1)*(p-1) ≡ 1 [MOD p]
          -- By cancellation (modInv_invol): modInv p (p-1) = p-1
          -- Use pow_pred_one for (p-1):
          -- modInv p (p-1) = mod ((p-1)^(p-2)) p
          -- = mod (modInv p (p-1)) p = modInv p (p-1) < p
          -- Both (p-1) and modInv p (p-1) are < p and:
          -- (p-1) * modInv p (p-1) ≡ 1 ≡ (p-1)*(p-1)
          -- Cancel (p-1): modInv p (p-1) ≡ (p-1)
          -- Since both < p: equal.
          -- The cancellation argument (same as pow_pred_one derivation):
          have h_cancel : modInv p (sub p 𝟙) ≡ sub p 𝟙 [MOD p] := by
            -- mul (sub p 𝟙) (modInv p (sub p 𝟙)) ≡ 𝟙 [MOD p]   [h_inv]
            -- mul (sub p 𝟙) (sub p 𝟙) ≡ 𝟙 [MOD p]              [h_sq_one]
            -- Cancel (sub p 𝟙): modInv p (sub p 𝟙) ≡ sub p 𝟙 [MOD p]
            -- This is the same add_mod_cancel argument but for ModEq
            -- Let Z := modInv p (sub p 𝟙)
            set Z := modInv p (sub p 𝟙)
            have hZ_lt : lt₀ Z p := modInv_lt hp hp1_lt
            -- We need: Z ≡ sub p 𝟙 [MOD p]
            -- From h_inv: (p-1)*Z ≡ 1 and h_sq_one: (p-1)*(p-1) ≡ 1
            -- So (p-1)*Z ≡ (p-1)*(p-1), cancel (p-1)
            -- Use the same trick: set up add_mod_cancel
            -- Actually use: mod ((p-1)*Z) p = mod ((p-1)*(p-1)) p = 1
            -- Then mod (mul (sub p 𝟙) Z) p = mod (mul (sub p 𝟙) (sub p 𝟙)) p
            -- By the same argument as pow_pred_one, cancel (sub p 𝟙)
            suffices h : Z = sub p 𝟙 by exact h ▸ modEq_refl p Z
            -- We know: Z < p, sub p 𝟙 < p, and (sub p 𝟙)*Z ≡ 1 [MOD p] [h_inv]
            -- And (sub p 𝟙)*(sub p 𝟙) ≡ 1 [MOD p] [h_sq_one]
            -- So (sub p 𝟙)*Z ≡ (sub p 𝟙)*(sub p 𝟙)
            -- => Z ≡ sub p 𝟙 [MOD p] by the cancellation argument
            -- Since Z < p and sub p 𝟙 < p: Z = sub p 𝟙
            have h_modZ : mod (mul (sub p 𝟙) Z) p = mod (mul (sub p 𝟙) (sub p 𝟙)) p := by
              unfold ModEq at h_inv h_sq_one
              exact h_inv.trans h_sq_one.symm
            -- Use the same add_mod_cancel: (sub p 𝟙)*Z = sub p 𝟙 + (sub p 𝟙)*(Z - sub p 𝟙 or vice versa)
            -- Actually just replicate the pow_pred_one argument for Z vs sub p 𝟙:
            by_cases h_le : le₀ Z (sub p 𝟙)
            · by_cases h_eq : Z = sub p 𝟙
              · exact h_eq
              · -- Z < sub p 𝟙
                have h_lt_Z : lt₀ Z (sub p 𝟙) := lt_of_le_of_ne h_le h_eq
                -- (sub p 𝟙) * Z = (sub p 𝟙) * (sub p 𝟙) - (sub p 𝟙) * (sub (sub p 𝟙) Z)
                -- (sub p 𝟙) * (sub (sub p 𝟙) Z) = (sub p 𝟙)^2 - (sub p 𝟙)*Z
                -- p | (sub p 𝟙) * (sub (sub p 𝟙) Z)
                -- Since sub (sub p 𝟙) Z ≤ sub p 𝟙 - 1 < p, and (sub p 𝟙) < p:
                -- (sub p 𝟙) * (sub (sub p 𝟙) Z) < p^2 but not necessarily < p
                -- This approach gets complicated. Let me use Nat transfer directly.
                exfalso
                have hZ_nat : Ψ Z < Ψ (sub p 𝟙) := isomorph_Ψ_lt.mpr h_lt_Z
                have h_modZ_nat : (Ψ (sub p 𝟙) * Ψ Z) % Ψ p =
                    (Ψ (sub p 𝟙) * Ψ (sub p 𝟙)) % Ψ p := by
                  rw [← isomorph_Ψ_mul, ← isomorph_Ψ_mul]
                  rw [← isomorph_Ψ_mod _ p (prime_ne_zero hp),
                      ← isomorph_Ψ_mod _ p (prime_ne_zero hp)]
                  exact congrArg Ψ h_modZ
                have h_cop_nat : Nat.Coprime (Ψ p) (Ψ (sub p 𝟙)) := by
                  unfold Nat.Coprime
                  rw [← isomorph_Ψ_gcd]
                  have hcop_p1 : gcd p (sub p 𝟙) = 𝟙 :=
                    prime_not_dvd_imp_coprime hp (prime_ndvd_lt hp hp1_pos hp1_lt)
                  rw [hcop_p1]; rfl
                have h_dvd : Ψ p ∣ Ψ (sub p 𝟙) * Ψ Z - Ψ (sub p 𝟙) * Ψ (sub p 𝟙) := by
                  have : Ψ (sub p 𝟙) * Ψ (sub p 𝟙) ≤ Ψ (sub p 𝟙) * Ψ Z := by
                    apply Nat.mul_le_mul_left; omega
                  exact Nat.dvd_of_mod_eq_zero (by
                    rw [Nat.sub_mod, h_modZ_nat.symm, Nat.sub_self, Nat.zero_mod])
                have h_factor : Ψ (sub p 𝟙) * Ψ Z - Ψ (sub p 𝟙) * Ψ (sub p 𝟙) =
                    Ψ (sub p 𝟙) * (Ψ Z - Ψ (sub p 𝟙)) := by
                  have : Ψ (sub p 𝟙) * Ψ (sub p 𝟙) ≤ Ψ (sub p 𝟙) * Ψ Z := by
                    apply Nat.mul_le_mul_left; omega
                  omega
                -- Contradiction: Ψ Z < Ψ (sub p 𝟙), so Ψ Z - Ψ (sub p 𝟙) = 0 (Nat subtraction)
                -- But h_dvd says Ψp | 0 which is fine but the direction was wrong
                -- Actually h_le says Z ≤ sub p 𝟙 and h_lt_Z says Z < sub p 𝟙
                -- So (sub p 𝟙)*Z < (sub p 𝟙)*(sub p 𝟙), and from mod equality we'd
                -- need Ψp | (sub p 𝟙)^2 - (sub p 𝟙)*Z = (sub p 𝟙)*(sub p 𝟙 - Z)
                have h_dvd2 : Ψ p ∣ Ψ (sub p 𝟙) * Ψ (sub p 𝟙) - Ψ (sub p 𝟙) * Ψ Z := by
                  have hge : Ψ (sub p 𝟙) * Ψ Z ≤ Ψ (sub p 𝟙) * Ψ (sub p 𝟙) := by
                    apply Nat.mul_le_mul_left; omega
                  exact Nat.dvd_of_mod_eq_zero (by
                    rw [Nat.sub_mod, h_modZ_nat, Nat.sub_self, Nat.zero_mod])
                rw [← Nat.mul_sub_one] at h_dvd2
                have h_p1_ne : Ψ (sub p 𝟙) ≠ 0 := by
                  rw [← isomorph_0_Ψ]; exact fun h => absurd (Ψ_inj _ _ h) (pos_ne_zero hp1_pos)
                have h_sub_ne : Ψ (sub p 𝟙) - Ψ Z ≠ 0 := by omega
                have h_cop2 := h_cop_nat.dvd_of_dvd_mul_left h_dvd2
                have h_sub_lt : Ψ (sub p 𝟙) - Ψ Z < Ψ p := by
                  have := isomorph_Ψ_lt.mpr hp1_lt; omega
                exact absurd (Nat.le_of_dvd (by omega) h_cop2) (by omega)
            · -- Z > sub p 𝟙
              push_neg at h_le
              have h_lt_Z : lt₀ (sub p 𝟙) Z := h_le
              -- Symmetric case: Ψ Z > Ψ (sub p 𝟙)
              have hZ_gt : Ψ (sub p 𝟙) < Ψ Z := isomorph_Ψ_lt.mpr h_lt_Z
              have h_modZ_nat : (Ψ (sub p 𝟙) * Ψ Z) % Ψ p =
                  (Ψ (sub p 𝟙) * Ψ (sub p 𝟙)) % Ψ p := by
                rw [← isomorph_Ψ_mul, ← isomorph_Ψ_mul]
                rw [← isomorph_Ψ_mod _ p (prime_ne_zero hp),
                    ← isomorph_Ψ_mod _ p (prime_ne_zero hp)]
                exact congrArg Ψ h_modZ
              have h_cop_nat : Nat.Coprime (Ψ p) (Ψ (sub p 𝟙)) := by
                unfold Nat.Coprime
                rw [← isomorph_Ψ_gcd]
                have hcop_p1 : gcd p (sub p 𝟙) = 𝟙 :=
                  prime_not_dvd_imp_coprime hp (prime_ndvd_lt hp hp1_pos hp1_lt)
                rw [hcop_p1]; rfl
              have h_dvd3 : Ψ p ∣ Ψ (sub p 𝟙) * (Ψ Z - Ψ (sub p 𝟙)) := by
                rw [Nat.mul_sub_one]
                exact Nat.dvd_of_mod_eq_zero (by
                  rw [Nat.sub_mod, h_modZ_nat.symm, Nat.sub_self, Nat.zero_mod])
              have h_cop3 := h_cop_nat.dvd_of_dvd_mul_left h_dvd3
              have h_sub_lt2 : Ψ Z - Ψ (sub p 𝟙) < Ψ p := by
                have := isomorph_Ψ_lt.mpr hZ_lt; omega
              have h_sub_ne2 : Ψ Z - Ψ (sub p 𝟙) ≠ 0 := by omega
              exact absurd (Nat.le_of_dvd (by omega) h_cop3) (by omega)
          -- From h_cancel: modInv p (sub p 𝟙) ≡ sub p 𝟙 [MOD p]
          -- Both < p, so equal:
          unfold ModEq at h_cancel
          rw [mod_small hZ_lt, mod_small hp1_lt] at h_cancel
          exact h_cancel
      -- h_cancel says modInv p (sub p 𝟙) = sub p 𝟙
      unfold ModEq at h_cancel
      rw [mod_small (modInv_lt hp hp1_lt), mod_small hp1_lt] at h_cancel
      exact h_cancel

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
        simp [listProd, mul_comm (factorial n') (σ n')]

    /-- If `b ∈ L`, then `listProd L = mul b (listProd (L.erase b))`. -/
    private theorem listProd_erase {b : ℕ₀} {L : List ℕ₀}
        (hb : b ∈ L) : listProd L = mul b (listProd (L.erase b)) := by
      induction L with
      | nil        => exact absurd hb (List.not_mem_nil b)
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
          rw [List.erase_cons_tail _ h, listProd_cons, ih hb_rest]
          -- mul a (mul b (listProd (rest.erase b))) = mul b (mul a (listProd (rest.erase b)))
          rw [← mul_assoc b a _, mul_comm b a, mul_assoc a b _]

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
        have hM_empty : M = [] := List.length_eq_zero.mp (Nat.le_zero.mp hlen)
        subst hM_empty
        exact modEq_refl p 𝟙
      | succ n' ih =>
        intro M hlen hnd_M hrange_M hclosed_M hnf_M
        match M with
        | []        => exact modEq_refl p 𝟙
        | a :: rest =>
          have ha_in  : a ∈ (a :: rest) := List.mem_cons_self a rest
          set b := modInv p a with hb_def
          have hb_in  : b ∈ (a :: rest) := hclosed_M a ha_in
          have hb_ne  : b ≠ a := hnf_M a ha_in
          have hb_rest : b ∈ rest := by
            rcases List.mem_cons.mp hb_in with h | h
            · exact absurd h.symm hb_ne
            · exact h
          -- rest' = rest with b removed
          let rest' := rest.erase b
          have hrest_len : rest.length ≤ n' :=
            Nat.le_of_succ_le_succ hlen
          have hrest'_len : rest'.length ≤ n' := by
            have h1 : rest'.length = rest.length - 1 :=
              List.length_erase_of_mem hb_rest
            omega
          -- rest'.Nodup
          have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd_M).2
          have hnd_rest' : rest'.Nodup := hnd_rest.erase b
          -- rest' ⊆ rest ⊆ a :: rest
          have hmem_rest' : ∀ x ∈ rest', x ∈ (a :: rest) := by
            intro x hx
            exact List.mem_cons_of_mem a (List.erase_subset b rest hx)
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
              exact absurd (List.erase_subset b rest hx) ha_not_rest
            have hmodx_in_L : modInv p x ∈ (a :: rest) := hclosed_M x hx_in_L
            -- modInv p x ≠ a (using involution: if modInv x = a then x = modInv a = b, but x ≠ b)
            have hx_ne_b : x ≠ b := fun h => by
              rw [h] at hx
              exact absurd hx (List.not_mem_erase_of_nodup hnd_rest)
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
              rw [← hb_def] at h_eq
              -- modInv p x = modInv p a
              -- Apply involution: x = modInv p (modInv p x) = modInv p (modInv p a) = a
              rw [h_eq] at hinv_x
              exact hx_ne_a (hinv_x.trans hinv_a.symm).symm
            -- modInv p x ∈ rest (since it's in a :: rest and ≠ a)
            have hmodx_in_rest : modInv p x ∈ rest := by
              rcases List.mem_cons.mp hmodx_in_L with h | h
              · exact absurd h hmodx_ne_a
              · exact h
            -- modInv p x ∈ rest and ≠ b → ∈ rest.erase b = rest'
            rwa [List.mem_erase_of_ne hmodx_ne_b]
          -- IH for rest'
          have ih_rest' : listProd rest' ≡ 𝟙 [MOD p] :=
            ih hrest'_len rest' hnd_rest' hrange_rest' hclosed_rest' hnf_rest'
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
          calc mul a (mul b (listProd rest'))
              ≡ mul a (mul b 𝟙) [MOD p] :=
                modEq_mul (modEq_refl p a) (modEq_mul (modEq_refl p b) ih_rest')
            _ = mul a b := by rw [mul_one]
            _ ≡ 𝟙 [MOD p] := h_ab

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
        | zero => exact ⟨[], by simp [range_from_one]⟩
        | succ n'' =>
          obtain ⟨t, ht⟩ := ih (succ_neq_zero n'')
          exact ⟨t ++ [σ (σ n'')], by rw [range_from_one, ht]; simp⟩

    /-- `range_from_one n` is nodup. -/
    private theorem range_from_one_nodup : ∀ n : ℕ₀, (range_from_one n).Nodup := by
      intro n
      induction n with
      | zero => simp [range_from_one]
      | succ n' ih =>
        rw [range_from_one]
        apply List.Nodup.append ih
        · exact List.nodup_singleton _
        · intro x hx hy
          simp at hy; subst hy
          have hx_le := mem_range_from_one_le hx
          exact absurd (lt_succ_self n') (le_not_lt hx_le)

    /-- `∀ x ∈ range_from_one n, 0 < x ∧ x ≤ n`. -/
    private theorem range_from_one_range (n : ℕ₀) :
        ∀ x ∈ range_from_one n, 𝟘 < x ∧ le₀ x n := by
      intro x hx
      exact ⟨pos_of_ne_zero x (mem_range_from_one_pos hx), mem_range_from_one_le hx⟩

    /-- For prime `p ≥ 5`, every `x ∈ {2,…,p−2}` satisfies `modInv p x ∈ {2,…,p−2}`
        and `modInv p x ≠ x`. -/
    private theorem inner_range_closed {p : ℕ₀} (hp : Prime p)
        (hp5 : le₀ (𝟙 + 𝟙 + 𝟙 + 𝟙 + 𝟙) p) :
        ∀ x, 𝟙 < x → lt₀ x (sub p 𝟙) →
          modInv p x ∈ (range_from_one n) → -- placeholder; see below
          𝟙 < modInv p x ∧ lt₀ (modInv p x) (sub p 𝟙) ∧ modInv p x ≠ x := by
      sorry -- placeholder; will be superseded

    /-- `factorial (sub p (𝟙 + 𝟙)) ≡ 𝟙 [MOD p]` for prime `p`. -/
    private theorem factorial_pred_pred_one {p : ℕ₀} (hp : Prime p) :
        factorial (sub p (𝟙 + 𝟙)) ≡ 𝟙 [MOD p] := by
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
          have h_sub : sub (σ (σ p'')) (𝟙 + 𝟙) = p'' := by
            simp [sub_succ_succ_eq]
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
              set n := σ (σ p'''') with hn_def
              -- range_from_one n has head 𝟙
              obtain ⟨inner, hinner⟩ := range_from_one_head_one n (succ_neq_zero _)
              rw [hinner, listProd_cons, one_mul]
              -- Now prove: listProd inner ≡ 1 [MOD p]
              -- inner = [2, ..., σ(σ p'''')] = [2,...,p-2] for p = σ(σ(σ(σ p'''')))
              -- Actually for now use prod_pairs:
              apply prod_pairs hp
              · -- inner.Nodup: it's the tail of range_from_one n which is nodup
                have hnd := range_from_one_nodup n
                rw [hinner] at hnd
                exact (List.nodup_cons.mp hnd).2
              · -- range: every x in inner satisfies 0 < x < p
                intro x hx
                have hx_in_L : x ∈ range_from_one n := by
                  rw [hinner]; exact List.mem_cons_of_mem 𝟙 hx
                have hx_range := range_from_one_range n x hx_in_L
                constructor
                · exact hx_range.1
                · -- x ≤ n = p-2 < p-1 < p
                  exact lt_of_le_of_lt hx_range.2 (by
                    apply lt_trans _ (one_lt_prime hp)
                    -- n = σ(σ p'''') = p - 2 < p - 1 < p
                    -- For σ(σ(σ(σ p''''))) prime:
                    -- n ≤ sub (σ(σ(σ(σ p'''')))) 𝟙 ... this needs more work
                    -- Use: x ≤ n < sub p 𝟙
                    sorry)
              · -- closure: ∀ x ∈ inner, modInv p x ∈ inner
                sorry
              · -- no fixed points: ∀ x ∈ inner, modInv p x ≠ x
                sorry

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
