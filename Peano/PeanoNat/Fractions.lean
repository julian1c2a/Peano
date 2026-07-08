/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Peano.PeanoNat.Arith
import Peano.PeanoNat.Lattice

namespace Peano
namespace Arith

open Peano.Axioms
open Peano.Order
open Peano.Add
open Peano.Mul
open Peano.Sub
open Peano.Div

theorem dvd_of_mul_dvd {a b c : ℕ₀} (hc : c ≠ 𝟘) (h : mul a c ∣ mul b c) : a ∣ b := by
  rcases h with ⟨k, hk⟩
  exact ⟨k, by
    apply mul_cancelation_right _ _ c hc
    have h1 : mul (mul a k) c = mul a (mul k c) := mul_assoc k a c
    have h2 : mul k c = mul c k := mul_comm k c
    have h3 : mul (mul a c) k = mul a (mul c k) := mul_assoc c a k
    rw [h1, h2, ← h3, ← hk]⟩

theorem gcd_div_self (a b : ℕ₀) (h : a ≠ 𝟘 ∨ b ≠ 𝟘) : gcd (div a (gcd a b)) (div b (gcd a b)) = 𝟙 := by
  have hg : gcd a b ≠ 𝟘 := by
    intro hg0
    rw [gcd_eq_zero_iff] at hg0
    rcases h with ha | hb
    · exact ha hg0.1
    · exact hb hg0.2
  let g := gcd a b
  let d := gcd (div a g) (div b g)
  have hd_div_a : d ∣ div a g := gcd_dvd_left _ _
  have hd_div_b : d ∣ div b g := gcd_dvd_right _ _
  rcases hd_div_a with ⟨x, hx⟩
  rcases hd_div_b with ⟨y, hy⟩
  have ha : a = mul (div a g) g := (div_mul_cancel hg (gcd_dvd_left a b)).symm
  have hb : b = mul (div b g) g := (div_mul_cancel hg (gcd_dvd_right a b)).symm
  have had : a = mul (mul d x) g := by rw [ha, hx]
  have hbd : b = mul (mul d y) g := by rw [hb, hy]
  have hdg_dvd_a : mul d g ∣ a := ⟨x, by
    rw [had]
    have h1 : mul (mul d x) g = mul d (mul x g) := mul_assoc x d g
    have h2 : mul x g = mul g x := mul_comm x g
    have h3 : mul (mul d g) x = mul d (mul g x) := mul_assoc g d x
    rw [h1, h2, ← h3]⟩
  have hdg_dvd_b : mul d g ∣ b := ⟨y, by
    rw [hbd]
    have h1 : mul (mul d y) g = mul d (mul y g) := mul_assoc y d g
    have h2 : mul y g = mul g y := mul_comm y g
    have h3 : mul (mul d g) y = mul d (mul g y) := mul_assoc g d y
    rw [h1, h2, ← h3]⟩
  have hdg_dvd_g : mul d g ∣ g := dvd_gcd hdg_dvd_a hdg_dvd_b
  rcases hdg_dvd_g with ⟨k, hk⟩
  have h_mul_eq : mul (mul d k) g = mul 𝟙 g := by
    have h1 : mul (mul d k) g = mul d (mul k g) := mul_assoc k d g
    have h2 : mul k g = mul g k := mul_comm k g
    have h3 : mul (mul d g) k = mul d (mul g k) := mul_assoc g d k
    rw [h1, h2, ← h3, ← hk, one_mul]
  have h_dk1 : mul d k = 𝟙 := mul_cancelation_right _ _ g hg h_mul_eq
  have h_dvd_one : d ∣ 𝟙 := ⟨k, h_dk1.symm⟩
  exact antisymm_divides h_dvd_one (one_divides d)



theorem cross_mul_eq_imp_reduced_eq {a b c d : ℕ₀}
  (hb : b ≠ 𝟘) (hd : d ≠ 𝟘)
  (h_cross : mul a d = mul b c)
  (hab : gcd a b = 𝟙) (hcd : gcd c d = 𝟙) :
  a = c ∧ b = d := by
  have hdvd_a_c : a ∣ c := by
    have h_a_dvd_bc : a ∣ mul b c := ⟨d, h_cross.symm⟩
    exact euclid_lemma hab h_a_dvd_bc
  have hdvd_c_a : c ∣ a := by
    have h_cross_symm : mul c b = mul d a := by
      have h1 : mul c b = mul b c := mul_comm c b
      have h2 : mul d a = mul a d := mul_comm d a
      rw [h1, ← h_cross, ← h2]
    have h_c_dvd_da : c ∣ mul d a := ⟨b, h_cross_symm.symm⟩
    exact euclid_lemma hcd h_c_dvd_da
  have h_a_eq_c : a = c := antisymm_divides hdvd_a_c hdvd_c_a
  have h_b_eq_d : b = d := by
    by_cases ha0 : a = 𝟘
    · have h_c0 : c = 𝟘 := by rw [← h_a_eq_c, ha0]
      have hb1 : b = 𝟙 := by
        have h_gcd_0_b : gcd 𝟘 b = b := gcd_zero_left b
        rw [ha0] at hab
        rw [h_gcd_0_b] at hab
        exact hab
      have hd1 : d = 𝟙 := by
        have h_gcd_0_d : gcd 𝟘 d = d := gcd_zero_left d
        rw [h_c0] at hcd
        rw [h_gcd_0_d] at hcd
        exact hcd
      rw [hb1, hd1]
    · have h_cross2 : mul a d = mul a b := by
        have h_cb : mul b c = mul b a := by rw [← h_a_eq_c]
        have h_ba : mul b a = mul a b := mul_comm b a
        rw [h_cb, h_ba] at h_cross
        exact h_cross
      exact (mul_cancelation_left a d b ha0 h_cross2).symm
  exact ⟨h_a_eq_c, h_b_eq_d⟩

end Arith
end Peano
