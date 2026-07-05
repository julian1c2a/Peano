import Peano.PeanoNat.Div

open Peano
open PeanoNat

theorem test_h_rad_lt (ra b d : ℕ₀) (hb : b ≠ 𝟘) (hd : d ≠ 𝟘) (hra : lt₀ ra b) : lt₀ (mul ra d) (mul b d) := by
  have h_bd_neq_0 : mul b d ≠ 𝟘 := eq_zero_of_mul_eq_zero hb hd
  have h_or : ra = 𝟘 ∨ ra ≠ 𝟘 := by
    cases ra
    · exact Or.inl rfl
    · exact Or.inr (succ_neq_zero _)
  cases h_or with
  | inl h_zero =>
    rw [h_zero, zero_mul]
    exact neq_0_then_lt_0 h_bd_neq_0
  | inr h_neq =>
    have h_lt : lt₀ (mul d ra) (mul d b) := le_lt_mul_lt_compat (le_refl d) hra h_neq hd
    rw [mul_comm d ra, mul_comm d b] at h_lt
    exact h_lt
