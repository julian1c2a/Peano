def test (A p : Nat) (hA : 0 < A) (hsq : A * A % p = 1) : p ∣ (A - 1) * (A + 1) := by
  have hfact : A * A - 1 = (A - 1) * (A + 1) := by
    have h1 : (A - 1) * (A + 1) = (A - 1) * A + (A - 1) * 1 := Nat.mul_add _ _ _
    have h2 : (A - 1) * A = A * A - 1 * A := Nat.sub_mul _ _ _
    have h3 : A ≤ A * A := Nat.le_mul_self A
    rw [h1, h2]
    have h4 : 1 * A = A := Nat.one_mul A
    have h5 : (A - 1) * 1 = A - 1 := Nat.mul_one _
    rw [h4, h5]
    omega
  rw [← hfact]
  refine ⟨A * A / p, ?_⟩
  have hdm := Nat.div_add_mod (A * A) p
  rw [hsq] at hdm; omega
