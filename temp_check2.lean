theorem test (a b c d : Nat) (hb : b > 0) (hd : d > 0) (h : a * d = c * b) : a / b = c / d := by
  have h1 : a / b = (a * d) / (b * d) := by exact (Nat.mul_div_mul_right a b hd).symm
  have h2 : c / d = (c * b) / (d * b) := by exact (Nat.mul_div_mul_right c d hb).symm
  rw [h] at h1
  rw [Nat.mul_comm d b] at h2
  rw [h1, h2]
