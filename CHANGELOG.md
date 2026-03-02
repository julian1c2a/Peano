# Changelog

## [Unreleased]

### Added (2026-03-02)

- `PeanoNatMul.lean`: Teorema `mul_sub (c a b : ℕ₀) (h_lt : Lt b a) : mul c (sub a b) = sub (mul c a) (mul c b)` — distributividad de la multiplicación sobre la resta truncada bajo condición `b < a`.
- `PeanoNatMul.lean`: Exportados `mul_le_mono_right`, `mul_sub` y `lt_of_lt_of_le` desde `Peano.Mul`.
- `PeanoNatArith.lean`: Teorema `divides_sub {a b c : ℕ₀} (h_lt : Lt b a) (ha : c ∣ a) (hb : c ∣ b) : c ∣ (sub a b)` — divisibilidad se preserva bajo la resta truncada.
- `PeanoNatArith.lean`: Teorema `divides_mod {a b c : ℕ₀} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (a % b)` — si `c` divide `a` y `b`, también divide el resto `a % b`.
- `PeanoNatArith.lean`: Demostración completa de `gcd_greatest (a b c : ℕ₀) : (c ∣ a ∧ c ∣ b) → c ∣ gcd a b` usando inducción bien fundada con patrón `H` doblemente generalizado.
- `PeanoNatArith.lean`: Exportados `divides_sub`, `divides_mod` y `gcd_greatest` desde `Peano.NatArith`.
- `REFERENCE.md`: Actualizada con los nuevos teoremas.
