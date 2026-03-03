# Changelog

## [Unreleased]

### Added (2026-03-03)

- `PeanoNatArith.lean`: Teorema `antisymm_divides {a b : ℕ₀} : a ∣ b → b ∣ a → a = b` — antisimetría de la divisibilidad en `ℕ₀`.
- `PeanoNatArith.lean`: Lema privado `gcd_divides_left (a b : ℕ₀) : gcd a b ∣ a` (y `gcd_divides_right`).
- `PeanoNatArith.lean`: Teorema `gcd_divides_max (a b : ℕ₀) : gcd a b ∣ max a b` y `gcd_divides_min`.
- `PeanoNatArith.lean`: Teorema `gcd_divides_linear_combo (a b n m : ℕ₀) : gcd a b ∣ (a * n + b * m)`.
- `PeanoNatArith.lean`: Lema privado `gcd_step (a b : ℕ₀) (hb : b ≠ 𝟘) : gcd a b = gcd b (a % b)` — paso de reducción euclideo; demostrado con `antisymm_divides` + `gcd_greatest`.
- `PeanoNatArith.lean`: Lema privado `bezout_additive` — forma OR de la identidad de Bézout (`∃ n m, G + n*min = m*max ∨ G + n*max = m*min`). Inducción bien fundada con 5 ramas; alternancia OR propagada en la rama recursiva.
- `PeanoNatArith.lean`: Teorema `bezout_natform (a b : ℕ₀) : ∃ n m, gcd a b = n * a - m * b ∨ gcd a b = n * b - m * a` — identidad de Bézout en forma natural (coeficientes ℕ₀).
- `PeanoNatArith.lean`: Lema privado `gcd_comm (a b : ℕ₀) : gcd a b = gcd b a` — conmutatividad del MCD en `ℕ₀`.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Definiciones `Divides₁`, `IsGCD₁`, `gcd₁`, `Coprime₁` para el subtipo `ℕ₁ = {n : ℕ₀ // n ≠ 𝟘}`.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Teoremas `divides₁_refl`, `divides₁_trans`, `divides₁_antisymm`.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Lema privado `mod_eq_zero_iff_divides {a b : ℕ₁} : a.val % b.val = 𝟘 ↔ b ∣₁ a`.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Lema privado `gcd₁_val_eq (a b : ℕ₁) : (gcd₁ a b).val = gcd a.val b.val` — puente entre `gcd₁` sobre `ℕ₁` y `gcd` sobre `ℕ₀`. La definición de `gcd₁` usa `dite` directo (sin `let r := …`) para que `unfold` + `dif_pos`/`dif_neg` funcionen sin que el elaborador desdoble el cuerpo recursivo.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Teoremas `gcd₁_comm`, `gcd₁_divides_left`, `gcd₁_divides_right`, `gcd₁_divides_both`.
- **`PeanoNatArith.lean` completamente demostrado** — cero `sorry`.
- `REFERENCE.md`: Actualizada con todos los teoremas nuevos y sección ℕ₁.

### Added (2026-03-02)

- `PeanoNatMul.lean`: Teorema `mul_sub (c a b : ℕ₀) (h_lt : Lt b a) : mul c (sub a b) = sub (mul c a) (mul c b)` — distributividad de la multiplicación sobre la resta truncada bajo condición `b < a`.
- `PeanoNatMul.lean`: Exportados `mul_le_mono_right`, `mul_sub` y `lt_of_lt_of_le` desde `Peano.Mul`.
- `PeanoNatArith.lean`: Teorema `divides_sub {a b c : ℕ₀} (h_lt : Lt b a) (ha : c ∣ a) (hb : c ∣ b) : c ∣ (sub a b)` — divisibilidad se preserva bajo la resta truncada.
- `PeanoNatArith.lean`: Teorema `divides_mod {a b c : ℕ₀} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (a % b)` — si `c` divide `a` y `b`, también divide el resto `a % b`.
- `PeanoNatArith.lean`: Demostración completa de `gcd_greatest (a b c : ℕ₀) : (c ∣ a ∧ c ∣ b) → c ∣ gcd a b` usando inducción bien fundada con patrón `H` doblemente generalizado.
- `PeanoNatArith.lean`: Exportados `divides_sub`, `divides_mod` y `gcd_greatest` desde `Peano.NatArith`.
- `REFERENCE.md`: Actualizada con los nuevos teoremas.
