# Changelog

## [Unreleased]

### Added (2026-03-15)

- **`PeanoNatLib/PeanoNatNewtonBinom.lean`** — módulo nuevo, `namespace Peano.NewtonBinom`.
  - `finSum (f : ℕ₀ → ℕ₀) : ℕ₀ → ℕ₀` — sumatorio finito Σ_{k=0}^{n} f(k); computable, recursión estructural.
  - Propiedades demostradas: `finSum_zero`, `finSum_succ`, `finSum_zero_fn`, `finSum_add_fn` (linealidad), `finSum_mul_const`, `finSum_mul_const_right` (escalado), `finSum_le_of_le` (monotonía), `finSum_pos` (positividad), `finSum_const` (suma constante = (n+1)·c).
  - `binomTerm a b n k` = C(n,k)·aᵏ·b^(n−k) — término k-ésimo del binomio; con `binomTerm_zero` y `binomTerm_self`.
  - `sum_binom_eq_pow_two (n)` — Σ_{k=0}^{n} C(n,k) = 2ⁿ. ⚠️ sorry en reindexación con Pascal.
  - `newton_binom (a b n)` — (a+b)ⁿ = Σ_{k=0}^{n} C(n,k)·aᵏ·b^(n−k). ⚠️ sorry en convolución de sumatorios (caso base demostrado).
  - `pow_add_split (n m k)` — nᵐ⁺ᵏ = nᵐ·nᵏ.
  - `exists_nm_growth` — ∃n=4, m=2, ∀k≥1, (n+k)ᵐ < n^(m+k). ⚠️ sorry en cota exponencial.
- **`Peano.lean`** — añadidos imports y re-exports de `PeanoNatPow`, `PeanoNatFactorial`, `PeanoNatBinom`, `PeanoNatNewtonBinom`.
- **`REFERENCE.md`** — secciones 13 (Pow, completada T13.7–T13.23), 14 (Factorial, nueva), 15 (Binom, nueva), 16 (Peano.lean raíz actualizada), 17 (NewtonBinom, nueva); tabla de módulos y namespaces ampliada.

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
