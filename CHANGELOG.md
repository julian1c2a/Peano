# Changelog

## [Unreleased]

### Added (2026-06-17)

- **Phase 25 — Teoría de grupos finitos**:
  - **Combinatorics/Counting.lean**: Conteo combinatorio.
  - **Combinatorics/Perm.lean**: Tipo de permutaciones (⚠ 1 sorry).
  - **Combinatorics/Sign.lean**: Signo de permutaciones (paridad de transposiciones).
  - **Combinatorics/Orbit.lean**: Órbitas de elementos bajo permutaciones.
  - **Combinatorics/Group.lean**: Grupo simétrico Sym(A) (⚠ 1 sorry).
  - **Combinatorics/GroupTheory/Action.lean**: Acciones de grupo (⚠ 4 sorry).
  - **Combinatorics/GroupTheory/Sylow/Cosets.lean**: Coclases (⚠ 5 sorry).
  - **Combinatorics/GroupTheory/Sylow/Sylow.lean**: Teoremas de Sylow (⚠ 3 sorry).
  - Build: 51 jobs, 14 sorry warnings, 0 errors.

- **Phase 24 — Conjuntos finitos y funciones**:
  - **ListsAndSets/ListList.lean**: Listas de listas.
  - **ListsAndSets/FSetFSet.lean**: Conjuntos de conjuntos finitos.
  - **ListsAndSets/FSetFunction.lean** (~90 declaraciones exportadas):
    - `MapOn`: funciones totales entre FSet, `id`, `comp`, `comp_assoc`.
    - `Im`: imagen, cardinalidad de la imagen.
    - Inyectividad, sobreyectividad, biyectividad con iff de cardinalidad.
    - `leftInverse`, `rightInverse`, `inverse` para biyecciones, `inverse_involution`.
    - Principio del Palomar: desigualdades de cardinalidad.
    - `PreIm`, fibras, restricción.
    - `BinOpOn`: operaciones binarias sobre FSet.
    - Endomorfismos (`EndoOn`), especialización para A → A.
    - `Perm`: tipo de permutaciones biyectivas, inversas, composición.
  - List.lean y FSet.lean migrados a `ListsAndSets/` subdirectory.

- **Phase 21.6 — Fermat.lean**:
  - **NumberTheory/Fermat.lean**: `fermat_little` — Pequeño Teorema de Fermat
    ($a^{p-1} \equiv 1 \pmod{p}$ si $p$ primo y $p \nmid a$).
  - Estrategia: reducción a coprimalidad + Euler + totient_prime.

- **Phase 21.1–21.2 — Digits y Pairing**:
  - **Digits.lean**: `digits`, `ofDigits`, `numDigits` — representación en base *b*.
  - **Pairing.lean**: `cantorPair`, `cantorUnpair` — emparejamiento de Cantor con inversas.

- **Prelim refactoring**:
  - `Prelim.lean` dividido en `Prelim/ExistsUnique.lean` (constructivo) y `Prelim/Classical.lean` (noncomputable).
  - **ConstructiveCheck.lean**: Módulo de verificación de constructividad.

- **MapOn.comp_assoc**: Asociatividad general de la composición de funciones entre FSet (proof: `rfl`).

### Added (2026-04-09)

- **Phase 21.7b — Orden avanzado**:
  - **Order.lean**: `lt_or_ge (a b : ℕ₀) : Lt a b ∨ Le b a`,
    `le_or_lt (a b : ℕ₀) : Le a b ∨ Lt b a` + exportados.
  - **WellFounded.lean**: `noncomputable strongRecOn {C : ℕ₀ → Sort _} (n) (h) : C n`
    (recursión fuerte), `strongInductionOn {P : ℕ₀ → Prop} (n) (h) : P n` (inducción
    fuerte). Ambos vía `well_founded_lt.recursion`.
  - **Decidable.lean**: `instance : DecidableRel (@LT.lt ℕ₀ _)` (envuelve `decidableLt`),
    `instance : DecidableRel (@LE.le ℕ₀ _)` (envuelve `decidableLe`).
  - Build: 33 jobs, 0 warnings, 0 sorry.

- **Phase 21 — Decidable Prime**:
  - **Primes.lean**: `prime_imp_smallestDivisor_eq_self` (p primo ⇒ smallestDivisor p = p),
    `isPrimeb` (test booleano: `ble 𝟚 n && decide (smallestDivisor n = n)`),
    `isPrimeb_iff` (iff a `Prime n`), `decidablePrime (n : ℕ₀) : Decidable (Prime n)`.
  - Build: 33 jobs, 0 warnings, 0 sorry.

- **Phase 21.8 — IsEven/IsOdd**:
  - **Arith.lean**: `IsEven (n) := n % 𝟚 = 𝟘`, `IsOdd (n) := n % 𝟚 = 𝟙`,
    `decidableIsEven`, `decidableIsOdd`, `even_zero`, `odd_one`, `even_or_odd`,
    `not_even_and_odd`, `not_even_iff_odd`, `not_odd_iff_even`. Exportados 12 símbolos nuevos.
  - Build: 33 jobs, 0 warnings, 0 sorry.

### Added (2026-04-09) [earlier]

- **Isomorfismos Nat↔ℕ₀ completos para mul, div, mod, pow, gcd, lcm (§ 20.5)**:
  Completados los 14 teoremas de isomorfismo restantes en 4 módulos:
  - **Mul.lean**: `isomorph_Ψ_mul`, `isomorph_Λ_mul` (inducción sobre `m`, cadena `calc`)
  - **Div.lean**: `isomorph_Ψ_div` (vía `Nat.div_eq_of_lt_le`),
    `isomorph_Ψ_mod` (requiere `m ≠ 𝟘`, vía `Nat.add_left_cancel` + `Nat.div_add_mod`),
    `isomorph_Λ_div`, `isomorph_Λ_mod` (patrón `congrArg Λ`)
  - **Pow.lean**: `isomorph_Ψ_pow`, `isomorph_Λ_pow` (inducción sobre `m`, cadena `calc`)
  - **Arith.lean**: `isomorph_Ψ_gcd` (inducción bien fundada + `gcd_step`),
    `isomorph_Λ_gcd`, `isomorph_Ψ_lcm` (`unfold` + rewrite), `isomorph_Λ_lcm`
  - **Isomorph.lean**: Actualizado con imports de Mul, Div, Pow, Arith + 6 bloques export nuevos.
  - **Peano.lean**: Exports actualizados para los 14 nuevos teoremas.
  - **Nota**: `isomorph_Ψ_mod` requiere `hm : m ≠ 𝟘` porque Peano define `mod n 𝟘 = 𝟘`
    mientras Lean core define `Nat.mod n 0 = n`.
  - Build: 30 jobs, 0 warnings, 0 sorry.

### Added (2026-04-10)

- **Log.lean — Logaritmo entero con resto (§ 20)**:
  Nuevo módulo `Peano/PeanoNat/Log.lean` (`namespace Peano.Log`).
  Definiciones: `logMod`, `log`, `logRem` — piso del logaritmo en base `b` con resto.
  Patrón `(k, r)` tal que `n = b^k + r` y `n < b^{k+1}`.
  Exacto (`n` potencia de `b`) sii `r = 0`.
  11 símbolos exportados: `logMod`, `log`, `logRem`, `log_zero`, `logRem_zero`,
  `log_of_lt`, `logRem_of_lt`, `log_one`, `logRem_one`, `logMod_spec`, `log_upper_bound`.
  Build: 14 jobs, 0 warnings, 0 sorry.

- **Sqrt.lean — Raíz cuadrada entera con resto (§ 21)**:
  Nuevo módulo `Peano/PeanoNat/Sqrt.lean` (`namespace Peano.Sqrt`).
  Definiciones: `sqrtMod`, `sqrt`, `sqrtRem` — piso de raíz cuadrada con resto.
  Patrón `(k, r)` tal que `n = k² + r` y `r < 2k + 1`.
  Exacto (cuadrado perfecto) sii `r = 0`.
  10 símbolos exportados: `sqrtMod`, `sqrt`, `sqrtRem`, `sqrt_zero`, `sqrtRem_zero`,
  `sqrt_one`, `sqrtRem_one`, `sqrtMod_spec`, `sqrtRem_lt`, `sqrt_upper_bound`.
  Build: 14 jobs, 0 warnings, 0 sorry.

### Changed (2026-04-09)

- **Arith.lean GCD/LCM/Coprime Mathlib-style extensions (§ 8)**:
  Made `gcd_comm`, `gcd_divides_left`, `gcd_divides_right` public (were private).
  Added 25 new theorems: `gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`,
  `gcd_zero_right`, `gcd_zero_left`, `gcd_one_right`, `gcd_one_left`, `gcd_self`,
  `gcd_eq_zero_iff`, `gcd_ne_zero_left`, `gcd_ne_zero_right`, `dvd_gcd_iff`,
  `gcd_assoc`, `IsGCD_gcd`, `div_mul_cancel`, `gcd_mul_lcm`, `lcm_comm`,
  `lcm_zero_left`, `lcm_zero_right`, `dvd_lcm_left`, `dvd_lcm_right`, `lcm_self`,
  `coprime_comm`, `coprime_one_right`, `coprime_one_left`.
  Updated export blocks in Arith.lean and Peano.lean.
  Build: 28 jobs, 0 warnings, 0 sorry.

- **Rename MaxMin → Lattice**: `Peano/PeanoNat/MaxMin.lean` renamed to
  `Peano/PeanoNat/Lattice.lean`. Namespace `Peano.MaxMin` → `Peano.Lattice`.
  All imports, opens, exports, and fully-qualified references updated across
  8 dependent files. Documentation updated in all `.md` files.

- **Lattice.lean Mathlib-style extensions (§ 7)**:
  Added 18 new theorems: `max_min_self`, `min_max_self` (absorption Mathlib naming),
  `min_le_max`, `max_eq_left_iff`, `max_eq_right_iff`, `min_eq_left_iff`,
  `min_eq_right_iff`, `max_le_iff`, `le_min_iff`, `max_le_max`, `min_le_min`,
  `max_left_comm`, `min_left_comm`, `max_right_comm`, `min_right_comm`,
  `max_succ_succ`, `min_succ_succ`. Export block: 74 symbols total.
  Build: 28 jobs, 0 warnings, 0 sorry.

- **FSet.lean warning fix**: Removed unused `hu` parameter from
  `uniqueKeys_factListAddFactor`.

### Changed (2026-04-10)

- **Phase 17 — Factor Combinatorics subdirectory**: Moved `Pow.lean`,
  `Factorial.lean`, `Binom.lean`, `NewtonBinom.lean` into
  `Peano/PeanoNat/Combinatorics/`. All internal cross-imports updated.
  - `Peano.lean` imports updated to `Peano.PeanoNat.Combinatorics.*`.
  - Build: 22/22 jobs, 0 sorry, 0 warnings.

- **Phase 16 — Factor Decidable module**: New reexport module
  `Peano/PeanoNat/Decidable.lean` that collects all Decidable instances
  (`decidableLt`, `decidableGt`, `decidableLe`, `decidableGe`), boolean
  comparison functions (`blt`, `bgt`, `ble`, `bge`), and their iff
  equivalence theorems from StrictOrder and Order into a single import.
  - Build: 22/22 jobs, 0 sorry, 0 warnings.

- **Phase 15 — Create Isomorph.lean**: New reexport module
  `Peano/PeanoNat/Isomorph.lean` that collects all 30 Nat↔ℕ₀ isomorphism
  theorems (Λ/Ψ injectivity, bijectivity, composition, commutativity with
  σ/τ, and operation-level isomorphisms for lt/le/max/min/add/sub) from
  6 source modules into a single import point.
  - `Peano.lean` updated with `import Peano.PeanoNat.Isomorph`.
  - Build: 21/21 jobs, 0 sorry, 0 warnings.

- **Phase 14 — Extract Prelim.lean**: Extracted `ExistsUnique`, `choose`,
  `choose_spec`, `choose_unique`, `choose_spec_unique`, `choose_uniq` and
  `∃¹` syntax macros from `PeanoNat.lean` into new `Peano/Prelim.lean`.
  - `PeanoNat.lean` now imports `Peano.Prelim` instead of `Init.Classical`.
  - `Peano.lean` updated with `import Peano.Prelim` + separate export block.
  - DEPENDENCIES.md updated (new Prelim node in dependency graph).
  - Build: 20/20 jobs, 0 sorry, 0 warnings.

### Changed (2026-04-08)

- **Phase 13 — Subdirectory restructure**: Moved 15 `PeanoNat*.lean` files into
  `Peano/PeanoNat/` subdirectory with stripped prefix names.
  - `PeanoNatAxioms.lean` → `PeanoNat/Axioms.lean`, `PeanoNatAdd.lean` → `PeanoNat/Add.lean`, etc.
  - All imports updated: `Peano.PeanoNatXxx` → `Peano.PeanoNat.Xxx`.
  - `PeanoNat.lean` remains as barrel module at `Peano/PeanoNat.lean`.
  - DEPENDENCIES.md updated with new paths and module names.
  - AI-GUIDE.md §22 updated with new directory structure + §22.1 Prelim.lean standard.
  - AI-GUIDE-update.md created as cross-project template document.
  - Build: 19/19 jobs, 0 sorry, 0 warnings.
- **Phase 11 — Warning cleanup**: Removed unused `Nat.sub` simp arg in Sub.lean:484.
  Build: 19/19, 0 warnings.

### Changed (2026-04-09)

- **Fase 10 — Migración de nombres de identificadores**: Todos los identificadores
  públicos migrados a convenciones Mathlib4 (NAMING-CONVENTIONS.md).
  - **PeanoNat.lean**: `EqFnGen`→`eqFnGen`, `Comp`→`comp`, `EqFn`→`eqFn`,
    `EqFn2`→`eqFn2`, `EqFnNat`→`eqFnNat`.
  - **PeanoNatAxioms.lean**: `AXIOM_*` prefijos eliminados (→ `isNat_zero`,
    `isNat_succ`, `zero_ne_succ`, `succ_isNat`, `succ_congr`, `succ_injective`,
    `induction_principle`), `is_zero`→`isZero`, `is_succ`→`isSucc`,
    `return_branch`→`returnBranch`.
  - **PeanoNatStrictOrder.lean**: `BLt`→`blt`, `BGt`→`bgt`, `nlt_0_0`→`not_lt_zero`,
    `lt_0_n`→`pos_of_ne_zero`, `lt_then_neq`→`ne_of_lt`.
  - **PeanoNatOrder.lean**: `BLe`→`ble`, `BGe`→`bge`, `Le'`→`le'`.
  - **PeanoNatMaxMin.lean**: `Lt_of_not_le`→`lt_of_not_le`, `eq_max_min_then_eq`→
    `eq_of_max_eq_min`, `if_neq_then_max_xor`→`max_ne_min_of_ne`,
    `neq_args_then_lt_min_max`→`lt_max_of_ne`, `nexists_max_abs`→`not_exists_max`.
  - **PeanoNatAdd.lean**: `add_cancelation`→`add_cancel`.
  - **PeanoNatMul.lean**: `mul_ldistr`→`mul_add`, `mul_rdistr`→`add_mul`,
    `mul_eq_zero_wp`→`eq_zero_of_mul_eq_zero`,
    `mul_le_then_exists_max_factor`→`exists_factor_of_mul_le`.
  - **PeanoNatDiv.lean**: `divMod_eq`→`divMod_spec`, `mod_lt_divisor`→`mod_lt`,
    `div_of_lt_snd_interval`→`div_eq_two`.
  - **PeanoNatArith.lean**: `Factors_of`→`factorsOf`.
  - Peano.lean export blocks actualizados.
  - Build verificado: 19/19 jobs, 0 sorry.

### Changed (2026-04-08)

- **Fase 8 — Archivo renombrado**: `Peano/PeanoNatLib.lean` → `Peano/PeanoNat.lean`.
  - Imports actualizados en los 15 módulos dependientes + `Peano.lean` + `_template.lean`.
  - `frozen_files.txt`, `locked_files.txt`, `new-module.bash` actualizados.
  - Documentación actualizada (README, CURRENT-STATUS-PROJECT, NEXT-STEPS).
  - Build verificado: 19/19 jobs, 0 sorry.
- **Directorio renombrado**: `PeanoNatLib/` → `Peano/` — todos los imports, scripts y documentación actualizados.
- **Copyright headers**: Añadidos a los 9 módulos que no los tenían (AI-GUIDE §19).
- **Comentarios de ruta**: `PeanoNatLib/` → `Peano/` en las cabeceras de los 16 módulos.
- **Scripts**: `gen-root.bash`, `new-module.bash`, `git-lock.bash`, `copiar_txt.bash` — referencias actualizadas.
- **lakefile.lean** y **Peano.lean**: Comentarios actualizados.
- **.gitignore**: Añadido `LSP_*.log`.
- **README.md**: Versión de Lean corregida `v4.23.0` → `v4.29.0`.
- **CURRENT-STATUS-PROJECT.md**: Añadidos 6 módulos faltantes (Pow, Factorial, Binom, NewtonBinom, Primes, PeanoNatLib), actualizada a 19 jobs.
- **NEXT-STEPS.md**: Reescrito con Fases 7–10 detalladas (plan de renombrado de archivo, namespaces, migración de identificadores).
- Build verificado: 19/19 jobs, 0 sorry.

### Added (2026-03-16)

- **`Peano/PeanoNatPrimes.lean`** — módulo completamente demostrado, **cero `sorry`**.
  - `unique_prime_factorization` — **TFA unicidad** completamente probado. Dos errores de compilación resueltos en las ramas `p = p₀` y `p ≠ p₀` del `by_cases` final: la rama positiva requería `simp [DList.filter, DList.length]` en lugar de `simp` simple; la rama negativa requería `simp [DList.filter, Ne.symm h_pp₀]` + `rw [filter_count_neq …]` (dirección directa) en lugar del `simp only` + `rw [← …]` insuficiente.
  - `coprime_dvd_of_dvd_mul` (**Lema de Gauss**) — demostración completa. Los `sorry` de aritmética con resta saturada se sustituyeron por `sub_k_add_k`, `add_k_sub_k`, `lt_self_add_r` y `sub_pos_iff_lt`.
  - `irreducible_imp_prime`, `prime_iff_irreducible`, `prime_iff_has_exactly_two_divisors` — demostradas sin `sorry`, dependiendo de `coprime_dvd_of_dvd_mul`.
  - Estado del módulo actualizado: el comentario de cabecera ya no indica ningún `sorry` legítimo.
- **`REFERENCE.md`** — sección 12 actualizada: eliminados todos los marcadores ⚠️ sorry de T12.10, T12.11, T12.14, T12.19 y T12.28; estado del módulo corregido a "completamente demostrado".

- **`Peano/PeanoNatNewtonBinom.lean`** — módulo completado sin ningún `sorry`.
  - `finSum_succ_left (f n)` — desplazamiento a la izquierda: Σ_{k=0}^{n+1} f(k) = f(0) + Σ_{k=0}^{n} f(k+1).
  - `finSum_reverse (f n)` — invariancia por inversión del índice: Σ_{k=0}^{n} f(k) = Σ_{k=0}^{n} f(n−k).
  - `sum_binom_eq_pow_two (n)` — **demostrado**: Σ_{k=0}^{n} C(n,k) = 2ⁿ. Prueba por inducción con `finSum_succ_left` y Pascal.
  - `newton_binom (a b n)` — **demostrado**: (a+b)ⁿ = Σ_{k=0}^{n} C(n,k)·aᵏ·b^(n−k). Prueba por inducción; paso usa `binomTerm_pascal_step`, `finSum_mul_const_right`, `finSum_add_fn` y álgebra.
  - `exists_nm_growth` — **demostrado** con testigo n=2, m=1: ∀k≥1, 2+k < 2·2ᵏ. Prueba por inducción en k con lema auxiliar privado `lt_add_double_of_lt_of_pos`.
  - Eliminados todos los `sorry` del módulo.
- **`REFERENCE.md`** — sección 17 actualizada: añadidos T17.9b (`finSum_succ_left`), T17.9c (`finSum_reverse`); eliminados marcadores ⚠️ sorry de T17.10, T17.13, T17.15; estado del módulo actualizado a "completamente demostrado"; testigo de `exists_nm_growth` corregido a n=2, m=1.
- **`README.md`** — sección `Peano.NewtonBinom` actualizada; eliminados marcadores ⚠️ sorry de `sum_binom_eq_pow_two`, `newton_binom`, `exists_nm_growth`.

### Added (2026-03-15)

- **`Peano/PeanoNatNewtonBinom.lean`** — módulo nuevo, `namespace Peano.NewtonBinom`.
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
