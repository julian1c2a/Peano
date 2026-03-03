# Archivo Temporal — Contexto de Sesión

**Última actualización:** 2026-03-03

---

## Estado actual del proyecto

`lake build` falla con errores en `PeanoNatArith.lean`. Todo lo demás compila.

---

## Objetivo de la sesión

Demostrar `theorem bezout_additive` (privado) que es prerequisito de `theorem bezout_natform`.

- `bezout_natform` **ya compila** ✅
- `bezout_additive` tiene **errores activos** ❌

---

## Enunciados de los teoremas

```lean4
-- Forma aditiva (prerequisito interno):
private theorem bezout_additive (a b : ℕ₀) :
    ∃ n m : ℕ₀, add (gcd a b) (mul n (min a b)) = mul m (max a b)

-- Forma de sustracción (ya compila, usa bezout_additive):
theorem bezout_natform (a b : ℕ₀) :
    ∃ n m : ℕ₀, gcd a b = sub (mul n (max a b)) (mul m (min a b))
```

---

## Teoremas auxiliares ya probados (compilan ✅)

- `gcd_step (a b : ℕ₀) (hb : b ≠ 𝟘) : gcd a b = gcd b (a % b)` — prueba algebraica vía `antisymm_divides`
- `gcd_comm`, `gcd_divides_gcd_symm`, `gcd_divides_first/second/both`
- `gcd_greatest`, `divides_mod`, `divides_sub`

---

## Estructura de la prueba de bezout_additive

```lean4
suffices H : ∀ (b a : ℕ₀), ∃ n m, gcd a b + n*min(a,b) = m*max(a,b)
  -- ATENCIÓN: orden de parámetros en H es (b, a), no (a, b)
  -- exact H b a  ← invierte el orden
intro b
induction b using well_founded_lt.induction
rename_i b ih   -- b es la variable de inducción (primer param de H)
intro a         -- a es el segundo parámetro de H
by_cases hb0 : b = 𝟘
· -- Rama b = 0: COMPILA ✅
· -- Rama b ≠ 0:
    -- IH: ih (a%b) h_mod_lt b  →  n', m', ih_eq: gcd b (a%b) + n'*(a%b) = m'*b
    -- gcd_step: rw [h_gcd_eq]
    -- let q := a / b   ← DENTRO del branch b≤a (no global)
    rcases le_total a b with h_le_ab | h_le_ba
    · -- a ≤ b: COMPILA ✅
        · a < b: COMPILA ✅
        · a = b (rw [h_eq_ab], NO usar subst): COMPILA ✅
    · -- b ≤ a: max=a, min=b ← TIENE ERRORES ❌
        by_cases hmod0 : a%b = 𝟘
        · a%b = 0 (a = q*b): COMPILA ✅
        · a%b ≠ 0: ← TIENE ERRORES LÓGICOS ❌
```

---

## Errores actuales del último `lake build`

### 1. `h_mul_mod` (línea ~569): `mul_assoc` con orden incorrecto

```
Tactic `rewrite` failed: Did not find (q*n')*b in n'*a - n'*(q*b) = n'*a - (n'*q)*b
```

**Causa:** `mul_assoc (n m k : ℕ₀) : mul (mul m n) k = mul m (mul n k)` — el primer arg es el "interior derecho".
`mul_assoc n' q b : (q*n')*b = n'*(q*b)` — busca `(q*n')*b` pero el goal tiene `n'*(q*b)` y quiere `(n'*q)*b`.

**Fix:** Usar `← mul_assoc q n' b` que tiene LHS = `(n'*q)*b` y RHS = `n'*(q*b)`:

```lean4
rw [h_mod_eq, mul_sub n' a (mul q b) h_qb_lt_a, ← mul_assoc q n' b]
```

### 2. `h_le_mul` (línea ~572): mismo problema de `mul_assoc`

```
Tactic `rewrite` failed: Did not find (q*n')*b in Le ((n'*q)*b) (n'*a)
```

**Fix:**

```lean4
have h_le_mul : Le (mul (mul n' q) b) (mul n' a) := by
  rw [mul_assoc q n' b]   -- reescribe (n'*q)*b → n'*(q*b)
  exact mul_le_mono_right n' (lt_imp_le _ _ h_qb_lt_a)
```

### 3. `step2` (línea ~591): `add_comm` con args invertidos

```
Tactic `rewrite` failed: Did not find (n'*a - (n'*q)*b)+gcd b (a%b)
  in: (gcd b (a%b)+n'*a - (n'*q)*b) = m'*b
```

Después de `rw [h_mul_mod] at ih_eq`, ih_eq tiene: `gcd + (n'*a - (n'*q)*b) = m'*b`.
`add_comm A B` busca `A + B` pero ih_eq tiene `B + A`. Args al revés.

**Fix:**

```lean4
rw [add_comm (gcd b (a % b)) (sub (mul n' a) (mul (mul n' q) b))] at ih_eq
```

### 4. `step3` (línea ~596): `sub_k_add_k` necesita `Le ((n'*q)*b) (n'*a + gcd)`

```
h_le_mul has type Le ((n'*q)*b) (n'*a) but expected Le ((n'*q)*b) ((n'*a)+gcd b (a%b))
```

**Fix:** Derivar la hipótesis de Le más fuerte:

```lean4
have h_le_mul2 : Le (mul (mul n' q) b) (add (mul n' a) (gcd b (a % b))) :=
  le_trans (mul (mul n' q) b) (mul n' a) _ h_le_mul (le_self_add _ _)
```

(O usar `le_trans` con `le_self_add`.)

### 5. Error final `h_move` (línea ~604): PROBLEMA LÓGICO FUNDAMENTAL

```
h_move has type  (gcd b (a%b) + n'*a) = (m'+n'*q)*b
but expected     (gcd b (a%b) + n'*b) = (m'+n'*q)*a
```

**Análisis matemático:** En la rama `b ≤ a, a%b ≠ 0`:

- IH da: `G + n'*(a%b) = m'*b`  (G = gcd b (a%b))
- Goal: `∃ n m, G + n*b = m*a`
- El código actual deriva: `G + n'*a = (m'+n'*q)*b` ← forma WRONGLY ORIENTED
- Los testigos correctos dependen de si `q*n' ≥ m'` o no (ver más abajo)

---

## Análisis matemático del caso problemático (`b ≤ a, a%b ≠ 0`)

De `G + n'*(a%b) = m'*b` y `a = q*b + (a%b)`:

La versión entera de Bézout da: `G = n'*a + (m' - q*n')*b`

Hay dos subcasos:

- **Si `q*n' ≥ m'`:** `G + (q*n' - m')*b = n'*a` → testigos `n = q*n'-m'`, `m = n'`
- **Si `q*n' < m'`:** `G = n'*a + (m'-q*n')*b` → esto es tipo II (`G + n'*a_max = coef*b_min`... NO funciona para la forma requerida directamente)

**Solución propuesta:** Hacer `by_cases hcase : Le (mul q n') m'` dentro de esa rama:

```lean4
by_cases hcase : Le (mul q n') m'
· -- q*n' ≤ m': testigos n = m'-q*n', m = n' NO, espera: G + (q*n'-m')*b = n'*a
  -- Pero q*n' ≤ m' significa q*n'-m' = 0 en truncado...
  -- Necesita sub truncada: n = sub (mul q n') m' pero si q*n'<m' esto da 0
  -- Mejor: split on Le m' (mul q n') para tener q*n' ≥ m'
  ...
· -- q*n' > m': la ecuación entera requiere forma tipo II
  -- Pero `bezout_additive` SIEMPRE tiene solución tipo I por la naturaleza del mcd
  ...
```

**Alternativa más simple**: reescribir toda la rama `b ≤ a` para llamar IH también con argumento `a` usando `gcd_comm`:

```lean4
-- Aplicar gcd_comm para intercambiar roles
-- gcd b (a%b) = gcd a b [vía h_gcd_eq inversa]  
-- Luego usar los testigos que ya funcionan para la rama a≤b
```

**Alternativa aún más simple**: Si tenemos `gcd + n'*a = (m'+n'*q)*b` y min=b, max=a, podemos intentar:

- Testigos: `n = add m' (mul n' q)`, `m = n'` si `G + (m'+n'*q)*b = n'*a`
- Pero esto requiere `n'*a ≥ G + (m'+n'*q)*b` lo cual no es obvio

---

## Estado del archivo PeanoNatArith.lean (líneas clave)

**Ramas que COMPILAN (no tocar):**

- Líneas ~478-480: `b = 0` (con `h_gcd_a0` y `zero_mul`)
- Líneas ~506-510: `a < b` (usa `mod_of_lt` directamente)
- Líneas ~511-525: `a = b` (usa `rw [h_eq_ab]`, NO `subst`)
- Líneas ~540-556: `b ≤ a, a%b = 0` (testigos `sub q 𝟙, 𝟙`)

**Ramas con errores (NO tocar las que compilan ya):**

- Líneas ~558-610: `b ≤ a, a%b ≠ 0` ← TODA esta rama necesita revisión

---

## Teoremas disponibles que pueden ser útiles

De `PeanoNatOrder.lean`:

- `lt_0n_then_le_1n_wp {n} (h : Lt 𝟘 n) : Le 𝟙 n`
- `le_trans`, `le_self_add`, `le_refl`

De `PeanoNatMul.lean`:

- `mul_assoc (n m k) : mul (mul m n) k = mul m (mul n k)` ← **OJO**: primer arg es interior-derecho
- `mul_rdistr`, `mul_ldistr`, `mul_comm`, `mul_sub`, `mul_le_mono_right`

De `PeanoNatSub.lean`:

- `sub_k_add_k (n k : ℕ₀) : Le k n → add (sub n k) k = n`
- `add_k_sub_k (n k : ℕ₀) : sub (add k n) k = n`
- `add_sub_assoc (n m k : ℕ₀) (h : Le k n) : add (sub n k) m = sub (add n m) k`

---

## ADVERTENCIA: trampas conocidas

1. **`mul_assoc` tiene orden de parámetros NO estándar**: `mul_assoc (n m k) : (m*n)*k = m*(n*k)`. Para reescribir `(n'*q)*b → n'*(q*b)` se necesita `mul_assoc q n' b`.

2. **`set` no existe** (es de Mathlib). Usar `let q := a / b`.

3. **`let q` NO se puede usar con `subst`**. En la rama `a = b` usar `rw [h_eq_ab]` en lugar de `subst h_eq_ab`.

4. **`gcd` es WF-recursivo → NO es rfl-reducible**. No usar `unfold gcd` + `rfl`. En su lugar usar `unfold gcd; rw [if_pos/if_neg ...]`.

5. **`Le a b = Lt a b ∨ a = b`** (no `a ≤ b` en sentido Nat). `rcases h_le with h_lt | h_eq`.

6. **`mul_sub c a b h : mul c (sub a b) = sub (mul c a) (mul c b)`** necesita `Lt b a` (no `Le`).
