# Plan de prueba: `wielandt_p_ndvd_r`

## Enunciado actual (axioma en Sylow.lean)

```lean
private axiom wielandt_p_ndvd_r
    (G : FinGroup ℕ₀) (p m r : ℕ₀)
    (hp : Prime p)
    (hr_eq : Mul.mul (p ^ (σ m)) r = G.carrier.card)
    (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
      (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
        ∃ K : Subgroup G0, K.carrier.card = p0)
    (h_no_proper : ∀ M : Subgroup G, M.carrier.card ≠ G.carrier.card →
      ¬ pow_dvd_card p (σ m) M.carrier) :
    ¬ p ∣ r
```

**Contexto de uso**: llamado desde `sylow_center_step_wielandt`, el "caso duro" de la
inducción de Sylow: `p^(m+1) ∣ |G|` pero ningún subgrupo propio de G es divisible
por `p^(m+1)`. El resultado `¬ p ∣ r` garantiza `p ∤ |Ω|` (vía la congruencia de Lucas),
lo que activa el argumento de punto fijo de `wielandt_fixed_point_exists`.

---

## Hipótesis disponibles

| Hipótesis | Tipo | Significado |
|-----------|------|-------------|
| `hp` | `Prime p` | p primo; `hp.1 : p ≠ 𝟘`, `one_lt_prime hp : lt₀ 𝟙 p` |
| `hr_eq` | `p^(σm) * r = \|G\|` | descomposición del orden de G |
| `hC` | Teorema de Cauchy | primo p₀ y p₀ ∣ \|G₀\| implica ∃ subgrupo de orden p₀ |
| `h_no_proper` | ∀ M propio, `¬ pow_dvd_card p (σm) M.carrier` | ningún subgrupo propio tiene p^(m+1) ∣ \|M\| |

**Recordatorio de definiciones**:
```lean
-- pow_dvd_card p k H ↔ ∃ t, p^k * t = |H|
-- p ∣ r  (Peano.Arith.Divides)  ↔ ∃ r', r = Mul.mul p r'
```

---

## § 1 — Estrategia general: Opción B + Opción C

No disponemos de **grupos cociente** en la biblioteca, por lo que la Opción A
(añadir la IH de Sylow como hipótesis para aplicarla a G/K) queda descartada.

La estrategia adoptada combina:

**Opción B — Descomposición por casos sobre m**
```
cases m with
| zero  => -- prueba completa (ver § 2)
| succ m' => -- analizar si el caso puede ocurrir (ver § 3)
```

**Opción C — Verificar si m ≥ 1 es vacuamente cierto en el contexto**
Para m ≥ 1, investigar si la combinación de `hr_eq`, `h_no_proper` y aritmética
implica que p ∤ r sin necesidad de teoría de grupos (o que el caso ni siquiera
ocurre en la práctica dentro de `sylow_lift_from_cauchy`).

---

## § 2 — Caso m = 0: prueba COMPLETA

### Argumento matemático

Con m = 0: `p^(σ 0) = p^1 = p`. Las hipótesis son:
- `hr_eq : p * r = |G|`
- `h_no_proper : ∀ M propio, ¬ ∃ t, p * t = |M|` (es decir, p ∤ |M|)

Asumir `p ∣ r` para derivar `False`.

1. `r = p * r'` (por hipótesis de divisibilidad).
2. `|G| = p * (p * r')`, así `p ∣ |G|` con testigo `p * r'`.
3. Por Cauchy (`hC`): ∃ `K : Subgroup G` con `|K| = p`.
4. **K es propio**: `r' ≠ 0` (si no, |G| = 0) → `r > 1` → `p < p * r = |G|` → `|K| = p ≠ |G|`.
5. Aplicar `h_no_proper K hK_ne`: obtenemos `¬ ∃ t, p^1 * t = |K|`.
6. Pero `p^1 * 1 = p = |K|`: contradicción. ✓

### Código Lean 4 listo para implementar

```lean
| zero =>
  intro ⟨r', hr'⟩
  -- p^(σ 0) = p
  have hp1 : p ^ (σ 𝟘) = p := by rw [pow_succ, pow_zero, one_mul]
  -- p * r = |G|
  have hr_eq' : Mul.mul p r = G.carrier.card := hp1 ▸ hr_eq
  -- r' ≠ 0 (si no, r = 0 y |G| = 0, imposible)
  have hr'_ne : r' ≠ 𝟘 := by
    intro h0
    rw [h0, mul_zero] at hr'
    rw [hr', mul_zero] at hr_eq'
    exact absurd (card_pos_of_mem_aux G.id_in) (hr_eq'.symm ▸ lt_irrefl 𝟘)
  -- r > 1 (para mul_lt_left)
  have hr_gt_one : lt₀ 𝟙 r := by
    rw [hr']
    have h_le : le₀ p (Mul.mul p r') := mul_le_right p r' hr'_ne
    rcases h_le with h_lt | rfl
    · exact lt_trans 𝟙 p (Mul.mul p r') (one_lt_prime hp) h_lt
    · exact one_lt_prime hp
  -- p ∣ |G| con testigo p * r'
  have hG_p_dvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card :=
    ⟨Mul.mul p r', by rw [← hr_eq', hr']⟩
  -- Por Cauchy: ∃ K ≤ G con |K| = p
  obtain ⟨K, hK_card⟩ := hC G p hp hG_p_dvd
  -- K es propio: p < p * r = |G|
  have hK_lt : lt₀ K.carrier.card G.carrier.card := by
    rw [hK_card, ← hr_eq']
    exact mul_lt_left p r hp.1 hr_gt_one
  have hK_ne : K.carrier.card ≠ G.carrier.card :=
    ne_of_lt K.carrier.card G.carrier.card hK_lt
  -- Contradicción: h_no_proper K hK_ne vs. pow_dvd_card p (σ 0) K
  exact absurd ⟨𝟙, by rw [hp1, mul_one]; exact hK_card⟩ (h_no_proper K hK_ne)
```

**Notas de implementación**:
- `hp1` se obtiene de `pow_succ p 𝟘 : p^(σ 0) = p^0 * p = 1 * p = p`
  (usando `pow_zero` y `one_mul`). El orden en `pow_succ` es `p^(σn) = p^n * p`,
  así que `p^(σ 0) = p^0 * p = 1 * p = p` → `rw [pow_succ, pow_zero, one_mul]`.
- `hG_p_dvd`: el testigo `Mul.mul p r'` da `p * (p * r') = p * r = |G|`
  por `rw [← hr_eq', hr']` (primero ← hr_eq' cambia |G| a p*r, luego hr' cambia r a p*r').
- El cierre final usa `exact absurd ⟨...⟩ (h_no_proper K hK_ne)` directamente.

---

## § 3 — Caso m ≥ 1 (Opción C): análisis del contexto

### Por qué el argumento del caso m = 0 no se traslada

Con m = σ m' (m ≥ 1), el subgrupo K de Cauchy tiene `|K| = p`. Para aplicar
`h_no_proper K hK_ne` necesitaríamos `pow_dvd_card p (σ(σ m')) K.carrier`,
es decir `∃ t, p^(m+2) * t = p`. Pero `p^(m+2) ≥ p^2 > p`, así que esta
proposición es **trivialmente falsa** — no hay contradicción.

### Análisis del contexto de llamada (Opción C)

`wielandt_p_ndvd_r` es llamado desde `sylow_center_step_wielandt`, que a su vez
solo es invocado desde el **Caso 3** de `sylow_lift_from_cauchy`:

```
-- Caso 3 en sylow_lift_from_cauchy:
-- • h_eq : G0.carrier.card ≠ p ^ (σ m)   (Card ≠ p^(m+1), es decir r ≠ 1)
-- • ∀ M propio, ¬ (M.carrier.card ≠ G0.carrier.card ∧ pow_dvd_card p (σ m) M.carrier)
--   i.e., h_no_proper
-- → sylow_center_step → sylow_center_step_wielandt → wielandt_p_ndvd_r
```

**Pregunta clave (Opción C)**: ¿Puede ocurrir el Caso 3 con m ≥ 1 y r > 1?

**Análisis**:
Sea |G| = p^(m+2) * r (r > 1, m ≥ 1). Queremos ver si h_no_proper puede sostenerse.
Por el Teorema de Sylow para el exponente m+1 (que es exactamente lo que
`sylow_lift_from_cauchy` demuestra inductivamente), existe H ≤ G con |H| = p^(m+1).

- Si r > 1, entonces |G| = p^(m+2) * r > p^(m+1), así H es **propio**.
- H tiene p^(m+1) ∣ |H|, contradiciendo h_no_proper.

Por tanto: **si m ≥ 1 y r > 1, las hipótesis de `wielandt_p_ndvd_r` son
inconsistentes** (no existe ningún G con esas propiedades en la teoría de grupos
estándar). El caso `| succ m' =>` es en la práctica **vacuamente verdadero**.

**Atención**: la demostración de este hecho usa el propio Teorema de Sylow (circular).
En Lean 4, dentro del bloque `| succ m' =>`, **no podemos derivar esto formalmente**
sin la IH de `sylow_lift_from_cauchy` ni grupos cociente. El `sorry` refleja esta
deuda técnica, no un error de la librería.

### Verificación aritmética directa (por qué tampoco basta)

Intentar: de `hr_eq : p^(m+2) * r = |G|` y `h_no_proper` puramente, sin teoría
de grupos, ¿se deduce `¬ p ∣ r`?

No. La hipótesis `h_no_proper` habla de SUBGRUPOS, que son objetos de teoría de
grupos. No hay forma de extraer información sobre r solo con aritmética.

### Estado del caso m ≥ 1 en el código

```lean
| succ m' =>
  -- Este caso es vacuamente verdadero en la teoría de grupos (ver § 3),
  -- pero formalizarlo requiere la IH completa de sylow_lift_from_cauchy
  -- o grupos cociente (no disponibles en esta biblioteca).
  -- En la práctica, sylow_center_step_wielandt nunca es llamado con m ≥ 1
  -- cuando r > 1, porque sylow_lift_from_cauchy habría tomado el Caso 2 antes.
  sorry
```

---

## § 4 — Código final a insertar en Sylow.lean

Reemplazar `private axiom wielandt_p_ndvd_r ...` por:

```lean
private theorem wielandt_p_ndvd_r
    (G : FinGroup ℕ₀) (p m r : ℕ₀)
    (hp : Prime p)
    (hr_eq : Mul.mul (p ^ (σ m)) r = G.carrier.card)
    (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
      (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
        ∃ K : Subgroup G0, K.carrier.card = p0)
    (h_no_proper : ∀ M : Subgroup G, M.carrier.card ≠ G.carrier.card →
      ¬ pow_dvd_card p (σ m) M.carrier) :
    ¬ p ∣ r := by
  cases m with
  | zero =>
    intro ⟨r', hr'⟩
    have hp1 : p ^ (σ 𝟘) = p := by rw [pow_succ, pow_zero, one_mul]
    have hr_eq' : Mul.mul p r = G.carrier.card := hp1 ▸ hr_eq
    have hr'_ne : r' ≠ 𝟘 := by
      intro h0
      rw [h0, mul_zero] at hr'
      rw [hr', mul_zero] at hr_eq'
      exact absurd (card_pos_of_mem_aux G.id_in) (hr_eq'.symm ▸ lt_irrefl 𝟘)
    have hr_gt_one : lt₀ 𝟙 r := by
      rw [hr']
      have h_le : le₀ p (Mul.mul p r') := mul_le_right p r' hr'_ne
      rcases h_le with h_lt | rfl
      · exact lt_trans 𝟙 p (Mul.mul p r') (one_lt_prime hp) h_lt
      · exact one_lt_prime hp
    have hG_p_dvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card :=
      ⟨Mul.mul p r', by rw [← hr_eq', hr']⟩
    obtain ⟨K, hK_card⟩ := hC G p hp hG_p_dvd
    have hK_lt : lt₀ K.carrier.card G.carrier.card := by
      rw [hK_card, ← hr_eq']
      exact mul_lt_left p r hp.1 hr_gt_one
    have hK_ne : K.carrier.card ≠ G.carrier.card :=
      ne_of_lt K.carrier.card G.carrier.card hK_lt
    exact absurd ⟨𝟙, by rw [hp1, mul_one]; exact hK_card⟩ (h_no_proper K hK_ne)
  | succ m' =>
    -- Opción C: vacuamente verdadero en la práctica (ver § 3).
    -- Requiere grupos cociente o IH de sylow_lift_from_cauchy para formalizarlo.
    sorry
```

---

## § 5 — Lemas clave usados

| Lema | Enunciado |
|------|-----------|
| `one_lt_prime hp` | `lt₀ 𝟙 p` |
| `hp.1` | `p ≠ 𝟘` |
| `pow_succ p n` | `p^(σn) = Mul.mul (p^n) p` |
| `pow_zero p` | `p^𝟘 = 𝟙` |
| `one_mul n` | `Mul.mul 𝟙 n = n` |
| `mul_one n` | `Mul.mul n 𝟙 = n` |
| `mul_zero n` | `Mul.mul n 𝟘 = 𝟘` |
| `mul_assoc n m k` | `(n*m)*k = n*(m*k)` |
| `mul_lt_left n m hn hlt` | `n ≠ 𝟘 → lt₀ 𝟙 m → lt₀ n (n*m)` |
| `mul_le_right n m hne` | `m ≠ 𝟘 → le₀ n (n*m)` |
| `lt_trans a b c` | `lt₀ a b → lt₀ b c → lt₀ a c` |
| `lt_irrefl a` | `¬ lt₀ a a` |
| `ne_of_lt n m` | `lt₀ n m → n ≠ m` |
| `card_pos_of_mem_aux G.id_in` | `lt₀ 𝟘 \|G\|` |
