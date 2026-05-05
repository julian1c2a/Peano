# Plan de prueba: `wielandt_p_ndvd_r`

## Enunciado

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

**Contexto**: Este lema se usa dentro de `sylow_center_step_wielandt`, en el caso duro de la
inducción de Sylow donde `p^(m+1) ∣ |G|` pero ningún subgrupo propio de G es divisible
por `p^(m+1)`. El objetivo es probar `¬ p ∣ r` para que el argumento binomial de Wielandt
(`binom_pow_p_mod`) pueda concluir `p ∤ |Ω|`.

---

## Hipótesis disponibles

| Hipótesis | Tipo | Significado |
|-----------|------|-------------|
| `hp` | `Prime p` | p es primo; en particular `hp.1 : p ≠ 𝟘`, `one_lt_prime hp : lt₀ 𝟙 p` |
| `hr_eq` | `p^(σ m) * r = \|G\|` | descomposición del orden de G |
| `hC` | Teorema de Cauchy | si p₀ primo y p₀ ∣ \|G₀\|, ∃ subgrupo de orden p₀ |
| `h_no_proper` | ∀ M propio, `¬ pow_dvd_card p (σ m) M.carrier` | ningún subgrupo propio tiene p^(m+1) ∣ \|M\| |

**Definición recordatorio**:

```lean
def pow_dvd_card (p k : ℕ₀) (H : ℕ₀FSet) : Prop :=
  ∃ m : ℕ₀, Mul.mul (p ^ k) m = H.card
```

Es decir, `pow_dvd_card p (σ m) M.carrier ↔ ∃ t, p^(σ m) * t = |M|`.

---

## Análisis del caso m = 0 (prueba completa)

### Por qué funciona

Con m = 0: `p^(σ 0) = p^1 = p`. Las hipótesis se convierten en:

- `hr_eq : p * r = |G|`
- `h_no_proper : ∀ M propio, ¬ ∃ t, p * t = |M|`

**Paso 1**: Asumir `p ∣ r`, obteniendo `r' : ℕ₀` con `r = p * r'` (por `hr : p ∣ r`).

**Paso 2**: Reescribir para mostrar `p ∣ |G|`:

```
|G| = p * r = p * (p * r') = p * (p * r')
```

Testigo para `hC`: `t = p * r'`, usando `mul_comm` y `mul_assoc`.

**Paso 3**: Aplicar `hC G p hp ⟨p * r', h_div_G⟩` para obtener `K : Subgroup G` con `|K| = p`.

**Paso 4**: Demostrar que K es propio (`|K| ≠ |G|`), es decir `p ≠ p * r`:

- De `r = p * r'` y `p ≥ 2` (por `prime_ge_two hp`): `r ≥ p ≥ 2`, así `p * r ≥ p * 2 > p`.
- Concretamente: `mul_lt_left p r (hp.1) (one_lt_prime hp)` da `p < p * r = |G|`.
- Por tanto `|K| = p ≠ |G|`.

**Paso 5**: Aplicar `h_no_proper K hK_ne` para obtener `h_neg : ¬ pow_dvd_card p 1 K.carrier`,
es decir `¬ ∃ t, p^1 * t = p`.

**Paso 6**: Construir la contradicción mostrando que `pow_dvd_card p 1 K.carrier` SÍ se cumple:

```lean
have : pow_dvd_card p 1 K.carrier := ⟨𝟙, by rw [pow_one, mul_one]; exact hK_card⟩
exact h_neg this
```

Aquí `pow_one p : p^1 = p` y `mul_one p : p * 1 = p` dan `p^1 * 1 = p = |K|`. ✓

### Esqueleto Lean 4 para m = 0

```lean
intro ⟨r', hr'⟩
-- r = p * r', luego |G| = p * (p * r')
have hG_eq : Mul.mul p (Mul.mul p r') = G.carrier.card := by
  rw [← hr_eq, ← mul_assoc, mul_comm p p, mul_assoc]
  -- hr_eq : p^1 * r = |G|, r = p * r'
  rw [pow_one, hr']
-- Cauchy: ∃ K con |K| = p
obtain ⟨K, hK_card⟩ := hC G p hp ⟨Mul.mul p r', hG_eq⟩
-- K es propio: |K| = p < |G|
have hK_lt : lt₀ K.carrier.card G.carrier.card := by
  rw [hK_card, ← hr_eq, pow_one]
  exact mul_lt_left p r hp.1 (one_lt_prime hp)
have hK_ne : K.carrier.card ≠ G.carrier.card := ne_of_lt hK_lt
-- h_no_proper contradice pow_dvd_card p 1 K
have h_neg := h_no_proper K hK_ne
have h_pos : pow_dvd_card p (σ 𝟘) K.carrier :=
  ⟨𝟙, by simp [pow_one, mul_one, hK_card]⟩
exact h_neg h_pos
```

---

## Análisis del caso m ≥ 1 (brecha matemática)

### Por qué el mismo argumento falla

Con m = σ m' (m ≥ 1), el subgrupo K de orden p satisface:

```
pow_dvd_card p (σ(σ m')) K.carrier  ↔  ∃ t, p^(σ(σ m')) * t = p
```

Dado que `p^(σ(σ m')) ≥ p^2 = p*p ≥ 2p > p`:

- Para `t = 𝟘`: `p^(σ(σ m')) * 0 = 0 ≠ p` (pues `p ≥ 2 > 0`).
- Para `t = 𝟙`: `p^(σ(σ m')) * 1 = p^(σ(σ m')) > p`.
- Para `t ≥ 𝟙`: el producto crece y nunca iguala p.

Por tanto `pow_dvd_card p (σ m) K.carrier` es **falsa** para K de orden p con m ≥ 1.
`h_no_proper K hK_ne` es una implicación verdadera pero **no genera contradicción**.

### Argumento matemático estándar (lo que falta)

Para m ≥ 1 el argumento de Wielandt requiere encontrar un subgrupo propio M con
`|M| = p^(m+1)`, lo cual requiere la **hipótesis inductiva de Sylow** (no solo Cauchy):

> **IH Sylow**: Para todo `H` con `|H| < |G|` y `p^(m+1) ∣ |H|`, existe subgrupo de H
> de orden `p^(m+1)`.

Con esa IH, el argumento sería:

1. `p ∣ r` → `p^(m+2) ∣ |G|`
2. Por Cauchy: `K ≤ G` con `|K| = p` (propio, ya que `|G| ≥ p^2 > p`)
3. `|G/K| = |G|/p = p^(m+1) * r'` (requiere cociente o argumento de índices)
4. `p^(m+1) ∣ |G/K|` con `|G/K| < |G|`
5. IH Sylow → `∃ M/K` subgrupo de `G/K` con `|M/K| = p^(m+1)` (en realidad |M|=p^(m+2)... )

Este camino requiere grupos cociente y el teorema de correspondencia, que no están disponibles
en esta biblioteca.

### Alternativa: caso m = 0 es el único relevante aquí

Revisando dónde se llama `wielandt_p_ndvd_r`: dentro de `sylow_center_step_wielandt`,
que a su vez es invocado únicamente desde el caso `m` fijo de `sylow_lift_from_cauchy`.
La inducción sobre `|G|` en `sylow_lift_from_cauchy` maneja los casos m ≥ 1 mediante:

- Caso 2 (subgrupo propio M con `p^(m+1) ∣ |M|`): aplicar IH a M.
- Caso 3 (ningún M propio cumple lo anterior): llamar a `sylow_center_step_wielandt`.

En el Caso 3, si `|G| = p^(m+1) * r` y ningún propio tiene `p^(m+1) ∣ |M|`, entonces
**desde la propia estructura inductiva se puede deducir que `p ∤ r`** sin necesidad de
`wielandt_p_ndvd_r`, porque si `p ∣ r` habría un subgrupo de orden `p^(m+1)` en G
— pero ese subgrupo sería propio o impropio, y ambos casos dan contradicción con las
hipótesis del Caso 3. Sin embargo, ese argumento es exactamente lo que `wielandt_p_ndvd_r`
debe probar, cerrando el círculo.

---

## Estrategia práctica recomendada

### Opción A: Añadir la IH de Sylow como hipótesis adicional

Cambiar la firma del axioma para incluir:

```lean
(hSylow : ∀ (H : FinGroup ℕ₀), lt₀ H.carrier.card G.carrier.card →
  pow_dvd_card p (σ m) H.carrier →
    ∃ K : Subgroup H, K.carrier.card = p ^ (σ m))
```

Con esa hipótesis extra, la prueba por m usando Cauchy + subgrupo cociente puede cerrarse.
Habría que verificar que el sitio de llamada puede proveer esta IH (proviene de la
inducción fuerte de `sylow_lift_from_cauchy`).

### Opción B: Descomponer por casos sobre m en el axioma

```lean
cases m with
| zero  => -- prueba completa como en §3
| succ m' => -- aquí se necesita la IH de Sylow como hipótesis adicional
```

### Opción C: Verificar si el contexto ya excluye m ≥ 1

En el Caso 3 de `sylow_lift_from_cauchy`, para m ≥ 1, la combinación de
`h_eq : |G| ≠ p^(σ m)` y `¬ h_ex : ∀ M propio, ¬ p^(σ m) ∣ |M|` podría
ser suficiente para derivar directamente `p ∤ r` sin necesidad de Cauchy,
usando sólo aritmética de divisibilidad sobre `|G| = p^(σ m) * r`.

---

## Lemas clave disponibles

| Lema | Enunciado |
|------|-----------|
| `one_lt_prime hp` | `lt₀ 𝟙 p` |
| `prime_ge_two hp` | `le₀ 𝟚 p` |
| `pow_one p` | `p^𝟙 = p` |
| `pow_zero p` | `p^𝟘 = 𝟙` |
| `pow_succ p n` | `p^(σ n) = p^n * p` |
| `pow_ne_zero hp.1 k` | `p^k ≠ 𝟘` |
| `pow_ge_one h_p_gt_0` | `p^k ≥ 𝟙` |
| `pow_lt_succ_exp h_p_gt_1` | `p^k < p^(σ k)` |
| `mul_lt_left n m hn hm` | `n ≠ 𝟘 → lt₀ 𝟙 m → lt₀ n (n*m)` |
| `mul_comm n m` | `n*m = m*n` |
| `mul_assoc n m k` | `(n*m)*k = n*(m*k)` |
| `mul_one n` | `n*𝟙 = n` |
| `card_pos_of_mem_aux G.id_in` | `lt₀ 𝟘 \|G\|` |

---

## Conclusión

- **m = 0**: prueba directa factible con los lemas disponibles. Ver esqueleto en §3.
- **m ≥ 1**: requiere hipótesis adicional (IH de Sylow) o maquinaria de grupos cociente
  no disponible en la librería.
- **Acción recomendada**: añadir `hSylow` como parámetro extra a `wielandt_p_ndvd_r` y
  verificar que el sitio de llamada en `sylow_center_step_wielandt` puede suministrarlo
  a partir de la inducción fuerte de `sylow_lift_from_cauchy`.
