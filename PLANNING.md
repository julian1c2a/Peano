# PLANNING — Track 1: `wielandt_p_ndvd_r` caso `succ m'`

*Autor: Julián Calderón Almendros*
*Última actualización: 2026-05-07*

---

## Objetivo

Eliminar el `sorry` en el caso `succ m'` de `wielandt_p_ndvd_r` en
`Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean` (~línea 3538).

Una vez resuelto, `Sylow.lean` tendrá **0 sorry + 2 private axioms** restantes
(`sylow_third_mod`, `sylow_third_dvd`).

---

## Firma del teorema objetivo

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
    ¬ p ∣ r
```

**Contexto**: `hC` es la hipótesis de Cauchy disponible desde `sylow_center_step_wielandt`.
**Hipótesis**: G tiene orden `p^(m+1) · r`; ningún subgrupo propio tiene orden divisible por `p^(m+1)`.
**Conclusión**: `p ∤ r`.

---

## Infraestructura existente relevante

### En `Sylow.lean`

| Símbolo | Línea ~ | Descripción |
|---------|---------|-------------|
| `pow_dvd_card` | ~600 | `pow_dvd_card p k S ↔ p^k ∣ S.card` |
| `subgroupToFinGroup` | private | Convierte `Subgroup G` en `FinGroup ℕ₀` |
| `subgroupOfSubgroup` | private | Sube subgrupos a través de un subgrupo |
| `cauchy_minimal` | ~1641 | `p ∣ |G| → ∃ K ≤ G, |K| = p` |
| `wielandt_fixed_point_exists` | ~3000 | Punto fijo de acción de G sobre Ω ✅ |
| `sylow_lift_from_cauchy` | ~3673 | Inducción fuerte sobre |G|; llama a `wielandt_p_ndvd_r` |

### En `QuotientGroup.lean`

```lean
noncomputable def quotientGroup (G : FinGroup ℕ₀) (H : Subgroup G)
    (hn : H.IsNormal) : FinGroup ℕ₀

theorem quotient_card (G : FinGroup ℕ₀) (H : Subgroup G) :
    (quotientCarrier G H).card = Peano.Div.div G.carrier.card H.carrier.card
```

**Importante**: `quotientGroup` devuelve `FinGroup ℕ₀`. El comentario obsoleto
en Sylow.lean (~línea 3580) que dice "G/K es FinGroup ℕ₀FSet" es INCORRECTO.

### En `NormalSubgroup.lean`

```lean
def center (G : FinGroup ℕ₀) : Subgroup G
theorem center_isNormal (G : FinGroup ℕ₀) : (center G).IsNormal
theorem central_subgroup_isNormal (G : FinGroup ℕ₀) (H : Subgroup G)
    (hH : ∀ h, h ∈ H.carrier.elems → h ∈ (center G).carrier.elems) : H.IsNormal
```

### En `CorrespondenceTheorem.lean`

```lean
def preimageSubgroup (G : FinGroup ℕ₀) (H : Subgroup G) (hn : H.IsNormal)
    (M' : Subgroup (quotientGroup G H hn)) : Subgroup G
```

**Verificar**: si tiene lemas de cardinalidad de preimagen (`preimage_subgroup_card`).

### En `WellFounded.lean`

```lean
def strongRecOn : ∀ {P : ℕ₀ → Sort u}, (n : ℕ₀) →
    (∀ m, (∀ k, lt₀ k m → P k) → P m) → P n
theorem strongInductionOn : ∀ {P : ℕ₀ → Prop}, (n : ℕ₀) →
    (∀ m, (∀ k, lt₀ k m → P k) → P m) → P n
```

---

## Gaps identificados — infraestructura faltante

### Gap 1: `p_group_center_nontrivial` ❌ FALTA

**Enunciado necesario**:

```lean
theorem p_group_center_nontrivial (G : FinGroup ℕ₀) (p m : ℕ₀)
    (hp : Prime p)
    (hpm : ∃ r, Mul.mul (pow p (σ m)) r = G.carrier.card) :
    p ∣ (center G).carrier.card
```

**Argumento**: ecuación de clases.

- `|G| = |Z(G)| + Σ_{x ∉ Z(G)} [G : C_G(x)]`
- Para x ∉ Z(G): `C_G(x)` es propio, `p ∣ [G : C_G(x)]`
- `p ∣ |G|` y `p ∣ Σ_{no-central}` ⟹ `p ∣ |Z(G)|`

**Dificultad**: alta. Requiere la acción de conjugación, la partición en clases,
y la aplicación de órbita-estabilizador. Ver `wielandt_p_ndvd_r.md` §L1.

### Gap 2: `preimage_subgroup_card` ❌ o 🔶

**Enunciado necesario**:

```lean
theorem preimage_subgroup_card (G : FinGroup ℕ₀) (H : Subgroup G) (hn : H.IsNormal)
    (M' : Subgroup (quotientGroup G H hn)) :
    (preimageSubgroup G H hn M').carrier.card =
      Mul.mul M'.carrier.card H.carrier.card
```

**Estado**: verificar en `CorrespondenceTheorem.lean` antes de reimplementar.

### Gap 3: Parámetro `HI` en `wielandt_p_ndvd_r`

El caso `succ m'` necesita la hipótesis inductiva fuerte sobre |G|.
La IH vive en `sylow_lift_from_cauchy` y debe pasarse a `wielandt_p_ndvd_r`.
Ver sección "Reformulación con HI explícita" en `wielandt_p_ndvd_r.md`.

---

## Ruta matemática para el caso `succ m'`

Sea `|G| = p^(m'+2) · r` (m = succ m').

1. **`p_group_center_nontrivial`** → `p ∣ |center G|`
2. **`hC` sobre `center G`** → `Z_G : Subgroup G` central, `|Z_G| = p`
3. **`central_subgroup_isNormal`** → `Z_G.IsNormal`
4. **`G' := quotientGroup G Z_G`** → `G' : FinGroup ℕ₀`, `|G'| = p^(m'+1) · r`
5. **`|G'| < |G|`** → `G'.carrier.card < G.carrier.card`
6. **Transferir `h_no_proper` a G'** via `preimage_subgroup_card` (Gap 2)
7. **Aplicar IH (HI)** a G' → `¬ p ∣ r`

El paso 7 usa que r es el mismo para G y G' (divisor libre de p por IH en G').

---

## Plan de implementación

### Fase A — Lemas de conjugación (en `NormalSubgroup.lean`)

1. `conj_action_is_group_action` — acción de G sobre G por conjugación
2. `conj_classes_partition` — las clases particionan G
3. `conj_class_card_eq_index` — |clase(x)| = [G : C_G(x)] (órbita-estabilizador)
4. `p_group_center_nontrivial` — consecuencia de la ecuación de clases

### Fase B — Cardinal de preimagen (en `CorrespondenceTheorem.lean`)

1. Leer `CorrespondenceTheorem.lean` completo
2. Si no existe: probar `preimage_subgroup_card`

### Fase C — Modificación de `wielandt_p_ndvd_r` (en `Sylow.lean`)

1. Añadir parámetro `HI` a la firma
2. Actualizar `sylow_center_step_wielandt` para pasar `HI`
3. Probar el caso `succ m'`

---

## Estimación

| Tarea | Dificultad | Líneas ~|
|-------|------------|--------|
| Acción de conjugación + clases | Media | 60–100 |
| `p_group_center_nontrivial` | Media-alta | 40–70 |
| `preimage_subgroup_card` | Media | 30–50 |
| Caso `succ m'` en Sylow.lean | Alta | 60–100 |
| **Total** | | **~190–320** |

---

## Estado después de completar Track 1

```
Sylow.lean: 0 sorry, 2 private axioms (sylow_third_mod, sylow_third_dvd)
Build: 64 jobs, 0 errores
```
