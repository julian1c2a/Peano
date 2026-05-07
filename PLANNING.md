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

- `hr_eq`: |G| = p^(m+1) · r
- `hC`: Teorema de Cauchy para cualquier grupo
- `h_no_proper`: ningún subgrupo propio tiene cardinal divisible por p^(m+1)

---

## Infraestructura existente relevante

### En `Sylow.lean`

| Símbolo | Línea ~ | Estado |
|---------|---------|--------|
| `pow_dvd_card` | ~600 | OK |
| `subgroupToFinGroup` | private | OK (mismo archivo) |
| `subgroupOfSubgroup` | private | OK (mismo archivo) |
| `cauchy_minimal` | ~1641 | OK |
| `wielandt_fixed_point_exists` | ~3000 | OK |
| `sylow_lift_from_cauchy` | ~3673 | OK (IH fuerte disponible) |

### En `QuotientGroup.lean`

```lean
noncomputable def quotientGroup (G : FinGroup ℕ₀) (H : Subgroup G)
    (hn : H.IsNormal) : FinGroup ℕ₀   -- devuelve FinGroup ℕ₀, no FinGroup ℕ₀FSet

theorem quotient_card (G : FinGroup ℕ₀) (H : Subgroup G) :
    (quotientCarrier G H).card = Peano.Div.div G.carrier.card H.carrier.card
```

Nota: el comentario obsoleto en Sylow.lean (~3580) que cita "FinGroup ℕ₀FSet"
como bloqueador es INCORRECTO. quotientGroup ya devuelve FinGroup ℕ₀.

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
-- Verificar: ¿existe preimage_subgroup_card aquí?
```

### En `WellFounded.lean`

```lean
def strongRecOn, theorem strongInductionOn  -- inducción fuerte sobre ℕ₀
```

---

## Gaps identificados

### Gap 1: `p_group_center_nontrivial` — FALTA

```lean
theorem p_group_center_nontrivial (G : FinGroup ℕ₀) (p m : ℕ₀)
    (hp : Prime p)
    (hpm : ∃ r, Mul.mul (pow p (σ m)) r = G.carrier.card) :
    p ∣ (center G).carrier.card
```

Argumento: ecuación de clases.
- |G| = |Z(G)| + Σ_{x no-central} [G : C_G(x)]
- Para x no-central: C_G(x) propio, p ∣ [G : C_G(x)] (G es p-grupo)
- p ∣ |G| y p ∣ suma → p ∣ |Z(G)|

Requiere: acción de conjugación, partición en clases, órbita-estabilizador para conjugación.
Ver wielandt_p_ndvd_r.md §L1 para sub-lemas.

### Gap 2: `preimage_subgroup_card` — verificar / FALTA

```lean
theorem preimage_subgroup_card (G : FinGroup ℕ₀) (H : Subgroup G) (hn : H.IsNormal)
    (M' : Subgroup (quotientGroup G H hn)) :
    (preimageSubgroup G H hn M').carrier.card =
      Mul.mul M'.carrier.card H.carrier.card
```

Verificar CorrespondenceTheorem.lean antes de reimplementar.

### Gap 3: Parámetro `HI` en `wielandt_p_ndvd_r`

El caso succ m' necesita la IH fuerte sobre |G|. Debe pasarse como parámetro.
Ver sección "Reformulación" en wielandt_p_ndvd_r.md.

---

## Ruta matemática — caso `succ m'`

Sea |G| = p^(m'+2) · r.

1. Gap 1 → p ∣ |center G|
2. hC sobre center G → Z_G : Subgroup G, |Z_G| = p, Z_G ⊆ center G
3. central_subgroup_isNormal → Z_G.IsNormal
4. G' := quotientGroup G Z_G → FinGroup ℕ₀, |G'| = p^(m'+1) · r
5. |G'| < |G| (pues |G| = p · |G'|, p ≥ 2)
6. Transferir h_no_proper a G' via Gap 2
7. HI(G') → ¬ p ∣ r

---

## Plan de implementación

### Fase A — En `NormalSubgroup.lean`

1. Acción de conjugación como GroupAction (verificar Action.lean primero)
2. Partición de G en clases de conjugación
3. |clase(x)| = [G : C_G(x)] via órbita-estabilizador
4. p_group_center_nontrivial

### Fase B — En `CorrespondenceTheorem.lean`

5. Leer el módulo completo
6. Si no existe: probar preimage_subgroup_card

### Fase C — En `Sylow.lean`

7. Añadir parámetro HI a wielandt_p_ndvd_r
8. Actualizar sylow_center_step_wielandt para pasar HI
9. Probar el caso succ m'

---

## Estimación

| Tarea | Dificultad | Líneas ~ |
|-------|------------|---------|
| Acción de conjugación + clases | Media | 60–100 |
| p_group_center_nontrivial | Media-alta | 40–70 |
| preimage_subgroup_card | Media | 30–50 |
| Caso succ m' en Sylow.lean | Alta | 60–100 |
| **Total** | | ~190–320 |

---

## Estado esperado tras Track 1

```
Sylow.lean: 0 sorry, 2 private axioms (sylow_third_mod, sylow_third_dvd)
Build: 64 jobs, 0 errores
```
