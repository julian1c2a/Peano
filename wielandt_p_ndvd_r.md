# Desguace: `wielandt_p_ndvd_r` — caso `succ m'`

*Autor: Julián Calderón Almendros*
*Última actualización: 2026-05-07*

---

## El teorema completo

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
- `h_no_proper`: ningún subgrupo propio de G tiene cardinal divisible por p^(m+1)

---

## Caso `zero` — ya demostrado

1. `hC` da K : Subgroup G con |K| = p
2. Si r > 1: |K| = p < |G| → K propio → contradice h_no_proper
3. Si r = 1: |G| = p, K = G (impropio), no hay contradicción vacua

---

## Caso `succ m'` — el sorry

```lean
| succ m' =>
  -- hr_eq : p^(m'+2) · r = |G|
  -- h_no_proper: ningún subgrupo propio tiene |·| divisible por p^(m'+2)
  -- Objetivo: ¬ p ∣ r
  sorry  -- TARGET
```

### Árbol de dependencias

```
¬ p ∣ r
└── [L8] HI aplicada a G' = G/Z_G
    ├── [L6] |G'| < |G|
    │    └── [L5] |G'| = p^(m'+1) · r  (quotient_card + aritmética)
    ├── [L7] h_no_proper' para G'
    │    └── preimage_subgroup_card    ← GAP 2
    └── G' := quotientGroup G Z_G
         ├── [L3] Z_G.IsNormal        (central_subgroup_isNormal) OK
         └── [L2] Z_G ⊆ center G, |Z_G| = p  (hC sobre center G)
              └── [L1] p ∣ |center G|  ← GAP 1 (p_group_center_nontrivial)
```

---

## Sub-lemas

### [L1] p_group_center_nontrivial — GAP 1

```lean
-- Para probar en NormalSubgroup.lean
theorem p_group_center_nontrivial (G : FinGroup ℕ₀) (p m : ℕ₀)
    (hp : Prime p)
    (hpm : ∃ r, Mul.mul (pow p (σ m)) r = G.carrier.card) :
    p ∣ (center G).carrier.card
```

**Estado**: NO EXISTE — hay que probar

Argumento (ecuación de clases):
- |G| = |Z(G)| + Σ_{x no-central} [G : C_G(x)]
- Para x no-central: C_G(x) propio, p ∣ [G : C_G(x)]
- p ∣ |G| y p ∣ suma no-central → p ∣ |Z(G)|

Sub-lemas necesarios:

```lean
-- L1a: acción de conjugación es GroupAction
-- L1b: órbitas de conjugación particionan G
-- L1c: |órbita(x)| = [G : C_G(x)]  (órbita-estabilizador)
-- L1d: |órbita(x)| = 1 ↔ x ∈ Z(G)
```

Verificar en Action.lean si orbit_stabilizer ya da lo necesario para L1c.

### [L2] Subgrupo central de orden p

```lean
-- Dado L1: p ∣ |center G|
-- hC da Z_cg : Subgroup (subgroupToFinGroup G (center G)) con |Z_cg| = p
-- Levantar a Z_G : Subgroup G vía subgroupOfSubgroup
-- Z_G.carrier.card = p, y Z_G ⊆ center G
```

**Estado**: factible — subgroupToFinGroup y subgroupOfSubgroup son privados en Sylow.lean

### [L3] Z_G es normal

```lean
have hZn : Z_G.IsNormal := central_subgroup_isNormal G Z_G hZ_G_central
```

**Estado**: OK — central_subgroup_isNormal existe en NormalSubgroup.lean

### [L4] G' = G/Z_G

```lean
let G' : FinGroup ℕ₀ := quotientGroup G Z_G hZn
```

**Estado**: OK — quotientGroup existe en QuotientGroup.lean, devuelve FinGroup ℕ₀.
El comentario obsoleto en Sylow.lean que cita "FinGroup ℕ₀FSet" es incorrecto.

### [L5] |G'| = p^(m'+1) · r

```lean
-- quotient_card: |G'| = |G| / |Z_G| = p^(m'+2)·r / p = p^(m'+1)·r
-- Necesita: pow_succ, mul_div_cancel_left (o equivalente)
```

**Estado**: factible con aritmética disponible

### [L6] |G'| < |G|

```lean
-- |G'| = p^(m'+1)·r, |G| = p^(m'+2)·r = p · |G'|
-- p ≥ 2 → |G'| < p·|G'| = |G|
```

**Estado**: factible con mul_lt_left o equivalente

### [L7] Transferir h_no_proper a G' — GAP 2

```lean
have h_no_proper' : ∀ M' : Subgroup G', M'.carrier.card ≠ G'.carrier.card →
    ¬ pow_dvd_card p (σ m') M'.carrier := by
  intro M' hM'_ne hM'_dvd
  let PIM := preimageSubgroup G Z_G hZn M'
  have hPIM_card : PIM.carrier.card = Mul.mul M'.carrier.card p :=
      preimage_subgroup_card G Z_G hZn M'  -- GAP 2
  -- p^(m'+1) ∣ |M'| → p^(m'+2) ∣ |M'|·p = |PIM|
  have hPIM_dvd : pow_dvd_card p (σ (succ m')) PIM.carrier := ...
  -- PIM es propio: |PIM| = |M'|·p < |G'|·p = |G|
  have hPIM_ne : PIM.carrier.card ≠ G.carrier.card := ...
  exact h_no_proper PIM hPIM_ne hPIM_dvd
```

**Estado**: requiere preimage_subgroup_card. Verificar CorrespondenceTheorem.lean primero.

### [L8] Hipótesis inductiva

```lean
exact HI G' hG'_lt m' r hG'_card h_no_proper'
```

**Estado**: requiere parámetro HI en la firma de wielandt_p_ndvd_r

---

## Reformulación con HI explícita

### Firma modificada propuesta

```lean
private theorem wielandt_p_ndvd_r
    (G : FinGroup ℕ₀) (p m r : ℕ₀)
    (hp : Prime p)
    (hr_eq : Mul.mul (p ^ (σ m)) r = G.carrier.card)
    (hC : ∀ (G0 : FinGroup ℕ₀) (p0 : ℕ₀), Prime p0 →
      (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
        ∃ K : Subgroup G0, K.carrier.card = p0)
    (HI : ∀ (G' : FinGroup ℕ₀), G'.carrier.card < G.carrier.card →
      ∀ (m' r' : ℕ₀),
      Mul.mul (p ^ (σ m')) r' = G'.carrier.card →
      (∀ M : Subgroup G', M.carrier.card ≠ G'.carrier.card →
        ¬ pow_dvd_card p (σ m') M.carrier) →
      ¬ p ∣ r')
    (h_no_proper : ∀ M : Subgroup G, M.carrier.card ≠ G.carrier.card →
      ¬ pow_dvd_card p (σ m) M.carrier) :
    ¬ p ∣ r
```

### Cambio en sylow_center_step_wielandt

```lean
-- Pasar HI construida desde la IH fuerte de sylow_lift_from_cauchy:
have hp_ndvd_r : ¬ p ∣ r :=
    wielandt_p_ndvd_r G p m r hp hr_eq hC
      (fun G' hlt m' r' hr' hnp' => ih_sylow G' hlt p m' r' hp hr' hC hnp')
      h_no_proper
```

La forma exacta de ih_sylow depende de la firma de sylow_lift_from_cauchy.
Leer líneas ~3673–3720 de Sylow.lean para conectar correctamente.

---

## Resumen — lo que falta

| # | Nombre | Archivo | Estado |
|---|--------|---------|--------|
| 1 | p_group_center_nontrivial (+ sub-lemas L1a–L1d) | NormalSubgroup.lean | FALTA |
| 2 | preimage_subgroup_card | CorrespondenceTheorem.lean | verificar / FALTA |
| 3 | Parámetro HI en wielandt_p_ndvd_r | Sylow.lean | pendiente |
| 4 | Caso succ m' completo | Sylow.lean | pendiente |

## Lo que ya existe

- quotientGroup → FinGroup ℕ₀ (QuotientGroup.lean) OK
- quotient_card OK
- center_isNormal, central_subgroup_isNormal (NormalSubgroup.lean) OK
- hC en contexto OK
- subgroupToFinGroup, subgroupOfSubgroup (private, Sylow.lean) OK
- preimageSubgroup (CorrespondenceTheorem.lean) OK
- strongRecOn / strongInductionOn (WellFounded.lean) OK

## Decisión de diseño

Opción A (recomendada): añadir HI como parámetro a wielandt_p_ndvd_r.
Opción B: mover el caso succ m' al cuerpo de sylow_lift_from_cauchy donde la IH ya vive.

Opción A es más modular. sylow_lift_from_cauchy ya construye su IH fuerte
con strongRecOn y puede pasarla directamente.
