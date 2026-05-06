# Next Steps — Eliminating the Remaining Private Axioms

*Last updated: 2026-05-06*
*Author: Julián Calderón Almendros*

---

## Current build state

`lake build` compila con **0 errores** y **1 sorry** en todo el proyecto (34 jobs).

Warnings activos (menores, no bloquean):

- `Sylow.lean:3207` — variable `hg_ne` sin usar (en `wielandt_orbit_partition`)
- `Sylow.lean:3307` — `wielandt_p_ndvd_r` usa `sorry`

`Sylow.lean` compila con **4 private axioms/sorries**:

| Axiom/sorry | Línea ~ | Usado por | Dificultad |
|---|---|---|---|
| `wielandt_fixed_point_exists` | ~2063 | `sylow_center_step_wielandt` | Difícil |
| `wielandt_p_ndvd_r` | ~3307 | `sylow_center_step_wielandt` | Media |
| `sylow_third_mod` | ~3464 | `sylow_third` | Muy difícil |
| `sylow_third_dvd` | ~3478 | `sylow_third` | Muy difícil |

**Completados en sesión 2026-05-06** (infraestructura Wielandt Pieza A):

- `wieldandtAct_gpow_add` — ✅ demostrado
- `wieldandtAct_gpow_fixed_of_gcd_one` — ✅ demostrado
- `wielandt_orbit_remove` — ✅ demostrado (6 propiedades de salida)
- `wielandt_orbit_partition` — ✅ **sorry eliminado** (|Ω| = |fix| + p·k)

**Eliminados** (histórico):

- `sylow_card_eq` — 2026-04-28
- `wielandt_omega_card` — 2026-04-28
- `sylow_second_incl` — ✅ **ELIMINADO** (reemplazado por `coset_conjugate_exists` en `CosetAction.lean`)

**Infrastructure disponible** (en `Binom.lean`):

- `prime_dvd_binom_prime` — `p ∣ C(p,k)` para `0 < k < p`
- `binom_prime_row` — `C(p·r, p) = r · C(p·r-1, p-1)`
- `binom_pr_p_mod` — `C(p·r, p) ≡ r (mod p)`
- `binom_pow_p_mod` — `C(p^n·r, p^n) ≡ r (mod p)` (Lucas)

---

## Módulos activos del proyecto

```
Peano/PeanoNat/
├── (aritmética base: Add, Sub, Mul, Div, Pow, Arith, Order, …)
├── NumberTheory/
│   ├── ModEq.lean           ✅ sin axiomas
│   ├── Fermat.lean          ✅ sin axiomas
│   ├── ChineseRemainder.lean ✅ sin axiomas
│   ├── Totient.lean         ✅ sin axiomas
│   └── Wilson.lean          ✅ sin axiomas  ← COMPLETADO 2026-05-05
├── Combinatorics/
│   ├── Binom.lean           ✅
│   ├── NewtonBinom.lean      ✅
│   ├── Perm.lean            ⚠ §3–§4 marcadas como "sorry" en comentarios
│   │                          (no son sorry reales — el código compila)
│   └── GroupTheory/
│       ├── Action.lean             ✅
│       ├── NormalSubgroup.lean     ✅ centralizer, normalizer, rightCoset, criterios
│       ├── QuotientGroup.lean      ✅ quotientGroup, quotientHomomorphism, imageSubgroup
│       ├── FirstIsomorphism.lean   ✅ homKer, homImg, firstIsoMap (inyectivo + sobreyectivo)
│       ├── SecondIsomorphism.lean  ✅ subgroupHN, interHN, secondIsoMap
│       ├── CorrespondenceTheorem.lean ✅ preimageSubgroup, SubgroupAbove, φ/ψ biyección  ← AÑADIDO 2026-05-05
│       └── Sylow/
│           ├── Cosets.lean       ✅
│           ├── CosetAction.lean  ✅ coset_conjugate_exists (cierra sylow_second_incl)
│           └── Sylow.lean        ⚠ 4 private axioms
└── Foundation/
    ├── CantorPairing.lean   ✅
    ├── GodelBeta.lean       ✅
    ├── Foundation.lean      ✅ (paraguas)
    ├── Initiality.lean      ✅
    ├── PeanoSystem.lean     ✅
    └── PureAxioms.lean      ✅ (6 axiomas de Peano — intencionales)
```

---

## Track 1 — `Wielandt.lean` (cierra `wielandt_p_ndvd_r` + `wielandt_fixed_point_exists`)

### Argumento matemático

Sea `|G| = p^(m+1) · r`. Define `Ω = { S ⊆ G.carrier.elems : |S| = p^(m+1) }`.

- `|Ω| = C(|G|, p^(m+1)) ≡ r (mod p)` por `binom_pow_p_mod` ✅
- `wielandt_p_ndvd_r`: p ∤ r — vía inducción fuerte sobre `|G|` (ver Paso 5 y 6).
- `wielandt_fixed_point_exists`: G actúa sobre Ω por traslación; p∤|Ω| →
  `mckay_orbit_count` da punto fijo → el estabilizador tiene orden `p^(m+1)`.

### Infraestructura ya disponible

- `sublistsOfLength` con propiedades `_mem_len`, `_mem_sub`, `_mem_sorted`,
  `_nodup_result`, `_complete`, `_card` ✅
- `wieldandtOmega (G : FinGroup ℕ₀) (N : ℕ₀) : List (List ℕ₀)` ✅
- `wielandt_omega_card` — `|Ω| = C(|G|, N)` ✅ (demostrado 2026-04-28)
- `binom_pow_p_mod` — `C(p^n·r, p^n) ≡ r (mod p)` ✅
- `mckay_orbit_count` ✅
- `cauchy_minimal` — `∃ K ≤ G, |K| = p` cuando `p ∣ |G|` ✅ (Sylow.lean:1641, 0 sorry)

### Infraestructura completada en sesión 2026-05-06 (Pieza A)

- `wieldandtAct_gpow_add` ✅ — g^(m+n)·S = g^m·(g^n·S)
- `wieldandtAct_gpow_fixed_of_gcd_one` ✅ — gcd(k,p)=1 + periodos ⟹ punto fijo
- `wielandt_orbit_remove` ✅ — extrae p-órbita de Ω con 6 propiedades
- `wielandt_orbit_partition` ✅ — |Ω| = |fix_g(Ω)| + p·k

### Plan de acción en 6 pasos (orden de implementación)

#### Paso 1 — Acción de G sobre Ω por traslación izquierda

Definir en `Sylow.lean` (junto a `wieldandtOmega`):

```lean
def wieldandtAct (G : FinGroup ℕ₀) (g : ℕ₀) (S : List ℕ₀) : List ℕ₀ :=
  (S.map (fun x => G.op g x)).mergeSort (· ≤ ·)
```

Demostrar:

- `wieldandtAct_mem_omega`: `S ∈ wieldandtOmega G N → wieldandtAct G g S ∈ wieldandtOmega G N`
  (preserva cardinalidad `N`, membresía en `G`, y orden — porque `G.op g` es biyección sobre `G.carrier`).
- `wieldandtAct_id`: `wieldandtAct G G.id S = S`
- `wieldandtAct_comp`: `wieldandtAct G g (wieldandtAct G h S) = wieldandtAct G (G.op g h) S`

#### Paso 2 — La acción es por permutaciones de Ω

Construir `wieldandtActPerm : FinGroup ℕ₀ → ℕ₀ → ℕ₀FSet → ℕ₀FSet` sobre el
`ℕ₀FSet` de índices de `wieldandtOmega` (índice `i : ℕ₀ < lengthₚ (wieldandtOmega G N)`).

Alternativamente, trabajar directamente sobre `List (List ℕ₀)` con la maquinaria
de `Action.lean` instanciada para `α = List ℕ₀` (elementos de `wieldandtOmega`).

Demostrar que la función `g ↦ wieldandtAct G g` es una acción de grupo en el sentido
de `Action.lean` (satisface `act_id` y `act_comp`).

#### Paso 3 — Puntos fijos

Un `S ∈ wieldandtOmega G N` es punto fijo si `∀ g ∈ G.carrier.elems, wieldandtAct G g S = S`.

Demostrar:

- `wieldandt_fixedPoint_is_subgroup`: si `S` es punto fijo entonces
  `S` es la carrier de un subgrupo de `G` de orden `N = p^(m+1)`.
  (Clave: S fijo ⟹ S cerrado bajo `G.op` y `G.inv` ⟹ subgrupo; `|S| = N` por definición de Ω.)
- `wieldandt_fixedPoint_exists_of_fix_nonempty`: si `fix ≠ ∅` entonces `∃ H : Subgroup G, H.carrier.card = N`.

#### Paso 4 — `wielandt_fixed_point_exists`

Con los pasos anteriores y `mckay_orbit_count`:

```lean
-- p ∤ |Ω| (por wielandt_p_ndvd_r, paso 6) ⟹ ∃ punto fijo ⟹ ∃ subgrupo de orden p^(m+1)
theorem wielandt_fixed_point_exists
    (G : FinGroup ℕ₀) (p m r : ℕ₀)
    (hp : Prime p) (hG : G.carrier.card = Mul.mul (pow p (succ m)) r)
    (hr : ¬ ∃ t, Mul.mul p t = r) :
    ∃ H : Subgroup G, H.carrier.card = pow p (succ m)
```

Prueba: `mckay_orbit_count` sobre la acción del Paso 2 da un índice fijo →
`wieldandt_fixedPoint_is_subgroup` da el subgrupo.

**Dependencia**: necesita `wielandt_p_ndvd_r` (Paso 6) para garantizar `p ∤ r`,
que implica `p ∤ |Ω|`.

#### Paso 5 — Modificar firma de `sylow_center_step_wielandt`

En `Sylow.lean`, cambiar la firma de `sylow_center_step_wielandt` para aceptar
la hipótesis inductiva `HI` como parámetro explícito, rompiendo la circularidad
con `sylow_first`:

```lean
-- Antes (circular):
private def sylow_center_step_wielandt
    (G : FinGroup ℕ₀) (p : ℕ₀) (hp : Prime p) ... : ...

-- Después (con HI explícito):
private def sylow_center_step_wielandt
    (G : FinGroup ℕ₀) (p : ℕ₀) (hp : Prime p)
    (HI : ∀ (G' : FinGroup ℕ₀) (r' : ℕ₀),
          lt₀ G'.carrier.card G.carrier.card →
          ¬ ∃ t, Mul.mul p t = r' →
          ∃ H' : Subgroup G', H'.carrier.card = p)
    ... : ...
```

Actualizar la llamada en `wielandt_p_ndvd_r` para pasar `HI` explícitamente.

#### Paso 6 — Reescribir `wielandt_p_ndvd_r` con inducción fuerte

Reemplazar el `private axiom wielandt_p_ndvd_r` por un `private theorem` usando
inducción fuerte sobre `G.carrier.card`:

```lean
private theorem wielandt_p_ndvd_r
    (G : FinGroup ℕ₀) (p m r : ℕ₀)
    (hp : Prime p) (hG : G.carrier.card = Mul.mul (pow p (succ m)) r) :
    ¬ ∃ t, Mul.mul p t = r := by
  -- Inducción fuerte sobre G.carrier.card
  induction h_card : G.carrier.card using Nat.strong_rec_on with
  | _ n ih => ...
  -- Caso m = 0: cauchy_minimal da K ≤ G con |K| = p,
  --   que es un subgrupo propio ⟹ contradicción con h_no_proper.
  -- Caso m ≥ 1: pasar ih como HI a sylow_center_step_wielandt
  --   (posible porque |G'| < |G| por hipótesis del paso inductivo).
```

**Caso m=0** (sin circularidad):

- `cauchy_minimal G p hp ⟨r, hG⟩` da `K : Subgroup G` con `K.carrier.card = p`.
- `K` es un subgrupo propio (su cardinal es `p < p·r = |G|` cuando `r ≥ 2`, o `|G|` es primo).
- Esto contradice `h_no_proper` en `sylow_center_step_wielandt`.

**Caso m≥1** (rompe la circularidad):

- El paso inductivo de Wielandt da un subgrupo `Z ≤ center(G)` de orden `p`.
- `G' = G/Z` satisface `|G'| = p^m · r < |G|`, luego `ih` aplicado a `G'` da `HI`.
- `sylow_center_step_wielandt G p hp HI ...` cierra el caso.

### Orden de ejecución dentro del Track 1

```
Paso 1  →  Paso 2  →  Paso 3  →  Paso 5  →  Paso 6  →  Paso 4
(act)      (perm)     (fix)      (firma)    (p∤r)      (∃ H)
```

(Paso 4 depende de Paso 6; Paso 6 depende de Paso 5; el resto es independiente.)

---

## Track 2 — `CosetAction.lean` ✅ COMPLETADO

`sylow_second_incl` ya no es un `private axiom`. `CosetAction.lean` exporta
`coset_conjugate_exists`, que `Sylow.lean` llama directamente en la prueba de
`sylow_second_incl` (ahora `private theorem`).

---

## Track 3 — `Conjugation.lean` (cierra `sylow_third_mod` + `sylow_third_dvd`)

### Esquema de prueba

**`sylow_third_mod`**: H (subgrupo de Sylow) actúa sobre `{subgrupos de Sylow}` por
conjugación. El único punto fijo es H. Por `mckay_orbit_count`, n_p ≡ 1 (mod p).

**`sylow_third_dvd`**: G actúa sobre `{subgrupos de Sylow}` por conjugación.
Por Sylow II (transitividad), acción transitiva: una sola órbita.
Por órbita-estabilizador, `n_p · |Stab_G(K)| = |G|`. Estabilizador = N_G(K) ⊇ K,
luego n_p ∣ |G|/|K|.

### Infraestructura necesaria

1. `normalizer (G : FinGroup ℕ₀) (K : Subgroup G) : ℕ₀FSet` — `N_G(K) = { g ∈ G | g⁻¹Kg = K }`.
2. `normalizer_is_subgroup`.
3. Codificación `List (Subgroup G) → ℕ₀FSet` via inyección de índices.
4. Acción de conjugación sobre `{subgrupos de Sylow}`.
5. Transitividad de la acción de conjugación (usa `sylow_second`).

### Bloqueador

`List (Subgroup G)` no es `ℕ₀FSet` — los elementos son `Subgroup G`, no `ℕ₀`.

**Camino corto** (sin Phase 5): inyectar cada `Subgroup G` en `sylows` a su índice
de lista (`ℕ₀`). Construir `ℕ₀FSet` de índices; mantener la biyección índice↔subgrupo
como lema auxiliar.

**Camino largo** (Phase 5): instanciar `FinGroup (Subgroup G)` — más limpio pero
requiere refactor completo de polimorfismo de FinGroup.

---

## Wilson's theorem — ✅ COMPLETADO (2026-05-05)

`Wilson.lean` compila con **0 errores** y **0 sorry**.

**Teorema central**:

```lean
theorem wilson {p : ℕ₀} (hp : Prime p) : p ∣ add (factorial (sub p 𝟙)) 𝟙
```

**Estrategia**: pairing argument sobre `{2, …, p−2}` — cada elemento se empareja con
su inverso modular, salvo puntos fijos (1 y p−1). Producto del rango interior ≡ 1 (mod p),
luego (p−1)! ≡ p−1 ≡ −1 (mod p).

---

## Warnings pendientes menores

Estos no bloquean ningún track pero conviene limpiarlos en algún momento:

| Archivo | Línea | Variable | Contexto |
|---------|-------|----------|---------|
| `PeanoNat.lean` | 28 | `n`, `m` | instancia de orden |
| `CosetAction.lean` | 292–294 | `h`, `r`, `h₁`, `h₂` | patrón en acción |
| `Sylow.lean` | 2027 | `hΩ_nd` | prueba Wielandt |

---

## Orden de ejecución

```
Wielandt.lean      ← siguiente prioridad (Track 1)
  └─ Conjugation.lean  ← después de Wielandt (Track 3)
```

Track 2 (`CosetAction.lean`) ya está completo.

---

## Phase F — Foundation: cadena Peano → Aczel → ZFC ✅ COMPLETADA (2026-05-02)

| Módulo | Estado |
|--------|--------|
| `CantorPairing.lean` | ✅ COMPLETADO (2026-05-02) |
| `GodelBeta.lean` | ✅ COMPLETADO (2026-05-02) |
| `Foundation.lean` (paraguas) | ✅ COMPLETADO (2026-05-02) |

Exporta `encodeList`/`decodeList`/`encode_decode` para que AczelSetTheory pueda
importar `Peano.PeanoNat.Foundation.GodelBeta` y fundamentar formalmente
`List ℕ₀ ≃ ℕ₀` sobre los axiomas de Peano, cerrando la cadena `PA → Aczel → ZFC`.

---

## Phase G — Documentación y cierre / Transición a AczelSetTheory

*Decisión adoptada 2026-05-02.*

### G.0 — Estado actual (2026-05-05)

| Ítem | Estado |
|------|---------|
| F.1 `CantorPairing.lean` | ✅ COMPLETADO (2026-05-02) |
| F.2 `GodelBeta.lean` | ✅ COMPLETADO (2026-05-02) |
| F.3 `Foundation.lean` paraguas | ✅ COMPLETADO (2026-05-02) |
| `Wilson.lean` | ✅ COMPLETADO (2026-05-05) |
| `NormalSubgroup.lean` | ✅ COMPLETADO |
| `QuotientGroup.lean` | ✅ COMPLETADO |
| `FirstIsomorphism.lean` | ✅ COMPLETADO |
| `SecondIsomorphism.lean` | ✅ COMPLETADO |
| `CorrespondenceTheorem.lean` | ✅ COMPLETADO (2026-05-05) |
| `CosetAction.lean` (Sylow II) | ✅ COMPLETADO |
| 4 axiomas privados Sylow | ❌ Pendiente (Tracks 1 y 3) |
| G.1 Migración documentación a `/doc/` | ❌ Pendiente |

### G.1 — Migración de documentación a `/doc/`

Puede hacerse en cualquier momento; no bloquea ni es bloqueada por los Tracks.

**Pasos**:

1. Crear `doc/` en la raíz del proyecto.
2. Crear `doc/INDEX.md` con tabla maestra de secciones.
3. Crear `doc/REFERENCE-{tema}.md` extrayendo secciones del `REFERENCE.md` actual:

   | Archivo destino | Secciones fuente |
   |-----------------|------------------|
   | `REFERENCE-Foundations.md` | §1–§5 |
   | `REFERENCE-Arithmetic.md` | §6–§15 |
   | `REFERENCE-NumberSets.md` | §16 |
   | `REFERENCE-NumberTheory.md` | §17–§25 |
   | `REFERENCE-Combinatorics.md` | §26–§38 |
   | `REFERENCE-GroupTheory.md` | §39–§44 |
   | `REFERENCE-Foundation.md` | §45+ |

4. Añadir header de navegación a cada archivo.
5. Reemplazar `REFERENCE.md` raíz por redirect/índice de una página.
6. Actualizar referencias en `README.md`, `CURRENT-STATUS-PROJECT.md`, `AI-GUIDE.md`.

### G.2 — Criterio de feature-freeze de Peano

Peano se declara **feature-frozen** cuando:

- [x] F.1 `CantorPairing.lean` ✅ (2026-05-02)
- [x] F.2 `GodelBeta.lean` sin sorry ✅ (2026-05-02)
- [x] F.3 `Foundation.lean` paraguas compilando ✅ (2026-05-02)
- [ ] G.1 Documentación migrada a `/doc/`

A partir del feature-freeze:

- Solo se aceptan: corrección de errores, actualización de `lean-toolchain`,
  mejoras de build, lemas menores solicitados por AczelSetTheory.
- No se desarrollan nuevos módulos matemáticos en Peano.

### G.3 — Handoff a AczelSetTheory

Una vez feature-frozen Peano:

1. Añadir dependencia en `AczelSetTheory/lakefile.lean`:

   ```lean
   require Peano from git
     "https://github.com/julian1c2a/Peano" @ "<sha-de-Foundation-sin-sorry>"
   ```

2. Crear en AczelSetTheory:

   ```
   AczelSetTheory/Foundation/
   └── ListFromPeano.lean   ← import + prueba List ℕ₀ ≃ ℕ₀ vía encode_decode
   ```

3. Todo el desarrollo matemático nuevo ocurre en AczelSetTheory (conjuntos
   hereditariamente finitos, relaciones de pertenencia, axiomas de Aczel,
   isomorfismo con ω de ZFC).

---

## FinGroup polymorphism — Phase 5 (largo plazo)

Current `FinGroup` requiere carrier ⊆ `ℕ₀`. Bloquea:

- Grupos cociente G/N (elementos son cosets, no `ℕ₀`)
- `FinGroup (Subgroup G)` para la acción de conjugación (Sylow III)

**Precondición**: completar Tracks 1 y 3 primero.
Después de que Sylow III esté cerrado, revisar la generalización de FinGroup.
