# Next Steps — Eliminating the Remaining Private Axioms

*Last updated: 2026-05-07*
*Author: Julián Calderón Almendros*

---

## Current build state

`lake build` compila con **0 errores** y **1 sorry** en todo el proyecto (34 jobs).

Warnings activos (menores, no bloquean):

- `Sylow.lean:3044` — variable `htrans` sin usar (en `wielandt_fixed_point_exists`)
- `Sylow.lean:3438` — variable `hg_ne` sin usar (en `wielandt_orbit_stab`)
- `Sylow.lean:3538` — declaración `wielandt_p_ndvd_r` usa `sorry` (caso `succ m'`)

`Sylow.lean` compila con **1 sorry + 2 private axioms**:

| Axiom/sorry | Línea ~ | Usado por | Dificultad |
|---|---|---|---|
| `wielandt_p_ndvd_r` (caso `succ m'`) | ~3586 | `sylow_center_step_wielandt` | Difícil |
| `sylow_third_mod` | ~3875 | `sylow_third` | Muy difícil |
| `sylow_third_dvd` | ~3889 | `sylow_third` | Muy difícil |

**Completados en sesión 2026-05-07**:

- `wielandt_fixed_point_exists` — ✅ **sorry/axiom eliminado** (demostrado como teorema completo)

**Completados en sesión 2026-05-06** (infraestructura Wielandt Pieza A):

- `wieldandtAct_gpow_add` — ✅ demostrado
- `wieldandtAct_gpow_fixed_of_gcd_one` — ✅ demostrado
- `wielandt_orbit_remove` — ✅ demostrado (6 propiedades de salida)
- `wielandt_orbit_partition` — ✅ **sorry eliminado** (|Ω| = |fix| + p·k)

**Eliminados** (histórico):

- `sylow_card_eq` — 2026-04-28
- `wielandt_omega_card` — 2026-04-28
- `sylow_second_incl` — ✅ **ELIMINADO** (reemplazado por `coset_conjugate_exists` en `CosetAction.lean`)
- `wielandt_fixed_point_exists` — ✅ **ELIMINADO** 2026-05-07

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
│           └── Sylow.lean        ⚠ 1 sorry + 2 private axioms
└── Foundation/
    ├── CantorPairing.lean   ✅
    ├── GodelBeta.lean       ✅
    ├── Foundation.lean      ✅ (paraguas)
    ├── Initiality.lean      ✅
    ├── PeanoSystem.lean     ✅
    └── PureAxioms.lean      ✅ (6 axiomas de Peano — intencionales)
```

---

## Track 1 — `Sylow.lean` (cierra `wielandt_p_ndvd_r` caso `succ m'`)

### Estado actual (2026-05-07)

`wielandt_fixed_point_exists` está **completamente demostrado** como `private theorem`
(0 sorry, 0 axiom privado). El único pendiente del Track 1 es el caso `succ m'` del
teorema `wielandt_p_ndvd_r`.

### Argumento matemático

Sea `|G| = p^(m+1) · r`. Define `Ω = { S ⊆ G.carrier.elems : |S| = p^(m+1) }`.

- `|Ω| = C(|G|, p^(m+1)) ≡ r (mod p)` por `binom_pow_p_mod` ✅
- `wielandt_p_ndvd_r`: p ∤ r — vía inducción fuerte sobre `|G|`.
- `wielandt_fixed_point_exists`: G actúa sobre Ω por traslación; p∤|Ω| →
  `wielandt_exists_nondvd_orbit_aux` da punto fijo → el estabilizador tiene orden `p^(m+1)`. ✅

### Infraestructura ya disponible

- `sublistsOfLength` con propiedades `_mem_len`, `_mem_sub`, `_mem_sorted`,
  `_nodup_result`, `_complete`, `_card` ✅
- `wieldandtOmega (G : FinGroup ℕ₀) (N : ℕ₀) : List (List ℕ₀)` ✅
- `wielandt_omega_card` — `|Ω| = C(|G|, N)` ✅ (demostrado 2026-04-28)
- `binom_pow_p_mod` — `C(p^n·r, p^n) ≡ r (mod p)` ✅
- `mckay_orbit_count` ✅
- `cauchy_minimal` — `∃ K ≤ G, |K| = p` cuando `p ∣ |G|` ✅ (Sylow.lean:1641, 0 sorry)
- `wieldandtAct_gpow_add` ✅
- `wieldandtAct_gpow_fixed_of_gcd_one` ✅
- `wielandt_orbit_remove` ✅
- `wielandt_orbit_partition` ✅ (|Ω| = |fix| + p·k)
- `wielandt_exists_nondvd_orbit_aux` ✅ (inducción estructural sobre |Ω|)
- `wielandt_fixed_point_exists` ✅ **COMPLETADO 2026-05-07**

### Pendiente: `wielandt_p_ndvd_r` caso `succ m'`

El teorema `wielandt_p_ndvd_r` prueba que si `|G| = p^(m+1) · r` y ningún
subgrupo propio de `G` es divisible por `p^(m+1)`, entonces `p ∤ r`.

El **caso `m = 0`** ya está demostrado: `cauchy_minimal` da `K : Subgroup G` con
`|K| = p`; `K` es propio y contradice `h_no_proper`.

El **caso `m' ≥ 1`** (succ m') tiene un `sorry`. El obstáculo es la circularidad:
la prueba del caso inductivo necesita aplicar Sylow a un grupo más pequeño `G'`
(un cociente `G/Z` donde `Z ≤ center(G)`, `|Z| = p`), pero eso requiere:

1. Construir el grupo cociente `G/Z` como `FinGroup ℕ₀` — disponible en `QuotientGroup.lean`.
2. Verificar `|G/Z| = p^m · r < |G|` — aritmética directa.
3. Aplicar la hipótesis inductiva fuerte sobre `|G'|` para obtener `H' ≤ G'` con `|H'| = p^(m+1)`.
4. Levantar `H'` a subgrupo de `G` — vía `FirstIsomorphism.lean` o preimagen.

**Bloqueador principal**: la inducción fuerte sobre `|G|` no está disponible directamente
en este contexto (Lean 4.29.0 sin Mathlib); requiere `Nat.strong_rec_on` o equivalente.
Además, el paso 3 introduce una circularidad si se llama recursivamente a `sylow_first` —
hay que pasar la hipótesis inductiva explícitamente como parámetro de `sylow_center_step_wielandt`.

### Plan de acción

#### Paso A — Modificar firma de `sylow_center_step_wielandt`

Añadir un parámetro explícito `HI` (hipótesis inductiva de Sylow para grupos más pequeños):

```lean
private theorem sylow_center_step_wielandt
    (HI : ∀ (G' : FinGroup ℕ₀),
          G'.carrier.card < G.carrier.card →
          ∀ (p' : ℕ₀), Prime p' → (∃ t, Mul.mul p' t = G'.carrier.card) →
          ∃ K : Subgroup G', K.carrier.card = p')
    (G : FinGroup ℕ₀) ...
```

#### Paso B — Reescribir el caso `succ m'` con inducción fuerte

```lean
| succ m' =>
  -- Sylow centrado: ∃ Z ≤ center(G), |Z| = p (por cauchy_minimal sobre center(G))
  -- G' := G / Z,  |G'| = p^m' · r  <  |G|
  -- HI aplicada a G' da H' ≤ G' con |H'| = p^(m+1)
  -- Preimagen de H' en G tiene orden p^(m+1) · |Z| = p^(m+2)... (revisar aritmética)
```

**Nota**: el argumento de Wielandt clásico construye el subgrupo de Sylow directamente
sobre `G` usando el punto fijo de la acción sobre `Ω`; no pasa por un cociente.
La alternativa más limpia puede ser demostrar `wielandt_p_ndvd_r` para `m = 0` (caso base)
y observar que el caso `succ m'` se reduce (por hipótesis `h_no_proper`) al caso en que
`G` mismo no tiene subgrupos propios de orden `p^(m+1)`, lo que —combinado con el argumento
de Wielandt sobre la acción de `G` sobre `Ω`— puede dar la contradicción directamente.

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
wielandt_p_ndvd_r (succ m')  ← siguiente prioridad (Track 1)
  └─ Conjugation.lean            ← después (Track 3)
```

Track 2 (`CosetAction.lean`) y `wielandt_fixed_point_exists` ya están completos.

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
| 1 sorry + 2 private axioms Sylow | ❌ Pendiente (Tracks 1 y 3) |
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
