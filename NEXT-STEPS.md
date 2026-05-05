# Next Steps — Eliminating the Remaining Private Axioms

*Last updated: 2026-05-05*
*Author: Julián Calderón Almendros*

---

## Current build state

`lake build` compila con **0 errores** y **0 sorry** en todo el proyecto (64 jobs).

Warnings activos (menores, no bloquean):

- `PeanoNat.lean:28` — `n`, `m` sin usar (en una definición de instancia)
- `CosetAction.lean:292–294` — variables de patrón sin usar en la acción
- `Sylow.lean:2027` — `hΩ_nd` sin usar

`Sylow.lean` compila con **4 private axioms** (antes eran 5):

| Axiom | Línea ~ | Usado por | Dificultad |
|---|---|---|---|
| `wielandt_fixed_point_exists` | ~2063 | `sylow_center_step_wielandt` | Difícil |
| `wielandt_p_ndvd_r` | ~2166 | `sylow_center_step_wielandt` | Media |
| `sylow_third_mod` | ~2464 | `sylow_third` | Muy difícil |
| `sylow_third_dvd` | ~2478 | `sylow_third` | Muy difícil |

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

- `|Ω| = C(|G|, p^(m+1)) ≡ r (mod p)` por `binom_pow_p_mod`.
- `wielandt_p_ndvd_r`: p ∤ r (por contradicción usando Cauchy en base m=0; ver nota).
- `wielandt_fixed_point_exists`: G actúa sobre Ω por traslación izquierda; p∤|Ω| → `mckay_orbit_count` da una órbita fija → el estabilizador tiene orden `p^(m+1)`.

### Infraestructura necesaria

1. `def sublistsOfLength : List ℕ₀ → ℕ₀ → List (List ℕ₀)` con 6 propiedades:
   `_mem_len`, `_mem_sub`, `_mem_sorted`, `_nodup_result`, `_complete`, `_card`.
2. `def wieldandtOmega (G : FinGroup ℕ₀) (N : ℕ₀) : List (List ℕ₀)`.
3. `wielandt_omega_card` — `|Ω| = C(|G|, N)`.
4. Acción de G sobre `List (List ℕ₀)` por traslación: `g • S = S.map (G.op g)`.
5. `wielandt_fixed_point_exists` — `∃ H : Subgroup G, H.carrier.card = N`.

### Nota sobre `wielandt_p_ndvd_r`

Para m=0: Cauchy da un subgrupo de orden p, contradiciendo `h_no_proper`. Directo.
Para m≥1: el argumento estándar usa Sylow I inductivamente (circular). **Estrategia**:
reestructurar `sylow_lift_from_cauchy` para aceptar la hipótesis inductiva como parámetro
explícito, rompiendo la circularidad. Requiere modificar la firma de
`sylow_center_step_wielandt` en `Sylow.lean` — hacer después de `wielandt_fixed_point_exists`.

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
