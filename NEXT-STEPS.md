# Next Steps — Estado post-Sylow y próximas tareas

*Última actualización: 2026-05-09*
*Autor: Julián Calderón Almendros*

---

## Estado actual del build (2026-05-09)

`lake build` compila con **0 errores**, **0 sorry** y **0 private axioms no intencionales**
en todo el proyecto (37 jobs).

Los únicos `private axiom` son los **6 axiomas de Peano** en `PureAxioms.lean` (intencionales).

Los tres teoremas de Sylow están completamente demostrados:

- `sylow_first` — ✅ existencia de p-subgrupos de Sylow
- `sylow_second` — ✅ todos los p-subgrupos de Sylow son conjugados
- `sylow_third` — ✅ n_p ≡ 1 (mod p) y n_p ∣ |G|

---

## Tareas pendientes (2026-05-09)

### T.1 — Ampliar `ConstructiveCheck.lean` ← SIGUIENTE

Añadir `#assert_constructive` para aritmética base, NumberTheory y Combinatorics pura.
Los módulos de GroupTheory y GodelBeta son explícitamente no constructivos (documentar).

### T.2 — Migración de documentación a `/doc/` (Phase G.1)

Ver sección §G.1 más abajo. No bloquea trabajo matemático.

### T.3 — Feature-freeze y handoff a AczelSetTheory (Phase G.2–G.3)

Precondición: T.2 completada.

---

## Hitos completados (histórico)

- `wieldandtAct_gpow_add` — ✅ demostrado
- `wieldandtAct_gpow_fixed_of_gcd_one` — ✅ demostrado
- `wielandt_orbit_remove` — ✅ demostrado (6 propiedades de salida)
- `wielandt_orbit_partition` — ✅ sorry eliminado (|Ω| = |fix| + p·k)
- `sylow_card_eq` — ✅ 2026-04-28
- `wielandt_omega_card` — ✅ 2026-04-28
- `sylow_second_incl` — ✅ reemplazado por `coset_conjugate_exists` en `CosetAction.lean`
- `wielandt_fixed_point_exists` — ✅ 2026-05-07
- `wielandt_p_ndvd_r` (caso succ m') — ✅ 2026-05-07
- `sylow_third_mod` — ✅ 2026-05-09
- `sylow_third_dvd` — ✅ 2026-05-09

---

## Módulos activos del proyecto (estado 2026-05-09)

```text
Peano/PeanoNat/
├── (aritmética base: Add, Sub, Mul, Div, Pow, Arith, Order, …)
├── ListsAndSets/
│   ├── FSet.lean                ✅ (Phase 5: API genérica — eq_of_mem_iff', sortList', ofList)
│   │                               ⚠ usa Classical.byContradiction en 1 lema — no constructivo
│   ├── FSetFunction.lean        ✅ ⚠ usa Classical.byContradiction — no constructivo
│   ├── EquivRel.lean            ✅ (Phase 5: nuevo — EquivRelOn, classOf, 17 símbolos)
│   └── (…)
├── NumberTheory/
│   ├── ModEq.lean           ✅ constructivo
│   ├── Fermat.lean          ✅ constructivo
│   ├── ChineseRemainder.lean ✅ constructivo
│   ├── Totient.lean         ✅ constructivo
│   └── Wilson.lean          ✅ constructivo (2026-05-05)
├── Combinatorics/
│   ├── Binom.lean           ✅ constructivo
│   ├── NewtonBinom.lean      ✅ constructivo
│   ├── Perm.lean            ✅ constructivo (comentarios §3-§4 son notas, no sorry reales)
│   └── GroupTheory/
│       ├── Action.lean             ✅ ⚠ usa Classical.em — no constructivo (teoría de grupos)
│       ├── NormalSubgroup.lean     ✅ ⚠ no constructivo (depende de Action)
│       ├── QuotientGroup.lean      ✅ ⚠ no constructivo
│       ├── FirstIsomorphism.lean   ✅ ⚠ no constructivo
│       ├── SecondIsomorphism.lean  ✅ ⚠ no constructivo
│       ├── CorrespondenceTheorem.lean ✅ ⚠ no constructivo (2026-05-05)
│       └── Sylow/
│           ├── Cosets.lean       ✅ constructivo (Phase 5)
│           ├── CosetAction.lean  ✅ ⚠ usa Classical.em — no constructivo
│           └── Sylow.lean        ✅ 0 sorry, 0 private axioms no intencionales (2026-05-09)
└── Foundation/
    ├── CantorPairing.lean   ✅ constructivo
    ├── GodelBeta.lean       ✅ ⚠ usa Classical.choose — no constructivo (intencional)
    ├── Foundation.lean      ✅ (paraguas)
    ├── Initiality.lean      ✅ constructivo
    ├── PeanoSystem.lean     ✅ constructivo
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

`List (Subgroup G)` no es `FSet α` genérico sin instancias adecuadas.

**Camino corto** (sin Phase 5): inyectar cada `Subgroup G` en `sylows` a su índice
de lista (`ℕ₀`). Construir `ℕ₀FSet` de índices; mantener la biyección índice↔subgrupo
como lema auxiliar.

**Camino largo** (Phase 5 — ✅ INFRAESTRUCTURA DISPONIBLE 2026-05-07):
instanciar `FinGroup (Subgroup G)` — ahora factible porque `FinGroup` es polimórfico
sobre `{α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]` y `Subgroup G`
tiene las instancias `instDecidableEqSubgroup`, `instLTSubgroup`, `instStrictLinearOrderSubgroup`.
La construcción concreta de `FinGroup (Subgroup G)` sigue pendiente.

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

## Orden de ejecución (2026-05-09)

Todos los tracks matemáticos están completados. El orden de trabajo restante es:

```text
T.1 ConstructiveCheck.lean (ampliar cobertura)  ← SIGUIENTE
T.2 Migración documentación a /doc/
T.3 Feature-freeze + handoff a AczelSetTheory
```

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

### G.0 — Estado actual (2026-05-09)

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
| Phase 5 polimorfismo FinGroup/FSet/EquivRel | ✅ COMPLETADO (2026-05-07) |
| Sylow.lean 0 sorry + 0 private axioms no intencionales | ✅ COMPLETADO (2026-05-09) |
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

## FinGroup polymorphism — Phase 5 ✅ COMPLETADA (2026-05-07)

**Descripción**: `FinGroup`, `Subgroup`, `GroupAction`, `leftCoset`, `cosetRel`,
`EquivRelOn` y toda la infraestructura de `Action.lean`, `Cosets.lean` y `FSet.lean`
son ahora completamente polimórficos sobre `{α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]`.

**Lo que se hizo**:

- `FSet.lean`: añadidos `sorted_nodup_unique_list'` (genérico privado), `FSet.eq_of_mem_iff'`,
  `sortedInsert'`, `sortList'`, `FSet.ofList` y sus lemas.
- `EquivRel.lean`: nuevo módulo con `EquivRelOn`, `classOf`, familia canónica, `classes` y 17 símbolos exportados.
- `Group.lean`: instancias `instDecidableEqSubgroup`, `instLTSubgroup`, `instStrictLinearOrderSubgroup`
  para poder usar `FSet (Subgroup G)`.
- `Cosets.lean` y `Action.lean`: completamente refactorizados a polimorfismo pleno.

**Consecuencia**: `FinGroup (Subgroup G)` es ahora instanciable (infraestructura disponible).
Solo `Sylow.lean` sigue usando `FinGroup ℕ₀` concretamente.

**Build resultante**: 64 jobs, 0 sorry, 3 private axioms en `Sylow.lean`.
