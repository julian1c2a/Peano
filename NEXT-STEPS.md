# Next Steps — Estado post-Sylow y próximas tareas

*Última actualización: 2026-07-13*
*Autor: Julián Calderón Almendros*

---

## Cambio de rumbo (2026-07-13) — ver DECISIONS.md ADR-017 y PLANNING.md

El proyecto se re-desarrolla como intuicionista/constructivista puro.

- Fase C.1 (`Combinatorics/GroupTheory/Action.lean`) — ✅ COMPLETADA (2026-07-13):
  los 2 `Classical.em` sustituidos por decidibilidad explícita; verificado con
  `#print axioms` que no queda `Classical.choice`.
- Fase C.7 (`ListsAndSets/EquivRel.lean`) — ✅ COMPLETADA (2026-07-13): la táctica
  `classical` (hallazgo no previsto en ADR-017 original) sustituida con el mismo
  patrón de C.1; verificado con `#print axioms`.
- Fase C.2 (`Sylow/CosetAction.lean`) — ✅ COMPLETADA (2026-07-13): el `Classical.em`
  sustituido por `List.all`/`decide`. Hallazgo importante: un `simp` genérico sin
  argumentos en un lema privado sin relación aparente (`card_eq_one_iff_singleton`)
  también tiraba de `Classical.choice` sin dejar rastro grepeable — localizado por
  bisección con `sorry`. Ver PLANNING.md Fase C.2 para la metodología, ahora
  obligatoria en C.3 también.
- Fase C.3 (`Sylow/Sylow.lean`) — texto ✅ limpio (2026-07-13): los 8
  `Classical.em`/`Classical.byContradiction` sustituidos caso a caso (swaps directos a
  `Decidable.em`/`Decidable.byContradiction` donde ya había instancia real; 2 casos
  con construcción manual vía `List.any`, uno de ellos con el mismo problema de `simp`
  genérico que C.2). Build 73 jobs, 0 sorry, 0 texto `Classical.`/`classical`.
- **Hallazgo nuevo, PENDIENTE DE DECISIÓN — Fase C.9**: pese al texto limpio,
  `#print axioms` muestra que `cauchy_minimal`, `sylow_lift_from_cauchy`,
  `sylow_first` y `sylow_third` (NO `sylow_second`) siguen dependiendo de
  `Classical.choice` — no por un descuido, sino porque **`Group.order`** (usado
  genuinamente por el argumento de Cauchy) está definido vía
  `choose_unique`/`Classical.indefiniteDescription`. Arreglarlo requiere redefinir
  `order` con búsqueda acotada (el orden divide `|G|` por Lagrange) — cambio de
  definición, no de táctica, con impacto en todo `Group.lean`. Ver `PLANNING.md`
  Fase C.9 para el análisis completo. **No decidido todavía si abordarlo ahora o en
  sesión aparte.**
- Fase C.4 (`Foundation/GodelBeta.lean`) — ✅ COMPLETADA (2026-07-13): los 2
  `Classical.choose`/`choose_spec` (en `encodeList`/`encode_decode`) eliminados. `b`
  ya era explícito (extraído a `godelB`); `c` no tiene fórmula cerrada (viene de CRT
  iterado), así que se evitó rehacer toda la cadena `simultaneous_congruences`/
  `chinese_remainder`/`bezout_natform` como `def`s computables, y en su lugar se
  acotó el rango de búsqueda (cualquier testigo se puede reducir mod `prod_mods b n`
  sin romper la especificación) y se buscó linealmente con `List.find?`/`decide`
  (`godelC`/`godelC_spec`, Fase C.4 en PLANNING.md tiene el detalle completo).
  Trampa nueva documentada: `+` está redefinido como `notation` sin precedencia
  (`Add.lean:1179`), rompe el parseo de `+` sobre `Nat` puro en ficheros con `open
  Peano.Add` — usar `Nat.succ`/`.succ` en su lugar. Build 73 jobs, 0 sorry, 0 texto
  `Classical.`/`classical`; `#print axioms` confirma que `encodeList`, `encode_decode`,
  `godelC`, `godelC_spec` y `godel_beta_seq` ya no dependen de `Classical.choice`.
- Fase C.9 (`Combinatorics/Group.lean`, `Group.order`) — ✅ COMPLETADA (2026-07-13):
  redefinido como búsqueda acotada (`List.find?` sobre `[1, |G|]`, acotado por
  `orderExists`), sin `choose_unique`/`Classical.indefiniteDescription`. Mismos nombres
  públicos (`order`, `order_pos`, `gpow_order_eq_id`, `order_minimal`, `order_le_card`),
  cero cambios para `Sylow.lean`. `#print axioms Peano.Group.order` → sin ningún
  axioma. Ver PLANNING.md Fase C.9 para las dos trampas nuevas documentadas (`omega`
  no entiende `Nat.pred`/`Nat.sub` en este entorno; `by_contra` no existe sin Mathlib,
  usar `Decidable.byContradiction`).
- **Tres hallazgos post-C.9, MISMA SESIÓN 2026-07-13 (ver PLANNING.md Fase C.9,
  sección "Hallazgo 1/2/3" para el detalle completo)**:
  1. ✅ RESUELTO: `List.mem_erase_of_ne`/`List.length_erase_of_mem` (núcleo de Lean 4)
     dependen de `Classical.choice` en sí mismos. El patrón que los usaba
     (`nodup_sub_len` inline) estaba copiado en 9 sitios de `Sylow.lean`; ya existía
     un `nodup_subset_length_le` constructivo (privado) en `FSetFunction.lean` — se
     exportó y se sustituyeron las 9 copias (~180 líneas menos).
  2. ✅ RESUELTO: `.choose`/`.choose_spec` (= `Classical.choose` sin la palabra
     "Classical" literal) usado directamente en `wielandt_p_ndvd_r` — sustituido por
     `obtain`.
  3. ✅ RESUELTO, trampa nueva importante: `omega` cerrando un objetivo NO aritmético
     (p. ej. un existencial) por contradicción invoca `Classical.choice` internamente
     — hay que aislar la contradicción con `exact absurd h (by omega)` en vez de
     llamar `omega` directo sobre el objetivo real. Puede haber más instancias de este
     patrón sin auditar en el resto de `Sylow.lean`.
  - **PENDIENTE, sin resolver al cerrar la sesión**: `sylow_lift_from_cauchy` (y por
    tanto `sylow_first`/`sylow_third`) SIGUE mostrando `Classical.choice` pese a que
    `wielandt_p_ndvd_r`, `sylow_center_step_wielandt`, `cauchy_minimal` y `lagrange`
    ya están todos limpios — la fuente está en alguna pieza de `sylow_lift_from_cauchy`
    todavía no auditada individualmente (`sylow_center_step`, `subgroupToFinGroup`,
    `subgroupOfSubgroup`, o algo dentro de su `have step`). Plan de bisección exacto
    para continuar mañana: PLANNING.md Fase C.9, "Plan exacto para continuar".
- **Siguiente paso concreto**: localizar y arreglar la fuente restante en
  `sylow_lift_from_cauchy` (ver plan arriba), luego continuar con
  C.5 (retirar `Prelim/Classical.lean`) y C.6 (`ConstructiveCheck.lean` exhaustivo).

## Estado actual del build (2026-07-13)

`lake build` compila con **0 errores**, **0 sorry** y **0 private axioms no intencionales**
en todo el proyecto (**73 jobs full build**, Lean 4.31.0 — verificar con
`bash check-docs-sync.bash` antes de confiar en esta cifra si ha pasado tiempo).

Los únicos `private axiom` son los **6 axiomas de Peano** en `PureAxioms.lean` (intencionales).

Los tres teoremas de Sylow están completamente demostrados:

- `sylow_first` — ✅ existencia de p-subgrupos de Sylow
- `sylow_second` — ✅ todos los p-subgrupos de Sylow son conjugados
- `sylow_third` — ✅ n_p ≡ 1 (mod p) y n_p ∣ |G|

Módulos añadidos tras 2026-05-09:
- `ThirdIsomorphism.lean` — ✅ (G/N)/(K/N)≅G/K, 10 exports, 0 sorry
- `Fractions.lean` — ✅ export block completo (`export Peano.Arith (...)`), corregido
  desde la nota anterior que decía que carecía de él (verificado 2026-07-13)

---

## Tareas pendientes

### T.1 — Ampliar `ConstructiveCheck.lean` — ahora es PLANNING.md Fase C.6

Absorbido por el plan de eliminación de Classical — ver PLANNING.md. Ya no es una
tarea aislada de cobertura, es la puerta de verificación de ADR-017.

### T.2 — Migración de documentación a `/doc/` (Phase G.1) ✅ COMPLETADO (2026-05-10)

Seis archivos `doc/REFERENCE-*.md` creados y pusheados en commit `85c8742`.
Ver §G.1 para los detalles. No bloquea trabajo matemático.

### T.3 — Feature-freeze y handoff a AczelSetTheory (Phase G.2–G.3) — POSPUESTO

Precondición ampliada (ADR-017): T.2 completada **y** PLANNING.md Fase C
(eliminación de Classical) completada.

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

## Track 1 — `Sylow.lean` ✅ COMPLETADO (2026-05-07)

`wielandt_p_ndvd_r` (incluido el caso `succ m'`) está completamente demostrado como `private theorem`.
Ver «Hitos completados» arriba.

### Historial (referencia)

`wielandt_fixed_point_exists` fue el último obstáculo: G actúa sobre Ω por traslación;
p∤|Ω| → `wielandt_exists_nondvd_orbit_aux` da punto fijo → estabilizador de orden p^(m+1). ✅

---

## Track 2 — `CosetAction.lean` ✅ COMPLETADO

`sylow_second_incl` ya no es un `private axiom`. `CosetAction.lean` exporta
`coset_conjugate_exists`, que `Sylow.lean` llama directamente en la prueba de
`sylow_second_incl` (ahora `private theorem`).

---

## Track 3 — `sylow_third_mod` + `sylow_third_dvd` ✅ COMPLETADO (2026-05-09)

`sylow_third_mod` y `sylow_third_dvd` están demostrados como `private theorem` (0 sorry).
`sylow_third` usa ambos para concluir n_p ≡ 1 (mod p) y n_p ∣ |G|.

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

## Orden de ejecución (2026-05-10)

Todos los tracks matemáticos están completados. Documentación migrada a `/doc/`. El orden restante es:

```text
T.1 ConstructiveCheck.lean (ampliar cobertura)  ← SIGUIENTE
T.2 Migración documentación a /doc/             ✅ COMPLETADO 2026-05-10
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
| G.1 Migración documentación a `/doc/` | ✅ COMPLETADO (2026-05-10) |

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
- [x] G.1 Documentación migrada a `/doc/` ✅ (2026-05-10)

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
