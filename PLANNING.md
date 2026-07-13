# PLANNING — Estado del proyecto

*Autor: Julián Calderón Almendros*
*Última actualización: 2026-07-13*

---

## Pivote arquitectónico (2026-07-13) — ver ADR-017 en DECISIONS.md

El proyecto se re-desarrolla como **completamente intuicionista y constructivista**:
`Classical.*` queda prohibido para código nuevo, y el código existente que lo usa
debe eliminarse progresivamente. Esto sustituye el plan previo de feature-freeze +
handoff directo a `AczelSetTheory` (§ "Trabajo pendiente" más abajo queda obsoleto;
ver la nueva sección **"Plan de desarrollo — eliminación de Classical"** al final de
este documento, que es ahora la hoja de ruta vigente).

## Estado actual (2026-07-13)

`lake build` compila con **0 errores**, **0 sorry** y **0 private axioms no intencionales**
en todo el proyecto (**73 jobs**, Lean 4.31.0).

Los tres teoremas de Sylow están completamente demostrados en `Sylow.lean`:

| Teorema | Estado |
|---------|--------|
| `sylow_first` — ∃ subgrupo de orden p^n | ✅ COMPLETADO |
| `sylow_second` — todos los p-Sylow son conjugados | ✅ COMPLETADO |
| `sylow_third` — n_p ≡ 1 (mod p) y n_p ∣ \|G\| | ✅ COMPLETADO (2026-05-09) |

Los private axioms que quedan en `PureAxioms.lean` son los **6 axiomas de Peano**
(intencionales y fundamentales — no son deuda técnica).

---

## Hitos completados (histórico)

### Sylow.lean — COMPLETADO (2026-05-09)

Todos los teoremas de los tres teoremas de Sylow fueron demostrados sin sorry
ni private axioms en sesiones sucesivas (2026-04-28 → 2026-05-09):

| Hito | Fecha | Notas |
|------|-------|-------|
| `wielandt_orbit_partition` | 2026-05-06 | Pieza A de Wielandt |
| `wielandt_fixed_point_exists` | 2026-05-07 | Pieza B de Wielandt |
| `wielandt_p_ndvd_r` (caso succ m') | 2026-05-07 | Inducción fuerte |
| `sylow_third_mod` | 2026-05-09 | n_p ≡ 1 (mod p) |
| `sylow_third_dvd` | 2026-05-09 | n_p \| \|G\| |
| Build 0 errores, 0 sorry | 2026-05-09 | 37 jobs OK |

### Infraestructura de GroupTheory — COMPLETADA

| Módulo | Estado |
|--------|--------|
| `NormalSubgroup.lean` | ✅ center, centralizer, criterios |
| `QuotientGroup.lean` | ✅ quotientGroup, quotientHomomorphism |
| `FirstIsomorphism.lean` | ✅ firstIsoMap (inyectivo + sobreyectivo) |
| `SecondIsomorphism.lean` | ✅ secondIsoMap |
| `CorrespondenceTheorem.lean` | ✅ preimageSubgroup, biyección |
| `CosetAction.lean` | ✅ coset_conjugate_exists (→ sylow_second) |
| Phase 5: polimorfismo FinGroup/FSet/EquivRel | ✅ 2026-05-07 |

### NumberTheory — COMPLETADA

| Módulo | Estado |
|--------|--------|
| `Wilson.lean` | ✅ 2026-05-05 |
| `Fermat.lean` | ✅ |
| `ChineseRemainder.lean` | ✅ |
| `Totient.lean` | ✅ |
| `ModEq.lean` | ✅ |

### Foundation (PA → Aczel → ZFC) — COMPLETADA (2026-05-02)

| Módulo | Estado |
|--------|--------|
| `CantorPairing.lean` | ✅ (constructivo — `antidiag`/`fst`/`snd` son `def`, no `noncomputable`) |
| `GodelBeta.lean` | ✅ matemáticamente, pero usa `Classical.choose` — deuda a eliminar, ver ADR-017 |
| `Foundation.lean` paraguas | ✅ |

---

## Trabajo pendiente (histórico, pre-pivote — ver plan vigente más abajo)

### P.1 — Actualizar y ampliar `ConstructiveCheck.lean`

Absorbido por la Fase C.5 del plan vigente (abajo) — deja de ser una tarea aislada y
pasa a ser la puerta de verificación de ADR-017.

### P.2 — Migración de documentación a `/doc/`

✅ COMPLETADA (2026-05-10). Ver `NEXT-STEPS.md` §G.1.

### P.3 — Criterio de feature-freeze y handoff a AczelSetTheory

**Pospuesto** — ver ADR-017 en `DECISIONS.md`. Pasa a ser la Fase D del plan vigente.

---

## Plan de desarrollo — eliminación de Classical (vigente desde 2026-07-13)

Hoja de ruta para ADR-017. Cubre también el resto de deuda de housekeeping detectada
en `AUDIT-2026-07-13.md` que no era puramente cosmética. Fases **A** y **B** ya están
cerradas (ejecutadas en la sesión de auditoría del 2026-07-13); **C** es el trabajo
matemático real pendiente; **D** reactiva el plan de handoff una vez C esté cerrada.

### Fase A — Housekeeping de documentación y tooling ✅ COMPLETADA (2026-07-13)

- [x] Sincronizar versión de Lean documentada (v4.29.0 → v4.31.0) en README/REFERENCE.
- [x] `check-docs-sync.bash` — nuevo script que compara el job-count real de
      `lake build` contra lo declarado en README/REFERENCE/NEXT-STEPS/CURRENT-STATUS;
      wireado en `AI-GUIDE.md` §"actualiza doc" y §"dame situación".
- [x] `Perm.lean` — eliminado `card_Sym` (placeholder `rfl` no probaba nada real) y los
      2 TODOs de ciclos/signatura (redundantes con `Sign.lean`, que ya reserva ese
      namespace). `ConstructiveCheck.lean` corregido: su comentario sobreestimaba el
      alcance real de `Classical.*` (ver ADR-017 para el alcance verificado).
- [x] `REFERENCE.md` — timestamp de cabecera unificado con el del cuerpo (2026-07-13).
- [x] `DEPENDENCIES.md` — grafo Mermaid regenerado por extracción real de `import`
      (ya no a mano); corregidas 2 aristas falsas (`Group → Perm`, `Orbit → Perm`);
      añadidos los 4 barrels temáticos reales y los módulos de `Foundation/`.
- [x] `CURRENT-STATUS-PROJECT.md` y este documento — actualizados a 73 jobs / Lean
      4.31.0 / 2026-07-13.
- [x] `fix_sylow.py` — era un script de parcheo de un solo uso para errores de
      `Sylow.lean` ya resueltos (verificado: el texto que buscaba reemplazar ya no
      existe en el fichero, y `Sylow.lean` compila con 0 errores). Eliminado de git y
      de disco.
- [x] 10 ficheros con `import` antes de la cabecera de copyright (viola AI-GUIDE.md
      §23) — corregidos bajo el protocolo de lock/unlock de `git-lock.bash`. Nota
      técnica descubierta en el proceso: un comentario de módulo `/-! ... -/` (bang)
      es una *declaración* de Lean y debe ir DESPUÉS de los `import`; un comentario
      plano `/- ... -/` (sin bang) es solo léxico y puede ir antes. Los ficheros que
      combinaban copyright + docstring de módulo en un único bloque `/-!` se
      partieron en dos: cabecera `/- Copyright... -/` antes del import, docstring
      `/-! # Título ... -/` después.
- [x] `Primes.lean` tiene el mismo problema de orden pero está **congelado**
      (`frozen_files.txt`) — no se ha tocado. Requiere una decisión explícita del
      usuario: ¿vale la pena un `thaw --confirm` por un reordenamiento cosmético de
      comentarios, o se documenta como excepción permanente? Ver Fase C.6.
- [x] `git-lock.bash list` tenía un bug real (no declarado en ninguna auditoría
      previa): imprimía las líneas de comentario (`#...`) de `frozen_files.txt`/
      `locked_files.txt` como si fueran ficheros congelados/bloqueados. Corregido.

### Fase B — Toolchain ✅ COMPLETADA (2026-07-13)

- [x] Verificado: Lean 4.31.0 es la última estable (4.32.0-rc1 es release candidate,
      no estable — no se sube a un RC). El proyecto compila **sin cambios** en
      v4.31.0 (73 jobs, 0 errores, 0 sorry) — la suposición inicial de que "algo no
      compila con esa versión" no se confirmó para este proyecto en concreto (podría
      referirse a otro proyecto hermano — ROBINSON_PlusPlus, FOL, ZfcSetTheory — no
      verificado aquí). `lean-toolchain` actualizado a v4.31.0.
- [ ] **Seguimiento**: cuando v4.32.0 salga de RC, repetir la prueba
      (`echo "leanprover/lean4:v4.32.0" > lean-toolchain && lake build`, revertir si
      falla) antes de adoptarla vía `update-toolchain.bash` (que commitea automático
      en éxito — revisar el diff antes de dejar que commitee).

### Fase C — Eliminación de `Classical.*` (núcleo de ADR-017, EN CURSO)

Alcance verificado por grep exhaustivo (ver ADR-017) — 3 focos vía `Classical.`
literal, más un 4º foco descubierto en C.1 (ver C.7): la táctica `classical` (sin
punto, sin prefijo `Classical.`) también instala `Classical.propDecidable` como
instancia local y **no aparece en un grep de `Classical\.`** — hay que buscarla
también como palabra suelta (`grep -rn '\bclassical\b'`).

**C.1 — `Combinatorics/GroupTheory/Action.lean`** ✅ COMPLETADA (2026-07-13). Los 2
usos de `Classical.em` (líneas 247 y 300 originales, sobre
`∃ z, z ∈ (ψ.orb x).elems ∧ z ∈ (ψ.orb y).elems` y `z ∈ (ψ.orb x).elems`) se
sustituyeron por: (1) un test de decidibilidad explícito vía
`(ψ.orb x).elems.any (fun z => decide (z ∈ (ψ.orb y).elems))` + `List.any_eq_true` /
`decide_eq_true_eq` para el existencial (no hay instancia `Decidable` automática
para un `∃` no acotado sobre `β`, hay que construirla a mano igual que el resto del
fichero ya hace en `GroupAction.orb`/`isFixed`); (2) `by_cases` directo para la
pertenencia a una lista (`z ∈ (ψ.orb x).elems`), que sí tiene instancia `Decidable`
automática vía `DecidableEq β`. Verificado con
`#print axioms Peano.Action.orbits_partition` (y `class_equation`,
`class_equation_split`): dependen solo de `[propext, Quot.sound]` — **cero**
`Classical.choice` — antes de esta sesión no se había hecho esta verificación
explícita, solo se confiaba en el grep textual. Build: 73 jobs, 0 sorry, 0 errores.

**Nota de precaución para C.2–C.3 (mismo fichero/familia)**: `by_cases`/`classical`
sobre un `∃` no acotado silenciosamente tira de `Classical.propDecidable` si está en
el contexto — **no basta con borrar la palabra `Classical.em` y poner `by_cases`**,
hay que verificar con `#print axioms` que el teorema resultante no menciona
`Classical.choice` antes de dar el paso por bueno (el caso C.7 de abajo es la prueba
de que el propio código de este proyecto ya tiene un caso así, escondido).

**C.2 — `Sylow/CosetAction.lean`** ✅ COMPLETADA (2026-07-13). El `Classical.em` de
la línea 439 (`∀ g ∈ G.carrier.elems, α.act g x₀ = x₀`, en `pgroup_fixed_point`) se
sustituyó por `G.carrier.elems.all (fun g => decide (α.act g x₀ = x₀))` +
`List.all_eq_true`/`decide_eq_true_eq` — mismo patrón que C.1 pero con `all` en vez
de `any` (cuantificador universal acotado, no existencial). **Hallazgo nuevo, más
sutil que C.7**: tras quitar el `Classical.em` explícito, `#print axioms` sobre
`coset_conjugate_exists` seguía mostrando `Classical.choice` — no por el `Classical.em`
ya arreglado, sino por un `simp at hlen` genérico (sin argumentos) en
`card_eq_one_iff_singleton`, un lema privado sin relación aparente con C.2. `simp` sin
argumentos puede resolver una meta apoyándose en `Decidable`/`Classical.propDecidable`
de forma completamente silenciosa — sin escribir `Classical.em`, sin `classical`, sin
ningún texto detectable por grep. Se sustituyó por el `simp only [List.length_cons] at
hlen; omega` explícito (mismo resultado matemático, sin la vía classical), verificado
por bisección con `sorry` (aislar qué sub-término del término de prueba cargaba el
axioma) — técnica documentada abajo en "Metodología de verificación" porque **va a
hacer falta repetirla en C.3**, que tiene muchas más tácticas `simp`/`by_contra`
genéricas. Build: 73 jobs, 0 sorry. `#print axioms coset_conjugate_exists` →
`[propext, Quot.sound]`, cero `Classical.choice`.

**Metodología de verificación (aplicar en C.3–C.6)**: `grep` de `Classical\.` y
`\bclassical\b` solo encuentra los usos *explícitos*. Un `simp`/`decide`/`omega` sin
argumentos puede tirar de `Classical.choice` sin dejar ningún rastro textual. El único
chequeo fiable es `#print axioms <teorema>` sobre cada teorema público tocado
(exportado) tras cada cambio. Si aparece `Classical.choice` inesperadamente y no está
claro por qué: (1) añadir temporalmente `#print axioms <lema_privado>` para cada lema
privado que use la prueba, uno por línea, justo antes de `end <Namespace>`; (2)
localizar cuál lo introduce; (3) dentro de ese lema, sustituir progresivamente
sub-pruebas por `sorry` (bisección) hasta que `Classical.choice` desaparezca del
reporte (quedará solo `sorryAx`) — el último trozo sorryado es el culpable; (4)
reemplazar ese trozo por una táctica más específica (`simp only [...]`, `omega`,
`decide` sobre un `Decidable` concreto) en vez de `simp`/`by_contra` genéricos; (5)
borrar los `#print axioms` temporales antes de terminar.

**C.3 — `Sylow/Sylow.lean`** ✅ literal `Classical.em`/`Classical.byContradiction`
eliminado (2026-07-13) — pero ver **C.9** abajo, hallazgo nuevo y más profundo que deja
esta fase realmente **abierta a nivel de axiomas**, pese a que el texto ya está limpio.

Los 8 usos (2 `Classical.em` en líneas 2913 y 4920/4922, 5 `Classical.byContradiction`
en 3947–4151) se sustituyeron caso a caso, no con un find-and-replace:

- Línea 2913 (`p ∣ lengthₚ (wieldandtOrb ...)`) → `by_cases` directo: `Divides`
  sobre `ℕ₀` ya tiene instancia `Decidable` real (`Primes.decidableDvd`, construida
  vía `dividesb`/`mod`, sin choice) — solo hacía falta usarla.
- Línea 4920 (`∃ k, mul p k = N'`) → **no** es literalmente `p ∣ N'` aunque lo parezca
  (la igualdad está invertida: `Divides p N' := ∃ k, N' = mul p k`). Se resolvió con
  `Decidable.em (p ∣ N')` + una conversión de orientación (`hk_eq.symm`) en el punto de
  extracción del testigo, dejando el resto de la prueba (que ya usaba `hk`/`hndvd` con
  la orientación original) intacto.
- Línea 4922 (`k = 𝟘`) → `Classical.em` → `Decidable.em` (swap directo, `DecidableEq
  ℕ₀` ya cubre esto).
- Líneas 3951/3988/4069/4151 (`Classical.byContradiction` sobre metas ya decidibles:
  igualdad en `ℕ₀`, divisibilidad, igualdad de `Bool`) → swap directo a
  `Decidable.byContradiction` (mismo lema que `Classical.byContradiction` pero
  tomando `[Decidable p]` en vez de asumir clásica — existe en `Init/Core.lean` del
  propio Lean 4 core, sin necesidad de nada del proyecto).
- Línea 3947 (`∃ g₀ ∈ G.carrier.elems, conjAct.act g₀ x ≠ x`) → igual que C.1/C.2,
  construcción manual vía `List.any`/`decide` (existencial no acotado automáticamente
  decidible). Aquí además apareció el mismo problema que en C.2: un `simp [hb] at
  htrue` genérico no cerraba la meta como se esperaba (`List.any_eq_true` es simp por
  defecto y reordena la normalización antes de poder usar `hb`) — se sustituyó por
  `rw [hb] at htrue; exact absurd htrue (by decide)`, explícito y sin ambigüedad de
  orden de reescritura.

Build tras las 8 correcciones: 73 jobs, 0 sorry, 0 `Classical.`/`classical` textual en
el fichero (verificado por grep).

**C.9 — NUEVO, más profundo que C.1–C.7: `Group.order` es la fuente real de
`Classical.choice` en 4 de los 5 teoremas exportados de `Sylow.lean`.**
Tras limpiar el texto de C.3, `#print axioms` sobre los 5 exports mostró:

| Teorema exportado | `Classical.choice`? |
|---|---|
| `cauchy_minimal` | ⚠️ SÍ |
| `sylow_lift_from_cauchy` | ⚠️ SÍ |
| `sylow_first` | ⚠️ SÍ |
| `sylow_second` | ✅ NO (`[propext, Quot.sound]`) |
| `sylow_third` | ⚠️ SÍ |

Bisección (probando con `#print axioms` los ~48 lemas privados declarados antes de
`cauchy_minimal`) aisló la fuente: **`order_dvd_of_pow_eq_id`** (línea 108) es el primer
lema en orden de declaración que carga `Classical.choice`, y lo hace simplemente porque
su enunciado menciona `order G g hg` — y `Group.order` (`Combinatorics/Group.lean:269`)
está definido como `choose_unique (order_wop G g hg)`, tirando directamente de
`Prelim.Classical.choose_unique`/`Classical.indefiniteDescription`. Confirmado con
`#print axioms Peano.Group.order` → `[propext, Classical.choice, Quot.sound]`.

A diferencia de C.1/C.2/C.7 (que eran usos *accidentales* de `Classical.em`/`classical`
donde una alternativa decidible ya existía y bastaba con sustituir la táctica), **esto
no es un descuido**: `order` se diseñó deliberadamente vía "extraer el mínimo con el
principio de buena ordenación + choice" en vez de una búsqueda acotada explícita. El
argumento de Cauchy (`cauchy_minimal`/`sylow_first`/`sylow_third`) necesita
genuinamente "el orden de un elemento" como noción, así que no se puede evitar sin
tocar la definición de `order` — a diferencia de C.1–C.3, esto **no es una sustitución
mecánica de una línea**, es un cambio de definición que se propaga por `Group.lean`
(módulo bloqueado pero no congelado, usado por prácticamente todo `GroupTheory/`).

**Camino constructivo disponible** (no aplicado todavía — requiere decisión y una
sesión propia): `order` es hallable por búsqueda acotada — el orden de `g` divide
`|G|` (Lagrange, ya demostrado en `Cosets.lean`), así que basta buscar linealmente el
menor `n` con `1 ≤ n ≤ G.carrier.card` tal que `g^n = e` (existe por Lagrange, el rango
es finito) en vez de invocar `well_ordering_principle` + `choose_unique` sobre un
predicado no acotado. Esto:

1. Requiere una nueva `def order'` (o redefinir `order`) vía recursión/búsqueda
   acotada sobre `List.range 1 (G.carrier.card + 1)` o similar, con una prueba de que
   el resultado coincide con la especificación actual (`order_spec`).
2. Toca `Group.lean`, que es dependencia transitiva de casi todo `GroupTheory/` —
   alto impacto, requiere re-verificar con `#print axioms` cada teorema público que
   mencione `order` tras el cambio (no solo en `Sylow.lean`, también en el propio
   `Group.lean` y cualquier otro consumidor).
3. Candidato natural para ejecutarse en la MISMA sesión que C.5 (retirar
   `Prelim/Classical.lean`) ya que ambos tocan el mismo problema de raíz — si `order`
   deja de depender de `choose_unique`, puede que `Prelim.Classical` quede sin
   consumidores reales en todo el proyecto (pendiente de verificar tras el cambio).

Pendiente de decisión del usuario sobre si abordar C.9 ahora o dejarlo documentado
para una sesión dedicada — es cualitativamente distinto (mayor alcance, mayor riesgo)
que el resto de la Fase C hecha hasta ahora.

**C.4 — `Foundation/GodelBeta.lean`** ✅ COMPLETADA (2026-07-13). Los 2
`Classical.choose`/`choose_spec` (encodeList, encode_decode) eliminados. Estrategia:

- `godel_beta_seq` se descompuso en `godelB n a` (el módulo b, ya explícito en la
  prueba original: `factorial (σ (max n (seqBound a n)))`, ahora un `def` público en
  vez de estar oculto tras el existencial) + `godel_beta_seq_aux` (privado, mismo
  enunciado con b fijado a `godelB n a`, sólo c existencial). `godel_beta_seq` se
  mantiene como wrapper público con el mismo enunciado de siempre (∃ c b, ...), para
  no romper el uso externo/docs.
- El testigo c, en cambio, **no tiene fórmula cerrada** (viene de CRT iterado vía
  `simultaneous_congruences`/`chinese_remainder`/`bezout_natform`, una cadena de
  ~4 ficheros que habría sido necesario rehacer como `def`s computables). Se evitó
  ese refactor mayor con un atajo constructivo: cualquier testigo c que satisfaga la
  especificación puede reducirse mod `prod_mods b n` sin romperla (`gmod b i ∣
  prod_mods b n` para i ≤ n, por periodicidad de β vía `ModEq`/`modEq_of_dvd`,
  reutilizando lemas ya existentes en el fichero). Eso acota el rango de búsqueda a
  `[0, prod_mods b n)`, finito y decidible (igualdad en ℕ₀ decidible), así que basta
  una búsqueda lineal (`List.find?` sobre `List.range`, con predicado `checkBetaSeq :
  ℕ₀ → Bool` vía `List.all`/`decide`) — sin necesidad de tocar la cadena CRT/Bezout.
  `godelC n a := (findBetaC n (godelB n a) a).getD 𝟘`, con `godelC_spec` demostrando
  que satisface la especificación (usa `List.find?_isSome`/`List.find?_some`, ambos
  en Lean4 core, no Mathlib).
- Trampa de sintaxis (nueva, documentar para futuras fases): el proyecto redefine `+`
  como `notation a "+" b => Peano.Add.add a b` (`Add.lean:1179`) SIN anotación de
  precedencia — esto captura también expresiones sobre `Nat` puro (no sólo ℕ₀) que
  usen `+` dentro de un fichero con `open Peano.Add`, rompiendo el parseo de
  expresiones como `k < Ψ n + 1 ↔ P` (error confuso: `failed to synthesize OfNat Prop
  1`). Solución: evitar `+` sobre `Nat` en estos ficheros y usar `Nat.succ`/`.succ`
  explícito en su lugar.
- Build: 73 jobs, 0 sorry, 0 texto `Classical.`/`classical`. `#print axioms` sobre
  `encodeList`, `encode_decode`, `godelC`, `godelC_spec`, `godel_beta_seq` →
  `[propext, Quot.sound]`, sin `Classical.choice`.

**C.5 — Retirar `Prelim/Classical.lean`**: una vez C.1–C.4 cerradas, ningún módulo de
producción debería seguir importando `Prelim.Classical`. Verificar con
`grep -rl "Peano.Prelim.Classical\|choose_unique\|Classical\." Peano/` → debe devolver
vacío (salvo el propio fichero). Retirar su `import`/`export` de `Prelim.lean` y
`Peano.lean`. Decisión pendiente: ¿se borra el fichero o se deja como reliquia
histórica sin importar desde ningún sitio? (Precedente del proyecto: preferir borrar
lo que ya no se usa — ver AI-GUIDE.md §16b, aunque ese párrafo habla de scratch files,
no de módulos de producción retirados; tratar como caso nuevo a decidir en el momento).

**C.6 — Ampliar `Peano/ConstructiveCheck.lean`**: añadir `#assert_constructive` para
**todo** símbolo público del proyecto (no solo aritmética base) — convertir el chequeo
en la puerta de compilación de ADR-017. Una vez C.1–C.5 cerradas, cualquier
declaración pública debería pasar; el comando ya existe y funciona (ver líneas 88–94
del fichero), solo falta la cobertura exhaustiva. Añadir también a este punto: decidir
qué hacer con `Primes.lean` congelado y su orden de copyright/import (Fase A, punto
pendiente) — buen momento para agrupar ambas decisiones si se hace un `thaw` puntual.

**C.7 — `ListsAndSets/EquivRel.lean`** ✅ COMPLETADA (2026-07-13, descubierta el mismo
día al resolver C.1 — no estaba en el alcance original de ADR-017).
`EquivRelOn.classOf_eq_or_disjoint` (línea 117) usaba la táctica `classical` — mismo
patrón exacto que C.1 (`∃ z, z ∈ (R.classOf a).elems ∧ z ∈ (R.classOf b).elems`,
seguido de `by_cases hza : z ∈ (R.classOf a).elems`) pero resuelto con `classical` en
vez de `Classical.em` explícito, por eso el grep original de `Classical\.` no lo
encontró. Se aplicó la misma construcción `List.any`/`decide` de C.1 sin cambios de
diseño. Verificado con `#print axioms`: `classOf_eq_or_disjoint`,
`canonicalClassFamily` y `classes_cover` dependen solo de `[propext, Quot.sound]` —
cero `Classical.choice`. `grep -n '\bclassical\b\|Classical\.'` sobre el fichero →
vacío. Build: 73 jobs, 0 sorry, 0 errores.

**Orden actualizado**: ~~C.1~~ ✅ → ~~C.7~~ ✅ → ~~C.2~~ ✅ → ~~C.3~~ ✅ (texto) →
~~C.4~~ ✅ → **C.9** (siguiente, por decisión del usuario 2026-07-13: redefinir
`Group.order` sin `Classical.choice`) → C.5 → C.6. Cada paso
debe cerrar con `lake build` limpio, `check-sorry.bash` en 0, **y una verificación
`#print axioms` del teorema tocado** antes de pasar al siguiente — no acumular cambios
sin verificar entre pasos, dado que `Sylow.lean` (C.3) es una prueba larga y frágil
(ver `feedback_lean4_tactics.md` en la memoria del asistente sobre las trampas de Lean
4.29+ con `rcases`/`cases`). **Recordatorio permanente**: antes de dar cualquier fase
de esta lista por cerrada, repetir también el grep de la palabra suelta `classical`
(no solo `Classical\.`) — C.7 demostró que el patrón oculto puede reaparecer en
cualquier fichero tocado por C.2–C.6.

### Fase D — Retomar feature-freeze + handoff a AczelSetTheory (bloqueada por C)

Precondición: Fase C completa (0 usos de `Classical.*` fuera de, como mucho, un
`Prelim/Classical.lean` ya retirado de la cadena de imports). Pasos: los ya
documentados en `NEXT-STEPS.md` §G.2–G.3, sin cambios — el criterio de feature-freeze
gana ahora una condición adicional: "0 `Classical.*` en el árbol de producción".
