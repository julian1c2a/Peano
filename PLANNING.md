# PLANNING — Estado del proyecto

*Autor: Julián Calderón Almendros*
*Última actualización: 2026-07-14*

---

> ## 🧊 PEANO ES `FEATURE-FROZEN` (2026-07-14) — ver DECISIONS.md ADR-018
>
> Cierre definitivo. El desarrollo activo continúa en **`AczelSetTheory`** — ver
> `NEXT-STEPS.md` §G.3 para el protocolo de handoff. Todo lo que sigue en este
> documento es histórico.

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

**C.9 — `Group.order` ✅ COMPLETADA (2026-07-13, por decisión del usuario: primero C.4,
luego C.9).** Redefinido como búsqueda acotada: `orderPred`/`orderFind` (predicado
`Bool` + `List.find?` sobre `List.range' 1 (Ψ G.carrier.card)`, candidatos codificados
como `Nat` vía `Λ`), `order := Λ ((orderFind G g).getD 0)`, con `order_spec` demostrado
aparte (`orderFind_isSome` + `orderFind_no_earlier` para minimalidad). Mismos nombres
públicos que antes (`order`, `order_pos`, `gpow_order_eq_id`, `order_ne_zero`,
`order_minimal`, `order_le_card`) — cero cambios para los consumidores (`Sylow.lean`).
`#print axioms Peano.Group.order` → **sin ningún axioma** (ni siquiera `propext`/
`Quot.sound`). `order_wop`/`choose_unique` eliminados del fichero.

Trampa nueva (además de la de `+`/`Sub.lean` ya documentada en C.4): `omega` en este
entorno **no** relaciona `Nat.pred`/`Nat.sub` escritos explícitamente con la resta real
(trata `Nat.sub x 1`/`x.pred` como átomos opacos, sin conectarlos a `x`) — hay que
evitarlos por completo y trabajar con `Nat.succ`/`Nat.exists_eq_succ_of_ne_zero` en su
lugar (cuantificar sobre el predecesor `j` en vez de sobre `v` con `v - 1`). También:
la táctica `by_contra` no existe en este entorno (sin Mathlib) — usar
`Decidable.byContradiction; intro h` (mismo patrón que C.1–C.3).

**Hallazgo 1 — RESUELTO (2026-07-13): `List.mem_erase_of_ne`/`List.length_erase_of_mem`
(núcleo de Lean 4, NO de este proyecto) dependen de `Classical.choice` en sí mismos.**
Verificado de forma completamente aislada: `#print axioms List.length_erase_of_mem` →
`[propext, Classical.choice, Quot.sound]`, sin código del proyecto de por medio. El
patrón que los usaba (`have nodup_sub_len : ... := by ... List.mem_erase_of_ne ...`,
"inline nodup_subset_length_le") estaba copiado y pegado en **9 sitios** de
`Sylow.lean` (bajo los nombres locales `nodup_sub_len` ×4, `nodup_sub_len_p` ×1,
`wieldandt_nodup_sub_len` ×1 con su propio `private theorem`, y `nodup_sub` ×2 dentro
de `nodup_same_card`/`nodup_same_card_ll`). **Arreglo aplicado**: ya existía en
`FSetFunction.lean:605` un `private theorem nodup_subset_length_le` que YA evitaba el
problema usando helpers propios y constructivos (`peano_mem_erase_of_ne`,
`peano_length_erase_of_mem`, ambos ya en el fichero, verificados sin
`Classical.choice`) — solo hacía falta quitarle `private` y exportarlo. Se hizo eso, y
se sustituyeron las 9 copias en `Sylow.lean` por llamadas directas a
`nodup_subset_length_le` (eliminando además ~180 líneas de código duplicado). Fichero
`FSetFunction.lean` también forma parte del commit de este hallazgo.

**Hallazgo 2 — RESUELTO (2026-07-13): `.choose`/`.choose_spec` (azúcar de
`Exists.choose`, que en Lean4 core ES `Classical.choose`) usado directamente en el
propio código del proyecto, en `wielandt_p_ndvd_r` (línea ~3870, dentro de
`h_p_dvd_orb`).** Grep de `Classical\.` no lo detecta (como con la táctica `classical`
en C.7) porque está escrito como `h.choose`/`h.choose_spec`, no como `Classical.choose`
literal. La eliminación de la existencial (`h_pow_dvd_stab : p^k ∣ ...`) para
reconstruir OTRA existencial (`pow_dvd_card ...`) es Prop→Prop, así que NO hace falta
choice: bastaba `obtain ⟨k, hk⟩ := h_pow_dvd_stab; exact h_stab_ndvd ⟨k, hk.symm⟩` en
vez de `⟨h_pow_dvd_stab.choose, h_pow_dvd_stab.choose_spec.symm⟩`. **Regla general para
el resto del fichero**: grep de `\.choose\b` (no solo `Classical\.`) antes de dar
cualquier fase por cerrada — ya se hizo una vez sobre `Sylow.lean` completo y no queda
ninguno, pero no se ha repetido sobre el resto del proyecto.

**Hallazgo 3 — RESUELTO (2026-07-13), trampa nueva importante para toda sesión futura:
`omega` cerrando un objetivo que NO es literalmente una proposición aritmética (p. ej.
un existencial `∃ y, ...`) invoca `Classical.choice` internamente**, aunque las
hipótesis en contexto sean aritméticas y la contradicción sea perfectamente
constructiva. Confirmado con un test aislado mínimo (sin ningún import del proyecto):
```
example {α} (b s : List α) (h1 : s.length + 1 + 1 = 1) : False := by omega
-- limpio: [propext, Quot.sound]
example {α} (b s : List α) (h1 : s.length + 1 + 1 = 1) : ∃ y : α, True := by omega
-- CONTAMINADO: [propext, Classical.choice, Quot.sound]
```
Se encontró en `wielandt_p_ndvd_r` (`h_stab_ne`, rama `cons b s` de un `cases` sobre
listas de longitud 1): `omega` se llamaba directamente sobre el objetivo real
(`∃ y, (conjAct.orb x).elems = [y]`), no sobre `False`. **Arreglo**: nunca llamar
`omega` (ni `decide`) directamente sobre un objetivo no aritmético para cerrarlo por
contradicción — primero obtener la negación aritmética por separado y combinar con
`absurd`: `exact absurd h1 (by omega)` en vez de `omega` a secas. Aplicado en
`wielandt_p_ndvd_r` línea ~3844. **Repetir este grep/patrón mental (buscar `omega`/
`decide` como última línea de una rama cuyo objetivo NO es `False` ni una desigualdad)
en el resto de `Sylow.lean` cuando se retome — es plausible que el mismo error exista
en otros sitios no visitados todavía** (el fichero tiene sublistsOfLength, McKay,
CosetAction, Correspondence, etc. con muchísimos `cases`/`omega` no auditados).

**Estado de `#print axioms` tras los 3 hallazgos (2026-07-13, fin de sesión)**:
- ✅ `Peano.Group.order` → sin axiomas.
- ✅ `Peano.Sylow.cauchy_minimal` → `[propext, Quot.sound]`.
- ✅ `wielandt_p_ndvd_r` (privado) → `[propext, Quot.sound]`.
- ✅ `sylow_center_step_wielandt` (privado) → `[propext, Quot.sound]`.
- ✅ `Peano.Cosets.lagrange` → `[propext, Quot.sound]`.
- ❌ **`Peano.Sylow.sylow_lift_from_cauchy` → SIGUE mostrando `Classical.choice`**,
  pese a que ya se comprobó que NINGUNA de sus piezas ya auditadas (arriba) lo
  contiene, y que `hC` es un parámetro abstracto (no se especializa a
  `cauchy_minimal` dentro de esta prueba, así que su contaminación no viene de ahí).
  Esto propaga a `sylow_first` y `sylow_third` (ambos siguen `Classical.choice`).
  **NO localizado todavía** — ver plan de continuación abajo.

### Fase C.9 — RESUELTA (2026-07-14): 4º y 5º hallazgo, `sylow_lift_from_cauchy`/`sylow_third` ya limpios

Siguiendo el "Plan exacto para continuar" de arriba: se comprobaron individualmente los
8 candidatos sin auditar (`sylow_center_step`, `subgroupToFinGroup`, `subgroupOfSubgroup`,
`improperSubgroup`, `mul_le_right`, `lt_of_le_of_ne`, `card_pos_of_mem_aux`,
`not_lt_zero`, `strongInductionOn`/`strongRecOn`) — **todos limpios**. La contaminación
de `sylow_lift_from_cauchy` no venía de ninguna pieza llamada, sino de su propio cuerpo
táctico.

**Hallazgo 4 — RESUELTO: `by_cases` sobre una existencial de `Subgroup` sin instancia
`Decidable` cae al fallback clásico, igual de invisible a grep que el patrón `omega`/
`decide` del Hallazgo 3 (misma familia de trampa, tácticas distintas).** En
`sylow_lift_from_cauchy` (dentro de `have step`), línea:
```lean
by_cases h_ex : ∃ M : Subgroup G0,
    M.carrier.card ≠ G0.carrier.card ∧ pow_dvd_card p (σ m) M.carrier
```
`Subgroup G0` no tiene manera automática de decidir esa existencial (no hay
`Fintype`/enumeración de subgrupos en el proyecto), así que `by_cases` usa
`Classical.propDecidable` en silencio. Confirmado en aislado: `by_cases h : P` sobre
un `opaque P : Prop` sin instancia → `[propext, Classical.choice, Quot.sound]`; el
resto de los `by_cases` del fichero (sobre igualdades de `ℕ₀`/listas, todas con
`DecidableEq` real) no lo hacen.

A diferencia de los Hallazgos 1–3 (sustitución mecánica de 1-2 líneas), este necesitaba
una **enumeración constructiva real de los subgrupos candidatos** — el proyecto ya tenía
la mitad de la infraestructura (`sublistsOfLength` sobre `G0.carrier.elems`, con
`_complete`/`_mem_sorted`/`_mem_sub`/`_mem_len` ya demostrados para el argumento de
Wielandt). Se añadió, en `Sylow.lean` justo después de `sublistsOfLength_card` (antes de
`wielandt_omega_card`, para que la declaración preceda su primer uso):

- `pow_dvd_card_iff_dvd` — reformula `pow_dvd_card` como `∣` ordinaria (incluso
  testigo, solo cambia el lado de la ecuación) para reutilizar el
  `Decidable (d ∣ n)` de `Primes.lean:396` (`decidableDvd`, ya existente).
- `subgroup_card_le` — `M.carrier.card ≤ G0.carrier.card` para cualquier subgrupo, vía
  `nodup_subset_length_le` (el mismo helper constructivo del Hallazgo 1) + conversión
  `Λ`/`Ψ`.
- `properSylowCandidateB` — predicado `Bool` decidible sobre `List ℕ₀`: ¿`G0.id ∈ l`,
  longitud ≠ `|G0|`, `p^(m+1) ∣ |l|`, y cerrado bajo `a·b⁻¹`?
- `allSublistsUpTo`/`allSublistsUpTo_sound`/`allSublistsUpTo_complete` — combina
  `sublistsOfLength` sobre todas las longitudes `0..|G0|` (`List.flatMap` +
  `List.range'`), con lema de completitud (cualquier sublista Sorted/subset/longitud
  acotada aparece en la enumeración).
- `findProperSylowCandidate` — `List.find?` sobre esa enumeración con el predicado Bool.
  `_some_spec` reconstruye el `Subgroup` testigo (vía `subgroup_of_op_inv_closed`, ya
  existente en `Group.lean:435`, criterio de un paso `a·b⁻¹ ∈ S`). `_none_spec` usa
  `List.find?_eq_none` + completitud para producir directamente `h_no_proper`.

En `sylow_lift_from_cauchy`, el `by_cases h_ex` se sustituyó por
`match hfind : findProperSylowCandidate G0 p m with | some l => ... | none => ...`
(un `match` sobre `Option`, siempre constructivo). Tras esto, `sylow_lift_from_cauchy` y
`sylow_first` quedaron en `[propext, Quot.sound]` — pero **`sylow_third` seguía
mostrando `Classical.choice`** (contaminación independiente, no heredada de
`sylow_lift_from_cauchy`).

**Hallazgo 5 — RESUELTO: `simp` genérico (sin lemas explícitos) sobre una hipótesis de
longitud de lista puede tirar de `Classical.choice` aunque el objetivo real de la meta
no tenga nada que ver.** Bisección (sorry sobre `have h_key` dentro de `sylow_third_mod`
→ se limpiaba; sorry sobre la mitad de su `cases l with | cons K₀ rest_l => ...` →
aislado a una única línea) localizó `Sylow.lean` (dentro de `h_orb_ne_one`, rama
`cons a rest_orb` → `cons b _`):

```lean
rw [h_orb_list] at h_len1
simp at h_len1   -- h_len1 : (a :: b :: _).length = 1, un absurdo aritmético
```

Confirmado en aislado (mínimo, sin imports del proyecto):

```lean
example (a b : Nat) (rest_orb : List Nat) (h_len1 : (a :: b :: rest_orb).length = 1) :
    True := by simp at h_len1
-- [propext, Classical.choice, Quot.sound] — el mismo objetivo con `omega` en vez de
-- `simp` (tras `simp only [List.length_cons]`) da [propext, Quot.sound]: limpio.
```

Arreglo: `simp only [List.length_cons] at h_len1; exact absurd h_len1 (by omega)` — el
mismo patrón del Hallazgo 3 (aislar la contradicción aritmética con `omega`/`absurd` en
vez de dejar que una táctica genérica cierre un objetivo no aritmético directamente),
aplicado esta vez a `simp` en vez de a `omega`/`decide` directo. **Trampa general
actualizada para toda sesión futura: no es solo `omega`/`decide` sobre un objetivo no
aritmético — `simp` sin argumentos también puede colarse por el mismo camino cuando
normaliza una hipótesis puramente aritmética (aquí de longitud de listas) usando algún
lema de su simp-set por defecto que internamente depende de choice. Mitigación: preferir
siempre `simp only [lemas explícitos]` seguido de `omega`/`exact absurd _ (by omega)`
frente a `simp`/`omega` a secas cuando se está cerrando una rama por contradicción
aritmética.**

**Estado final verificado (2026-07-14)**: `Group.order` (sin axiomas), `cauchy_minimal`,
`sylow_lift_from_cauchy`, `sylow_first`, `sylow_second`, `sylow_third` — los 6 en
`[propext, Quot.sound]` o menos, **cero `Classical.choice`**. `lake build` completo
(73 jobs) + `check-sorry.bash` limpios. Commiteado siguiendo el patrón
`feat(ADR-017): Fase C.9 ...`.

**Pendiente para retomar**: C.5 (retirar `Prelim/Classical.lean` — probable que ya no
tenga consumidores reales, verificar con
`grep -rl "Peano.Prelim.Classical\|choose_unique\|Classical\." Peano/`) y C.6
(`ConstructiveCheck.lean` exhaustivo, incluyendo añadir `#assert_constructive` para los
6 teoremas de Sylow ahora limpios y para las nuevas defs `properSylowCandidateB`/
`findProperSylowCandidate`/etc.).

Comando de verificación rápida usado toda la sesión (guardado en el scratchpad de la
sesión, recrear si hace falta):
```lean
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Sylow
import Peano.PeanoNat.Combinatorics.Group

#print axioms Peano.Group.order
#print axioms Peano.Sylow.cauchy_minimal
#print axioms Peano.Sylow.sylow_lift_from_cauchy
#print axioms Peano.Sylow.sylow_first
#print axioms Peano.Sylow.sylow_second
#print axioms Peano.Sylow.sylow_third
```

### Fase C.6 — ✅ COMPLETADA (2026-07-14): `ConstructiveCheck.lean` exhaustivo + 2 hallazgos nuevos

Objetivo: extender `ConstructiveCheck.lean` para cubrir **todo símbolo exportado
(`export X.Y (...)`) de todo módulo del proyecto**, no solo el subconjunto de
aritmética base cubierto hasta ahora. Metodología: extracción programática (script
Python) de los 69 bloques `export` en 57 ficheros bajo `Peano/` (1508 tokens crudos),
exclusión de las 14 excepciones ya documentadas (`Initiality.morph_fn*`/`peano_unique`,
`PureAxioms.PurePA`/`pa_parity`, `Prelim.choose*`), deduplicación global por nombre
completamente cualificado (para no repetir `#assert_constructive` sobre el mismo
símbolo cuando lo re-exportan varios ficheros — p. ej. `Isomorph.lean` y
`Decidable.lean` son ficheros "shim" que re-exportan símbolos ya declarados en
`Add.lean`/`Order.lean`/etc.; tras dedup contribuyeron 0 y 1 líneas nuevas
respectivamente), y verificación de la sutileza de doble-namespace mencionada en el
encargo (`FSet.lean` tiene un `namespace FSet` reabierto dentro de `namespace Peano`,
así que tokens ya vienen pre-cualificados como `FSet.ext` dentro del bloque `export
Peano.FSet (...)`, resolviendo a `Peano.FSet.FSet.ext` — la concatenación simple
`NS + "." + token` ya lo maneja bien sin necesidad de un caso especial).

**Resultado**: 1300 líneas `#assert_constructive` nuevas (de 1304 generadas, 4
excluidas por el hallazgo nuevo de abajo) añadidas a `ConstructiveCheck.lean`, sobre
53 módulos adicionales (arriba de los ~20 ya cubiertos), para un total de 1421
comprobaciones activas. Import nuevos: `Axioms`, `Arith`, `Fractions`, `Decidable`,
`Combinatorics.{Product,Perm,Group}`, `GroupTheory.*` (cadena completa hasta
`Sylow/Sylow.lean`), `ListsAndSets.{List,FSet,FSetFunction,EquivRel}`,
`NumberTheory.{Totient,Wilson,Fermat}`, `NumberSets`, `Foundation.{PeanoSystem,
Initiality}` (solo los símbolos constructivos de `Initiality`, no los 7 ya excluidos),
`Isomorph`, `Prelim`, `Prelim.ExistsUnique`. Ningún símbolo tuvo que saltarse por
fallo de resolución de nombre (`resolveGlobalConstNoOverload` los resolvió todos a la
primera tras el ajuste de dedup) — no hizo falta el mecanismo de "saltar con
comentario" previsto en el encargo para notaciones/símbolos no resolubles.

**Hallazgo nuevo 1 — RESUELTO: `String.drop`/`String.extract`/`String.toList` del
núcleo de Lean 4.31 dependen de `Classical.choice`.** Al comprobar por primera vez
`Peano.tupleRepr`/`Peano.natsTupleRepr`/`Peano.instHTupleReprCons`/
`Peano.List.instReprPeanoVal` (instancias `Repr` para tuplas, nunca antes cubiertas
por `ConstructiveCheck.lean`), aparecieron con `Classical.choice`. Bisección aislada
(sin ningún import del proyecto) confirmó que **no era código del proyecto**: `#print
axioms String.drop`/`String.extract`/`String.toList` → `[propext, Classical.choice,
Quot.sound]` en este toolchain (Lean 4.31.0, API `String.Slice`), mientras que
`String.append`/`String.push`/comparación `=`/interpolación `s!"..."` son limpios.
Causa: las tres instancias usaban `tailStr.drop 1` para recortar el corchete de
apertura de la representación de la cola antes de reconcatenar. Arreglo (en
`Peano/PeanoNat/Tuple.lean`, que SÍ estaba solo `locked`, no `frozen`): se introdujeron
`tupleReprInner`/`natsTupleReprInner` y un método `reprInner` en la clase
`HTupleRepr` que construyen el contenido **sin corchetes** de forma recursiva, y los
corchetes se añaden una única vez al envolver — eliminando por completo la necesidad
de `.drop`/`.extract`/`.toList` sobre `String`. Verificado:
`#print axioms Peano.tupleRepr` (y las otras 3) → `[propext]`, cero
`Classical.choice`. `Peano.List.instReprPeanoVal` se limpió automáticamente al
recompilar (llama a `tupleRepr`/`natsTupleRepr`). Build + `check-sorry.bash` limpios
tras el cambio.

**Hallazgo nuevo 2 — ✅ RESUELTO (2026-07-14, thaw autorizado por el usuario):
`Peano.Order.well_ordering_principle` usaba `by_cases` sobre un predicado `P`
arbitrario sin `[DecidablePred P]`.** En `Order.lean`, dentro de la inducción de
`well_ordering_principle`, la línea
`by_cases h_exists_le_n' : (∃ k', le₀ k' n' ∧ P k')` no tenía instancia `Decidable`
disponible porque `P : ℕ₀ → Prop` era completamente arbitrario (sin hipótesis de
decidibilidad en la firma) — caía a `Classical.propDecidable`. Contaminaba en cadena:
`Peano.WellFounded.well_ordering_principle` (llama a la de `Order.lean`) y
`Peano.Mul.exists_unique_mul_le_and_lt_succ_mul`/`exists_factor_of_mul_le` (llaman a
la de `WellFounded.lean` con predicados que, en la práctica, SÍ son decidibles —
`fun j => lt₀ m (mul j n)`). Diagnóstico y arreglo verificados primero **en
aislamiento** (fuera del árbol frozen, dos rondas de prueba: la primera con
`[DecidablePred P]` solo en la firma de `wop` sin una instancia real para la
existencial acotada seguía cayendo a `Classical.choice` — `decidableBExLe_of_bool`
es un `def`, no una `instance`, así que por sí solo NO lo recoge la búsqueda de
instancias; la segunda ronda, envolviéndolo en una `instance` real, dio
`[propext]` limpio incluso a través del patrón `let P := fun j => lt₀ m (mul j n)`
que usa `Mul.lean` — el `let` no bloquea la resolución de instancias como se temía).

Autorizado el `thaw --confirm` puntual de `Order.lean`/`WellFounded.lean`/`Mul.lean`
(estaban en `frozen_files.txt`, protección más fuerte que `locked_files.txt`). Cambios
aplicados:

- `Order.lean`: nueva `instance decidableExistsLe {P} [DecidablePred P] (n) :
  Decidable (∃ k, le₀ k n ∧ P k)` (envolviendo `decidableBExLe_of_bool` con
  `Pb := fun k => decide (P k)` y `h_iff := fun _ => Iff.of_eq decide_eq_true_eq`),
  reubicada — junto con `bexLe`/`bexLe_true_imp_exists`/`bexLe_false_imp_not_exists`/
  `decidableBExLe_of_bool`, que antes estaban declarados DESPUÉS de
  `well_ordering_principle` en el fichero — a ANTES de `well_ordering_principle`
  (Lean exige declaración antes de uso; verificado que ninguna de sus dependencias
  internas requería nada declarado entre medias). `well_ordering_principle` ganó
  `[DecidablePred P]` en la firma.
- `WellFounded.lean`: `well_ordering_principle` ganó `[DecidablePred P]` en la firma
  (una línea).
- `Mul.lean`: **sin cambios** — el `by_cases`/`let P := ...` existente recogió la
  nueva instancia automáticamente, exactamente como predijo la prueba aislada.

Verificado con `#print axioms` tras reconstruir: los 4 símbolos
(`Peano.Order.well_ordering_principle`, `Peano.WellFounded.well_ordering_principle`,
`Peano.Mul.exists_unique_mul_le_and_lt_succ_mul`, `Peano.Mul.exists_factor_of_mul_le`)
→ `[propext]`, sin `Classical.choice` ni siquiera `Quot.sound`. Los 3 ficheros se
volvieron a congelar (`freeze`) tras el arreglo. `#assert_constructive` añadido para
los 4 en `ConstructiveCheck.lean` (antes excluidos con comentario). **Con esto, la
única excepción de `Classical.*` que queda en todo el proyecto es la metateoría
documentada arriba (`Initiality.lean`/`PureAxioms.lean`, Fase C.5)** — no queda ningún
hallazgo pendiente de ADR-017.

**Estado final (2026-07-14)**: `lake build Peano.ConstructiveCheck` (1420 asserts) y
`lake build` completo (73 jobs) + `bash check-sorry.bash` — ambos limpios, 0 errores,
0 sorry.

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

**C.5 — Retirar `Prelim/Classical.lean`** ✅ CERRADA (2026-07-14, con excepción
documentada en vez de retirada completa). El grep
`grep -rl "Peano.Prelim.Classical\|choose_unique\|Classical\." Peano/` (ejecutado tras
cerrar C.9) **no** devolvió vacío: hay 2 consumidores reales,
`Foundation/Initiality.lean` (`morph_fn`/`morph_as_morph`/`peano_unique`) y
`Foundation/PureAxioms.lean` (`ψ`, vía `φ_surj`). Investigado su alcance: ambos prueban
resultados de unicidad/isomorfismo sobre `PeanoSystem` **abstractos** (no sobre `ℕ₀`
concreto) — inherentemente no constructivos, no hay nada que enumerar/acotar cuando se
cuantifica sobre un tipo arbitrario. **Verificado que la contaminación no se propaga**:
`grep` confirma que nada fuera de esos dos ficheros usa `morph_fn`/`peano_unique`/`ψ`/
`φ_ψ`/`ℕ₀_pa`, y que nada en todo el árbol importa el módulo paraguas
`Foundation/Foundation.lean` que los agrupa (junto a `CantorPairing`/`GodelBeta`, ya
constructivos). **Decisión**: aceptar `Prelim/Classical.lean` como la única excepción
intencional y documentada de ADR-017 — no se borra ni se retira el `import`. Comentario
de cabecera de `ConstructiveCheck.lean` actualizado para reflejar esta excepción
(reemplaza el comentario obsoleto que aún listaba `Action.lean`/`CosetAction.lean`/
`Sylow.lean`/`GodelBeta.lean` como no constructivos — ya estaban resueltos desde C.1–C.4
y C.9). Añadidos también `#assert_constructive` para `GodelBeta.encodeList`/
`encode_decode` (pendientes desde C.4, confirmados limpios).

**C.6 — Ampliar `Peano/ConstructiveCheck.lean`** ✅ COMPLETADA (2026-07-14) — ver la
sección dedicada más arriba ("Fase C.6") para el detalle completo.

**Pendiente, NO parte de C.6**: `Primes.lean` sigue con el orden de copyright/import
invertido (Fase A, punto marcado pendiente de decisión) — sigue frozen, no se ha
tocado; sin relación con la cobertura de `ConstructiveCheck.lean`.

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
~~C.4~~ ✅ → ~~C.9~~ ✅ (`Group.order` + `sylow_lift_from_cauchy`/`sylow_third`,
cerrada 2026-07-14) → ~~C.5~~ ✅ (excepción documentada, cerrada 2026-07-14) →
~~C.6~~ ✅ (cobertura exhaustiva + `well_ordering_principle`, cerrada 2026-07-14).
**Fase C completa — ADR-017 cerrado** (solo queda la excepción documentada de C.5).
Siguiente: Fase D (retomar feature-freeze + handoff a AczelSetTheory). Cada paso
debe cerrar con `lake build` limpio, `check-sorry.bash` en 0, **y una verificación
`#print axioms` del teorema tocado** antes de pasar al siguiente — no acumular cambios
sin verificar entre pasos, dado que `Sylow.lean` (C.3) es una prueba larga y frágil
(ver `feedback_lean4_tactics.md` en la memoria del asistente sobre las trampas de Lean
4.29+ con `rcases`/`cases`). **Recordatorio permanente**: antes de dar cualquier fase
de esta lista por cerrada, repetir también el grep de la palabra suelta `classical`
(no solo `Classical\.`) — C.7 demostró que el patrón oculto puede reaparecer en
cualquier fichero tocado por C.2–C.6.

### Fase D — Retomar feature-freeze + handoff a AczelSetTheory ✅ DECLARADA (2026-07-14, ver DECISIONS.md ADR-018)

Precondición: Fase C completa (0 usos de `Classical.*` fuera de, como mucho, un
`Prelim/Classical.lean` ya retirado de la cadena de imports) — **cumplida** (con la
excepción documentada y aceptada de C.5: `Prelim/Classical.lean` no se retiró, pero
está confirmado sin propagación fuera de `Initiality.lean`/`PureAxioms.lean`).

**Decisión tomada por el usuario (2026-07-14)**: Peano se declara `feature-frozen`,
cierre definitivo (ADR-018). `NEXT-STEPS.md` §G.2 marcado ✅ declarado, §G.3 (handoff)
es ahora el "siguiente paso activo" del proyecto — pero se ejecuta desde
`AczelSetTheory`, no desde este repo. El SHA de cierre para
`AczelSetTheory/lakefile.lean`'s `require Peano from git ... @ <sha>` es
`1e327533b6df7fbb02097ef99d605a865e601427` (verificar que está pusheado a
`origin/master` antes de usarlo). **La próxima sesión de trabajo matemático se abre en
`AczelSetTheory`, no en Peano** — este repo pasa a mantenimiento (correcciones,
toolchain, lemas menores pedidos por `AczelSetTheory`).
