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

### Fase C — Eliminación de `Classical.*` (núcleo de ADR-017, PENDIENTE)

Alcance verificado por grep exhaustivo (ver ADR-017) — solo 3 focos, no los ~12
ficheros que sugería la documentación histórica.

**C.1 — `Combinatorics/GroupTheory/Action.lean`** (2 usos de `Classical.em`, líneas
247 y 300): ambos son `rcases Classical.em (∃ z, ...)` sobre predicados acerca de
`FSet`/`FSetFunction`. Como el dominio es un `FSet` finito con `DecidableEq`, el
predicado `∃ z, z ∈ (ψ.orb x).elems ∧ z ∈ (ψ.orb y).elems` debería admitir una
instancia `Decidable` (búsqueda finita sobre una lista) — reemplazar
`Classical.em P` por `by_cases h : P` una vez exista o se derive esa instancia.

**C.2 — `Sylow/CosetAction.lean`** (1 uso, línea 439): mismo patrón,
`∀ g ∈ G.carrier.elems, α.act g x₀ = x₀` sobre un `FSet` finito — decidible en
principio (cuantificador acotado sobre una lista finita con igualdad decidible).

**C.3 — `Sylow/Sylow.lean`** (2 `Classical.em` + 5 `Classical.byContradiction`,
líneas 2913–4151, 4920–4922): el módulo más grande y más delicado — es el que cierra
los tres teoremas de Sylow, está **bloqueado pero no congelado**. Cada
`Classical.byContradiction; intro h` es candidato a convertirse en
`by_cases h : P` seguido de refutar la rama `¬P` — mecánico una vez C.1/C.2 sienten el
patrón, pero requiere re-verificar cada prueba tras el cambio (no es un
find-and-replace seguro a ciegas).

**C.4 — `Foundation/GodelBeta.lean`** (`Classical.choose`/`choose_spec`, líneas
587–588 y 636–639): reconstrucción de la función β de Gödel. Seguir el precedente ya
sentado por `CantorPairing.antidiag` (ya constructivo, vía búsqueda acotada/recursión
bien fundada en vez de `choose_unique`) — el rango de búsqueda para el testigo de
`godel_beta_seq` es finito y acotado por construcción, así que un `Nat.rec`/
`WellFounded.fix` explícito debería reemplazar el `choose`.

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

**Orden sugerido**: C.1 → C.2 (mismo patrón, más simple primero) → C.4 (independiente,
se puede paralelizar) → C.3 (el más grande, dejarlo para cuando el patrón esté rodado)
→ C.5 → C.6. Cada paso debe cerrar con `lake build` limpio y `check-sorry.bash` en 0
antes de pasar al siguiente — no acumular cambios sin verificar entre pasos, dado que
`Sylow.lean` (C.3) es una prueba larga y frágil (ver `feedback_lean4_tactics.md` en la
memoria del asistente sobre las trampas de Lean 4.29+ con `rcases`/`cases`).

### Fase D — Retomar feature-freeze + handoff a AczelSetTheory (bloqueada por C)

Precondición: Fase C completa (0 usos de `Classical.*` fuera de, como mucho, un
`Prelim/Classical.lean` ya retirado de la cadena de imports). Pasos: los ya
documentados en `NEXT-STEPS.md` §G.2–G.3, sin cambios — el criterio de feature-freeze
gana ahora una condición adicional: "0 `Classical.*` en el árbol de producción".
