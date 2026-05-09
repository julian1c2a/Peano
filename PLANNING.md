# PLANNING — Estado del proyecto

*Autor: Julián Calderón Almendros*
*Última actualización: 2026-05-09*

---

## Estado actual (2026-05-09)

`lake build` compila con **0 errores**, **0 sorry** y **0 private axioms no intencionales**
en todo el proyecto (37 jobs).

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
| `CantorPairing.lean` | ✅ |
| `GodelBeta.lean` | ✅ (usa Classical.choose — intencional) |
| `Foundation.lean` paraguas | ✅ |

---

## Trabajo pendiente

### P.1 — Actualizar y ampliar `ConstructiveCheck.lean`

Añadir `#assert_constructive` para todos los módulos de aritmética,
NumberTheory y Combinatorics pura. Documentar los módulos explícitamente
no constructivos (GroupTheory, GodelBeta, FSet/FSetFunction).

Estado: **EN CURSO** (2026-05-09).

### P.2 — Migración de documentación a `/doc/`

Ver `NEXT-STEPS.md` §G.1 para el plan detallado.
No bloquea ni es bloqueada por ninguna tarea matemática.

### P.3 — Criterio de feature-freeze y handoff a AczelSetTheory

Ver `NEXT-STEPS.md` §G.2–G.3.
Precondición: P.2 completada.
