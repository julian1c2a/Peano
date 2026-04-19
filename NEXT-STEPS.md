# Next Steps — Peano

**Last updated:** 2026-04-19
**Author**: Julián Calderón Almendros

> Plan operativo simplificado: solo estado actual, bloqueos reales y siguientes pasos ejecutables.

---

## 1. Estado Actual (snapshot)

- Build global: OK (51 jobs).
- Errores: 0.
- Sorries activos: 4 (todos en `Sylow.lean`).
- Warnings no-sorry: 3 (variables no usadas en Group.lean).

### 1.1. Completado recientemente (sesión 2026-04-17–19)

- `FSet.eq_of_mem_iff` en `ListsAndSets/FSet.lean`.
- `card_eq_mul_of_uniform_fibers` en `ListsAndSets/FSetFunction.lean`.
- `lagrange` en `Combinatorics/GroupTheory/Sylow/Cosets.lean` — **cerrado**.
- `orbit_stabilizer` y `orbits_partition` en `Combinatorics/GroupTheory/Action.lean` — **cerrados**.
- `cauchy_minimal_axiom` convertido de `axiom` a `sorry` (trazable en build).

### 1.2. Sorries vigentes (fuente de verdad)

Todos en `Combinatorics/GroupTheory/Sylow/Sylow.lean`:

| Línea | Teorema | Estrategia conocida |
|---|---|---|
| ~93 | `cauchy_minimal` | G actúa sobre p-tuplos con producto e; órbitas de tamaño 1 ó p |
| ~110 | `sylow_lift_from_cauchy` | Inducción en m; normalizar con cociente G/K, aplicar Cauchy |
| ~122 | `sylow_second` | Acción de H sobre G/K por multiplicación izquierda; conteo mod p |
| ~142 | `sylow_third` | Acción por conjugación + Sylow II + conteo mod p |

---

## 2. Prioridad Inmediata (P0) — Cerrar Sylow.lean

### 2.1. `cauchy_minimal` — **primer objetivo**

Objetivo: `∃ K : Subgroup G, K.carrier.card = p`.

Estrategia:

- Construir el conjunto `T = { (g₁,…,gₚ) ∈ Gᵖ | g₁·…·gₚ = e }`. `|T| = |G|^(p-1)` que es divisible por `p`.
- G actúa sobre T por rotación cíclica de la tupla.
- Las órbitas tienen tamaño 1 ó p (p primo, órden de la acción divide a p).
- `|T| ≡ #{órbitas de tamaño 1} (mod p)` → al menos p órbitas fijas → p ≥ 2 → existe una fija con `g ≠ e` → ese g tiene orden p → genera un subgrupo de orden p.

Herramientas disponibles:

- `Action.lean` (órbitas, tamaños) ✅
- `FSetFunction` (conteo, fibras) ✅
- `Cosets.lean` (Lagrange) ✅

Criterio de salida: `cauchy_minimal` sin sorry.

### 2.2. `sylow_lift_from_cauchy`

Dependencia: `cauchy_minimal` cerrado.

Estrategia:

- Inducción sobre m.
- Dado H de orden pᵐ, N(H)/H tiene orden divisible por p (vía Lagrange + hipótesis p^(m+1) | |G|).
- Cauchy en N(H)/H da K/H de orden p → K de orden pᵐ⁺¹.

### 2.3. `sylow_second`

Dependencia: Sylow I completo, acciones sobre G/K disponibles.

### 2.4. `sylow_third`

Dependencia: `sylow_second`.

---

## 3. Documentación (P1)

- Actualizar `CURRENT-STATUS-PROJECT.md` al pasar de 4 → 0 sorry.
- Actualizar `CHANGELOG.md` por lote de cierres de Sylow.
- Mantener `REFERENCE.md` sincronizado.

---

## 4. Checklist de ejecución

- [x] `FSet.eq_of_mem_iff` en FSet.lean
- [x] `card_eq_mul_of_uniform_fibers` en FSetFunction.lean
- [x] Cerrar `lagrange` (Cosets)
- [x] Cerrar `orbit_stabilizer` y `orbits_partition` (Action)
- [x] `cauchy_minimal_axiom` → sorry (trazable)
- [ ] Cerrar `cauchy_minimal` (Sylow/cauchy)
- [ ] Cerrar `sylow_lift_from_cauchy`
- [ ] Cerrar `sylow_second`
- [ ] Cerrar `sylow_third`
- [ ] Dejar build con 0 sorry
- [ ] Sincronizar `REFERENCE.md`, `CHANGELOG.md`, `CURRENT-STATUS-PROJECT.md`

---

## 5. Comandos de control

- `lake build`
- `lake build 2>&1 | Select-String -Pattern "error|sorry|warning"`
- `Get-ChildItem -Recurse -Filter "*.lean" -Path "Peano" | Select-String -Pattern "^\s+sorry"`
- `grep -n "sorry" Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`

<!-- AUTO-UPDATE-2026-04-17-START -->
## Actualizacion de estado - 2026-04-17

- Estado del build: compila en el estado actual de la rama makingdecidable.
- Lagrange: cerrado en Sylow/Cosets con conteo por fibras y clases de cosets.
- GroupAction: sorries cerrados en orbit_stabilizer y orbits_partition.
- Sylow I: caso base n=0 cerrado; estructura separada en paso de Cauchy y paso de elevacion.
- Nota temporal: cauchy_minimal se apoya en un axioma explicito cauchy_minimal_axiom para continuar el desarrollo.
- Pendientes activos en Sylow: sylow_lift_from_cauchy, sylow_second, sylow_third.
- Objetivo proximo: reemplazar cauchy_minimal_axiom por demostracion interna y completar Sylow I.

<!-- AUTO-UPDATE-2026-04-17-END -->
