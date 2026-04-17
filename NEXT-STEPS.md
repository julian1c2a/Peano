# Next Steps — Peano

**Last updated:** 2026-04-17
**Author**: Julián Calderón Almendros

> Plan operativo simplificado: solo estado actual, bloqueos reales y siguientes pasos ejecutables.

---

## 1. Estado Actual (snapshot)

- Build global: OK (51 jobs).
- Errores: 0.
- Sorries activos: 6.
- Warnings no-sorry: 3 (variables no usadas en Group.lean).

### 1.1. Completado recientemente

- `FSet.eq_of_mem_iff` en `ListsAndSets/FSet.lean`.
- `card_eq_mul_of_uniform_fibers` en `ListsAndSets/FSetFunction.lean`.
- Proyección en `REFERENCE.md` actualizada al estado de ambos módulos.

### 1.2. Sorries vigentes (fuente de verdad)

- `Combinatorics/GroupTheory/Sylow/Cosets.lean`: 1 (`lagrange`).
- `Combinatorics/GroupTheory/Action.lean`: 2 (`orbit_stabilizer`, `orbits_partition`).
- `Combinatorics/GroupTheory/Sylow/Sylow.lean`: 3.

---

## 2. Prioridad Inmediata (P0)

## 2.1. Cerrar `lagrange` en Cosets

Objetivo:
- Probar `∃ k, mul H.carrier.card k = G.carrier.card`.

Estrategia:
- Definir/aplicar el mapa a clases laterales.
- Usar `card_eq_mul_of_uniform_fibers` con fibras uniformes de tamaño `|H|`.
- Obtener `k = |G/H|`.

Criterio de salida:
- `Cosets.lean` sin sorry.

## 2.2. Cerrar `Action.lean`

Objetivo:
- Resolver `orbit_stabilizer`.
- Resolver rama restante de `orbits_partition`.

Dependencia:
- Consumir `lagrange` ya cerrado.

Criterio de salida:
- `Action.lean` sin sorry.

## 2.3. Cerrar `Sylow.lean`

Objetivo:
- Eliminar 3 sorrys restantes.

Dependencia:
- `Cosets.lean` y `Action.lean` completos.

Criterio de salida:
- `Sylow.lean` sin sorry.

---

## 3. Documentación (P1)

- Mantener `REFERENCE.md` sincronizado cada vez que se cierre un sorry en módulos de grupos.
- Actualizar `CHANGELOG.md` por lote de cierres (Cosets/Action/Sylow).
- Actualizar `CURRENT-STATUS-PROJECT.md` al pasar de 6 → 0 sorry.

---

## 4. Checklist de ejecución

- [x] `FSet.eq_of_mem_iff` en FSet.lean
- [x] `card_eq_mul_of_uniform_fibers` en FSetFunction.lean
- [x] Verificar `lake build`
- [ ] Cerrar `lagrange` (Cosets)
- [ ] Cerrar `orbit_stabilizer` y `orbits_partition` (Action)
- [ ] Cerrar 3 sorrys de Sylow
- [ ] Dejar build con 0 sorry
- [ ] Sincronizar `REFERENCE.md`, `CHANGELOG.md`, `CURRENT-STATUS-PROJECT.md`

---

## 5. Comandos de control

- `lake build`
- `lake build 2>&1 | Select-String -Pattern "error|sorry|warning"`
- `grep -n "sorry" Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean`
- `grep -n "sorry" Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- `grep -n "sorry" Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
