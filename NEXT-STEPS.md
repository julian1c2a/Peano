# Next Steps — Peano

**Last updated:** 2026-04-22
**Author**: Julián Calderón Almendros

> Plan operativo simplificado: solo estado actual, bloqueos reales y siguientes pasos ejecutables.

---

## 1. Estado Actual (snapshot)

- Build global: OK (52 jobs).
- Errores: 0.
- Sorries activos: 4 (todos en `Sylow.lean`).
- `check-sorry.bash` total: 8 (4 Sylow + 2 en Perm.lean comentarios + 2 en Primes.lean comentarios).
- Warnings no-sorry: 4 (1 `unused variable` en Sylow.lean, 3 en Group.lean).

### 1.1. Completado recientemente (sesión 2026-04-22)

- **`mckay_orbit_remove` demostrado sin sorry** (`Sylow.lean`):
  - Dado `v ∈ S` no fijo, extrae la órbita de tamaño `p` bajo `rotateVector` y devuelve `S' = S \ orbit(v)` con `S'.Nodup`, cierre bajo rotación, `|S| = |S'| + p`, y `fix(S) = fix(S')`.
  - Sub-lemas internos completos: `orb_inj`, `orbit_no_fixed`, `rl_inj`, `orbit_preimage`, `orbit_closed_rv`, `nodup_sub_len`, `filter_part`.
  - `mckay_orbit_count` también compila limpiamente (ya estaba estructurado, usa `mckay_orbit_remove`).

### 1.1. Completado recientemente (sesión 2026-04-20)

- **Infraestructura McKay en `Sylow.lean`**: Creado el tipo `Vector` (longitud fija), `allVectorsList` (generador de combinaciones), y probada la preservación (`mckayShiftList_mem`) e inyectividad (`mckayShiftList_inj`) de la operación de rotación de McKay sobre listas.
- Errores de compilación resueltos; el archivo compila limpiamente a falta de los sorries lógicos.

### 1.1. Completado recientemente (sesión 2026-04-19)

- Todos los lemas privados de `cauchy_minimal` en `Sylow.lean` — **cerrados sin sorry**:
  - `card_pos_of_mem_aux`, `order_dvd_of_pow_eq_id`, `order_eq_prime_of_pow`, `gpow_lt_p_mem_cyclic`, `cyclicSubgroup_card_eq_prime`.
  - Biyección `Fin₀Set(p) → ⟨g⟩` formalizada completamente (inyectividad + sobreyectividad).
- Infraestructura Sylow.lean saneada: `open Peano.Sub`, `private abbrev Prime`, correcciones de `by_contra`, `rcases rfl`, orientación de igualdades.
- `actualiza doc` añadido como comando en AI-GUIDE.md § 29.

### 1.1. Completado en sesiones anteriores (2026-04-17–18)

- `FSet.eq_of_mem_iff` en `ListsAndSets/FSet.lean`.
- `card_eq_mul_of_uniform_fibers` en `ListsAndSets/FSetFunction.lean`.
- `lagrange` en `Combinatorics/GroupTheory/Sylow/Cosets.lean` — **cerrado**.
- `orbit_stabilizer` y `orbits_partition` en `Combinatorics/GroupTheory/Action.lean` — **cerrados**.
- `cauchy_minimal_axiom` convertido de `axiom` a `sorry` (trazable en build).

### 1.2. Sorries vigentes (fuente de verdad)

Todos en `Combinatorics/GroupTheory/Sylow/Sylow.lean`:

| Línea | Teorema | Estrategia conocida |
|---|---|---|
| ~1190 | `mckay_p_dvd_powEqId` | Conectar `mckay_orbit_count` (probado) con el conteo de `{g ∈ G | g^p = e}` sobre G^p |
| ~1273 | `sylow_lift_from_cauchy` | Inducción en m; normalizar con cociente G/K, aplicar Cauchy |
| ~1307 | `sylow_second` | Acción de H sobre G/K por multiplicación izquierda; conteo mod p |
| ~1324 | `sylow_third` | Acción por conjugación + Sylow II + conteo mod p |

---

## 2. Prioridad Inmediata (P0) — Cerrar Sylow.lean

### 2.1. `cauchy_minimal` — **primer objetivo**

Objetivo: Terminar de probar `mckay_p_dvd_powEqId` para cerrar el teorema de Cauchy.

Estrategia:

- Ya tenemos `allVectorsList` que genera las tuplas de longitud $p-1$, tamaño $|G|^{p-1}$.
- Ya tenemos `mckayShiftList` que opera sobre estas tuplas.
- Declarar la permutación `Perm` oficial instanciándola con `mckayShiftList`.
- Probar que aplicar la permutación $p$ veces es la identidad.
- Usar Ecuación de Clases/Órbitas para el conteo módulo $p$.

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
- [x] `mckay_orbit_remove` y `mckay_orbit_count` — cerrados (2026-04-22)
- [ ] Cerrar `mckay_p_dvd_powEqId` (conecta `mckay_orbit_count` con el conteo sobre G^p)
- [ ] Cerrar `cauchy_minimal` (depende de `mckay_p_dvd_powEqId`)
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
