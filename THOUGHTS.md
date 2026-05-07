# Thoughts — Peano

**Last updated:** 2026-05-07
*Author: Julián Calderón Almendros

> This is an informal design journal. Records ideas, open questions, and lessons
> learned. Not normative — purely exploratory. Useful for AI context on "why"
> decisions were made.
>
> **Branch status**: This branch finalizes when Sylow.lean is complete (0 private
> axioms) and documentation is migrated to `/doc/`. Phase G.4 (AczelSetTheory
> handoff) follows after freezing and merging.

---

## Design Philosophy

This project formalizes Peano arithmetic from scratch in Lean 4, deriving all
8 Peano axioms as theorems from the inductive type `ℕ₀`. No external dependencies
(not even Mathlib). The goal is a complete, self-contained arithmetic library
covering: order, arithmetic operations (add, sub, mul, div, mod, pow), primes,
factorial, binomial coefficients, Newton binomial theorem, group theory, and the
three Sylow theorems.

---

## Open Questions

- [ ] Should export blocks in Peano.lean be migrated to individual leaf modules per §30?
- [ ] Is the Peano/ vs Peano namespace mismatch worth resolving?
- [ ] Should FSetFunction.lean (~1550 lines, ~92 declarations) be split into smaller modules?
- [ ] How to approach `sylow_third_mod` and `sylow_third_dvd`? (requires constructing
  `FinGroup (Subgroup G)` — infrastructure now available via Phase 5, but the concrete
  `instance` still needs to be built)

**Resolved questions:**

- ~~How to approach the remaining sorry in group theory modules~~ → All 3 Sylow theorems
  closed; 3 private axioms remain (`wielandt_p_ndvd_r`, `sylow_third_mod`, `sylow_third_dvd`).
- ~~FSet design: Quotient vs sorted list~~ → Sorted list (ADR-007).
- ~~FinGroup polymorphism approach~~ → Phase 5 COMPLETADA (2026-05-07): pleno polimorfismo
  sobre `{α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]` en toda la infraestructura.
- ~~Phase F Foundation (CantorPairing + GodelBeta)~~ → Phase F completamente terminada
  (2026-05-02): F.1 CantorPairing ✅, F.2 GodelBeta ✅, F.3 paraguas Foundation.lean ✅.

---

- Gap 1: p_group_center_nontrivial (ecuación de clases) — hay que    probar en NormalSubgroup.lean — ✅ COMPLETADO (2026-05-07)
- Gap 2: preimage_subgroup_card — ✅ COMPLETADO (2026-05-07): `CorrespondenceTheorem.lean` exporta `preimage_subgroup_card`
- Gap 3: añadir parámetro HI (IH fuerte) a wielandt_p_ndvd_r : *HACIÉNDOSE* — requiere refactorización de Sylow.lean para pasar HI a través de sylow_center_step_wielandt → coset_conjugate_exists → wielandt_p_ndvd_r; el caso succ m' es bloqueado por la falta de soporte de grupos cociente en FinGroup (Phase 5).

---

## Architectural decisions — AczelSetTheory (2026-05-02)

**¿Puede AczelSetTheory definir `Nat` a partir de `HFSet` solo?**

Sí: una vez que el embedding Peano → Aczel es lógicamente completo, el desarrollo
matemático nuevo ocurre en AczelSetTheory — por ejemplo `def Nat := List Unit` o
directamente sobre `HFSet`. Todo lo computable en Peano es computable en AczelSetTheory;
Peano pasa a modo mantenimiento.

**Consecuencia para este proyecto**: solo quedan los coletazos abiertos (3 axiomas
privados en Sylow.lean) y la migración de documentación a `/doc/`. El desarrollo
matemático principal pasa a AczelSetTheory.

**Documentación**: La migración de `REFERENCE.md` monolítico a `REFERENCE-{Tema}.md`
en árbol bajo `/doc/` es importante para que los asistentes de IA puedan navegar sin
perder contexto. Cada nodo de documentación debe ofrecer enlaces hacia los nodos
adyacentes.

---

## Lessons Learned

### Inductive Type Approach

- Defining `ℕ₀` as an inductive type gives all Peano axioms for free as proven theorems
- The recursion principle is the most powerful tool — all arithmetic flows from it
- Well-foundedness proofs are needed for termination of recursive definitions

### Module Organization

- The linear dependency chain (Axioms → Order → Arithmetic → Advanced) works well
- Each module builds strictly on previous ones — no circular dependencies
- 64 build jobs; `FSetFunction.lean` is the largest module (~1500 lines, ~92 exports)

### Documentation

- REFERENCE.md must be self-sufficient for AI assistants
- The "project" protocol (AI-GUIDE.md §12) prevents documentation drift

### Isomorfismos Nat↔ℕ₀ (2026-04-09)

- **`Coe Nat ℕ₀` causa ambigüedad de operadores**: `(Ψ x + 1) * Ψ y` es ambiguo entre
  ops de Peano y ops de Nat. Solución: evitar `show` con aritmética infix; usar rewrites
  explícitos (`Nat.add_mul`, `Nat.one_mul`) o calificadores (`Nat.div`).
- **Patrón `congrArg Ψ` + rewrite en hipótesis**: Cuando `rw [isomorph_Ψ_add]` en el
  objetivo reescribe al revés (por la coerción), transportar la hipótesis con
  `congrArg Ψ h_eq` y luego `rw [...] at h_transported`.
- **`isomorph_Ψ_mod` requiere `m ≠ 𝟘`**: Peano define `mod n 𝟘 = 𝟘` pero
  Lean core define `Nat.mod n 0 = n`. No hay isomorfismo incondicionado.
- **`omega` no resuelve div/mod no-lineales**: Hay que usar `Nat.div_eq_of_lt_le` explícitamente.

### Foundation/GodelBeta.lean (2026-05-02)

- **`List.map_congr` no existe en Lean 4 core**: el nombre correcto es `List.map_congr_left`.
- **`isomorph_Λ_le i m : le₀ (Λ i) (Λ m) ↔ i ≤ m`**: la dirección `.mp` va de `i ≤ m` a
  `le₀ (Λ i) (Λ m)`, no al revés. Confundir la dirección bloquea la prueba silenciosamente.
- **`set` tactic no disponible**: en Lean 4 core sin Mathlib, usar `let`/`have` en su lugar.
- **`List.range_succ_eq_map`**: existe en Lean 4 core; permite demostrar `list_map_getD_range`
  por inducción con `simp [List.range_succ_eq_map]` (cierra automáticamente).
- **`List.length_pos.mpr` no existe en este contexto**: usar `Nat.succ_pos xs.length`.
- **`noncomputable def` + `Classical.choice`**: la no-computabilidad de `encodeList` es
  inevitable; el `decodeList` sí es computable (puro `map` sobre `List.range`).

### Phase 5 — Polimorfismo completo de FinGroup/FSet (2026-05-07)

Refactorización completa de `Action.lean`, `Cosets.lean`, `FSet.lean`, `Group.lean`
y nuevo módulo `EquivRel.lean`. Lecciones:

- **`sorted_nodup_unique_list'` debe ir ANTES de `namespace FSet`**: en Lean 4.29.0
  sin Mathlib, las `private theorem` con pattern matching estilo ecuación no se ven
  dentro del namespace si se definen después de abrirlo.
- **`[DecidableEq α]` es obligatorio en lemas de unicidad de listas ordenadas**: la
  prueba de igualdad por extensión requiere comparar elementos por igualdad.
- **`FSet.eq_of_mem_iff'` vs `FSet.eq_of_mem_iff`**: la versión anterior era específica
  para `ℕ₀`. Fue necesario añadir `eq_of_mem_iff'` genérico para el refactor polimórfico.
- **Instancias de `Subgroup`**: para `FSet (Subgroup G)` hacen falta
  `instDecidableEqSubgroup`, `instLTSubgroup`, `instStrictLinearOrderSubgroup` en `Group.lean`.
  La igualdad se basa en `carrier`; el orden lexicográfico sobre `elems` es suficiente.
- **`▸`-chaining en `htail` causa type mismatch**: al reescribir con `▸` en cadena,
  el tipo del goal puede quedar en forma reducida que no coincide con la siguiente reescritura.
  Solución: usar `have h_lt : x < z := ...; rw [h_eq, hxy] at h_lt; exact absurd h_lt (slo.irrefl y)`.

### Wielandt / Sylow (2026-05-06 – 2026-05-07)

- **`well_founded_lt.induction`**: la forma correcta de hacer inducción bien fundada
  sobre `ℕ₀` es via `well_founded_lt.induction`. El `ih` resultante tiene la forma
  `∀ m, lt₀ m n → P m`, lo que requiere proporcionar la prueba de `lt₀` explícitamente.
- **Rama no-fija con `wielandt_orbit_remove`**: extrae exactamente p elementos de Ω
  (la p-órbita de S), reduciendo el tamaño de la lista. Garantiza terminación de la
  inducción: en la rama no-fija, `lengthₚ Ω_rem = lengthₚ Ω − p < n`.
- **`calc` con `← add_assoc` + `← mul_succ`**: cierre algebraico del caso no-fijo:
  `add (mul p k') p = mul p (σ k')` via `← mul_succ`.
- **6ª propiedad de `wielandt_orbit_remove`**: se necesita `∀ T, T ∈ Ω' → T ∈ Ω`
  (inclusión) para propagar `hΩ_sorted`/`hΩ_mem` al IH de `wielandt_orbit_partition`.
- **`bezout_natform`**: devuelve identidad de Bézout en forma `∃ bn bm, 𝟙 = sub (mul bn k) (mul bm p) ∨ ...`.
  Para usar en `wieldandtAct_gpow_fixed_of_gcd_one` hay que tratar ambas ramas del `rcases`
  simétricamente.
- **Lean 4.29.0 trampas en inducción sobre listas**: `rcases h with rfl` sobre `a = x`
  (variable de inducción) puede eliminar `x` en lugar de `a`; usar `cases` + `rw` explícito.
  `congrArg σ` falla porque `σ` es notación; usar `rw [ih ...]` directamente.
