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

**Resolved questions:**

- ~~How to approach the remaining sorry in group theory modules~~ → All 3 Sylow theorems
  closed; 3 private axioms remain (`wielandt_p_ndvd_r`, `sylow_third_mod`, `sylow_third_dvd`).
- ~~FSet design: Quotient vs sorted list~~ → Sorted list (ADR-007).
- ~~FinGroup polymorphism approach~~ → Phase 5 COMPLETADA (2026-05-07): pleno polimorfismo
  sobre `{α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]` en toda la infraestructura.
- ~~Phase F Foundation (CantorPairing + GodelBeta)~~ → Phase F completamente terminada
  (2026-05-02): F.1 CantorPairing ✅, F.2 GodelBeta ✅, F.3 paraguas Foundation.lean ✅.

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

### Como probar el lema de Zasenhauss

Digamos que tenemos un grupo (notación multiplicativa) `G` y dos subgrupos `H` y `K` de `G`. Además tenemos un subgrupo normal de `H`, digamos `N`, y otros subgrupo normal de `K`, digamos `M`.

En símbolos:

- `G` es un grupo
- `H ≤ G` y `K ≤ G`
- `N ⊲ H` y `M ⊲ K`

El lema de Zasenhauss dice:

$$
\begin{aligned}
& N \cap K \quad ⊴ \quad H \cap K \\
& H \cap M \quad ⊴ \quad H \cap K \\
& (N \cap K)(H \cap M) \quad ⊴ \quad H \cap K \\
& N (H ∩ M) \quad ⊴ \quad N (H ∩ K) \\
& M (N ∩ K) \quad ⊴ \quad M (H ∩ K) \\
& \frac {N (H ∩ K)} {N (H ∩ M)} \quad ≅ \quad \frac {H ∩ K} {(N \cap K)(H \cap M)}  \quad ≅ \quad \frac {M (H ∩ K)} {M (N ∩ K)}
\end{aligned}
$$
