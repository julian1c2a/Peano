# Thoughts — Peano

**Last updated:** 2026-04-08 21:00
**Author**: Julián Calderón Almendros

> This is an informal design journal. Record ideas, alternatives considered,
> open questions, and future directions here. Not normative — purely exploratory.
> Useful for AI context on "why" decisions were made.

---

## Design Philosophy

This project formalizes Peano arithmetic from scratch in Lean 4, deriving all
8 Peano axioms as theorems from the inductive type `ℕ₀`. No external dependencies
(not even Mathlib). The goal is a complete, self-contained arithmetic library
covering: order, arithmetic operations (add, sub, mul, div, mod, pow), primes,
factorial, binomial coefficients, and the Newton binomial theorem.

---

## Ideas and Alternatives

### 2026-04-08 — Infrastructure modernization

Migrated from the old `.bat`-based freeze system to the template-standard
`git-lock.bash` system with two levels (lock + freeze), pre-commit hook, and
Makefile integration. The old system only had freeze/unfreeze with no
session-based locking.

---

## Open Questions

- [ ] Should export blocks in Peano.lean be migrated to individual leaf modules per §30?
- [ ] Is the Peano/ vs Peano namespace mismatch worth resolving?

---

## Lessons Learned

### Inductive Type Approach

- Defining `ℕ₀` as an inductive type gives all Peano axioms for free as proven theorems
- The recursion principle is the most powerful tool — all arithmetic flows from it
- Well-foundedness proofs are needed for termination of recursive definitions

### Module Organization

- The linear dependency chain (Axioms → Order → Arithmetic → Advanced) works well
- Each module builds strictly on previous ones — no circular dependencies
- 16 modules is manageable without subdirectories

### Documentation

- REFERENCE.md must be self-sufficient for AI assistants
- The "project" protocol (AI-GUIDE.md §12) prevents documentation drift

---

## Future Directions

- Integer extension (ℤ from ℕ₀)
- Rational numbers (ℚ from ℤ)
- Connection to Lean 4's native `Nat` type
