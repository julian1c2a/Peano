# Development Workflow

**Author**: Julián Calderón Almendros
*Last updated: 2026-04-17*

Complete guide for working on this Peano arithmetic formalization project.

---

## Part 1: Daily Development Workflow

### Starting a work session

```bash
# 1. Check which files are unlocked
bash git-lock.bash list

# If more than one file is unlocked from a previous session, lock all:
# bash git-lock.bash lock Peano/SomeModule.lean

# 2. Check current sorry status
make sorry
```

### Creating a new module

```bash
# Creates Peano/ModuleName.lean from _template.lean
# and adds the import to Peano.lean
make new NAME=ModuleName

# For nested modules:
make new NAME=Algebra/Ring
```

Then edit the generated file. When done:

```bash
bash git-lock.bash lock Peano/ModuleName.lean
```

### Editing an existing module

```bash
# 1. Unlock the file
bash git-lock.bash unlock Peano/PeanoNatAdd.lean

# 2. Edit...

# 3. Lock when done
bash git-lock.bash lock Peano/PeanoNatAdd.lean
```

### The one-file rule

> **At most one `.lean` file may be unlocked at any time.**

If you need to switch to a different file mid-session:

```bash
bash git-lock.bash lock Peano/CurrentModule.lean
bash git-lock.bash unlock Peano/NextModule.lean
```

### Building

```bash
make build          # compile full project
make rebuild        # clean + compile
```

### Checking proofs

```bash
make sorry          # list all sorry in project
make status         # lock status + sorry count
```

---

## Part 2: Commit Protocol

### Before committing

```bash
# 1. Verify only the intended files are unlocked
bash git-lock.bash list

# 2. Check for sorry
make sorry

# 3. Update REFERENCE.md
#    Project modified .lean files → REFERENCE.md
#    (See AI-GUIDE.md §12)
```

### Committing

```bash
# Stage specific files (avoid git add -A to prevent accidents)
git add Peano/ModuleName.lean REFERENCE.md CHANGELOG.md

git commit -m "feat: add ModuleName with N definitions and M theorems"
```

### After committing — lock all modified .lean files

```bash
bash git-lock.bash lock Peano/ModuleName.lean

# Commit the updated locked_files.txt
git add locked_files.txt
git commit -m "chore: lock ModuleName after completion"
```

### Ending a session

```bash
# Lock ALL modified .lean files
bash git-lock.bash list   # verify none remain unlocked

git push origin master
```

---

## Part 3: Updating the Lean Toolchain

```bash
# Try a new version — automatically builds and commits on success
bash update-toolchain.bash v4.29.0

# On failure it restores the previous version automatically
```

---

## Part 4: Regenerating the Root Module

If you add/remove modules manually without using `new-module.bash`:

```bash
bash gen-root.bash
```

This scans `Peano/` for all `.lean` files (excluding `_template.lean`) and
regenerates the import section of `Peano.lean`, preserving any export blocks after
the last import line.

---

## Part 5: AI Assistant Sessions

When starting a session with an AI assistant:

1. **Point to AI-GUIDE.md** — the AI reads this first
2. **Point to REFERENCE.md** — the AI uses this instead of loading all `.lean` files
3. **Remind the one-file rule** — unlock only the target module
4. **At session end** — AI locks all modified files and updates `REFERENCE.md`, `CHANGELOG.md`

Key commands to tell the AI:

```
bash git-lock.bash list                        # what is currently unlocked?
bash git-lock.bash unlock Peano/File.lean # unlock for editing
bash git-lock.bash lock Peano/File.lean   # lock after completion
make sorry                                     # any sorry left?
```

---

## Quick Reference

```bash
bash git-lock.bash init              # install git hook (once per clone)
bash git-lock.bash list              # show locked files
bash git-lock.bash lock File.lean    # lock a file
bash git-lock.bash unlock File.lean  # unlock a file
make new NAME=Module                 # create new module
make build                           # compile
make sorry                           # check for sorry
make status                          # lock + sorry status
bash gen-root.bash                   # regenerate root imports
bash update-toolchain.bash vX.Y.Z    # update Lean version
```

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

<!-- AUTO-UPDATE-2026-04-23-START -->
## Actualizacion de estado - 2026-04-23

- Estado del build: 52 jobs · 0 errores · 2 sorry warnings (sylow_second, sylow_third).
- cauchy_minimal: completamente demostrado (McKay). mckay_p_dvd_powEqId cerrado.
- sylow_lift_from_cauchy: demostrado por induccion fuerte sobre |G| con axioma temporal sylow_center_step.
- Nuevos helpers privados: subgroupToFinGroup, subgroupOfSubgroup, sylow_center_step.
- Pendientes activos: sylow_second, sylow_third; axioma sylow_center_step (requiere cociente / Wielandt).

<!-- AUTO-UPDATE-2026-04-23-END -->

<!-- AUTO-UPDATE-2026-04-23b-START -->
## Actualizacion de estado - 2026-04-23b

- Estado del build: 52 jobs · 0 errores · 0 warnings.
- Sylow.lean: todos los teoremas cerrados (0 sorry, 5 axiomas privados).
- Binom.lean: nuevo import Primes.lean; tres nuevos lemas: prime_not_dvd_of_pos_lt (privado), prime_not_dvd_factorial (privado), prime_dvd_binom_prime (publico).
- NEXT-STEPS.md: ruta de Wielandt documentada (Lucas + combinatoria para eliminar sylow_center_step).
- Pendientes activos: C(pr,p) = r·C(pr-1,p-1), C(pr,p) ≡ r (mod p), Wielandt, 5 axiomas privados de Sylow.

<!-- AUTO-UPDATE-2026-04-23b-END -->

<!-- AUTO-UPDATE-2026-04-24-START -->
## Actualizacion de estado - 2026-04-24

- Estado del build: 52 jobs · 0 errores · 0 warnings.
- Binom.lean: nuevo teorema binom_prime_row (publico) y auxiliar privado binom_prime_row_aux.
  - Prueba: via binom_mul_factorials + mul_cancelation_right + mul_cancelation_left (sin set, sin conv_lhs).
  - Enuncia: C(p·r, p) = r · C(p·r−1, p−1) para p ≠ 0, r ≠ 0.
- REFERENCE.md: entrada T16.10 agregada.
- NEXT-STEPS.md: pasos 2 y 4 marcados como completados; siguiente meta: C(p·r, p) ≡ r (mod p).
- Pendientes activos: C(pr,p) ≡ r (mod p), Lucas, Wielandt, 5 axiomas privados de Sylow.

<!-- AUTO-UPDATE-2026-04-24-END -->

