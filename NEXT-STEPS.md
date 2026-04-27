# Next Steps — Eliminating the Remaining Private Axioms

*Last updated: 2026-04-27*
*Author: Julián Calderón Almendros*

---

## Current status

`Sylow.lean` compiles with 0 errors and 0 sorry warnings.
All three Sylow theorems are formally closed, backed by 5 private axioms:

| Axiom | Used by | Difficulty |
|---|---|---|
| `sylow_card_eq` | `sylow_second` | Medium |
| `sylow_second_incl` | `sylow_second` | Hard |
| `sylow_center_step` | `sylow_lift_from_cauchy` | Hard |
| `sylow_third_mod` | `sylow_third` | Very hard |
| `sylow_third_dvd` | `sylow_third` | Very hard |

---

## Roadmap: eliminating `sylow_center_step` via Wielandt's combinatorial proof

The standard textbook proof of Sylow I uses either:

- **Class equation + Cauchy on Z(G) + quotient G/⟨z⟩** — blocked: FinGroup requires `ℕ₀` elements, no quotient groups.
- **Wielandt's combinatorial argument** — feasible: reduces to a congruence `C(p^n·r, p^n) ≡ r (mod p)`.

We follow **Wielandt's path**.

### Wielandt's argument (sketch)

Let `|G| = p^n · r` with `p ∤ r`. Consider the set
`Ω = { X ⊆ G : |X| = p^n }`, with `|Ω| = C(p^n·r, p^n)`.

`G` acts on `Ω` by left translation. A fixed point of this action is a subgroup of order `p^n` (Sylow p-subgroup).

By Lucas / direct congruence: `C(p^n·r, p^n) ≡ r (mod p)`, so `p ∤ |Ω|`.

Since `G` acts and `p ∤ |Ω|`, at least one orbit has size not divisible by `p`, hence size 1 (it is a fixed point), giving a Sylow p-subgroup.

### Step-by-step proof plan

**Step 1 — `p | C(p,k)` for `0 < k < p`** *(in `Binom.lean`)*

Key tool: `binom_mul_factorials : C(n,k) · k! · (n-k)! = n!`

Proof sketch:

- `p | p!` (p divides its own factorial)
- `p ∤ k!` for `k < p` (no factor from 1..k is divisible by p) — requires `prime_not_dvd_of_pos_lt`
- `p ∤ (p-k)!` similarly
- From `C(p,k) · k! · (p-k)! = p!` and `p ∤ (k! · (p-k)!)`, conclude `p | C(p,k)` via `coprime_dvd_of_dvd_mul`

Sub-lemmas needed:

- `prime_not_dvd_of_pos_lt` (private): `p prime, 0 < a < p → p ∤ a`
- `prime_not_dvd_factorial` (private): `p prime, k < p → p ∤ k!`
- `prime_dvd_binom_prime` (public): `p prime, 0 < k < p → p | C(p,k)`

**Step 2 — `C(p·r, p) = r · C(p·r-1, p-1)`** *(algebraic identity, in `Binom.lean`)* ✓ DONE (`binom_prime_row`)

From `binom_mul_factorials` applied twice:

- `C(p·r, p) · p! · (p·r-p)! = (p·r)!`
- `C(p·r-1, p-1) · (p-1)! · (p·r-p)! = (p·r-1)!`

Divide: `C(p·r, p) / C(p·r-1, p-1) = (p·r)! / (p · (p·r-1)!) = r`.

In ℕ₀ (no division): prove via `mul_left_cancel` applied to the factorial equation.

**Step 3 — `C(p·r, p) ≡ r (mod p)` by induction** *(in `Binom.lean` or new `Lucas.lean`)*

Use Step 2 + `p | C(p,k)` (Step 1 generalized) to show `C(p·r, p) ≡ r·C(p·r-1,p-1) ≡ r (mod p)` by induction on r.

Full Lucas' theorem: `C(p^n·r, p^n) ≡ r (mod p)`.

**Step 4 — Wielandt's combinatorial argument** *(in `Sylow.lean` or new `Wielandt.lean`)*

- Define `Ω` as the list of all p^n-element sublists of G.
- `|Ω| = C(|G|, p^n)`.
- G-action by left translation on Ω.
- Fixed point ↔ left-translation-stable set of size p^n ↔ subgroup.
- `C(p^n·r, p^n) ≡ r (mod p)` and `p ∤ r` → `p ∤ |Ω|` → some orbit has size not divisible by p → size 1 (p-group orbit counting) → fixed point exists.

**Step 5 — Replace `sylow_center_step` axiom** *(in `Sylow.lean`)*

With Wielandt established, `sylow_center_step` follows:
given `p^(m+1) | |G|` and no proper subgroup has order `p^(m+1)`, a Wielandt fixed point gives the required subgroup.

---

## Roadmap: eliminating `sylow_card_eq`

Add `pow_dvd_pow` to `Pow.lean`:

```
pow_dvd_pow : a ≤ b → p^a | p^b
```

Then: if `p^n | |G|` and `¬p^(n+1) | |G|`, then `n` is unique (the Sylow exponent is well-defined).
Both Sylow p-subgroups have order `p^n` by definition → `sylow_card_eq` follows.

---

## Roadmap: eliminating `sylow_second_incl`

Build H-action on G/K (cosets as `ℕ₀FSet`):

- Cosets already in library (Sylow/Cosets.lean).
- H acts by left multiplication on left cosets of K.
- Adapt `mckay_orbit_count` to show: since |H| is a p-power and |G/K| = |G|/|K| ≡ 1 ≢ 0 (mod p) (K is Sylow), some coset is fixed.
- Fixed coset `rK` means H·rK = rK, i.e., r⁻¹Hr ⊆ K.

---

## Roadmap: eliminating `sylow_third_mod` and `sylow_third_dvd`

Requires:

- Normalizer `N_G(K) = { g ∈ G | g⁻¹Kg = K }` (not yet in library).
- G-action by conjugation on `List (Subgroup G)`.
- Orbit-stabilizer theorem applied to this action.
- For `sylow_third_mod`: H acts on Sylow subgroups; unique fixed point K with H=K → n_p ≡ 1 (mod p).
- For `sylow_third_dvd`: orbit of K under G-conjugation has size |G|/|N_G(K)|; stabilizer = N_G(K) ⊇ K; so size divides |G|/|K| which divides |G|.

These require substantial new infrastructure. **Do after** the Wielandt path is complete.

---

## FinGroup polymorphism (long term)

Current `FinGroup` requires carrier ⊆ `ℕ₀` (via `ℕ₀FSet`). This blocks:

- Quotient groups G/N
- Subgroup actions on `List (Subgroup G)` (elements are `Subgroup G`, not `ℕ₀`)

**Plan**: Make `FinGroup` a typeclass over an arbitrary type `α`:

```lean
class FinGroup (α : Type) where
  elems : FSet α        -- finite set with decidable equality
  op : α → α → α
  id : α
  inv : α → α
  -- axioms: assoc, id_left, id_right, inv_left, inv_right
```

This would allow:

- `FinGroup (Subgroup G)` instantiation for the conjugation action.
- Quotient groups as `FinGroup (Coset G N)`.
- Full generality for Sylow III and Sylow II.

**When to do this**: After completing the Wielandt path and closing `sylow_center_step`. The refactor is independent of combinatorics work.

---

## Refactoring: Lists and Sets — architectural plan

*(Full details in `ListasYConjuntos.md`)*

Goal: transition `List.lean` / `FSet.lean` / related modules from an implementation tightly coupled to `ℕ₀` toward a fully abstract, polymorphic design, culminating in a recursive universal type (`UnivVal`) capable of representing arbitrary nested hierarchies.

### Phase 1 — Consolidation (`ListList.lean` → `List.lean`)

`ListList.lean` only adds typeclass instances (`LE`, `LT`, `DecidableRel`, `Repr`) to types already defined in `List.lean`, fragmenting types from their core behaviour.

Actions:

- Move all sections from `ListList.lean` (§11–§15) to the end of `List.lean`.
- Delete `ListList.lean`.
- Update all imports that reference `ListList` (e.g. in `FSetFSet.lean`) to point to `Peano.PeanoNat.ListsAndSets.List`.

### Phase 2 — Mathematical foundations: `StrictLinearOrder`

`sortedInsert` in `FSet.lean` is hard-wired to `ℕ₀` because it depends on `ℕ₀`-specific trichotomy / transitivity theorems.

Actions:

- Define `StrictLinearOrder α` typeclass (irrefl, trans, trichotomy, decidable `<`) in a new `Order.lean` or `StrictOrder.lean`.
- Derive asymmetry as a lemma from irrefl + trans (not a separate axiom).
- Instantiate for `ℕ₀`, `ℕ₁`, `ℕ₂`, `Tuple n` using existing project theorems.

### Phase 3 — Algorithm generalisation (`FSet.lean`)

`insert`, `ofList`, `filter` on finite sets are currently limited to `FSet ℕ₀`.

Actions:

- Move `sortedInsert` and its correctness proof from `FSet.lean` into `List.lean`.
- Generalise its signature to `List α` with `[StrictLinearOrder α]`.
- Make `FSet` operations generic: `FSet α` for any type with `StrictLinearOrder`.

### Phase 4 — Recursive universe (`UnivVal`)

`PeanoVal` manually encodes each nesting level (`ofNat`, `ofNatList`, `ofTuple`, `ofTupleList`), causing combinatorial explosion: `DecidableEq` / `LT` currently require 36 cases. Adding `List (List α)` would multiply cases further.

Proposed design:

```lean4
inductive Level where | base | sub1 | sub2

def Level.toType {α α₁ α₂ : Type} : Level → Type
  | .base => α | .sub1 => α₁ | .sub2 => α₂

inductive UnivVal {α α₁ α₂ : Type} : Type where
  | ofScalar (lvl : Level) (x : Level.toType lvl) : UnivVal
  | ofTuple  (n : ℕ₀)      (t : Tuple n)          : UnivVal
  | ofList   (xs : List UnivVal)                   : UnivVal
```

Benefits: free recursion via `ofList`, structural induction collapses 36 cases to a handful, `FSet UnivVal` can host arbitrary mathematical structures.

---

## Immediate priorities

Now I have the full picture. Respondo a [1] y [2]:

[1] Fusión FSetFSet → FSet: Sí, es factible con el mismo método. El riesgo §11 (instLEList) se resuelve igual que antes: colocarlo al final del archivo fusionado, después de toda la maquinaria FSet. Solo FSetFunction.lean importa FSetFSet.

[2] Acción 2: Generalizar sortedInsert. Requiere primero añadir una instancia puente DecidableRel desde StrictLinearOrder.

Orden de ejecución: primero [2] (modifica código), después [1] (fusión mecánica).

## Immediate priorities (this session)

1. ~~`prime_not_dvd_of_pos_lt` (private, `Binom.lean`)~~ ✓ DONE
2. ~~`prime_not_dvd_factorial` (private, `Binom.lean`)~~ ✓ DONE
3. ~~`prime_dvd_binom_prime` (public, `Binom.lean`)~~ ✓ DONE
4. ~~Prove `C(p·r, p) = r · C(p·r-1, p-1)` (`binom_prime_row`)~~ ✓ DONE
5. **Next**: Prove `C(p·r, p) ≡ r (mod p)` by induction on r using `binom_prime_row` and `prime_dvd_binom_prime`.
   - Requires: modular arithmetic (Mod.lean or similar) — or inline the argument with `Divides`.
   - Key induction: C(pr, p) = r·C(pr-1,p-1), and p | C(p,k) for 0 < k < p implies the congruence holds via an inductive congruence argument on r.

---

## Refactoring: Polimorfismo de FinGroup

Esto es un cambio masivo que afecta a todos los teoremas y estructuras dependientes (`Subgroup`, `GroupHom`, etc.).

Dado el alcance, se presentan dos opciones:

### Opción A — Cambio completo (más limpio, más trabajo)

- Reescribir `Group.lean` completo con `FinGroup (α : Type) [DecidableEq α]`
- Actualizar `Action.lean`, `Cosets.lean`, `Sylow.lean` consecuentemente
- Esto rompe la API existente pero es más correcto matemáticamente

### Opción B — Compatibilidad gradual (menos disruptivo)

- Definir `FinGroup` polimórfico como `FinGroup (α : Type) [DecidableEq α]`
- Mantener `FinGroupNat` como alias de `FinGroup ℕ₀` para compatibilidad
- Actualizar los archivos dependientes gradualmente

**Recomendación**: Opción A para un codebase más limpio a largo plazo.

**Estado actual del refactoring**:

- ~~Fusión FSetFSet → FSet~~ ✓ DONE
- ~~Polimorfismo de Tuple~~ ✓ DONE
- ~~Limpieza de aliases *ListList~~ ✓ DONE
- ~~**Implementar Opción A para `FinGroup`**~~ ✓ DONE (2026-04-27)

### Detalles del refactoring de FinGroup (completado)

Archivos modificados:
- **`StrictOrder.lean`**: añadida instancia `instIrreflLTOfSLO : IrreflLT α` desde `StrictLinearOrder α`.
- **`Group.lean`**: `FinGroup (α : Type) [DecidableEq α] [LT α] [StrictLinearOrder α]` con `carrier : FSet α`, `id : α`. Alias de compatibilidad: `abbrev ℕ₀FinGroup := FinGroup ℕ₀`.
- **`Action.lean`**, **`Cosets.lean`**, **`Sylow.lean`**: `(G : FinGroup)` → `(G : FinGroup ℕ₀)` en todas las signaturas.

Build final: **51 jobs, 0 errores**.

### Siguientes fases de FinGroup (largo plazo)

- **Fase 2 — `Action.lean`**: Genericizar `GroupAction` con `act : α → β → β` para tipo de acción β arbitrario.
- **Fase 3 — `Cosets.lean`**: Propagar `α` en signaturas de cosetos.
- **Fase 4 — `Sylow.lean`**: Solo cambios mecánicos; mantener prueba de McKay intacta.
- **Fase 5**: `FinGroup (Subgroup G)` para la acción de conjugación (Sylow III).
