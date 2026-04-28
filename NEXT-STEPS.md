# Next Steps — Eliminating the Remaining Private Axioms

*Last updated: 2026-04-28*
*Author: Julián Calderón Almendros*

---

## Current status

`Sylow.lean` compiles with 0 errors and 0 sorry warnings.
All three Sylow theorems are formally closed, backed by **5 private axioms** (down from 7):

| Axiom | Line | Used by | Difficulty |
|---|---|---|---|
| `wielandt_fixed_point_exists` | ~2062 | `sylow_center_step_wielandt` | Hard |
| `wielandt_p_ndvd_r` | ~2165 | `sylow_center_step_wielandt` | Medium |
| `sylow_second_incl` | ~2374 | `sylow_second` | Hard |
| `sylow_third_mod` | ~2442 | `sylow_third` | Very hard |
| `sylow_third_dvd` | ~2456 | `sylow_third` | Very hard |

*(Eliminated: `sylow_card_eq` 2026-04-28, `wielandt_omega_card` 2026-04-28)*

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

**Step 1 — `p | C(p,k)` for `0 < k < p`** *(in `Binom.lean`)* ✓ DONE (`prime_dvd_binom_prime`)

**Step 2 — `C(p·r, p) = r · C(p·r-1, p-1)`** *(algebraic identity, in `Binom.lean`)* ✓ DONE (`binom_prime_row`)

**Step 3 — `C(p·r, p) ≡ r (mod p)` by induction + Lucas** *(in `Binom.lean`)* ✓ DONE (`binom_pr_p_mod`, `binom_pow_p_mod`)

**Step 4a — `wielandt_omega_card`** *(in `Sylow.lean`)* ✓ DONE (2026-04-28)

- `sublistsOfLength : List ℕ₀ → ℕ₀ → List (List ℕ₀)` with 6 properties proved.
- `|sublistsOfLength G.carrier.elems N| = C(|G|, N)` via `binom_pascal`.

**Step 4b — `wielandt_p_ndvd_r`** *(in `Sylow.lean`)* ❌ TODO

- Goal: `¬ p ∣ r` given `p^(m+1) · r = |G|`, Cauchy, and no proper subgroup has order `p^(m+1)`.
- Key: `binom_pow_p_mod` gives `C(|G|, N) ≡ r (mod p)` → if `p∤r` then `p∤|Ω|`.
- For m=0: Cauchy gives subgroup of order p = p^1, contradicts h_no_proper. ✓
- For m≥1: need inductive use of Sylow I (not available in axiom signature — may require restructuring).

**Step 4c — `wielandt_fixed_point_exists`** *(in `Sylow.lean`)* ❌ TODO

- Goal: `∃ H : Subgroup G, H.carrier.card = N` (corrected conclusion as of 2026-04-28).
- G acts on Ω by left translation; p∤|Ω| → by `mckay_orbit_count` some orbit has size not divisible by p → size 1 → stabilizer Stab_G(S₀) satisfies |Stab_G(S₀)| = N via orbit-stabilizer.
- Needs: define G-action on `List (List ℕ₀)`, adapt `mckay_orbit_count`.

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
5. ~~`binom_pr_p_mod` — C(p·r, p) ≡ r (mod p) by induction on r~~ ✓ DONE
6. ~~`binom_pow_p_mod` — C(p^n·r, p^n) ≡ r (mod p), Lucas (Binom.lean)~~ ✓ DONE
7. ~~`sylow_card_eq` — uniqueness of Sylow exponent (Sylow.lean)~~ ✓ DONE (2026-04-28)
8. ~~`wielandt_omega_card` — ∃ Ω of N-sublists of G with |Ω|=C(|G|,N) (Sylow.lean)~~ ✓ DONE (2026-04-28)
9. **Next: `wielandt_p_ndvd_r`** — ¬p∣r given p^(m+1)·r = |G| and no proper subgroup of order p^(m+1).
   - Key tool: `binom_pow_p_mod` already available. If p∤r then p∤|Ω|.
10. **Next: `wielandt_fixed_point_exists`** — ∃ H : Subgroup G, H.carrier.card = N.
    - G acts on Ω; p∤|Ω| → some orbit has size not divisible by p → size 1 → Stab_G(S₀) has order N (orbit-stabilizer).
    - Needs: adapt `mckay_orbit_count` to the action on `List (List ℕ₀)`.

---

## Refactoring: Polimorfismo de FinGroup

Esto es un cambio masivo que afecta a todos los teoremas y estructuras dependientes (`Subgroup`, `GroupHom`, etc.).

Dado el alcance, se presentan dos opciones:

### Opción A — Cambio completo (más limpio, más trabajo) ESTA ES LA OPCIÓN ELEGIDA

- Reescribir `Group.lean` completo con `FinGroup (α : Type) [DecidableEq α]`
- Actualizar `Action.lean`, `Cosets.lean`, `Sylow.lean` consecuentemente
- Esto rompe la API existente pero es más correcto matemáticamente

### Opción B — Compatibilidad gradual (menos disruptivo) ESTA OPCIÓN ES RECHAZADA

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
