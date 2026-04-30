# Next Steps — Eliminating the Remaining Private Axioms

*Last updated: 2026-04-30*
*Author: Julián Calderón Almendros*

---

## Current build state

`Sylow.lean` compiles with 0 errors and 0 sorry.
All three Sylow theorems are formally closed, backed by **5 private axioms**:

| Axiom | Line ~ | Used by | Difficulty |
|---|---|---|---|
| `wielandt_fixed_point_exists` | ~2062 | `sylow_center_step_wielandt` | Hard |
| `wielandt_p_ndvd_r` | ~2165 | `sylow_center_step_wielandt` | Medium |
| `sylow_second_incl` | ~2374 | `sylow_second` | Hard |
| `sylow_third_mod` | ~2442 | `sylow_third` | Very hard |
| `sylow_third_dvd` | ~2456 | `sylow_third` | Very hard |

*(Eliminated: `sylow_card_eq` 2026-04-28, `wielandt_omega_card` 2026-04-28)*

**Previously available infrastructure** (in `Binom.lean`):

- `prime_dvd_binom_prime` — `p ∣ C(p,k)` for `0 < k < p`
- `binom_prime_row` — `C(p·r, p) = r · C(p·r-1, p-1)`
- `binom_pr_p_mod` — `C(p·r, p) ≡ r (mod p)`
- `binom_pow_p_mod` — `C(p^n·r, p^n) ≡ r (mod p)` (Lucas)

---

## Module plan: new files to create

Each proof track gets its own module. No new infrastructure goes directly into `Sylow.lean`.

```
Peano/PeanoNat/Combinatorics/GroupTheory/
├── Sylow/
│   ├── Cosets.lean        — existing: left/right cosets, Lagrange
│   ├── Sylow.lean         — existing: 3 theorems, 5 private axioms
│   ├── Wielandt.lean      — NEW: Wielandt combinatorial proof (Sylow I)
│   ├── CosetAction.lean   — NEW: H-action on G/K, fixed cosets (Sylow II)
│   └── Conjugation.lean   — NEW: G-action on Sylows, normalizer (Sylow III)
```

---

## Track 1 — `Wielandt.lean` (closes `wielandt_p_ndvd_r` + `wielandt_fixed_point_exists`)

### Mathematical argument

Let `|G| = p^(m+1) · r`. Define `Ω = { S ⊆ G.carrier.elems : |S| = p^(m+1) }`.

- `|Ω| = C(|G|, p^(m+1)) ≡ r (mod p)` by `binom_pow_p_mod`.
- `wielandt_p_ndvd_r`: p ∤ r (by contradiction using Cauchy for base m=0; circular for m≥1 — see note below).
- `wielandt_fixed_point_exists`: G acts on Ω by left translation; p∤|Ω| → `mckay_orbit_count` gives a fixed orbit → stabilizer has order `p^(m+1)`.

### Infrastructure needed in `Wielandt.lean`

1. `def sublistsOfLength : List ℕ₀ → ℕ₀ → List (List ℕ₀)` — already proved in previous session; re-implement here.
   Six properties: `_mem_len`, `_mem_sub`, `_mem_sorted`, `_nodup_result`, `_complete`, `_card`.
2. `def wieldandtOmega (G : FinGroup ℕ₀) (N : ℕ₀) : List (List ℕ₀)` — sublists of size N.
3. `wielandt_omega_card` — `|Ω| = C(|G|, N)`.
4. G-action on `List (List ℕ₀)` by left translation: `g • S = S.map (G.op g)`.
5. `wielandt_fixed_point_exists` — ∃ H : Subgroup G, H.carrier.card = N.

### Note on `wielandt_p_ndvd_r`

For m=0: Cauchy gives a subgroup of order p, contradicting `h_no_proper`. ✓ straightforward.
For m≥1: the standard argument uses Sylow I inductively (circular). **Strategy**: restructure
`sylow_lift_from_cauchy` to accept the inductive hypothesis as an explicit parameter, breaking
the circularity. This requires modifying the signature of `sylow_center_step_wielandt` in
`Sylow.lean` — do after `wielandt_fixed_point_exists` is complete.

---

## Track 2 — `CosetAction.lean` (closes `sylow_second_incl`)

### Proof sketch

H acts on G/K (cosets of K in G) by left multiplication: `h • (rK) = (h*r)K`.

Since K is a Sylow p-subgroup, `|G/K| = |G|/|K|` is not divisible by p.
By `mckay_orbit_count`, some coset `rK` is a fixed point.
Fixed coset: `∀ h ∈ H, h * r * K = r * K` ↔ `r⁻¹ * h * r ∈ K` ↔ `r⁻¹Hr ⊆ K`.

### Infrastructure needed in `CosetAction.lean`

1. `cosetToFSet (G : FinGroup ℕ₀) (K : Subgroup G) (r : ℕ₀) : ℕ₀FSet` — the coset `rK` as a finite set.
2. `cosetQuotient (G : FinGroup ℕ₀) (K : Subgroup G) : List ℕ₀FSet` — list of distinct cosets (already partially in `Cosets.lean`).
3. H-action on `cosetQuotient`: `hAct h rK = (h*r)K`; well-definedness proof.
4. `cosetQuotient_card_not_dvd_p` — `p ∤ |G/K|` when K is Sylow.
5. Apply `mckay_orbit_count` to get fixed coset; extract `r⁻¹Hr ⊆ K`.

### Prerequisites

- `FSet.union`, `FSet.image` from `FSet.lean` (§ 12, in progress).
- `cosetRepresentatives` and `coset_partition` from `Cosets.lean`.

---

## Track 3 — `Conjugation.lean` (closes `sylow_third_mod` + `sylow_third_dvd`)

### Conjugation proof sketch

**`sylow_third_mod`**: H (a Sylow subgroup) acts on the set `{Sylow subgroups}` by conjugation.
The unique fixed point is H itself. By `mckay_orbit_count`, n_p ≡ 1 (mod p).

**`sylow_third_dvd`**: G acts on `{Sylow subgroups}` by conjugation.
By Sylow II (transitivity), this action is transitive: single orbit.
By orbit-stabilizer, `n_p · |Stab_G(K)| = |G|`. Stabilizer = N_G(K) ⊇ K, so n_p ∣ |G|/|K|.

### Infrastructure needed in `Conjugation.lean`

1. `normalizer (G : FinGroup ℕ₀) (K : Subgroup G) : ℕ₀FSet` — `N_G(K) = { g ∈ G | g⁻¹Kg = K }`.
2. `normalizer_is_subgroup` — N_G(K) is a subgroup.
3. Encoding `List (Subgroup G) → ℕ₀FSet` via index injection (or FSet.image using FinGroup(Subgroup G)).
4. Conjugation action on `{Sylow subgroups}`.
5. Transitivity of conjugation action (uses `sylow_second` from `Sylow.lean`).

### Blocker

`List (Subgroup G)` is not a `ℕ₀FSet` — elements are `Subgroup G`, not `ℕ₀`.

**Short path** (no Phase 5): inject each `Subgroup G` in `sylows` to its list index (a `ℕ₀`).
Build a `ℕ₀FSet` of indices; carry the index↔subgroup correspondence as a side lemma.

**Long path** (Phase 5): instantiate `FinGroup (Subgroup G)` — cleaner but requires
the full FinGroup polymorphism refactor.

---

## FSet additions — `FSet.lean` § 12 (in progress)

Needed by CosetAction.lean and Conjugation.lean. Adds to `FSet.lean`:

| Operation | Signature | Needed by |
| --- | --- | --- |
| `FSet.union` | `FSet α → FSet α → FSet α` | coset partition proofs |
| `FSet.inter` | `FSet α → FSet α → FSet α` | coset disjointness |
| `FSet.image` | `(α → β) → FSet α → FSet β` | cosetToFSet, index encoding |
| `FSet.quotient` | `(α → α → Bool) → FSet α → List (FSet α)` | coset quotient list |

All require `[StrictLinearOrder α]` (union/inter) or `[StrictLinearOrder β]` (image).
`FSet.quotient` returns `List (FSet α)` (not a `FSet (FSet α)`) to avoid needing
`StrictLinearOrder (FSet α)` in the generic case.

---

## Execution order

```
FSet.lean § 12          ← in progress today
  └─ CosetAction.lean   ← next after FSet
  └─ Wielandt.lean      ← parallel track (no FSet dependency)
        └─ Conjugation.lean  ← after CosetAction + Wielandt
```

---

## FinGroup polymorphism — Phase 5 (long term)

Current `FinGroup` requires carrier ⊆ `ℕ₀`. Blocking:

- Quotient groups G/N (elements are cosets, not `ℕ₀`)
- `FinGroup (Subgroup G)` for the conjugation action (Sylow III)

**Precondition**: complete the three tracks above first.
After Sylow III is closed, revisit FinGroup generalization.
