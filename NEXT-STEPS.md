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

---

## Phase F — Completar Foundation: prerequisito para la cadena Peano → Aczel → ZFC

*Añadido: 2026-05-02*

**Objetivo**: exportar desde este proyecto `encodeList`/`decodeList`/`encode_decode` para que
AczelSetTheory pueda importar `Peano.PeanoNat.Foundation.GodelBeta` y fundamentar formalmente
`List ℕ₀ ≃ ℕ₀` sobre los axiomas de Peano, cerrando la cadena `PA → Aczel → ZFC`.

Esta phase es completamente paralela a los Tracks 1–3 de eliminación de axiomas de Sylow.
No hay dependencias cruzadas.

---

### F.1 — `CantorPairing.lean` (11 sorry)

Necesario porque `GodelBeta.lean` usa `pair`/`fst`/`snd` para codificar el par `(c, b)` como
un único `ℕ₀`.

**Sorry pendientes y estrategia de prueba**:

| # | Teorema | Estrategia |
|---|---------|------------|
| 1 | `triag_zero` | `simp [triag]` + `Div` sobre `0 * 1 / 2 = 0` |
| 2 | `triag_succ` | requiere `two_dvd_mul_succ`; `T(n+1) = T(n) + (n+1)` por álgebra de `Div` |
| 3 | `triag_strict_mono` | de `triag_succ` + `lt₀` por inducción en la cadena `m < n` |
| 4 | `triag_le_of_le` | de `triag_strict_mono` + reflexividad de `le₀` |
| 5 | `triag_le_pair` | `pair m n = T(m+n) + m ≥ T(m+n)` por `le_add_right` |
| 6 | `pair_lt_triag_succ` | `T(m+n+1) = T(m+n)+(m+n+1) > T(m+n)+m` porque `m < m+n+1` |
| 7 | `antidiag_exists` | inducción en `z`: caso succ usa `triag_strict_mono` + orden bien fundado |
| 8 | `antidiag_unique` | tricotomía `lt₀`: si `w₁ < w₂` entonces `T(w₁+1) ≤ T(w₂) ≤ z`, contradice `z < T(w₁+1)` |
| 9 | `pair_fst` | `fst(pair m n) = T(m+n)+m − T(m+n) = m` por `add_sub_cancel_left` |
| 10 | `pair_snd` | `snd = (m+n) − m = n` por `add_sub_cancel_left` |
| 11 | `pair_surj` | `pair(fst z, snd z) = T(antidiag z) + (z − T(antidiag z)) = z` por `add_sub_of_le` |

**Lemas auxiliares nuevos** (dentro de `CantorPairing.lean` o importados de `Sub.lean`/`Arith.lean`):

```lean
-- 1. Divisibilidad exacta del número triangular
private theorem two_dvd_mul_succ (n : ℕ₀) : (𝟙 + 𝟙) ∣ n * σ n
-- Dem.: inducción; 0*1 = 0 ∣ 2; paso: (n+1)*(n+2) = n*(n+1) + 2*(n+1),
--       y 2 ∣ n*(n+1) por HI, luego 2 ∣ suma.

-- 2. Cancelación: a + b - a = b (en ℕ₀, con a ≤ a + b automáticamente)
private theorem add_sub_cancel_left (a b : ℕ₀) : a + b - a = b
-- Dem.: inducción en a; usa sub_succ y succ_sub_succ.

-- 3. Reconstrucción: T(w) ≤ z → z < T(w+1) → z = T(w) + (z - T(w))
private theorem sub_add_of_le {a b : ℕ₀} (h : le₀ a b) : a + (b - a) = b
```

**Orden interno de prueba**: `two_dvd_mul_succ` → `triag_zero`/`triag_succ` →
`triag_strict_mono` → `triag_le_of_le` → `triag_le_pair`/`pair_lt_triag_succ` →
`antidiag_exists` → `antidiag_unique` → `pair_fst` → `pair_snd` → `pair_surj`.

---

### F.2 — `GodelBeta.lean` (crear desde cero)

**Firma pública del módulo**:

```lean
namespace Peano.Foundation

-- Función β de Gödel: β(c, b, i) = c % (1 + (i+1)·b)
def beta (c b i : ℕ₀) : ℕ₀ := c % (𝟙 + σ i * b)

-- Representación de secuencias finitas por CRT
theorem godel_beta_seq (n : ℕ₀) (a : ℕ₀ → ℕ₀) :
    ∃ c b : ℕ₀, ∀ i, i ≤ n → beta c b i = a i

-- Codificación de listas: (c, b) = pair c_val b_val
def encodeList (l : List ℕ₀) : ℕ₀
def decodeList (z : ℕ₀) (n : ℕ₀) : List ℕ₀

theorem encode_decode (l : List ℕ₀) :
    decodeList (encodeList l) l.length = l
theorem list_decode_length (z n : ℕ₀) :
    (decodeList z n).length = n

end Peano.Foundation
```

**Dependencias**:

```lean
import Peano.PeanoNat.NumberTheory.ChineseRemainder  -- chinese_remainder
import Peano.PeanoNat.Combinatorics.Factorial         -- factorial, factorial_pos
import Peano.PeanoNat.Arith                           -- Coprime, bezout_natform
import Peano.PeanoNat.Foundation.CantorPairing        -- pair, fst, snd
```

**Lema central — coprimalidad de módulos de Gödel**:

```lean
private theorem godel_mod_coprime (i j b : ℕ₀)
    (hij : lt₀ i j) (hb : (j - i) ∣ b) :
    Coprime (𝟙 + σ i * b) (𝟙 + σ j * b)
-- Dem.: si p | gcd, entonces p | (σ j - σ i)·b y p | 1 + σ i·b.
--       De p | (σ j - σ i)·b y (j-i) | b → p | b.
--       De p | 1 + σ i·b y p | σ i·b → p | 1. Contradicción.
```

**Lema de separación suficiente** (para `b = n!`):

```lean
private theorem godel_factorial_coprime (n i j : ℕ₀)
    (hi : le₀ i n) (hj : le₀ j n) (hij : i ≠ j) :
    Coprime (𝟙 + σ i * factorial n) (𝟙 + σ j * factorial n)
-- Dem.: wlog i < j; entonces (j - i) ≤ n, luego (j - i) | n! = b.
--       Aplicar godel_mod_coprime.
```

**Estrategia para `godel_beta_seq`**: inducción en `n`; en cada paso aplicar `chinese_remainder`
al par de módulos coprime `(1 + (n+1)·b, producto anterior)`.

---

### F.3 — `Foundation.lean` (paraguas, trivial)

```lean
-- Peano/PeanoNat/Foundation.lean
import Peano.PeanoNat.Foundation.PeanoSystem
import Peano.PeanoNat.Foundation.Initiality
import Peano.PeanoNat.Foundation.PureAxioms
import Peano.PeanoNat.Foundation.CantorPairing
import Peano.PeanoNat.Foundation.GodelBeta
```

Añadir en `Peano.lean` (raíz):

```lean
import Peano.PeanoNat.Foundation
```

---

### Orden de ejecución de Phase F

```
F.1: CantorPairing.lean ✅ COMPLETADO
        │
        ▼
F.2: GodelBeta.lean
  └── godel_mod_coprime
  └── godel_factorial_coprime
  └── godel_beta_seq        (usa chinese_remainder)
  └── encodeList / decodeList / encode_decode
        │
        ▼
F.3: Foundation.lean (paraguas, trivial)
        │
        ▼
  Importable por AczelSetTheory
```
