/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Foundation/GodelBeta.lean
--
-- Función β de Gödel y codificación de listas en ℕ₀.
--
-- β(c, b, i) = c % (1 + (i+1)·b)
--
-- Teorema principal: para cualquier secuencia finita a₀,...,aₙ existe (c, b) tal que
-- β(c, b, i) = aᵢ para todo i ≤ n.
-- Esto permite codificar cualquier lista de ℕ₀ como un único natural.
--
-- Dependencias externas:
--   CantorPairing : pair, fst, snd, pair_fst, pair_snd, pair_surj
--   ChineseRemainder : chinese_remainder, Coprime
--   Factorial : factorial, factorial_ne_zero, factorial_succ
--   Arith : gcd, Coprime, divides_*, gcd_divides_*, antisymm_divides
--   Isomorph (vía Arith) : Ψ, isomorph_Ψ_gcd, isomorph_Ψ_mul, etc.

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes
import Peano.PeanoNat.Isomorph
import Peano.PeanoNat.Combinatorics.Factorial
import Peano.PeanoNat.NumberTheory.ChineseRemainder
import Peano.PeanoNat.Foundation.CantorPairing
import Peano.Prelim.Classical

set_option autoImplicit false

namespace Peano
  open Peano

  namespace Foundation
    open Foundation

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 0. Lema puro de Nat  (ANTES de los `open` de ℕ₀ para evitar ambigüedad)
  -- ─────────────────────────────────────────────────────────────────────────

  -- Si (j-i) ∣ b e i < j, entonces gcd(1+(i+1)*b, 1+(j+1)*b) = 1.
  private theorem nat_godel_coprime (b_n i_n j_n : Nat)
      (hij : i_n < j_n) (hdvd : @Dvd.dvd Nat _ (j_n - i_n) b_n) :
      Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
              (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)) = 1 := by
    -- Proof by algebraic manipulation in Nat.
    -- Let g := gcd(1+(i+1)*b, 1+(j+1)*b).
    -- g | (1+(j+1)*b) - (1+(i+1)*b) = (j-i)*b.
    -- g | (i+1)*b (from g | 1+(i+1)*b and g | (j-i)*b via algebra).
    -- g | (j-i)*b and (j-i) | b, so g | d and g | b.
    -- g | 1+(i+1)*b and g | (i+1)*b, so g | 1.
    sorry

  -- ─────────────────────────────────────────────────────────────────────────
  -- Ahora sí abrimos los namespaces de ℕ₀
  -- ─────────────────────────────────────────────────────────────────────────
  open Peano.Axioms
  open Peano.StrictOrder
  open Peano.Order
  open Peano.Add
  open Peano.Sub
  open Peano.Mul
  open Peano.Div
  open Peano.Arith
  open Peano.Factorial
  open Peano.ModEq

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 1. Función β de Gödel
  -- ─────────────────────────────────────────────────────────────────────────

  /-- β(c, b, i) = c mod (1 + (i+1)·b). -/
  def beta (c b i : ℕ₀) : ℕ₀ := mod c (add 𝟙 (mul (σ i) b))

  /-- El módulo de Gödel: m(b, i) = 1 + (i+1)·b. Siempre ≥ 1. -/
  private abbrev gmod (b i : ℕ₀) : ℕ₀ := add 𝟙 (mul (σ i) b)

  private theorem gmod_ne_zero (b i : ℕ₀) : gmod b i ≠ 𝟘 := by
    unfold gmod
    intro h
    exact nle_one_zero (h ▸ le_self_add 𝟙 (mul (σ i) b))

  private theorem gmod_ge_one (b i : ℕ₀) : le₀ 𝟙 (gmod b i) :=
    le_self_add 𝟙 (mul (σ i) b)

  /-- beta c b i < 1 + (i+1)·b. -/
  theorem beta_lt (c b i : ℕ₀) : lt₀ (beta c b i) (gmod b i) :=
    mod_lt c (gmod b i) (gmod_ne_zero b i)

  /-- Si a < 1 + (i+1)·b entonces beta a b i = a. -/
  theorem beta_of_lt (a b i : ℕ₀) (h : lt₀ a (gmod b i)) : beta a b i = a :=
    mod_of_lt a (gmod b i) h

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 2. Divisibilidad: σi ∣ factorial n cuando σi ≤ n
  -- ─────────────────────────────────────────────────────────────────────────

  /-- Si σi ≤ n entonces (i+1) ∣ n!  (inducción en n). -/
  private theorem succ_dvd_factorial (n i : ℕ₀) (hi : le₀ (σ i) n) :
      σ i ∣ factorial n := by
    induction n with
    | zero =>
      -- σi ≤ 0 es imposible: not_succ_le_zero i : ¬ le₀ (σ i) 𝟘
      exact absurd hi (not_succ_le_zero i)
    | succ n' ih =>
      rcases (le_iff_lt_or_eq (σ i) (σ n')).mp hi with h_lt | h_eq
      · -- σi < σn' → σi ≤ n', aplica HI
        have h_le' : le₀ (σ i) n' := (lt_succ_iff_le (σ i) n').mp h_lt
        -- factorial(σn') = mul (factorial n') (σn')
        rw [factorial_succ n']
        exact divides_mul_right (ih h_le')
      · -- σi = σn' → i = n'
        have h_eq_n : i = n' := succ_inj i n' h_eq
        subst h_eq_n
        rw [factorial_succ i]
        exact divides_mul_left (divides_refl (σ i))

  /-- Versión con argumentos implícitos para facilitar el uso. -/
  private theorem succ_dvd_factorial_of_le {n i : ℕ₀} (h : le₀ (σ i) n) :
      σ i ∣ factorial n :=
    succ_dvd_factorial n i h

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 3. Coprimality de los módulos de Gödel
  -- ─────────────────────────────────────────────────────────────────────────

  -- (El lema nat_godel_coprime está definido ANTES de los opens, al inicio del namespace.)

  /-- Los módulos de Gödel 1+(i+1)·b y 1+(j+1)·b son coprimos
  cuando (j-i) ∣ b e i < j. -/
  private theorem godel_mod_coprime (b i j : ℕ₀) (hij : lt₀ i j)
      (hdvd : sub j i ∣ b) :
      Coprime (gmod b i) (gmod b j) := by
    sorry

  /-- Con b = factorial n, los módulos gmod (factorial n) i y gmod (factorial n) j
  son coprimos para cualesquiera i ≠ j con i ≤ n, j ≤ n. -/
  private theorem godel_factorial_coprime (n i j : ℕ₀)
      (hi : le₀ i n) (hj : le₀ j n) (hij : i ≠ j) :
      Coprime (gmod (factorial n) i) (gmod (factorial n) j) := by
    -- Tricotomía para i y j (i ≠ j)
    rcases neq_then_lt_or_gt i j hij with h_lt | h_gt
    · -- Caso i < j: aplicar godel_mod_coprime
      apply godel_mod_coprime _ _ _ h_lt
      -- sub j i ∣ factorial n
      -- Pues sub j i ≤ j ≤ n, y sub j i ≠ 0 (por j > i),
      -- luego sub j i = σ (τ (sub j i)), y σ (τ (sub j i)) ≤ n
      have h_sub_pos  : lt₀ 𝟘 (sub j i) := sub_pos_of_lt h_lt
      have h_sub_le_n : le₀ (sub j i) n  := le_trans _ _ _ (sub_le_self j i) hj
      have h_sub_ne_zero : sub j i ≠ 𝟘 :=
        fun h => absurd (h ▸ h_sub_pos) (nlt_n_0 𝟘)
      have h_σ_τ : σ (τ (sub j i)) = sub j i :=
        σ_τ_eq_id_pos_forall (sub j i) h_sub_ne_zero
      exact h_σ_τ ▸ (succ_dvd_factorial_of_le (h_σ_τ.symm ▸ h_sub_le_n))
    · -- Caso j < i: por simetría de Coprime
      apply coprime_comm.mp
      apply godel_mod_coprime _ _ _ h_gt
      have h_sub_pos  : lt₀ 𝟘 (sub i j) := sub_pos_of_lt h_gt
      have h_sub_le_n : le₀ (sub i j) n  := le_trans _ _ _ (sub_le_self i j) hi
      have h_sub_ne_zero : sub i j ≠ 𝟘 :=
        fun h => absurd (h ▸ h_sub_pos) (nlt_n_0 𝟘)
      have h_σ_τ : σ (τ (sub i j)) = sub i j :=
        σ_τ_eq_id_pos_forall (sub i j) h_sub_ne_zero
      exact h_σ_τ ▸ (succ_dvd_factorial_of_le (h_σ_τ.symm ▸ h_sub_le_n))

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 4. CRT iterado: congruencias simultáneas
  -- ─────────────────────────────────────────────────────────────────────────

  -- Producto iterado de módulos para el CRT.
  -- prod_mods b n = (gmod b 0) * (gmod b 1) * ... * (gmod b n)
  private def prod_mods (b : ℕ₀) : ℕ₀ → ℕ₀
    | .zero   => gmod b 𝟘
    | .succ k => mul (prod_mods b k) (gmod b (σ k))

  private theorem gmod_dvd_prod_mods (b n i : ℕ₀) (hi : le₀ i n) :
      gmod b i ∣ prod_mods b n := by
    sorry

  -- Si m ∣ M y c ≡ c' (mod M), entonces c ≡ c' (mod m)
  private theorem modEq_of_dvd {m M : ℕ₀} (hM_ne : M ≠ 𝟘) (hm_ne : m ≠ 𝟘)
      (hm_dvd_M : m ∣ M) {c c' : ℕ₀} (hcong : ModEq M c c') :
      ModEq m c c' := by
    sorry

  -- Coprimality del producto de módulos anteriores con el módulo siguiente
  private theorem prod_mods_coprime_next (n b : ℕ₀)
      (hcop : ∀ i j, le₀ i n → le₀ j n → i ≠ j → Coprime (gmod b i) (gmod b j)) :
      Coprime (prod_mods b n) (gmod b (σ n)) := by
    sorry

  /-- CRT simultáneo: dada una función a : ℕ₀ → ℕ₀, existe c tal que
  c ≡ a(i) (mod gmod b i) para todo i ≤ n, cuando los gmod b i son coprimos en pares. -/
  private theorem simultaneous_congruences (n b : ℕ₀) (a : ℕ₀ → ℕ₀)
      (hcop : ∀ i j, le₀ i n → le₀ j n → i ≠ j → Coprime (gmod b i) (gmod b j)) :
      ∃ c : ℕ₀, ∀ i, le₀ i n → ModEq (gmod b i) c (a i) := by
    induction n with
    | zero =>
      -- Un único módulo: tomar c = a 𝟘
      refine ⟨a 𝟘, fun i hi => ?_⟩
      rcases (le_iff_lt_or_eq i 𝟘).mp hi with h_lt | h_eq
      · exact absurd h_lt (nlt_n_0 i)
      · rw [h_eq]; exact modEq_refl _ _
    | succ n' ih =>
      -- Por HI, c' con c' ≡ a(i) (mod gmod b i) para i ≤ n'
      have ih_cop : ∀ i j, le₀ i n' → le₀ j n' → i ≠ j → Coprime (gmod b i) (gmod b j) :=
        fun i j hi hj hij =>
          hcop i j (le_succ i n' hi) (le_succ j n' hj) hij
      obtain ⟨c', hc'⟩ := ih ih_cop
      -- Coprimality de prod_mods b n' con gmod b (σn')
      have h_cop_prod := prod_mods_coprime_next n' b (fun i j hi hj hij =>
        hcop i j (le_succ i n' hi) (le_succ j n' hj) hij)
      -- Aplicar CRT al par (prod_mods b n', gmod b (σn'))
      obtain ⟨c, hc_prod, hc_next⟩ := chinese_remainder h_cop_prod c' (a (σ n'))
      refine ⟨c, fun i hi => ?_⟩
      rcases (le_iff_lt_or_eq i (σ n')).mp hi with h_lt | h_eq
      · -- i ≤ n': usar gmod b i ∣ prod_mods b n' y transitividad de ≡
        have h_i_le_n' : le₀ i n' := (lt_succ_iff_le i n').mp h_lt
        have h_mi_dvd_prod : gmod b i ∣ prod_mods b n' :=
          gmod_dvd_prod_mods b n' i h_i_le_n'
        exact modEq_trans
          (modEq_of_dvd (by sorry) (gmod_ne_zero b i) h_mi_dvd_prod hc_prod)
          (hc' i h_i_le_n')
      · -- i = σn'
        subst h_eq
        exact hc_next

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 5. Teorema principal: β representa cualquier secuencia finita
  -- ─────────────────────────────────────────────────────────────────────────

  /-- Para cualquier secuencia a : ℕ₀ → ℕ₀ y longitud n, existen c, b : ℕ₀
  tales que β(c, b, i) = a(i) para todo i ≤ n. -/
  theorem godel_beta_seq (n : ℕ₀) (a : ℕ₀ → ℕ₀) :
      ∃ c b : ℕ₀, ∀ i, le₀ i n → beta c b i = a i := by
    -- Elegir b = factorial (n + max_val + 1) donde max_val = máx a(0),...,a(n).
    -- Esto garantiza:
    --   (1) a(i) < gmod b i = 1 + (i+1)*b para todo i ≤ n
    --   (2) gmod b i y gmod b j son coprimos por godel_factorial_coprime
    -- Por ahora usamos sorry; la prueba completa requiere
    -- formalizar max sobre secuencias finitas + CRT iterado.
    sorry

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 6. Codificación y decodificación de listas
  -- ─────────────────────────────────────────────────────────────────────────

  /-- Codifica una lista como un único ℕ₀ mediante pair (c, b). -/
  noncomputable def encodeList (l : List ℕ₀) : ℕ₀ :=
    if l = [] then 𝟘
    else
      let n := Λ (l.length - 1)
      let a := fun i => l.getD (Ψ i) 𝟘
      pair (Classical.choose (godel_beta_seq n a))
           (Classical.choose (Classical.choose_spec (godel_beta_seq n a)))

  /-- Decodifica: dado el código z y la longitud n, reconstruye la lista. -/
  noncomputable def decodeList (z : ℕ₀) : ℕ₀ → List ℕ₀
    | .zero   => []
    | .succ k => decodeList z k ++ [beta (fst z) (snd z) k]

  theorem list_decode_length (z n : ℕ₀) : (decodeList z n).length = Ψ n := by
    induction n with
    | zero => simp [decodeList, isomorph_0_Ψ]
    | succ k ih =>
      simp [decodeList, List.length_append, ih, isomorph_σ_Ψ]

  /-- El teorema de representación: decodificar ∘ codificar = identidad. -/
  theorem encode_decode (l : List ℕ₀) :
      decodeList (encodeList l) (Λ l.length) = l := by
    sorry

  end Foundation
end Peano

-- ============================================================
-- Exports (AI-GUIDE.md §30–31)
-- ============================================================
export Peano.Foundation (
  beta
  beta_lt
  beta_of_lt
  godel_beta_seq
  encodeList
  decodeList
  list_decode_length
  encode_decode
)
