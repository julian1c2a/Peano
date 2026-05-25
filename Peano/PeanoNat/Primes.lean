import Peano.PeanoNat.Arith
import Peano.PeanoNat.ListsAndSets.List
import Peano.PeanoNat.Combinatorics.Product

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatPrimes.lean
-- Teorema Fundamental de la Aritmética para los naturales de Peano.
--
-- § 0. Lemas internos de gcd (re-derivados, privados en PeanoNatArith)
-- § 1. Propiedades básicas de Prime
-- § 2. Irreducibilidad y relación con Prime
-- § 3. Coprimalidad y lema de Gauss
-- § 4. Listas de primos y función producto
-- § 5. Divisor primo: todo n ≥ 2 tiene uno
-- § 6. Existencia de factorización prima (TFA — Existencia)
-- § 7. Unicidad de la factorización prima  (TFA — Unicidad)
-- § 8. Factorización computable (factorize : ℕ₂ → FactFSet)

namespace Peano
  open Peano

  namespace Primes
      open Peano.Axioms
      open Peano.Order
      open Peano.StrictOrder
      open Peano.Add
      open Peano.Sub
      open Peano.Mul
      open Peano.Div
      open Peano.Lattice
      open Peano.Arith
      open Peano.List
      open Peano.Product
      open Peano.FSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 0. gcd_dvd_left / gcd_dvd_right / gcd_comm' (privados en PeanoNatArith)
    -- ══════════════════════════════════════════════════════════════════

    private theorem gcd_dvd_left (a b : ℕ₀) : gcd a b ∣ a := by
      rcases le_total a b with h | h
      · have := gcd_divides_min a b; rwa [le_then_min_eq_left a b h] at this
      · have := gcd_divides_max a b; rwa [le_then_max_eq_left a b h] at this

    private theorem gcd_dvd_right (a b : ℕ₀) : gcd a b ∣ b := by
      rcases le_total a b with h | h
      · have := gcd_divides_max a b; rwa [le_then_max_eq_right a b h] at this
      · have := gcd_divides_min a b; rwa [le_then_min_eq_right a b h] at this

    private theorem gcd_comm' (a b : ℕ₀) : gcd a b = gcd b a :=
      antisymm_divides
        (gcd_greatest b a (gcd a b) ⟨gcd_dvd_right a b, gcd_dvd_left a b⟩)
        (gcd_greatest a b (gcd b a) ⟨gcd_dvd_right b a, gcd_dvd_left b a⟩)

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Propiedades básicas de Prime
    -- ══════════════════════════════════════════════════════════════════

    theorem prime_ne_zero {p : ℕ₀} (hp : Prime p) : p ≠ 𝟘 := hp.1

    theorem prime_ne_one {p : ℕ₀} (hp : Prime p) : p ≠ 𝟙 := hp.2.1

    theorem one_lt_prime {p : ℕ₀} (hp : Prime p) : lt₀ 𝟙 p := by
      rcases trichotomy 𝟙 p with h | h | h
      · exact h
      · exact absurd h.symm (prime_ne_one hp)
      · exact absurd (lt_b_1_then_b_eq_0 h) (prime_ne_zero hp)

    theorem prime_ge_two {p : ℕ₀} (hp : Prime p) : le₀ 𝟚 p := by
      -- 𝟚 = σ 𝟙;  tricotomía entre σ 𝟙 y p
      rcases trichotomy (σ 𝟙) p with h_lt | h_eq | h_gt
      · exact Or.inl h_lt
      · exact Or.inr h_eq
      · -- h_gt : lt₀ p (σ 𝟙);  lt_then_le_succ_wp → le₀ p 𝟙
        have h_le : le₀ p 𝟙 := lt_then_le_succ_wp h_gt
        rcases h_le with h_lt1 | h_eq1
        · exact absurd (lt_b_1_then_b_eq_0 h_lt1) (prime_ne_zero hp)
        · exact absurd h_eq1 (prime_ne_one hp)

    theorem not_prime_one : ¬ Prime 𝟙 := fun hp => prime_ne_one hp rfl
    theorem not_prime_zero : ¬ Prime 𝟘 := fun hp => prime_ne_zero hp rfl

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. Irreducibilidad
    -- ══════════════════════════════════════════════════════════════════

    def Irreducible (p : ℕ₀) : Prop :=
      p ≠ 𝟙 ∧ ∀ a b : ℕ₀, mul a b = p → a = 𝟙 ∨ b = 𝟙

    theorem mul_eq_one {a b : ℕ₀} (h : mul a b = 𝟙) : a = 𝟙 ∧ b = 𝟙 := by
      have ha_ne : a ≠ 𝟘 := by
        intro h0; rw [h0, zero_mul] at h; exact absurd h (Ne.symm (succ_neq_zero 𝟘))
      have hb_ne : b ≠ 𝟘 := by
        intro h0; rw [h0, mul_zero] at h; exact absurd h (Ne.symm (succ_neq_zero 𝟘))
      have ha_le : le₀ a 𝟙 := divides_le ⟨b, h.symm⟩ (succ_neq_zero 𝟘)
      have hb_le : le₀ b 𝟙 := divides_le ⟨a, h.symm.trans (mul_comm a b)⟩ (succ_neq_zero 𝟘)
      constructor
      · rcases ha_le with h_lt | h_eq
        · exact absurd (lt_b_1_then_b_eq_0 h_lt) ha_ne
        · exact h_eq
      · rcases hb_le with h_lt | h_eq
        · exact absurd (lt_b_1_then_b_eq_0 h_lt) hb_ne
        · exact h_eq

    theorem prime_divisors {p d : ℕ₀} (hp : Prime p) (hd : d ∣ p) : d = 𝟙 ∨ d = p := by
      rcases hd with ⟨k, hk⟩
      rcases hp.2.2 d k ⟨𝟙, by rw [mul_one, hk]⟩ with h_pd | h_pk
      · exact Or.inr (antisymm_divides ⟨k, hk⟩ h_pd)
      · left
        rcases h_pk with ⟨m, hm⟩
        -- hm : k = mul p m
        rw [hm, ← mul_assoc, mul_comm d p, mul_assoc] at hk
        -- hk : p = mul p (mul d m)
        have h_dm : mul d m = 𝟙 :=
          mul_cancelation_left p (mul d m) 𝟙 (prime_ne_zero hp)
            (hk.symm.trans (mul_one p).symm)
        exact (mul_eq_one h_dm).1

    theorem prime_imp_irreducible {p : ℕ₀} (hp : Prime p) : Irreducible p :=
      ⟨prime_ne_one hp, fun a b hab => by
        have ha_dvd : a ∣ p := ⟨b, hab.symm⟩
        rcases prime_divisors hp ha_dvd with ha1 | hap
        · exact Or.inl ha1
        · right
          rw [hap] at hab
          exact mul_cancelation_left p b 𝟙 (prime_ne_zero hp) (hab.trans (mul_one p).symm)⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Coprimalidad y lema de Gauss
    -- ══════════════════════════════════════════════════════════════════

    theorem coprime_symm {a b : ℕ₀} (h : Coprime a b) : Coprime b a := by
      unfold Coprime IsGCD at *
      exact ⟨h.2.1, h.1, fun c ⟨hcb, hca⟩ => h.2.2 c ⟨hca, hcb⟩⟩

    theorem gcd_eq_one_iff_coprime (a b : ℕ₀) : gcd a b = 𝟙 ↔ Coprime a b := by
      constructor
      · intro h_gcd
        unfold Coprime IsGCD
        refine ⟨one_divides a, one_divides b, fun c ⟨hca, hcb⟩ => ?_⟩
        have : c ∣ gcd a b := gcd_greatest a b c ⟨hca, hcb⟩
        rwa [h_gcd] at this
      · intro h_cop
        unfold Coprime IsGCD at h_cop
        have hg_one : gcd a b ∣ 𝟙 :=
          h_cop.2.2 (gcd a b) ⟨gcd_dvd_left a b, gcd_dvd_right a b⟩
        exact antisymm_divides hg_one (one_divides _)

    theorem prime_not_dvd_imp_coprime {p a : ℕ₀} (hp : Prime p) (hna : ¬ p ∣ a) :
        gcd p a = 𝟙 := by
      have hg_p := gcd_dvd_left p a
      rcases prime_divisors hp hg_p with h1 | hp_eq
      · exact h1
      · exact absurd (hp_eq ▸ gcd_dvd_right p a) hna


    /--
    Si `p` es primo y `p ∤ a`, entonces `gcd p a = 1`.
    Esta es la forma directa del lema fundamental para la línea de Euler/Fermat.
    -/
    theorem gcd_eq_one_of_prime_not_dvd {p a : ℕ₀} (hp : Prime p) (hna : ¬ p ∣ a) :
        gcd p a = 𝟙 :=
      prime_not_dvd_imp_coprime hp hna

    theorem prime_coprime_or_dvd {p n : ℕ₀} (hp : Prime p) : p ∣ n ∨ Coprime p n := by
      have hp0 := prime_ne_zero hp
      by_cases h : (n % p) = 𝟘
      · -- n % p = 0 → p ∣ n
        left
        have h_spec : n = add (mul (n / p) p) (n % p) := divMod_spec n p hp0
        rw [h, add_zero] at h_spec
        exact ⟨n / p, h_spec.trans (mul_comm _ _)⟩
      · -- n % p ≠ 0 → ¬(p ∣ n) → coprime
        right
        have hndvd : ¬ p ∣ n := by
          intro ⟨k, hk⟩
          have h_spec : n = add (mul (n / p) p) (n % p) := divMod_spec n p hp0
          have h_dvd_mod : p ∣ (n % p) := divides_mod ⟨k, hk⟩ (divides_refl p)
          have h_mod_lt : lt₀ (n % p) p := mod_lt n p hp0
          exact h (by
            by_cases h_ne : (n % p) = 𝟘
            · exact h_ne
            · exact absurd h_mod_lt (le_not_lt (divides_le h_dvd_mod h_ne)))
        exact (gcd_eq_one_iff_coprime p n).mp (prime_not_dvd_imp_coprime hp hndvd)

    /-- **Lema de Gauss**: mcd(a,b) = 1 ∧ a ∣ b·c → a ∣ c.
        La demostración usa bezout_natform y sub_k_add_k/subₕₖ_eq_iff_eq_add_of_le.
      Los pasos de aritmética que involucran resta saturada quedan pendientes
        mientras se completan las lemmas adicionales de PeanoNatSub. -/
    theorem coprime_dvd_of_dvd_mul {a b c : ℕ₀}
        (hcop : Coprime a b) (hdvd : a ∣ mul b c) : a ∣ c := by
      rw [← gcd_eq_one_iff_coprime] at hcop
      obtain ⟨n, m, h_bez⟩ := bezout_natform a b
      rw [hcop] at h_bez
      -- Tratar c = 0 de forma especial
      by_cases hc_ne : c = 𝟘
      · rw [hc_ne]; exact divides_zero a
      · rcases h_bez with h | h
        · -- Caso 1: 𝟙 = sub (mul n a) (mul m b)
          have h_lt : lt₀ (mul m b) (mul n a) :=
            (sub_pos_iff_lt (mul n a) (mul m b)).mp (h ▸ Or.inr rfl)
          have h1 : a ∣ mul (mul n a) c := by
            rw [mul_assoc]; exact divides_mul_left (divides_mul_right (divides_refl a))
          have h2 : a ∣ mul (mul m b) c := by
            rw [mul_assoc]; exact divides_mul_left hdvd
          -- n·a = m·b + 1  →  (n·a)·c = (m·b)·c + c
          have h_na_c : mul (mul n a) c = add (mul (mul m b) c) c := by
            have h_sk := sub_k_add_k (mul n a) (mul m b) (lt_imp_le_wp h_lt)
            rw [← h] at h_sk   -- h_sk : add 𝟙 (mul m b) = mul n a
            rw [h_sk.symm, add_mul, one_mul]
            exact add_comm c (mul (mul m b) c)
          have h_sub_c : sub (mul (mul n a) c) (mul (mul m b) c) = c := by
            rw [h_na_c]
            exact add_k_sub_k c (mul (mul m b) c)
          have h_lt2 : lt₀ (mul (mul m b) c) (mul (mul n a) c) := by
            rw [h_na_c]; exact lt_self_add_r (mul (mul m b) c) c hc_ne
          rw [← h_sub_c]
          exact divides_sub h_lt2 h1 h2
        · -- Caso 2: 𝟙 = sub (mul n b) (mul m a)  (simétrico)
          have h_lt : lt₀ (mul m a) (mul n b) :=
            (sub_pos_iff_lt (mul n b) (mul m a)).mp (h ▸ Or.inr rfl)
          have h1 : a ∣ mul (mul n b) c := by
            rw [mul_assoc]; exact divides_mul_left hdvd
          have h2 : a ∣ mul (mul m a) c := by
            rw [mul_assoc]; exact divides_mul_left (divides_mul_right (divides_refl a))
          -- n·b = m·a + 1  →  (n·b)·c = (m·a)·c + c
          have h_nb_c : mul (mul n b) c = add (mul (mul m a) c) c := by
            have h_sk := sub_k_add_k (mul n b) (mul m a) (lt_imp_le_wp h_lt)
            rw [← h] at h_sk   -- h_sk : add 𝟙 (mul m a) = mul n b
            rw [h_sk.symm, add_mul, one_mul]
            exact add_comm c (mul (mul m a) c)
          have h_sub_c : sub (mul (mul n b) c) (mul (mul m a) c) = c := by
            rw [h_nb_c]
            exact add_k_sub_k c (mul (mul m a) c)
          have h_lt2 : lt₀ (mul (mul m a) c) (mul (mul n b) c) := by
            rw [h_nb_c]; exact lt_self_add_r (mul (mul m a) c) c hc_ne
          rw [← h_sub_c]
          exact divides_sub h_lt2 h1 h2

    -- ──────────────────────────────────────────────────────────────────
    -- Irreducible → Prime y equivalencias (dependen de coprime_dvd_of_dvd_mul)
    -- ──────────────────────────────────────────────────────────────────

    /-- **Irreducible → Prime**: si p es irreducible (y p ≠ 0), entonces es primo. -/
    theorem irreducible_imp_prime {p : ℕ₀} (hp0 : p ≠ 𝟘) (hirr : Irreducible p) :
        Prime p :=
      ⟨hp0, hirr.1, fun a b hdvd => by
        rcases gcd_dvd_left p a with ⟨k, hk⟩
        rcases hirr.2 (gcd p a) k hk.symm with h1 | hk1
        · exact Or.inr (coprime_dvd_of_dvd_mul
            ((gcd_eq_one_iff_coprime p a).mp h1) hdvd)
        · have hgp : gcd p a = p := by
            rw [hk1, mul_one] at hk; exact hk.symm
          exact Or.inl (hgp ▸ gcd_dvd_right p a)⟩

    /-- **Def. C ↔ Def. A**: Prime (Euclides) ↔ p ≠ 0 ∧ Irreducible. -/
    theorem prime_iff_irreducible {p : ℕ₀} :
        Prime p ↔ (p ≠ 𝟘 ∧ Irreducible p) :=
      ⟨fun hp => ⟨prime_ne_zero hp, prime_imp_irreducible hp⟩,
       fun ⟨hp0, hirr⟩ => irreducible_imp_prime hp0 hirr⟩

    /-- **Def. B**: p tiene exactamente dos divisores — todos los divisores de p
        son 1 ó p, y p ≠ 1. -/
    def HasExactlyTwoDivisors (p : ℕ₀) : Prop :=
      (∀ d : ℕ₀, d ∣ p → d = 𝟙 ∨ d = p) ∧ p ≠ 𝟙

    theorem not_has_two_divisors_one : ¬ HasExactlyTwoDivisors 𝟙 :=
      fun h => h.2 rfl

    theorem not_has_two_divisors_zero : ¬ HasExactlyTwoDivisors 𝟘 := by
      intro ⟨hall, _⟩
      rcases hall 𝟚 (divides_zero 𝟚) with h | h
      · exact absurd (succ_inj_pos_wp h) (succ_neq_zero 𝟘)
      · exact absurd h (succ_neq_zero (σ 𝟘))

    /-- **Def. C ↔ Def. B**: Prime ↔ HasExactlyTwoDivisors. -/
    theorem prime_iff_has_exactly_two_divisors {p : ℕ₀} :
        Prime p ↔ HasExactlyTwoDivisors p := by
      constructor
      · intro hp
        exact ⟨fun d hd => prime_divisors hp hd, prime_ne_one hp⟩
      · intro ⟨hall, hp1⟩
        have hp0 : p ≠ 𝟘 := by
          intro h0; subst h0
          rcases hall 𝟚 (divides_zero 𝟚) with h | h
          · exact absurd (succ_inj_pos_wp h) (succ_neq_zero 𝟘)
          · exact absurd h (succ_neq_zero (σ 𝟘))
        apply irreducible_imp_prime hp0
        refine ⟨hp1, fun a b hab => ?_⟩
        rcases hall a ⟨b, hab.symm⟩ with ha1 | hap
        · exact Or.inl ha1
        · right
          rw [← hap] at hab
          exact mul_cancelation_left a b 𝟙 (hap ▸ hp0)
            (hab.trans (mul_one a).symm)

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Listas de primos
    -- ══════════════════════════════════════════════════════════════════

    def PrimeList (ps : List ℕ₀) : Prop :=
      ∀ p, p ∈ ps → Prime p

    theorem product_list_pos {ps : List ℕ₀} (hps : PrimeList ps) :
        lt₀ 𝟘 (product_list ps) := by
      induction ps with
      | nil => exact lt_0_1
      | cons p ps ih =>
        simp [product_list]
        apply mul_pos
        · exact neq_0_then_lt_0 (prime_ne_zero (hps p (List.mem_cons.mpr (Or.inl rfl))))
        · exact ih (fun q hq => hps q (List.mem_cons.mpr (Or.inr hq)))

    /-- **Euclides para listas**: p primo, p ∣ ∏ ps → ∃ q ∈ ps, p ∣ q. -/
    theorem prime_dvd_product_list {p : ℕ₀} (hp : Prime p) :
        ∀ ps : List ℕ₀, p ∣ product_list ps →
          ∃ q, q ∈ ps ∧ p ∣ q := by
      intro ps
      induction ps with
      | nil =>
        simp [product_list]
        intro h
        have h_le_p_1 : le₀ p 𝟙 := divides_le h (succ_neq_zero 𝟘)
        have h_le_2_1 : le₀ 𝟚 𝟙 := le_trans 𝟚 p 𝟙 (prime_ge_two hp) h_le_p_1
        rcases h_le_2_1 with h_lt | h_eq
        · exact absurd h_lt (lt_asymm 𝟙 (σ 𝟙) (lt_succ_self 𝟙))
        · exact absurd (succ_inj_pos_wp h_eq) (succ_neq_zero 𝟘)
      | cons q qs ih =>
        simp [product_list]
        intro h_dvd
        rcases hp.2.2 q (product_list qs) h_dvd with h_pq | h_pqs
        · exact Or.inl h_pq
        · exact Or.inr (ih h_pqs)

    /-- Un número primo que divide a un producto divide a alguno de los factores. -/
    theorem prime_dvd_mul {p a b : ℕ₀} (hp : Prime p) (hdvd : p ∣ mul a b) :
        p ∣ a ∨ p ∣ b :=
      hp.2.2 a b hdvd

    -- ══════════════════════════════════════════════════════════════════
    -- § 5. Factorización computable
    -- ══════════════════════════════════════════════════════════════════

    /-- Búsqueda del menor divisor de `n` partiendo del candidato `c`.
        `fuel` controla la terminación (decrece en cada paso).
        Computable: Sí. -/
    def smallestDivisorAux (n c : ℕ₀) : ℕ₀ → ℕ₀
      | .zero => c
      | .succ f' =>
        if dividesb c n then c
        else smallestDivisorAux n (σ c) f'

    /-- Menor divisor ≥ 2 de `n` (para `n ≥ 2`).
        Computable: Sí. Dependencias: `dividesb`. -/
    def smallestDivisor (n : ℕ₀) : ℕ₀ :=
      smallestDivisorAux n 𝟚 n

    -- ── 8.1. Lemas puente: dividesb ↔ divisibilidad ────────────────

    /-- Si `dividesb d n = true` (y `d ≠ 0`), entonces `d ∣ n`. -/
    theorem dividesb_true_imp_dvd {d n : ℕ₀} (hd : d ≠ 𝟘) :
        dividesb d n = true → d ∣ n := by
      intro h
      have hmod : (n % d) = 𝟘 := of_decide_eq_true h
      have h_spec : n = add (mul (n / d) d) (n % d) := divMod_spec n d hd
      rw [hmod, add_zero] at h_spec
      exact ⟨n / d, h_spec.trans (mul_comm _ _)⟩

    /-- Si `d ∣ n` (y `d ≠ 0`), entonces `dividesb d n = true`. -/
    theorem dvd_imp_dividesb_true {d n : ℕ₀} (hd : d ≠ 𝟘) :
        d ∣ n → dividesb d n = true := by
      intro hdvd
      show decide ((n % d) = 𝟘) = true
      apply decide_eq_true
      have h_div_mod : d ∣ (n % d) := divides_mod hdvd (divides_refl d)
      have h_mod_lt : lt₀ (n % d) d := mod_lt n d hd
      by_cases h_ne : (n % d) = 𝟘
      · exact h_ne
      · exact absurd h_mod_lt (le_not_lt (divides_le h_div_mod h_ne))

    private theorem dividesb_self {n : ℕ₀} (hn : n ≠ 𝟘) :
        dividesb n n = true :=
      dvd_imp_dividesb_true hn (divides_refl n)

    /-- `dividesb d n = true ↔ d ∣ n`, para `d ≠ 0`. -/
    theorem dividesb_iff_dvd {d n : ℕ₀} (hd : d ≠ 𝟘) :
        dividesb d n = true ↔ d ∣ n :=
      ⟨dividesb_true_imp_dvd hd, dvd_imp_dividesb_true hd⟩

    /-- `d ∣ n` es decidible computacionalmente mediante `dividesb`. -/
    instance decidableDvd (d n : ℕ₀) : Decidable (d ∣ n) :=
      if hd : d = 𝟘 then
        if hn : n = 𝟘 then
          isTrue (by subst hd; subst hn; exact divides_refl 𝟘)
        else
          isFalse (by intro h; subst hd; exact hn ((zero_divides_iff n).mp h))
      else
        if h : dividesb d n = true then
          isTrue (dividesb_true_imp_dvd hd h)
        else
          isFalse (fun hdvd => h (dvd_imp_dividesb_true hd hdvd))

    -- ── 8.2. Especificación de smallestDivisorAux ──────────────────

    /-- Lema maestro: `smallestDivisorAux n c fuel` devuelve el menor valor
        `d ≥ c` que divide a `n` (y `d ≤ n`),
        siempre que `c ≤ n` y `fuel` sea suficiente (`n ≤ c + fuel`).
        El cuarto componente dice que todo candidato entre `c` y `d` no divide. -/
    theorem smallestDivisorAux_spec (n : ℕ₀) (hn : le₀ 𝟚 n) :
        ∀ (c fuel : ℕ₀), le₀ 𝟚 c → le₀ c n → le₀ n (add c fuel) →
        dividesb (smallestDivisorAux n c fuel) n = true ∧
        le₀ c (smallestDivisorAux n c fuel) ∧
        le₀ (smallestDivisorAux n c fuel) n ∧
        (∀ e, le₀ c e → lt₀ e (smallestDivisorAux n c fuel) →
          dividesb e n = false) := by
      intro c fuel hc hcn hfuel
      induction fuel generalizing c with
      | zero =>
        rw [add_zero] at hfuel
        have heq := le_antisymm c n hcn hfuel
        simp only [smallestDivisorAux]
        rw [heq]
        have hn0 : n ≠ 𝟘 := by
          intro h0; rw [h0] at hn; exact lt_zero 𝟚 (Or.resolve_right hn (succ_neq_zero 𝟙))
        exact ⟨dividesb_self hn0, le_refl n, le_refl n,
               fun e he h_lt => absurd h_lt (le_not_lt he)⟩
      | succ f' ih =>
        simp only [smallestDivisorAux]
        by_cases h_div : dividesb c n = true
        · -- c divide a n → resultado = c
          simp [h_div]
          exact ⟨le_refl c, hcn, fun _ hce h_lt => absurd h_lt (le_not_lt hce)⟩
        · -- c no divide a n → resultado = smallestDivisorAux n (σ c) f'
          have h_div_false : dividesb c n = false := Bool.eq_false_iff.mpr h_div
          simp [h_div_false]
          have hc_ne_n : c ≠ n := by
            intro heq; rw [heq] at h_div
            have hn0 : n ≠ 𝟘 := by
              intro h0; rw [h0] at hn
              exact lt_zero 𝟚 (Or.resolve_right hn (succ_neq_zero 𝟙))
            exact h_div (dividesb_self hn0)
          have hsc_le_n : le₀ (σ c) n :=
            lt_nm_then_le_nm_wp (lt_of_le_neq_wp hcn hc_ne_n)
          have hsc2 : le₀ 𝟚 (σ c) :=
            le_trans 𝟚 c (σ c) hc (Or.inl (lt_self_σ_self c))
          have hfuel' : le₀ n (add (σ c) f') := by
            rw [succ_add]; rw [add_succ] at hfuel; exact hfuel
          obtain ⟨h1, h2, h3, h4⟩ := ih (σ c) hsc2 hsc_le_n hfuel'
          refine ⟨h1, le_trans c (σ c) _ (Or.inl (lt_self_σ_self c)) h2, h3,
                  fun e hce h_lt => ?_⟩
          -- Si e = c, sabemos dividesb c n = false.
          -- Si le₀ (σ c) e, usamos h4 (IH).
          rcases hce with h_lt_ce | h_eq_ce
          · exact h4 e (lt_nm_then_le_nm_wp h_lt_ce) h_lt
          · rw [← h_eq_ce]; exact h_div_false

    -- ── 8.3. Propiedades de smallestDivisor ────────────────────────

    /-- `smallestDivisor n` divide a `n` (para `n ≥ 2`). -/
    theorem smallestDivisor_dvd {n : ℕ₀} (hn : le₀ 𝟚 n) :
        smallestDivisor n ∣ n := by
      unfold smallestDivisor
      have hfuel : le₀ n (add 𝟚 n) :=
        le_trans n (add n 𝟚) (add 𝟚 n)
          (Or.inl (lt_self_add_r n 𝟚 (succ_neq_zero 𝟙)))
          (le_of_eq_wp (add_comm n 𝟚))
      obtain ⟨h_div, h_ge, h_le, _⟩ := smallestDivisorAux_spec n hn 𝟚 n (le_refl 𝟚) hn hfuel
      have h_d_ne_0 : smallestDivisorAux n 𝟚 n ≠ 𝟘 := by
        intro h0; rw [h0] at h_ge
        exact lt_zero 𝟚 (Or.resolve_right h_ge (succ_neq_zero 𝟙))
      exact dividesb_true_imp_dvd h_d_ne_0 h_div

    /-- `smallestDivisor n ≥ 2` (para `n ≥ 2`). -/
    theorem smallestDivisor_ge_two {n : ℕ₀} (hn : le₀ 𝟚 n) :
        le₀ 𝟚 (smallestDivisor n) := by
      unfold smallestDivisor
      have hfuel : le₀ n (add 𝟚 n) :=
        le_trans n (add n 𝟚) (add 𝟚 n)
          (Or.inl (lt_self_add_r n 𝟚 (succ_neq_zero 𝟙)))
          (le_of_eq_wp (add_comm n 𝟚))
      obtain ⟨_, h_ge, _, _⟩ := smallestDivisorAux_spec n hn 𝟚 n (le_refl 𝟚) hn hfuel
      exact h_ge

    /-- `smallestDivisor n ≤ n` (para `n ≥ 2`). -/
    theorem smallestDivisor_le {n : ℕ₀} (hn : le₀ 𝟚 n) :
        le₀ (smallestDivisor n) n := by
      unfold smallestDivisor
      have hfuel : le₀ n (add 𝟚 n) :=
        le_trans n (add n 𝟚) (add 𝟚 n)
          (Or.inl (lt_self_add_r n 𝟚 (succ_neq_zero 𝟙)))
          (le_of_eq_wp (add_comm n 𝟚))
      obtain ⟨_, _, h_le, _⟩ := smallestDivisorAux_spec n hn 𝟚 n (le_refl 𝟚) hn hfuel
      exact h_le

    /-- `smallestDivisor n` es el *menor* divisor ≥ 2 de `n`:
        ningún `e` con `2 ≤ e < smallestDivisor n` divide a `n`. -/
    theorem smallestDivisor_not_dvd_of_lt {n e : ℕ₀} (hn : le₀ 𝟚 n)
        (he2 : le₀ 𝟚 e) (hlt : lt₀ e (smallestDivisor n)) : ¬(e ∣ n) := by
      have hfuel : le₀ n (add 𝟚 n) :=
        le_trans n (add n 𝟚) (add 𝟚 n)
          (Or.inl (lt_self_add_r n 𝟚 (succ_neq_zero 𝟙)))
          (le_of_eq_wp (add_comm n 𝟚))
      obtain ⟨_, _, _, h_min⟩ :=
        smallestDivisorAux_spec n hn 𝟚 n (le_refl 𝟚) hn hfuel
      intro hdvd
      have he_ne0 : e ≠ 𝟘 := by
        intro h0; rw [h0] at he2
        exact lt_zero 𝟚 (Or.resolve_right he2 (succ_neq_zero 𝟙))
      have h_false := h_min e he2 hlt
      exact absurd (dvd_imp_dividesb_true he_ne0 hdvd)
        (Bool.eq_false_iff.mp h_false)

    /-- Si `p` es primo y `p ∣ n` con `n ≥ 2`, entonces `smallestDivisor n ≤ p`. -/
    theorem smallestDivisor_le_of_prime_dvd {n p : ℕ₀} (hn : le₀ 𝟚 n)
        (hp : Prime p) (hdvd : p ∣ n) : le₀ (smallestDivisor n) p := by
      rcases le_or_lt (smallestDivisor n) p with h | h_lt
      · exact h
      · exact absurd hdvd (smallestDivisor_not_dvd_of_lt hn (prime_ge_two hp) h_lt)

    /-- `smallestDivisor n` es primo para todo `n ≥ 2`. -/
    theorem smallestDivisor_prime {n : ℕ₀} (hn : le₀ 𝟚 n) :
        Prime (smallestDivisor n) := by
      have hge2 := smallestDivisor_ge_two hn
      have hdvd := smallestDivisor_dvd hn
      have hne0 : smallestDivisor n ≠ 𝟘 := by
        intro h0; rw [h0] at hge2
        exact lt_zero 𝟚 (Or.resolve_right hge2 (succ_neq_zero 𝟙))
      apply irreducible_imp_prime hne0
      refine ⟨?_, fun a b hab => ?_⟩
      · -- smallestDivisor n ≠ 1
        intro h1; rw [h1] at hge2
        exact le_then_ngt 𝟚 𝟙 hge2 (lt_succ_self 𝟙)
      · -- Si mul a b = smallestDivisor n, entonces a = 1 ó b = 1.
        by_cases ha1 : a = 𝟙
        · exact Or.inl ha1
        · by_cases hb1 : b = 𝟙
          · exact Or.inr hb1
          · exfalso
            have ha0 : a ≠ 𝟘 := by
              intro h0; rw [h0, zero_mul] at hab; exact hne0 hab.symm
            have hb0 : b ≠ 𝟘 := by
              intro h0; rw [h0, mul_zero] at hab; exact hne0 hab.symm
            have ha2 : le₀ 𝟚 a := by
              rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 ha0) with h | h
              · exact lt_then_le_succ_wp h
              · exact absurd h.symm ha1
            have hb2 : le₀ 𝟚 b := by
              rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hb0) with h | h
              · exact lt_then_le_succ_wp h
              · exact absurd h.symm hb1
            -- a < smallestDivisor n: a * b = sd(n) y b ≥ 2 → a < sd(n)
            have ha_lt : lt₀ a (smallestDivisor n) := by
              rw [← hab]
              exact lt_of_lt_of_le
                (by have := mul_lt_right a 𝟚 ha0 (lt_succ_self 𝟙)
                    rwa [mul_comm 𝟚 a] at this)
                (by have := mul_le_mono_right a hb2
                    rwa [mul_comm 𝟚 a, mul_comm b a] at this)
            -- a ∣ smallestDivisor n ∣ n → a ∣ n
            have ha_dvd_sd : a ∣ smallestDivisor n := ⟨b, hab.symm⟩
            have ha_dvd_n  : a ∣ n := divides_trans ha_dvd_sd hdvd
            -- Contradice smallestDivisor_not_dvd_of_lt
            exact smallestDivisor_not_dvd_of_lt hn ha2 ha_lt ha_dvd_n

    /-- Si `smallestDivisor n = n` y `n ≥ 2`, entonces `n` es irreducible. -/
    theorem smallestDivisor_eq_self_imp_irreducible {n : ℕ₀} (hn : le₀ 𝟚 n)
        (h_sd : smallestDivisor n = n) : Irreducible n := by
      have hn0 : n ≠ 𝟘 := by
        rintro rfl; exact lt_zero 𝟚 (Or.resolve_right hn (succ_neq_zero 𝟙))
      have hn1 : n ≠ 𝟙 := by
        rintro rfl
        rcases hn with h | h
        · exact lt_asymm 𝟙 (σ 𝟙) (lt_succ_self 𝟙) h
        · exact absurd (succ_inj_pos_wp h) (succ_neq_zero 𝟘)
      -- Extraer la propiedad de minimalidad de smallestDivisor
      have hfuel : le₀ n (add 𝟚 n) :=
        le_trans n (add n 𝟚) (add 𝟚 n)
          (Or.inl (lt_self_add_r n 𝟚 (succ_neq_zero 𝟙)))
          (le_of_eq_wp (add_comm n 𝟚))
      obtain ⟨_, _, _, h_min⟩ := smallestDivisorAux_spec n hn 𝟚 n (le_refl 𝟚) hn hfuel
      -- h_min : ∀ e, le₀ 𝟚 e → lt₀ e (smallestDivisorAux n 𝟚 n) → dividesb e n = false
      -- Reescribir usando h_sd:
      have h_sd_raw : smallestDivisorAux n 𝟚 n = n := h_sd
      rw [h_sd_raw] at h_min
      -- h_min : ∀ e, le₀ 𝟚 e → lt₀ e n → dividesb e n = false
      refine ⟨hn1, fun a b hab => ?_⟩
      by_cases ha1 : a = 𝟙
      · exact Or.inl ha1
      · by_cases hb1 : b = 𝟙
        · exact Or.inr hb1
        · exfalso
          have ha0 : a ≠ 𝟘 := by
            intro h0; rw [h0, zero_mul] at hab; exact hn0 hab.symm
          have hb0 : b ≠ 𝟘 := by
            intro h0; rw [h0, mul_zero] at hab; exact hn0 hab.symm
          have ha2 : le₀ 𝟚 a := by
            rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 ha0) with h | h
            · exact lt_then_le_succ_wp h
            · exact absurd h.symm ha1
          have hb2 : le₀ 𝟚 b := by
            rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hb0) with h | h
            · exact lt_then_le_succ_wp h
            · exact absurd h.symm hb1
          have ha_lt : lt₀ a n := by
            rw [← hab]
            exact lt_of_lt_of_le
              (by have := mul_lt_right a 𝟚 ha0 (lt_succ_self 𝟙)
                  rwa [mul_comm 𝟚 a] at this)
              (by have := mul_le_mono_right a hb2
                  rwa [mul_comm 𝟚 a, mul_comm b a] at this)
          have h_no_div : dividesb a n = false := h_min a ha2 ha_lt
          have h_yes_div : dividesb a n = true :=
            dvd_imp_dividesb_true ha0 ⟨b, hab.symm⟩
          exact absurd h_yes_div (Bool.eq_false_iff.mp h_no_div)

    /-- Construye la factorización prima de `n` acumulando en `acc`.
        En cada paso extrae el menor divisor `p` con `smallestDivisor`,
        lo añade vía `addFactor` y recurre con `n / p`.
        `fuel` controla la terminación.
        Computable: Sí. Dependencias: `smallestDivisor`, `FactFSet.addFactor`. -/
    def factorizeAux : ℕ₀ → ℕ₀ → FactFSet → FactFSet
      | _, .zero, acc => acc
      | n, .succ fuel', acc =>
        let p := smallestDivisor n
        if hp0 : p = 𝟘 then acc
        else
          let p₁ : ℕ₁ := ⟨p, hp0⟩
          if hp1 : p₁.val = 𝟙 then acc
          else
            let p₂ : ℕ₂ := ⟨p₁, hp1⟩
            let n' := n / p
            if le₀ 𝟚 n' then
              factorizeAux n' fuel' (acc.addFactor p₂)
            else
              acc.addFactor p₂

    /-- Factorización prima computable de `n ∈ ℕ₂`.
        Devuelve un `FactFSet` — lista de pares `(primo, exponente)`
        ordenada por base, con exponentes ≥ 1.
        Computable: Sí. Dependencias: `smallestDivisor`, `FactFSet.addFactor`. -/
    def factorize (n : ℕ₂) : FactFSet :=
      factorizeAux n.val.val n.val.val FactFSet.empty
    -- ══════════════════════════════════════════════════════════════════
    -- § 6. Todo n ≥ 2 tiene un divisor primo
    -- ══════════════════════════════════════════════════════════════════

    /-- Irreducible implica "prima para divisibilidad de productos"
        (usa coprime_dvd_of_dvd_mul para el caso gcd = 1). -/
    private theorem irreducible_prime_dvd_mul {p a b : ℕ₀}
        (hirr : Irreducible p) (hdvd : p ∣ mul a b) : p ∣ a ∨ p ∣ b := by
      have hp0 : p ≠ 𝟘 := by
        intro h0; rw [h0] at hirr
        exact absurd ((hirr.2 𝟘 𝟘 (by rw [zero_mul])).elim id id).symm (succ_neq_zero 𝟘)
      by_cases h_mod : (a % p) = 𝟘
      · -- a % p = 0 → p ∣ a
        left
        have h_spec : a = add (mul (a / p) p) (a % p) := divMod_spec a p hp0
        rw [h_mod, add_zero] at h_spec
        exact ⟨a / p, h_spec.trans (mul_comm _ _)⟩
      · -- a % p ≠ 0 → ¬(p ∣ a) → gcd(p,a) = 1 → Gauss → p ∣ b
        right
        have h : ¬ p ∣ a := by
          intro ⟨k, hk⟩
          have h_dvd_mod : p ∣ (a % p) := divides_mod ⟨k, hk⟩ (divides_refl p)
          have h_mod_lt : lt₀ (a % p) p := mod_lt a p hp0
          exact h_mod (by
            by_cases h_ne : (a % p) = 𝟘
            · exact h_ne
            · exact absurd h_mod_lt (le_not_lt (divides_le h_dvd_mod h_ne)))
        -- gcd(p,a) ∣ p, y p irreducible → gcd(p,a) = 1 ó gcd(p,a) = p
        have hg_p := gcd_dvd_left p a
        -- Usamos irreducible para factorizar p:
        -- Si existiera k con p = gcd(p,a) · k, entonces hirr.2 dictamina
        -- gcd(p,a) = 1 ó k = 1 (i.e., gcd(p,a) = p → p ∣ a → absurdo)
        -- El testigo k = p / gcd(p,a); la igualdad requiere un lema de Div:
        --   p = gcd(p,a) · (p / gcd(p,a)) + (p % gcd(p,a))
        -- y gcd(p,a) ∣ p → p % gcd(p,a) = 0 → p = gcd(p,a) · (p / gcd(p,a))
        -- Esto es: divMod_spec + mod_eq_zero_iff_divides (de PeanoNatArith ℕ₁)
        -- Por ahora queda pendiente este paso auxiliar:
        have h_factor : ∃ k, p = mul (gcd p a) k := by
          rcases hg_p with ⟨k, hk⟩; exact ⟨k, hk⟩
        rcases h_factor with ⟨k, hk⟩
        rcases hirr.2 (gcd p a) k hk.symm with hg1 | hk1
        · -- gcd(p,a) = 1 → Coprime p a → Gauss → p ∣ b
          have hcop : Coprime p a :=
            (gcd_eq_one_iff_coprime p a).mp hg1
          exact coprime_dvd_of_dvd_mul hcop hdvd
        · -- k = 1 → gcd(p,a) = p → p ∣ a: contradicción
          have : gcd p a = p := by
            rw [hk1, mul_one] at hk; exact hk.symm
          exact absurd (this ▸ gcd_dvd_right p a) h

    /-- Todo n ≥ 2 tiene un divisor primo. -/
    theorem exists_prime_divisor (n : ℕ₀) (hn : le₀ 𝟚 n) :
        ∃ p, Prime p ∧ p ∣ n := by
      induction n using well_founded_lt.induction
      rename_i n ih
      by_cases h_eq : smallestDivisor n = n
      · -- smallestDivisor n = n → n es irreducible
        have hirr := smallestDivisor_eq_self_imp_irreducible hn h_eq
        refine ⟨n,
          ⟨fun h0 => absurd ((hirr.2 𝟘 𝟘 (by rw [h0, mul_zero])).elim id id).symm
                             (succ_neq_zero 𝟘),
           hirr.1,
           fun a b hdvd => irreducible_prime_dvd_mul hirr hdvd⟩,
          divides_refl n⟩
      · -- smallestDivisor n ≠ n → usar a := smallestDivisor n como divisor propio
        have ha_dvd : smallestDivisor n ∣ n := smallestDivisor_dvd hn
        have ha2 : le₀ 𝟚 (smallestDivisor n) := smallestDivisor_ge_two hn
        have ha_le : le₀ (smallestDivisor n) n := smallestDivisor_le hn
        have ha_lt_n : lt₀ (smallestDivisor n) n :=
          lt_of_le_neq_wp ha_le h_eq
        rcases ih (smallestDivisor n) ha_lt_n ha2 with ⟨p, hp, h_pa⟩
        exact ⟨p, hp, divides_trans h_pa ha_dvd⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § 7. TFA — Existencia de factorización prima
    -- ══════════════════════════════════════════════════════════════════

    theorem exists_prime_factorization (n : ℕ₀) (hn : le₀ 𝟚 n) :
        ∃ ps : List ℕ₀, PrimeList ps ∧ product_list ps = n := by
      induction n using well_founded_lt.induction
      rename_i n ih
      by_cases h_eq : smallestDivisor n = n
      · -- smallestDivisor n = n → n irreducible → n primo
        have hirr := smallestDivisor_eq_self_imp_irreducible hn h_eq
        have hn_prime : Prime n :=
          ⟨fun h0 => absurd ((hirr.2 𝟘 𝟘 (by rw [h0, mul_zero])).elim id id).symm
                             (succ_neq_zero 𝟘),
           hirr.1,
           fun a b hdvd => irreducible_prime_dvd_mul hirr hdvd⟩
        exact ⟨[n],
               fun p hp =>
                 (mem_cons p n []).mp hp |>.elim (· ▸ hn_prime) (fun h => absurd h List.not_mem_nil),
               by simp [product_list, mul_one]⟩
      · -- smallestDivisor n ≠ n → factores a := sd n, b := n / a
        have hn0 : n ≠ 𝟘 := by
          rintro rfl; rcases hn with h | h
          · exact lt_zero 𝟚 h
          · exact absurd h (succ_neq_zero 𝟙)
        have ha_dvd : smallestDivisor n ∣ n := smallestDivisor_dvd hn
        have ha2 : le₀ 𝟚 (smallestDivisor n) := smallestDivisor_ge_two hn
        have ha0 : smallestDivisor n ≠ 𝟘 := by
          intro h0; rw [h0] at ha2
          exact lt_zero 𝟚 (Or.resolve_right ha2 (succ_neq_zero 𝟙))
        let b := div n (smallestDivisor n)
        have h_mul : mul b (smallestDivisor n) = n :=
          div_mul_cancel ha0 ha_dvd
        have hb0 : b ≠ 𝟘 := by
          intro h0; rw [h0, zero_mul] at h_mul; exact hn0 h_mul.symm
        have hb1 : b ≠ 𝟙 := by
          intro h1; rw [h1, one_mul] at h_mul; exact h_eq h_mul
        have hb2 : le₀ 𝟚 b := by
          rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hb0) with h_lt | h_eq'
          · exact lt_then_le_succ_wp h_lt
          · exact absurd h_eq'.symm hb1
        have ha_lt_n : lt₀ (smallestDivisor n) n :=
          lt_of_le_neq_wp (smallestDivisor_le hn) h_eq
        have hb_lt_n : lt₀ b n := by
          rw [← h_mul, mul_comm]
          exact lt_of_lt_of_le
            (by have := mul_lt_right b 𝟚 hb0 (lt_succ_self 𝟙)
                rwa [mul_comm 𝟚 b] at this)
            (by have := mul_le_mono_right b ha2
                rwa [mul_comm 𝟚 b] at this)
        obtain ⟨ps_a, hps_a, h_prod_a⟩ := ih (smallestDivisor n) ha_lt_n ha2
        obtain ⟨ps_b, hps_b, h_prod_b⟩ := ih b hb_lt_n hb2
        refine ⟨ps_a ++ ps_b, ?_, ?_⟩
        · intro p hm
          rw [mem_append] at hm
          exact hm.elim (hps_a p) (hps_b p)
        · rw [product_append, h_prod_a, h_prod_b, mul_comm, h_mul]

    -- ══════════════════════════════════════════════════════════════════
    -- § 8. TFA — Unicidad de la factorización prima
    -- ══════════════════════════════════════════════════════════════════

    theorem mem_dvd_product {q : ℕ₀} {l : List ℕ₀} (h : q ∈ l) :
        q ∣ product_list l := by
      induction l with
      | nil => exact absurd h List.not_mem_nil
      | cons x xs ih =>
        rcases (mem_cons q x xs).mp h with h_eq | h_mem
        · simp [product_list]; rw [← h_eq]
          exact divides_mul_right (divides_refl q)
        · simp [product_list]
          exact divides_trans (ih h_mem) (divides_mul_left (divides_refl _))

    -- ──────────────────────────────────────────────────────────────────
    -- Auxiliares para unicidad (remove_one y propiedades)
    -- ──────────────────────────────────────────────────────────────────

    /-- Elimina la primera ocurrencia de p. -/
    private def remove_one (p : ℕ₀) : List ℕ₀ → List ℕ₀
      | []       => []
      | q :: qs => if q = p then qs else q :: (remove_one p qs)

    private theorem product_remove_one {p : ℕ₀} :
        ∀ l : List ℕ₀, p ∈ l →
          product_list l = mul p (product_list (remove_one p l)) := by
      intro l hm
      induction l with
      | nil => exact absurd hm List.not_mem_nil
      | cons q qs ih =>
        by_cases h : q = p
        · subst h
          simp [remove_one, product_list]
        · simp only [remove_one, if_neg h, product_list]
          rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd rfl h
          · rw [ih hm, ← mul_assoc, mul_comm q p, mul_assoc]

    private theorem primelist_remove_one {p : ℕ₀} {l : List ℕ₀}
        (hm : p ∈ l) (hpl : PrimeList l) : PrimeList (remove_one p l) := by
      induction l with
      | nil => exact absurd hm List.not_mem_nil
      | cons q qs ih =>
        by_cases h : q = p
        · subst h
          simp only [remove_one]
          intro r hr; exact hpl r (List.mem_cons.mpr (Or.inr hr))
        · simp only [remove_one, if_neg h]
          rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd rfl h
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hpl r (List.mem_cons.mpr (Or.inl rfl))
            · exact ih hm (fun r hr => hpl r (List.mem_cons.mpr (Or.inr hr))) r hr

    /-- Quitar p de l no afecta la longitud del filtro de p' ≠ p. -/
    private theorem filter_count_neq {p p' : ℕ₀} (hne : p ≠ p') :
        ∀ l : List ℕ₀, p ∈ l →
          lengthₚ (List.filter (fun q => decide (q = p')) l) =
          lengthₚ (List.filter (fun q => decide (q = p')) (remove_one p l)) := by
      intro l
      induction l with
      | nil => intro hm; exact absurd hm List.not_mem_nil
      | cons q qs ih =>
        intro hm
        by_cases hqp : q = p
        · subst hqp
          simp only [remove_one, List.filter]
          have : decide (q = p') = false := by simp [hne]
          simp [this]
        · simp only [remove_one, if_neg hqp, List.filter]
          rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd rfl hqp
          · by_cases hqp' : q = p'
            · simp only [show decide (q = p') = true from decide_eq_true_eq.mpr hqp',
                         lengthₚ_cons]
              exact congrArg (fun n => σ n) (ih hm)
            · have : decide (q = p') = false := by simp [hqp']
              simp only [this]
              exact ih hm

    /-- La multiplicidad de p en l es 1 + la multiplicidad en remove_one p l. -/
    private theorem filter_count_eq {p : ℕ₀} :
        ∀ l : List ℕ₀, p ∈ l →
          lengthₚ (List.filter (fun q => decide (q = p)) l) =
          σ (lengthₚ (List.filter (fun q => decide (q = p)) (remove_one p l))) := by
      intro l
      induction l with
      | nil => intro hm; exact absurd hm List.not_mem_nil
      | cons q qs ih =>
        intro hm
        by_cases h : q = p
        · simp [h, remove_one, List.filter, lengthₚ_cons]
        · simp only [remove_one, if_neg h, List.filter]
          have hdf : decide (q = p) = false := by simp [h]
          simp only [hdf]
          rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd rfl h
          · exact ih hm

    private theorem prime_list_nil_of_prod_one {qs : List ℕ₀}
        (hpl : PrimeList qs) (h : product_list qs = 𝟙) : qs = [] := by
      cases qs with
      | nil => rfl
      | cons q qs' =>
        rw [product_cons] at h
        exact absurd (mul_eq_one h).1 (prime_ne_one (hpl q (List.mem_cons.mpr (Or.inl rfl))))

    /-- **TFA — Unicidad.** Dos listas de primos con igual producto tienen
        la misma multiplicidad para cada primo. -/
    theorem unique_prime_factorization :
        ∀ ps qs : List ℕ₀,
          PrimeList ps → PrimeList qs →
          product_list ps = product_list qs →
          ∀ p : ℕ₀, Prime p →
            lengthₚ (List.filter (fun q => decide (q = p)) ps) =
            lengthₚ (List.filter (fun q => decide (q = p)) qs) := by
      intro ps
      induction ps with
      | nil =>
        intro qs _ hqs h_prod p _
        rw [product_nil] at h_prod
        have hqs_nil := prime_list_nil_of_prod_one hqs h_prod.symm
        subst hqs_nil
        simp [List.filter, lengthₚ]
      | cons p₀ ps' ih =>
        intro qs hps hqs h_prod p hp
        have hp₀     : Prime p₀    := hps p₀ (List.mem_cons.mpr (Or.inl rfl))
        have hps'    : PrimeList ps' := fun r hr => hps r (List.mem_cons.mpr (Or.inr hr))
        rw [product_cons] at h_prod
        -- p₀ ∣ ∏ qs
        have hp₀_dvd : p₀ ∣ product_list qs := ⟨product_list ps', h_prod.symm⟩
        -- ∃ q ∈ qs, p₀ ∣ q
        obtain ⟨q, hq_mem, hq_dvd⟩ := prime_dvd_product_list hp₀ qs hp₀_dvd
        -- q primo y p₀ ∣ q  →  p₀ = q
        have hq_prime : Prime q := hqs q hq_mem
        rcases prime_divisors hq_prime hq_dvd with h1 | heq
        · exact absurd h1 (prime_ne_one hp₀)
        · have hp₀_mem : p₀ ∈ qs := heq ▸ hq_mem
          -- qs' = qs sin una copia de p₀
          have hqs'    : PrimeList (remove_one p₀ qs) :=
            primelist_remove_one hp₀_mem hqs
          have h_prod_qs : product_list qs = mul p₀ (product_list (remove_one p₀ qs)) :=
            product_remove_one qs hp₀_mem
          -- cancelar p₀
          have h_prod' : product_list ps' = product_list (remove_one p₀ qs) :=
            mul_cancelation_left p₀ _ _ (prime_ne_zero hp₀) (h_prod.trans h_prod_qs)
          have ih_eq := ih (remove_one p₀ qs) hps' hqs' h_prod' p hp
          by_cases h_pp₀ : p = p₀
          · subst h_pp₀
            -- count p₀ (p₀ :: ps') = σ (count p₀ ps')
            simp [List.filter, lengthₚ_cons]
            -- count p₀ qs = σ (count p₀ (remove_one p₀ qs))
            rw [filter_count_eq qs hp₀_mem]
            rw [ih_eq]
          · -- count p (p₀ :: ps') = count p ps'  (p ≠ p₀)
            simp [List.filter, Ne.symm h_pp₀]
            -- count p qs = count p (remove_one p₀ qs)
            rw [filter_count_neq (Ne.symm h_pp₀) qs hp₀_mem]
            exact ih_eq


    -- ══════════════════════════════════════════════════════════════════
    -- § 9. Alias exportable de Prime y conjunto ℙ
    -- ══════════════════════════════════════════════════════════════════

    /-- Alias de `Peano.Arith.Prime` en el namespace `Peano.Primes`,
        para que sea exportable junto con los resultados de este módulo.
        Computable: No (Prop). Dependencias: `Peano.Arith.Prime`. -/
    abbrev Prime (p : ℕ₀) : Prop := Peano.Arith.Prime p

    /-- El **conjunto de los números primos** como subtipo de ℕ₂.
        ℙ := { n ∈ ℕ₂ // Prime n.val.val }
        donde ℕ₂ = { n : ℕ₁ // n.val ≠ 1 } y ℕ₁ = { n : ℕ₀ // n ≠ 0 },
        de modo que todo n : ℙ satisface n ≠ 0, n ≠ 1, y es primo.
        Computable: No (Prop). Dependencias: `ℕ₂`, `Prime`. -/
    def ℙ : Type := {n : ℕ₂ // Prime n.val.val}

    -- ══════════════════════════════════════════════════════════════════
    -- § 9. Decidabilidad de Prime
    -- ══════════════════════════════════════════════════════════════════

    /-- Si `p` es primo, `smallestDivisor p = p`. -/
    theorem prime_imp_smallestDivisor_eq_self {p : ℕ₀} (hp : Prime p) :
        smallestDivisor p = p := by
      have h2 : le₀ 𝟚 p := prime_ge_two hp
      have h_dvd := smallestDivisor_dvd h2
      have h_ge2 := smallestDivisor_ge_two h2
      rcases prime_divisors hp h_dvd with h1 | heq
      · -- smallestDivisor p = 𝟙, contradice ≥ 2
        exfalso
        rw [h1] at h_ge2
        exact le_then_ngt 𝟚 𝟙 h_ge2 (lt_succ_self 𝟙)
      · exact heq

    /-- Test booleano de primalidad: computable. -/
    def isPrimeb (n : ℕ₀) : Bool :=
      ble₀ 𝟚 n && decide (smallestDivisor n = n)

    /-- `isPrimeb n = true ↔ Prime n`. -/
    theorem isPrimeb_iff {n : ℕ₀} :
        isPrimeb n = true ↔ Prime n := by
      constructor
      · intro h
        simp [isPrimeb, Bool.and_eq_true] at h
        obtain ⟨h_ble, h_sd⟩ := h
        have h2 : le₀ 𝟚 n := (ble_iff_Le 𝟚 n).mp h_ble
        have hirr := smallestDivisor_eq_self_imp_irreducible h2 h_sd
        have hn0 : n ≠ 𝟘 := by
          rintro rfl; exact lt_zero 𝟚 (Or.resolve_right h2 (succ_neq_zero 𝟙))
        exact irreducible_imp_prime hn0 hirr
      · intro hp
        simp [isPrimeb, Bool.and_eq_true]
        exact ⟨(ble_iff_Le 𝟚 n).mpr (prime_ge_two hp),
               prime_imp_smallestDivisor_eq_self hp⟩

    instance decidablePrime (n : ℕ₀) : Decidable (Prime n) :=
      if h : isPrimeb n = true
      then isTrue (isPrimeb_iff.mp h)
      else isFalse (fun hp => h (isPrimeb_iff.mpr hp))

  end Primes

end Peano

export Peano.Primes (
    Prime
    ℙ
    Irreducible
    HasExactlyTwoDivisors
    prime_ne_zero
    prime_ge_two
    prime_divisors
    prime_ne_one
    irreducible_imp_prime
    prime_iff_irreducible
    not_has_two_divisors_one
    not_has_two_divisors_zero
    prime_iff_has_exactly_two_divisors
    PrimeList
    product_list_pos
    prime_dvd_product_list
    prime_dvd_mul
    exists_prime_divisor
    exists_prime_factorization
    unique_prime_factorization
    smallestDivisorAux_spec
    smallestDivisor
    smallestDivisor_not_dvd_of_lt
    smallestDivisor_le_of_prime_dvd
    smallestDivisor_prime
    factorize
    isPrimeb
    isPrimeb_iff
    decidablePrime
    dividesb_true_imp_dvd
    dvd_imp_dividesb_true
    dividesb_iff_dvd
    decidableDvd
)
