/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- PeanoNatLib/PeanoNatPrimes.lean
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

import PeanoNatLib.PeanoNatArith

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
      open Peano.MaxMin
      open Peano.Arith
      open Classical

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

    theorem one_lt_prime {p : ℕ₀} (hp : Prime p) : Lt 𝟙 p := by
      rcases trichotomy 𝟙 p with h | h | h
      · exact h
      · exact absurd h.symm (prime_ne_one hp)
      · exact absurd (lt_b_1_then_b_eq_0 h) (prime_ne_zero hp)

    theorem prime_ge_two {p : ℕ₀} (hp : Prime p) : Le 𝟚 p := by
      -- 𝟚 = σ 𝟙;  tricotomía entre σ 𝟙 y p
      rcases trichotomy (σ 𝟙) p with h_lt | h_eq | h_gt
      · exact Or.inl h_lt
      · exact Or.inr h_eq
      · -- h_gt : Lt p (σ 𝟙);  lt_then_le_succ_wp → Le p 𝟙
        have h_le : Le p 𝟙 := lt_then_le_succ_wp h_gt
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
      have ha_le : Le a 𝟙 := divides_le ⟨b, h.symm⟩ (succ_neq_zero 𝟘)
      have hb_le : Le b 𝟙 := divides_le ⟨a, h.symm.trans (mul_comm a b)⟩ (succ_neq_zero 𝟘)
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

    /-- **Irreducible → Prime**: si p es irreducible (y p ≠ 0), entonces es primo.
        La demostración usa el lema de Gauss (coprime_dvd_of_dvd_mul), que a su
        vez depende de bezout_natform y aritmética de resta. Transitivamente
        hereda los sorry de coprime_dvd_of_dvd_mul. -/
    theorem irreducible_imp_prime {p : ℕ₀} (hp0 : p ≠ 𝟘) (hirr : Irreducible p) :
        Prime p :=
      ⟨hp0, hirr.1, fun a b hdvd => by
        -- gcd(p, a) divide a p
        rcases gcd_dvd_left p a with ⟨k, hk⟩
        -- hk : p = mul (gcd p a) k  (por definición de divisibilidad)
        -- Irreducibilidad de p: gcd(p,a) = 1 ó k = 1
        rcases hirr.2 (gcd p a) k hk.symm with h1 | hk1
        · -- gcd(p, a) = 1  →  Coprime p a  →  Gauss  →  p ∣ b
          -- (gcd_eq_one_iff_coprime y coprime_dvd_of_dvd_mul se definen en §3;
          --  hasta que se refactorice el orden, sorry transitivo aquí)
          exact Or.inr (by sorry)
        · -- k = 1  →  gcd(p, a) = p  →  p ∣ a
          have hgp : gcd p a = p := by
            rw [hk1, mul_one] at hk; exact hk.symm
          exact Or.inl (hgp ▸ gcd_dvd_right p a)⟩

    -- ──────────────────────────────────────────────────────────────────
    -- Equivalencias entre definiciones de primo
    -- ──────────────────────────────────────────────────────────────────

    /-- **Def. C ↔ Def. A**: Prime (Euclides) es equivalente a p ≠ 0 ∧ Irreducible.
        La dirección ← hereda el sorry de coprime_dvd_of_dvd_mul. -/
    theorem prime_iff_irreducible {p : ℕ₀} :
        Prime p ↔ (p ≠ 𝟘 ∧ Irreducible p) := by
      constructor
      · intro hp
        exact ⟨prime_ne_zero hp, prime_imp_irreducible hp⟩
      · intro ⟨hp0, hirr⟩
        exact irreducible_imp_prime hp0 hirr

    /-- **Def. B**: p tiene exactamente dos divisores — todos los divisores de p
        son 1 ó p, y p ≠ 1. Esta formulación excluye automáticamente p = 0
        (porque todo natural divide a 0) y p = 1 (por la segunda cláusula). -/
    def HasExactlyTwoDivisors (p : ℕ₀) : Prop :=
      (∀ d : ℕ₀, d ∣ p → d = 𝟙 ∨ d = p) ∧ p ≠ 𝟙

    /-- 1 no tiene exactamente dos divisores (la condición p ≠ 1 falla). -/
    theorem not_has_two_divisors_one : ¬ HasExactlyTwoDivisors 𝟙 :=
      fun h => h.2 rfl

    /-- 0 no tiene exactamente dos divisores: 𝟚 ∣ 0 pero 𝟚 ≠ 1 y 𝟚 ≠ 0. -/
    theorem not_has_two_divisors_zero : ¬ HasExactlyTwoDivisors 𝟘 := by
      intro ⟨hall, _⟩
      rcases hall 𝟚 (divides_zero 𝟚) with h | h
      · -- 𝟚 = 𝟙: succ_inj_pos_wp da σ𝟘 = 𝟘, absurdo por succ_neq_zero
        exact absurd (succ_inj_pos_wp h) (succ_neq_zero 𝟘)
      · -- 𝟚 = 𝟘: σ(σ𝟘) = 𝟘  →  absurdo
        exact absurd h (succ_neq_zero (σ 𝟘))

    /-- **Def. C ↔ Def. B**: Prime es equivalente a HasExactlyTwoDivisors.
        Dirección →: prime_divisors + prime_ne_one.
        Dirección ←: reducir a irreducible_imp_prime (hereda sorry de Gauss). -/
    theorem prime_iff_has_exactly_two_divisors {p : ℕ₀} :
        Prime p ↔ HasExactlyTwoDivisors p := by
      constructor
      · intro hp
        exact ⟨fun d hd => prime_divisors hp hd, prime_ne_one hp⟩
      · intro ⟨hall, hp1⟩
        -- p ≠ 0: si p = 0, entonces 𝟚 ∣ 0, pero hall daría 𝟚 = 1 ó 𝟚 = 0 — ambas falsas
        have hp0 : p ≠ 𝟘 := by
          intro h0
          subst h0
          rcases hall 𝟚 (divides_zero 𝟚) with h | h
          · exact absurd (succ_inj_pos_wp h) (succ_neq_zero 𝟘)
          · exact absurd h (succ_neq_zero (σ 𝟘))
        apply irreducible_imp_prime hp0
        refine ⟨hp1, fun a b hab => ?_⟩
        rcases hall a ⟨b, hab.symm⟩ with ha1 | hap
        · exact Or.inl ha1
        · right
          -- a = p y a·b = p  →  p·b = p·1  →  b = 1
          rw [← hap] at hab
          exact mul_cancelation_left a b 𝟙 (hap ▸ hp0)
            (hab.trans (mul_one a).symm)

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

    theorem prime_coprime_or_dvd {p n : ℕ₀} (hp : Prime p) : p ∣ n ∨ Coprime p n :=
      (em (p ∣ n)).imp id
        (fun h => (gcd_eq_one_iff_coprime p n).mp (prime_not_dvd_imp_coprime hp h))

    /-- **Lema de Gauss**: mcd(a,b) = 1 ∧ a ∣ b·c → a ∣ c.
        La demostración usa bezout_natform y sub_k_add_k/subₕₖ_eq_iff_eq_add_of_le.
        Los pasos de aritmética que involucran resta saturada se marcan con sorry
        mientras se completan las lemmas adicionales de PeanoNatSub. -/
    theorem coprime_dvd_of_dvd_mul {a b c : ℕ₀}
        (hcop : Coprime a b) (hdvd : a ∣ mul b c) : a ∣ c := by
      rw [← gcd_eq_one_iff_coprime] at hcop
      obtain ⟨n, m, h_bez⟩ := bezout_natform a b
      rw [hcop] at h_bez
      -- Tratar c = 0 de forma especial
      rcases em (c = 𝟘) with hc0 | hc_ne
      · rw [hc0]; exact divides_zero a
      rcases h_bez with h | h
      · -- Caso 1: 𝟙 = sub (mul n a) (mul m b)
        -- (Aritmética de resta natural: sorry pendiente de completar)
        have h_lt : Lt (mul m b) (mul n a) := by
          exact (sub_pos_iff_lt (mul n a) (mul m b)).mp (h ▸ Or.inr rfl)
        -- mul n a = mul m b + 1
        -- multiplicar por c → mul (mul n a) c = mul (mul m b) c + c
        -- a ∣ mul (mul n a) c y a ∣ mul (mul m b) c → a ∣ c
        have h1 : a ∣ mul (mul n a) c := by
          rw [mul_assoc]; exact divides_mul_left (divides_mul_right (divides_refl a))
        have h2 : a ∣ mul (mul m b) c := by
          rw [mul_assoc]; exact divides_mul_left hdvd
        -- sub (mul (mul n a) c) (mul (mul m b) c) = c
        -- (Requiere probar que mul (mul n a) c = mul (mul m b) c + c,
        --  lo que se sigue de: 1 = n·a − m·b → n·a = m·b + 1 → n·a·c = m·b·c + c)
        have h_sub_c : sub (mul (mul n a) c) (mul (mul m b) c) = c := by sorry
        have h_lt2 : Lt (mul (mul m b) c) (mul (mul n a) c) := by sorry
        rw [← h_sub_c]
        exact divides_sub h_lt2 h1 h2
      · -- Caso 2: 𝟙 = sub (mul n b) (mul m a)  (simétrico)
        have h_lt : Lt (mul m a) (mul n b) := by
          exact (sub_pos_iff_lt (mul n b) (mul m a)).mp (h ▸ Or.inr rfl)
        have h1 : a ∣ mul (mul n b) c := by
          rw [mul_assoc]; exact divides_mul_left hdvd
        have h2 : a ∣ mul (mul m a) c := by
          rw [mul_assoc]; exact divides_mul_left (divides_mul_right (divides_refl a))
        have h_sub_c : sub (mul (mul n b) c) (mul (mul m a) c) = c := by sorry
        have h_lt2 : Lt (mul (mul m a) c) (mul (mul n b) c) := by sorry
        rw [← h_sub_c]
        exact divides_sub h_lt2 h1 h2

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Listas de primos y función producto
    -- ══════════════════════════════════════════════════════════════════

    def PrimeList (ps : DList ℕ₀) : Prop :=
      ∀ p, DList.Mem p ps → Prime p

    def product_list : DList ℕ₀ → ℕ₀
      | DList.nil       => 𝟙
      | DList.cons p ps => mul p (product_list ps)

    @[simp] theorem product_nil : product_list DList.nil = 𝟙 := rfl

    @[simp] theorem product_cons (p : ℕ₀) (ps : DList ℕ₀) :
        product_list (DList.cons p ps) = mul p (product_list ps) := rfl

    theorem product_append (l1 l2 : DList ℕ₀) :
        product_list (DList.append l1 l2) =
          mul (product_list l1) (product_list l2) := by
      induction l1 with
      | nil => simp [DList.append, one_mul]
      | cons p ps ih => simp [DList.append, ih, mul_assoc]

    theorem product_list_pos {ps : DList ℕ₀} (hps : PrimeList ps) :
        Lt 𝟘 (product_list ps) := by
      induction ps with
      | nil => exact lt_0_1
      | cons p ps ih =>
        simp [product_list]
        apply mul_pos
        · exact neq_0_then_lt_0 (prime_ne_zero (hps p (Or.inl rfl)))
        · exact ih (fun q hq => hps q (Or.inr hq))

    /-- **Euclides para listas**: p primo, p ∣ ∏ ps → ∃ q ∈ ps, p ∣ q. -/
    theorem prime_dvd_product_list {p : ℕ₀} (hp : Prime p) :
        ∀ ps : DList ℕ₀, p ∣ product_list ps →
          ∃ q, DList.Mem q ps ∧ p ∣ q := by
      intro ps
      induction ps with
      | nil =>
        simp [product_list]
        intro h
        -- p ∣ 1 y p ≥ 2, pero 1 < 2: contradicción
        have h_le_p_1 : Le p 𝟙 := divides_le h (succ_neq_zero 𝟘)
        have h_le_2_1 : Le 𝟚 𝟙 := le_trans 𝟚 p 𝟙 (prime_ge_two hp) h_le_p_1
        rcases h_le_2_1 with h_lt | h_eq
        · -- Lt (σ 𝟙) 𝟙: lt_succ_self 𝟙 da Lt 𝟙 (σ 𝟙), luego asimetría
          exact absurd h_lt (lt_asymm 𝟙 (σ 𝟙) (lt_succ_self 𝟙))
        · -- σ (σ 𝟘) = σ 𝟘: succ_inj da σ 𝟘 = 𝟘, absurdo
          exact absurd (succ_inj_pos_wp h_eq) (succ_neq_zero 𝟘)
      | cons q qs ih =>
        simp [product_list]
        intro h_dvd
        rcases hp.2.2 q (product_list qs) h_dvd with h_pq | h_pqs
        · exact ⟨q, Or.inl rfl, h_pq⟩
        · rcases ih h_pqs with ⟨r, hr_mem, hr_dvd⟩
          exact ⟨r, Or.inr hr_mem, hr_dvd⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § 5. Todo n ≥ 2 tiene un divisor primo
    -- ══════════════════════════════════════════════════════════════════

    /-- Irreducible implica "prima para divisibilidad de productos"
        (usa coprime_dvd_of_dvd_mul para el caso gcd = 1). -/
    private theorem irreducible_prime_dvd_mul {p a b : ℕ₀}
        (hirr : Irreducible p) (hdvd : p ∣ mul a b) : p ∣ a ∨ p ∣ b := by
      rcases em (p ∣ a) with h | h
      · exact Or.inl h
      · right
        -- gcd(p,a) ∣ p, y p irreducible → gcd(p,a) = 1 ó gcd(p,a) = p
        have hg_p := gcd_dvd_left p a
        -- Usamos irreducible para factorizar p:
        -- Si existiera k con p = gcd(p,a) · k, entonces hirr.2 dictamina
        -- gcd(p,a) = 1 ó k = 1 (i.e., gcd(p,a) = p → p ∣ a → absurdo)
        -- El testigo k = p / gcd(p,a); la igualdad requiere un lema de Div:
        --   p = gcd(p,a) · (p / gcd(p,a)) + (p % gcd(p,a))
        -- y gcd(p,a) ∣ p → p % gcd(p,a) = 0 → p = gcd(p,a) · (p / gcd(p,a))
        -- Esto es: divMod_eq + mod_eq_zero_iff_divides (de PeanoNatArith ℕ₁)
        -- Por ahora sorry este paso auxiliar:
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
    theorem exists_prime_divisor (n : ℕ₀) (hn : Le 𝟚 n) :
        ∃ p, Prime p ∧ p ∣ n := by
      induction n using well_founded_lt.induction
      rename_i n ih
      -- ¿Es n irreducible?
      rcases em (Irreducible n) with hirr | hnirr
      · -- n irreducible: construir Prime n
        refine ⟨n,
          ⟨fun h0 => absurd ((hirr.2 𝟘 𝟘 (by rw [h0, mul_zero])).elim id id).symm
                             (succ_neq_zero 𝟘),
           hirr.1,
           fun a b hdvd => irreducible_prime_dvd_mul hirr hdvd⟩,
          divides_refl n⟩
      · -- n no irreducible → ∃ a b, mul a b = n, a ≠ 1, b ≠ 1
        have hn0 : n ≠ 𝟘 := by
          rintro rfl
          rcases hn with h | h
          · exact lt_zero 𝟚 h
          · exact absurd h (succ_neq_zero 𝟙)
        have hn1 : n ≠ 𝟙 := by
          rintro rfl
          rcases hn with h | h
          · exact lt_asymm 𝟙 (σ 𝟙) (lt_succ_self 𝟙) h
          · exact absurd (succ_inj_pos_wp h) (succ_neq_zero 𝟘)
        have h_notfact : ∃ a b : ℕ₀, mul a b = n ∧ a ≠ 𝟙 ∧ b ≠ 𝟙 := by
          rw [Irreducible] at hnirr
          push_neg at hnirr
          rcases hnirr hn1 with ⟨a, b, h_ab, h_ne⟩
          exact ⟨a, b, h_ab,
            fun h => h_ne (Or.inl h),
            fun h => h_ne (Or.inr h)⟩
        obtain ⟨a, b, h_ab, ha1, hb1⟩ := h_notfact
        have ha0 : a ≠ 𝟘 := by
          intro h0; rw [h0, zero_mul] at h_ab; exact hn0 h_ab.symm
        have hb0 : b ≠ 𝟘 := by
          intro h0; rw [h0, mul_zero] at h_ab; exact hn0 h_ab.symm
        have ha2 : Le 𝟚 a := by
          rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 ha0) with h_lt | h_eq
          · exact lt_then_le_succ_wp h_lt
          · exact absurd h_eq.symm ha1
        have hb2 : Le 𝟚 b := by
          rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hb0) with h_lt | h_eq
          · exact lt_then_le_succ_wp h_lt
          · exact absurd h_eq.symm hb1
        -- a < n: n = a·b ≥ a·2 > a
        have ha_lt_n : Lt a n := by
          rw [← h_ab]
          have h1 : Lt a (mul a 𝟚) := by
            have := mul_lt_right a 𝟚 ha0 (lt_succ_self 𝟙)
            rwa [mul_comm 𝟚 a] at this
          have h2 : Le (mul a 𝟚) (mul a b) := by
            have := mul_le_mono_right a hb2
            rwa [mul_comm 𝟚 a, mul_comm b a] at this
          exact lt_of_lt_of_le h1 h2
        rcases ih a ha_lt_n ha2 with ⟨p, hp, h_pa⟩
        exact ⟨p, hp, divides_trans h_pa ⟨b, h_ab.symm⟩⟩

    -- ══════════════════════════════════════════════════════════════════
    -- § 6. TFA — Existencia de factorización prima
    -- ══════════════════════════════════════════════════════════════════

    theorem exists_prime_factorization (n : ℕ₀) (hn : Le 𝟚 n) :
        ∃ ps : DList ℕ₀, PrimeList ps ∧ product_list ps = n := by
      induction n using well_founded_lt.induction
      rename_i n ih
      rcases em (Irreducible n) with hirr | hnirr
      · have hn_prime : Prime n :=
          ⟨fun h0 => absurd ((hirr.2 𝟘 𝟘 (by rw [h0, mul_zero])).elim id id).symm
                             (succ_neq_zero 𝟘),
           hirr.1,
           fun a b hdvd => irreducible_prime_dvd_mul hirr hdvd⟩
        exact ⟨DList.cons n DList.nil,
               fun p hp =>
                 (mem_cons p n DList.nil).mp hp |>.elim (· ▸ hn_prime) False.elim,
               by simp [product_list, mul_one]⟩
      · have hn0 : n ≠ 𝟘 := by
          rintro rfl
          rcases hn with h | h
          · exact lt_zero 𝟚 h
          · exact absurd h (succ_neq_zero 𝟙)
        have hn1 : n ≠ 𝟙 := by
          rintro rfl
          rcases hn with h | h
          · exact lt_asymm 𝟙 (σ 𝟙) (lt_succ_self 𝟙) h
          · exact absurd (succ_inj_pos_wp h) (succ_neq_zero 𝟘)
        have h_notfact : ∃ a b : ℕ₀, mul a b = n ∧ a ≠ 𝟙 ∧ b ≠ 𝟙 := by
          rw [Irreducible] at hnirr
          push_neg at hnirr
          rcases hnirr hn1 with ⟨a, b, h_ab, h_ne⟩
          exact ⟨a, b, h_ab,
            fun h => h_ne (Or.inl h),
            fun h => h_ne (Or.inr h)⟩
        obtain ⟨a, b, h_ab, ha1, hb1⟩ := h_notfact
        have ha0 : a ≠ 𝟘 := by
          intro h0; rw [h0, zero_mul] at h_ab; exact hn0 h_ab.symm
        have hb0 : b ≠ 𝟘 := by
          intro h0; rw [h0, mul_zero] at h_ab; exact hn0 h_ab.symm
        have ha2 : Le 𝟚 a := by
          rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 ha0) with h_lt | h_eq
          · exact lt_then_le_succ_wp h_lt
          · exact absurd h_eq.symm ha1
        have hb2 : Le 𝟚 b := by
          rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hb0) with h_lt | h_eq
          · exact lt_then_le_succ_wp h_lt
          · exact absurd h_eq.symm hb1
        have ha_lt_n : Lt a n := by
          rw [← h_ab]
          have h1 : Lt a (mul a 𝟚) := by
            have := mul_lt_right a 𝟚 ha0 (lt_succ_self 𝟙)
            rwa [mul_comm 𝟚 a] at this
          exact lt_of_lt_of_le h1 (by
            have := mul_le_mono_right a hb2
            rwa [mul_comm 𝟚 a, mul_comm b a] at this)
        have hb_lt_n : Lt b n := by
          rw [← h_ab, mul_comm]
          have h1 : Lt b (mul b 𝟚) := by
            have := mul_lt_right b 𝟚 hb0 (lt_succ_self 𝟙)
            rwa [mul_comm 𝟚 b] at this
          exact lt_of_lt_of_le h1 (by
            have := mul_le_mono_right b ha2
            rwa [mul_comm 𝟚 b, mul_comm a b] at this)
        obtain ⟨ps_a, hps_a, h_prod_a⟩ := ih a ha_lt_n ha2
        obtain ⟨ps_b, hps_b, h_prod_b⟩ := ih b hb_lt_n hb2
        refine ⟨DList.append ps_a ps_b, ?_, ?_⟩
        · intro p hm
          rw [mem_append] at hm
          exact hm.elim (hps_a p) (hps_b p)
        · rw [product_append, h_prod_a, h_prod_b, h_ab]

    -- ══════════════════════════════════════════════════════════════════
    -- § 7. TFA — Unicidad de la factorización prima
    -- ══════════════════════════════════════════════════════════════════

    theorem mem_dvd_product {q : ℕ₀} {l : DList ℕ₀} (h : DList.Mem q l) :
        q ∣ product_list l := by
      induction l with
      | nil => exact h.elim
      | cons x xs ih =>
        rcases (mem_cons q x xs).mp h with h_eq | h_mem
        · simp [product_list]; rw [← h_eq]
          exact divides_mul_right (divides_refl q)
        · simp [product_list]
          exact divides_trans (ih h_mem) (divides_mul_left (divides_refl _))

    /-- **TFA — Unicidad.**
        Dos listas de primos con el mismo producto tienen la misma
        multiplicidad de cada primo.

        Esquema de la demostración (por inducción sobre length ps):
          Base: ps = nil → producto = 1 = producto qs → qs = nil.
          Paso: sea p₀ la cabeza de ps. Entonces p₀ ∣ ∏qs.
            Por prime_dvd_product_list, ∃ q ∈ qs tal que p₀ ∣ q.
            Como q es primo y p₀ primo: p₀ = q.
            Relocalizamos q al frente de qs y cancelamos p₀ en ambos productos.
            La IH da igualdad de multiplicidades para el resto.         -/
    theorem unique_prime_factorization :
        ∀ ps qs : DList ℕ₀,
          PrimeList ps → PrimeList qs →
          product_list ps = product_list qs →
          ∀ p : ℕ₀, Prime p →
            DList.length (DList.filter (fun q => decide (q = p)) ps) =
            DList.length (DList.filter (fun q => decide (q = p)) qs) := by
      sorry

  end Primes

end Peano
