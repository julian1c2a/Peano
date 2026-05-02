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
import Peano.PeanoNat.Lattice
import Peano.PeanoNat.NumberTheory.ChineseRemainder
import Peano.PeanoNat.Foundation.CantorPairing
import Peano.Prelim.Classical

set_option autoImplicit false

-- ─────────────────────────────────────────────────────────────────────────
-- § 0. Lema puro de Nat  (FUERA de `open Peano` para evitar la ambigüedad
--      con la coacción Nat → ℕ₀ que introduce ese `open`).
-- ─────────────────────────────────────────────────────────────────────────

-- Si (j-i) ∣ b e i < j, entonces gcd(1+(i+1)*b, 1+(j+1)*b) = 1.
private theorem nat_godel_coprime (b_n i_n j_n : Nat)
    (hij : i_n < j_n) (hdvd : @Dvd.dvd Nat Nat.instDvd (Nat.sub j_n i_n) b_n) :
    Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
            (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)) = 1 := by
  -- g = gcd(mi, mj) where mi=1+(i+1)*b, mj=1+(j+1)*b.  We show g | 1.
  -- Naming: mi = 1+(i_n+1)*b_n, mj = 1+(j_n+1)*b_n, d = j_n-i_n
  apply Nat.eq_one_of_dvd_one
  -- g | mi and g | mj
  have h_mi : @Dvd.dvd Nat Nat.instDvd
                (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                         (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n)) :=
    Nat.gcd_dvd_left _ _
  have h_mj : @Dvd.dvd Nat Nat.instDvd
                (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                         (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)) :=
    Nat.gcd_dvd_right _ _
  -- (A) (j_n+1)*b_n = (i_n+1)*b_n + (j_n-i_n)*b_n
  -- Key arithmetic: (i_n+1) + (j_n-i_n) = j_n+1
  --   (i_n+1) + (j_n-i_n)
  --   = (j_n-i_n) + (i_n+1)         [add_comm]
  --   = (j_n-i_n) + i_n + 1         [add_assoc.symm]
  --   = j_n + 1                      [sub_add_cancel]
  have key_add : Nat.add (Nat.add i_n 1) (Nat.sub j_n i_n) = Nat.add j_n 1 :=
    (Nat.add_comm (Nat.add i_n 1) (Nat.sub j_n i_n)).trans
      ((Nat.add_assoc (Nat.sub j_n i_n) i_n 1).symm.trans
        (congrArg (fun x => Nat.add x 1) (Nat.sub_add_cancel (Nat.le_of_lt hij))))
  have h_prod : Nat.mul (Nat.add j_n 1) b_n =
                Nat.add (Nat.mul (Nat.add i_n 1) b_n) (Nat.mul (Nat.sub j_n i_n) b_n) :=
    (congrArg (fun x => Nat.mul x b_n) key_add).symm.trans
      (Nat.add_mul (Nat.add i_n 1) (Nat.sub j_n i_n) b_n)
  -- (1) g | (j_n-i_n)*b_n
  -- h_sub : g | mj - mi.  We need: mj - mi = (j-i)*b
  -- mj - mi = (1+(j+1)*b) - (1+(i+1)*b)
  --         = (j+1)*b - (i+1)*b   [Nat.add_sub_add_left]
  --         = ((j+1)-(i+1))*b ... no, use h_prod
  --         = (i+1)*b + (j-i)*b - (i+1)*b   [h_prod]
  --         = (j-i)*b              [Nat.add_sub_cancel_left]
  have h_eq1 : Nat.sub (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n))
                       (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
               = Nat.mul (Nat.sub j_n i_n) b_n :=
    Eq.trans (Nat.add_sub_add_left 1 _ _)
      (Eq.trans (congrArg (Nat.sub · _) h_prod) (Nat.add_sub_cancel_left _ _))
  have h_g_dvd_db : @Dvd.dvd Nat Nat.instDvd
                      (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                               (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                      (Nat.mul (Nat.sub j_n i_n) b_n) :=
    h_eq1 ▸ (Nat.dvd_sub h_mj h_mi)
  -- (B) d * mi = d + (i_n+1) * (d * b_n)
  have h_alg : Nat.mul (Nat.sub j_n i_n) (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n)) =
               Nat.add (Nat.sub j_n i_n)
                       (Nat.mul (Nat.add i_n 1) (Nat.mul (Nat.sub j_n i_n) b_n)) :=
    (Nat.mul_add (Nat.sub j_n i_n) 1 (Nat.mul (Nat.add i_n 1) b_n)).trans
      ((congrArg (Nat.add · _) (Nat.mul_one _)).trans
        (congrArg (Nat.add _) (Nat.mul_left_comm _ _ _)))
  -- g | d*mi
  have h_g_dvd_d_mi : @Dvd.dvd Nat Nat.instDvd
                        (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                                 (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                        (Nat.mul (Nat.sub j_n i_n) (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))) :=
    Nat.dvd_mul_left_of_dvd h_mi (Nat.sub j_n i_n)
  -- g | (i_n+1)*(d*b_n)
  have h_g_dvd_ib_d : @Dvd.dvd Nat Nat.instDvd
                         (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                                  (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                         (Nat.mul (Nat.add i_n 1) (Nat.mul (Nat.sub j_n i_n) b_n)) :=
    Nat.dvd_mul_left_of_dvd h_g_dvd_db (Nat.add i_n 1)
  -- (2) g | d
  -- h_sub2 : g | d*mi - (i+1)*(d*b)
  -- d*mi - (i+1)*(d*b) = (d + (i+1)*(d*b)) - (i+1)*(d*b)   [h_alg]
  --                    = d                                    [Nat.add_sub_cancel_left]
  have h_eq2 : Nat.sub (Nat.mul (Nat.sub j_n i_n) (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n)))
                       (Nat.mul (Nat.add i_n 1) (Nat.mul (Nat.sub j_n i_n) b_n))
               = Nat.sub j_n i_n :=
    (congrArg (fun x => Nat.sub x _) h_alg).trans
      ((congrArg (Nat.sub · _) (Nat.add_comm _ _)).trans (Nat.add_sub_cancel_left _ _))
  have h_g_dvd_d : @Dvd.dvd Nat Nat.instDvd
                     (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                              (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                     (Nat.sub j_n i_n) :=
    h_eq2 ▸ (Nat.dvd_sub h_g_dvd_d_mi h_g_dvd_ib_d)
  -- (3) g | b_n
  have h_g_dvd_b : @Dvd.dvd Nat Nat.instDvd
                     (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                              (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                     b_n :=
    Nat.dvd_trans h_g_dvd_d hdvd
  -- (4) g | (i_n+1)*b_n
  have h_g_dvd_ib : @Dvd.dvd Nat Nat.instDvd
                      (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                               (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                      (Nat.mul (Nat.add i_n 1) b_n) :=
    Nat.dvd_mul_left_of_dvd h_g_dvd_b (Nat.add i_n 1)
  -- (5) g | 1:  mi - (i+1)*b = 1+(i+1)*b - (i+1)*b = 1
  have h_eq3 : Nat.sub (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                       (Nat.mul (Nat.add i_n 1) b_n) = 1 :=
    Nat.add_sub_cancel 1 _
  -- Construimos el dvd con tipo explícito, luego reescribimos h_eq3 sobre la hipótesis
  -- (▸ sobre la meta abstraería todos los '1' incluyendo los del gcd)
  have h_dvd_sub : @Dvd.dvd Nat Nat.instDvd
                     (Nat.gcd (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                              (Nat.add 1 (Nat.mul (Nat.add j_n 1) b_n)))
                     (Nat.sub (Nat.add 1 (Nat.mul (Nat.add i_n 1) b_n))
                              (Nat.mul (Nat.add i_n 1) b_n)) :=
    Nat.dvd_sub h_mi h_g_dvd_ib
  rw [h_eq3] at h_dvd_sub
  exact h_dvd_sub

namespace Peano
  open Peano

  namespace Foundation
    open Foundation

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
  open Peano.Lattice
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
    -- Traducir todo a Nat y aplicar nat_godel_coprime
    -- Paso 1: hdvd en Nat
    obtain ⟨k, hk⟩ := hdvd
    have hdvd_nat : @Dvd.dvd Nat Nat.instDvd (Nat.sub (Ψ j) (Ψ i)) (Ψ b) := by
      refine ⟨Ψ k, ?_⟩
      have := congrArg Ψ hk
      rw [isomorph_Ψ_mul, isomorph_Ψ_sub] at this
      exact this
    -- Paso 2: i < j en Nat
    have hij_nat : Ψ i < Ψ j := (isomorph_Ψ_lt i j).mp hij
    -- Paso 3: Nat.gcd = 1
    have hgcd_nat : Nat.gcd (Ψ (gmod b i)) (Ψ (gmod b j)) = 1 := by
      -- Ψ (gmod b k) = 1 + (k+1)*b en Nat
      have hi_eq : Ψ (gmod b i) = Nat.add 1 (Nat.mul (Nat.add (Ψ i) 1) (Ψ b)) := by
        unfold gmod
        rw [isomorph_Ψ_add, isomorph_Ψ_mul, isomorph_σ_Ψ]
        rfl
      have hj_eq : Ψ (gmod b j) = Nat.add 1 (Nat.mul (Nat.add (Ψ j) 1) (Ψ b)) := by
        unfold gmod
        rw [isomorph_Ψ_add, isomorph_Ψ_mul, isomorph_σ_Ψ]
        rfl
      rw [hi_eq, hj_eq]
      exact nat_godel_coprime (Ψ b) (Ψ i) (Ψ j) hij_nat hdvd_nat
    -- Paso 4: gcd (gmod b i) (gmod b j) = 𝟙
    have hgcd_eq : gcd (gmod b i) (gmod b j) = 𝟙 := by
      have h := isomorph_Ψ_gcd (gmod b i) (gmod b j)
      rw [hgcd_nat] at h
      -- h : Ψ (gcd ...) = 1 = Ψ 𝟙
      exact Ψ_inj _ _ h
    -- Paso 5: Coprime = IsGCD a b 𝟙, y tenemos IsGCD_gcd reescrito
    unfold Coprime
    rw [← hgcd_eq]
    exact IsGCD_gcd (gmod b i) (gmod b j)

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
    induction n with
    | zero =>
      -- hi : le₀ i 𝟘  →  i = 𝟘
      rcases (le_iff_lt_or_eq i 𝟘).mp hi with h_lt | h_eq
      · exact absurd h_lt (nlt_n_0 i)
      · subst h_eq; unfold prod_mods; exact divides_refl _
    | succ n' ih =>
      unfold prod_mods
      rcases (le_iff_lt_or_eq i (σ n')).mp hi with h_lt | h_eq
      · -- i ≤ n': gmod b i ∣ prod_mods b n'  → divide también al producto
        have h_i_le_n' : le₀ i n' := (lt_succ_iff_le i n').mp h_lt
        exact divides_mul_right (ih h_i_le_n')
      · -- i = σ n'
        subst h_eq
        exact divides_mul_left (divides_refl _)

  -- Si m ∣ M y c ≡ c' (mod M), entonces c ≡ c' (mod m)
  private theorem modEq_of_dvd {m M : ℕ₀} (hM_ne : M ≠ 𝟘) (hm_ne : m ≠ 𝟘)
      (hm_dvd_M : m ∣ M) {c c' : ℕ₀} (hcong : ModEq M c c') :
      ModEq m c c' := by
    -- ModEq M c c' : mod c M = mod c' M
    -- Queremos: mod c m = mod c' m
    -- En Nat: si m_n ∣ M_n y c_n % M_n = c'_n % M_n entonces c_n % m_n = c'_n % m_n
    -- Prueba: c_n % m_n = c_n % M_n % m_n = c'_n % M_n % m_n = c'_n % m_n
    unfold ModEq at *
    apply Ψ_inj
    rw [isomorph_Ψ_mod c m hm_ne, isomorph_Ψ_mod c' m hm_ne]
    have hcong_nat : Ψ c % Ψ M = Ψ c' % Ψ M := by
      have h := congrArg Ψ hcong
      rw [isomorph_Ψ_mod c M hM_ne, isomorph_Ψ_mod c' M hM_ne] at h
      exact h
    obtain ⟨k, hk⟩ := hm_dvd_M
    have hk_nat : Ψ M = Nat.mul (Ψ m) (Ψ k) := by
      have h := congrArg Ψ hk
      rw [isomorph_Ψ_mul] at h; exact h
    -- x % M % m = x % m cuando m ∣ M  [Nat.mod_mod_of_dvd]
    have hm_dvd_M_nat : @Dvd.dvd Nat Nat.instDvd (Ψ m) (Ψ M) := ⟨Ψ k, hk_nat⟩
    have key : ∀ x : Nat, x % Ψ M % Ψ m = x % Ψ m := fun x =>
      Nat.mod_mod_of_dvd x hm_dvd_M_nat
    calc Ψ c % Ψ m
        = Ψ c % Ψ M % Ψ m := (key (Ψ c)).symm
      _ = Ψ c' % Ψ M % Ψ m := by rw [hcong_nat]
      _ = Ψ c' % Ψ m := key (Ψ c')

  -- Lema auxiliar: si cada factor de prod_mods es coprimo con R, el producto también lo es
  private theorem prod_mods_coprime_with (n b : ℕ₀) (R : ℕ₀)
      (h : ∀ i, le₀ i n → Nat.gcd (Ψ (gmod b i)) (Ψ R) = 1) :
      Nat.gcd (Ψ (prod_mods b n)) (Ψ R) = 1 := by
    induction n with
    | zero =>
      simp only [prod_mods]
      exact h 𝟘 (le_refl 𝟘)
    | succ n' ih =>
      simp only [prod_mods, isomorph_Ψ_mul]
      have hP := ih (fun i hi => h i (le_succ i n' hi))
      have hQ := h (σ n') (le_refl (σ n'))
      -- Goal: gcd ((Ψ P).mul (Ψ Q)) (Ψ R) = 1
      -- donde P = prod_mods b n', Q = gmod b (σ n')
      -- Probar: gcd (gmod * P) R = P.gcd R  luego usar hP
      show ((Ψ (prod_mods b n')).mul (Ψ (gmod b (σ n')))).gcd (Ψ R) = 1
      -- hQ : gmod.gcd R = 1, necesitamos R.gcd gmod = 1
      have hQ_rev : (Ψ R).gcd (Ψ (gmod b (σ n'))) = 1 := Nat.gcd_comm _ _ ▸ hQ
      -- gcd (P * Q) R = gcd (Q * P) R = gcd R (Q * P) = gcd R P (por gcd_mul_right_right)
      --                                                = gcd P R = 1 (por hP)
      have step1 : ((Ψ (prod_mods b n')).mul (Ψ (gmod b (σ n')))).gcd (Ψ R) =
          ((Ψ (gmod b (σ n'))).mul (Ψ (prod_mods b n'))).gcd (Ψ R) :=
        congrArg (fun x => x.gcd (Ψ R)) (Nat.mul_comm _ _)
      have step2 : ((Ψ (gmod b (σ n'))).mul (Ψ (prod_mods b n'))).gcd (Ψ R) =
          (Ψ R).gcd ((Ψ (gmod b (σ n'))).mul (Ψ (prod_mods b n'))) :=
        Nat.gcd_comm _ _
      have step3 : (Ψ R).gcd ((Ψ (gmod b (σ n'))).mul (Ψ (prod_mods b n'))) =
          (Ψ R).gcd (Ψ (prod_mods b n')) :=
        Nat.gcd_mul_right_right_of_gcd_eq_one hQ_rev
      have step4 : (Ψ R).gcd (Ψ (prod_mods b n')) = (Ψ (prod_mods b n')).gcd (Ψ R) :=
        Nat.gcd_comm _ _
      rw [step1, step2, step3, step4]
      exact hP

  -- Helper: Ψ 𝟙 = 1
  private theorem Ψ_one_eq_one : Ψ 𝟙 = 1 := by
    show Ψ (σ 𝟘) = 1
    rw [isomorph_σ_Ψ, isomorph_0_Ψ]

  -- Helper: Coprime ℕ₀ → Nat.gcd = 1
  private theorem coprime_to_nat_gcd (a b : ℕ₀) (hcab : Coprime a b) :
      Nat.gcd (Ψ a) (Ψ b) = 1 := by
    obtain ⟨-, -, h3⟩ := hcab
    have hgcd_one : gcd a b = 𝟙 :=
      antisymm_divides (h3 _ ⟨gcd_dvd_left a b, gcd_dvd_right a b⟩) (one_divides _)
    have heq := isomorph_Ψ_gcd a b
    rw [hgcd_one, Ψ_one_eq_one] at heq
    exact heq.symm

  -- Helper: Nat.gcd = 1 → Coprime ℕ₀
  private theorem nat_gcd_to_coprime (a b : ℕ₀) (h : Nat.gcd (Ψ a) (Ψ b) = 1) :
      Coprime a b := by
    unfold Coprime IsGCD
    refine ⟨one_divides _, one_divides _, fun c ⟨hca, hcb⟩ => ?_⟩
    have hcgcd := dvd_gcd hca hcb
    have hgcd_one : gcd a b = 𝟙 := by
      apply Ψ_inj
      rw [isomorph_Ψ_gcd, h, Ψ_one_eq_one]
    rwa [hgcd_one] at hcgcd

  -- Coprimality del producto de módulos anteriores con el módulo siguiente
  private theorem prod_mods_coprime_next (n b : ℕ₀)
      (hcop : ∀ i j, le₀ i (σ n) → le₀ j (σ n) → i ≠ j → Coprime (gmod b i) (gmod b j)) :
      Coprime (prod_mods b n) (gmod b (σ n)) := by
    apply nat_gcd_to_coprime
    apply prod_mods_coprime_with
    intro i hi
    -- hi : le₀ i n, necesitamos gcd (Ψ (gmod b i)) (Ψ (gmod b (σ n))) = 1
    -- i ≠ σ n porque le₀ i n implica ¬ lt₀ n i, pero lt₀ n (σ n)
    have h_ne : i ≠ σ n := fun heq => by
      have h1 : le₀ (σ n) n := heq ▸ hi
      have h2 : lt₀ n (σ n) := (lt_succ_iff_le n n).mpr (le_refl n)
      exact absurd h2 (nlt_of_le h1)
    exact coprime_to_nat_gcd _ _ (hcop i (σ n) (le_succ i n hi) (le_refl (σ n)) h_ne)

  /-- CRT simultáneo: dada una función a : ℕ₀ → ℕ₀, existe c tal que
  c ≡ a(i) (mod gmod b i) para todo i ≤ n, cuando los gmod b i son coprimos en pares. -/
  private theorem prod_mods_pos (n b : ℕ₀) : lt₀ 𝟘 (prod_mods b n) := by
    induction n with
    | zero =>
      simp only [prod_mods]
      exact pos_of_ne_zero _ (gmod_ne_zero b 𝟘)
    | succ n' ih =>
      simp only [prod_mods]
      exact mul_pos ih (pos_of_ne_zero _ (gmod_ne_zero b (σ n')))

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
      have h_cop_prod := prod_mods_coprime_next n' b hcop
      -- Aplicar CRT al par (prod_mods b n', gmod b (σn'))
      obtain ⟨c, hc_prod, hc_next⟩ := chinese_remainder h_cop_prod c' (a (σ n'))
      refine ⟨c, fun i hi => ?_⟩
      rcases (le_iff_lt_or_eq i (σ n')).mp hi with h_lt | h_eq
      · -- i ≤ n': usar gmod b i ∣ prod_mods b n' y transitividad de ≡
        have h_i_le_n' : le₀ i n' := (lt_succ_iff_le i n').mp h_lt
        have h_mi_dvd_prod : gmod b i ∣ prod_mods b n' :=
          gmod_dvd_prod_mods b n' i h_i_le_n'
        exact modEq_trans
          (modEq_of_dvd (fun h => absurd (h ▸ prod_mods_pos n' b) (lt_irrefl 𝟘))
            (gmod_ne_zero b i) h_mi_dvd_prod hc_prod)
          (hc' i h_i_le_n')
      · -- i = σn'
        subst h_eq
        exact hc_next

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 5. Teorema principal: β representa cualquier secuencia finita
  -- ─────────────────────────────────────────────────────────────────────────

  -- Cota superior para la secuencia a sobre [0, n]
  private def seqBound (a : ℕ₀ → ℕ₀) : ℕ₀ → ℕ₀
    | .zero   => a 𝟘
    | .succ k => max (seqBound a k) (a (σ k))

  private theorem seqBound_ge (a : ℕ₀ → ℕ₀) : ∀ n i, le₀ i n → le₀ (a i) (seqBound a n) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rcases (le_iff_lt_or_eq i 𝟘).mp hi with h_lt | h_eq
      · exact absurd h_lt (nlt_n_0 i)
      · subst h_eq; exact le_refl _
    | succ n' ih =>
      intro i hi
      rcases (le_iff_lt_or_eq i (σ n')).mp hi with h_lt | h_eq
      · exact le_trans _ _ _ (ih i ((lt_succ_iff_le i n').mp h_lt))
            (le_max_left (seqBound a n') (a (σ n')))
      · subst h_eq; exact le_max_right (seqBound a n') (a (σ n'))

  /-- Para cualquier secuencia a : ℕ₀ → ℕ₀ y longitud n, existen c, b : ℕ₀
  tales que β(c, b, i) = a(i) para todo i ≤ n. -/
  theorem godel_beta_seq (n : ℕ₀) (a : ℕ₀ → ℕ₀) :
      ∃ c b : ℕ₀, ∀ i, le₀ i n → beta c b i = a i := by
    -- Elegimos K = max(n, seqBound a n) y b = factorial (σ K).
    -- (1) Coprimality: i,j ≤ n ≤ K ≤ σ K, via godel_factorial_coprime (σ K).
    -- (2) Cota: a i ≤ seqBound a n ≤ K < σ K ≤ factorial(σ K) = b ≤ gmod b i.
    let M := seqBound a n
    let K := max n M
    let b := factorial (σ K)
    -- Coprimality
    have hcop : ∀ i j, le₀ i n → le₀ j n → i ≠ j →
        Coprime (gmod b i) (gmod b j) := by
      intro i j hi hj hij
      -- i ≤ n ≤ K ≤ σ K
      have h_sK : le₀ K (σ K) := lt_imp_le K (σ K) (lt_succ_self K)
      have hi_sK : le₀ i (σ K) :=
        le_trans _ _ _ hi (le_trans _ _ _ (le_max_left n M) h_sK)
      have hj_sK : le₀ j (σ K) :=
        le_trans _ _ _ hj (le_trans _ _ _ (le_max_left n M) h_sK)
      exact godel_factorial_coprime (σ K) i j hi_sK hj_sK hij
    -- Aplicar CRT
    obtain ⟨c, hc⟩ := simultaneous_congruences n b a hcop
    refine ⟨c, b, fun i hi => ?_⟩
    -- Mostrar a i < gmod b i
    have ha_lt : lt₀ (a i) (gmod b i) := by
      -- Paso 1: K < σ K ≤ factorial (σ K) = b
      have hK_lt_sK : lt₀ K (σ K) := lt_succ_self K
      have hsK_le_b : le₀ (σ K) b := by
        show le₀ (σ K) (factorial (σ K))
        rw [factorial_succ]
        -- mul (factorial K) (σ K) ≥ mul 𝟙 (σ K) = σ K
        have h_mono : le₀ (mul 𝟙 (σ K)) (mul (factorial K) (σ K)) :=
          mul_le_mono_right (σ K) (factorial_ge_one K)
        rwa [one_mul] at h_mono
      -- Paso 2: a i ≤ M ≤ K < b ≤ gmod b i
      have hai_le_M : le₀ (a i) M := seqBound_ge a n i hi
      have hM_le_K : le₀ M K := le_max_right n M
      have hK_lt_b : lt₀ K b :=
        lt_of_lt_of_le hK_lt_sK hsK_le_b
      -- a i ≤ K < b, so a i < b
      have hai_le_K : le₀ (a i) K :=
        le_trans _ _ _ hai_le_M hM_le_K
      have hai_lt_b : lt₀ (a i) b := by
        rcases (le_iff_lt_or_eq (a i) K).mp hai_le_K with h | h
        · exact lt_trans _ _ _ h hK_lt_b
        · exact h ▸ hK_lt_b
      -- b ≤ gmod b i = add 𝟙 (mul (σ i) b)
      -- b ≤ mul (σ i) b ≤ add 𝟙 (mul (σ i) b)
      have hb_le_gmod : le₀ b (gmod b i) := by
        show le₀ b (add 𝟙 (mul (σ i) b))
        -- b = mul 𝟙 b ≤ mul (σ i) b
        have h1 : le₀ (mul 𝟙 b) (mul (σ i) b) :=
          mul_le_mono_right b (succ_le_succ_if (zero_le i))
        rw [one_mul] at h1
        -- mul (σ i) b ≤ add 𝟙 (mul (σ i) b)
        have h2 : le₀ (mul (σ i) b) (add 𝟙 (mul (σ i) b)) := by
          rw [add_comm]; exact le_self_add (mul (σ i) b) 𝟙
        exact le_trans _ _ _ h1 h2
      -- a i < b ≤ gmod b i, so a i < gmod b i
      rcases (le_iff_lt_or_eq b (gmod b i)).mp hb_le_gmod with h | h
      · exact lt_trans _ _ _ hai_lt_b h
      · exact h ▸ hai_lt_b
    -- Ahora: beta c b i = mod c (gmod b i) = mod (a i) (gmod b i) = a i
    unfold beta
    rw [hc i hi]
    exact mod_of_lt (a i) (gmod b i) ha_lt

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

  -- Lema auxiliar: decodeList z m = map (beta c b ∘ Λ) (range (Ψ m))
  private theorem decodeList_eq_map (z m : ℕ₀) :
      decodeList z m =
        (List.range (Ψ m)).map (fun i => beta (fst z) (snd z) (Λ i)) := by
    induction m with
    | zero =>
      simp only [decodeList, isomorph_0_Ψ, List.range_zero, List.map_nil]
    | succ k ih =>
      simp only [decodeList, isomorph_σ_Ψ, List.range_succ, List.map_append, List.map_cons,
                 List.map_nil, ← ih]
      simp only [ΛΨ]

  -- Lema: map (getD l) (range l.length) = l
  private theorem list_map_getD_range : ∀ (l : List ℕ₀),
      (List.range l.length).map (fun i => l.getD i 𝟘) = l := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp [List.range_succ_eq_map]
      exact ih

  /-- El teorema de representación: decodificar ∘ codificar = identidad. -/
  theorem encode_decode (l : List ℕ₀) :
      decodeList (encodeList l) (Λ l.length) = l := by
    cases h_empty : l with
    | nil =>
      simp only [List.length_nil, isomorph_0_Λ, decodeList]
    | cons x xs =>
      -- l = x :: xs, l ≠ []
      have h_l_ne : (x :: xs) ≠ [] := List.cons_ne_nil x xs
      -- Parámetros de encodeList
      let n := Λ ((x :: xs).length - 1)
      let a : ℕ₀ → ℕ₀ := fun i => (x :: xs).getD (Ψ i) 𝟘
      have spec := godel_beta_seq n a
      let c := Classical.choose spec
      have rest := Classical.choose_spec spec
      let b := Classical.choose rest
      have hbeta := Classical.choose_spec rest
      -- encodeList (x :: xs) = pair c b
      have henc : encodeList (x :: xs) = pair c b := by
        simp only [encodeList, h_l_ne, ite_false]; rfl
      rw [henc, decodeList_eq_map, pair_fst, pair_snd, ΨΛ]
      -- Mostrar map (fun i => beta c b (Λ i)) (range (x::xs).length) = x :: xs
      have h_len_pos : 0 < (x :: xs).length := Nat.succ_pos xs.length
      have h_map_eq : (List.range (x :: xs).length).map (fun i => beta c b (Λ i)) =
                      (List.range (x :: xs).length).map (fun i => (x :: xs).getD i 𝟘) := by
        apply List.map_congr_left
        intro i hi
        simp only [List.mem_range] at hi
        have hi_le_n : le₀ (Λ i) n := by
          show le₀ (Λ i) (Λ ((x :: xs).length - 1))
          apply (isomorph_Λ_le i ((x :: xs).length - 1)).mp
          omega
        have h_eq := hbeta (Λ i) hi_le_n
        simp only [a, ΨΛ] at h_eq
        exact h_eq
      rw [h_map_eq]
      exact list_map_getD_range (x :: xs)

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
