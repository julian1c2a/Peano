/-
# Teorema de Fermat (Peano/PeanoNat/NumberTheory/Fermat.lean)

Pequeño Teorema de Fermat: para todo primo p y todo a ∈ ℕ₀,
  a ^ p ≡ a [MOD p].

Estrategia: inducción sobre a usando el binomio de Newton.
  Base: 0^p = 0 ≡ 0 [MOD p].
  Paso: (a+1)^p = Σ C(p,k)·a^k·1^(p-k).
        Los términos con 0 < k < p son divisibles por p,
        así que (a+1)^p ≡ a^p + 1 ≡ a + 1 [MOD p].
-/
import Peano.PeanoNat.NumberTheory.Totient
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Combinatorics.Binom
import Peano.PeanoNat.Combinatorics.NewtonBinom
import Peano.PeanoNat.Combinatorics.Factorial
import Peano.PeanoNat.Combinatorics.Summation
import Peano.PeanoNat.NumberTheory.ModEq

set_option autoImplicit false

namespace Peano
   open Peano
   open Peano.Sub
   open Peano.Axioms
   open Peano.StrictOrder
   open Peano.Order
   open Peano.Add
   open Peano.Mul
   open Peano.Div
   open Peano.Arith
   open Peano.Pow
   open Peano.Binom
   open Peano.Factorial
   open Peano.NewtonBinom
   open Peano.Summation
   open Peano.ModEq
   open Peano.Primes hiding Prime

   namespace Fermat

      /-!
      ## § 1. Prime divides own factorial
      -/

      /-- `p` divides `factorial p` for `p ≠ 𝟘`. -/
      private theorem dvd_factorial_self {p : ℕ₀} (hp : p ≠ 𝟘) :
          Divides p (factorial p) := by
        cases p with
        | zero => exact absurd rfl hp
        | succ p' =>
          rw [factorial_succ]
          exact ⟨factorial p', mul_comm (factorial p') (σ p')⟩

      /-!
      ## § 2. Prime does not divide smaller nonzero numbers
      -/

      /-- If `k ≠ 𝟘` and `k < p`, then `¬(p ∣ k)`. -/
      private theorem prime_not_dvd_of_lt {p k : ℕ₀}
          (hk_ne : k ≠ 𝟘) (hk_lt : lt₀ k p) : ¬(Divides p k) := by
        intro h_dvd
        have h_le := divides_le h_dvd hk_ne
        exact absurd hk_lt (le_not_lt h_le)

      /-!
      ## § 3. Prime does not divide factorial of smaller numbers
      -/

      /-- For prime `p`, if `n < p` then `¬(p ∣ factorial n)`. -/
      private theorem prime_not_dvd_factorial_lt {p n : ℕ₀}
          (hp : Arith.Prime p) (hlt : lt₀ n p) : ¬(Divides p (factorial n)) := by
        induction n with
        | zero =>
          rw [factorial_zero]
          intro h_dvd
          have h_le_1 : le₀ p 𝟙 := divides_le h_dvd (succ_neq_zero 𝟘)
          have h_1_lt : lt₀ 𝟙 p := one_lt_prime hp
          exact absurd h_1_lt (le_not_lt h_le_1)
        | succ n' ih =>
          rw [factorial_succ]
          intro h_dvd_prod
          -- p | factorial n' · σ n'  →  p | factorial n' ∨ p | σ n'
          have h_or := hp.2.2 (factorial n') (σ n') h_dvd_prod
          rcases h_or with h_dvd_fact | h_dvd_sn
          · exact ih (lt_trans n' (σ n') p (lt_succ_self n') hlt) h_dvd_fact
          · exact prime_not_dvd_of_lt (succ_neq_zero n') hlt h_dvd_sn

      /-!
      ## § 4. Prime divides binomial coefficient C(p, k) for 0 < k < p
      -/

      /-- For prime `p`, if `0 < k < p` then `p ∣ C(p, k)`. -/
      private theorem prime_dvd_binom {p k : ℕ₀}
          (hp : Arith.Prime p) (hk_pos : lt₀ 𝟘 k) (hk_lt : lt₀ k p) :
          Divides p C(p, k) := by
        -- From binom_mul_factorials: C(p,k) · k! · (p-k)! = p!
        have h_le : le₀ k p := lt_imp_le_wp hk_lt
        have h_binom_eq := binom_mul_factorials h_le
        -- p | p!
        have h_p_ne : p ≠ 𝟘 := prime_ne_zero hp
        have h_dvd_pfact := dvd_factorial_self h_p_ne
        -- p | C(p,k) · k! · (p-k)!
        have h_dvd_prod : Divides p (mul (mul C(p, k) (factorial k)) (factorial (sub p k))) :=
          h_binom_eq ▸ h_dvd_pfact
        -- p ∤ (p-k)! because sub p k < p (since k > 0)
        have hk_ne : k ≠ 𝟘 := by
          intro h_eq; rw [h_eq] at hk_pos; exact absurd hk_pos (lt_irrefl 𝟘)
        have h_sub_lt : lt₀ (sub p k) p :=
          sub_lt_self_wp h_le hk_ne
        have h_not_dvd_sub : ¬(Divides p (factorial (sub p k))) :=
          prime_not_dvd_factorial_lt hp h_sub_lt
        -- p ∤ k! because k < p
        have h_not_dvd_k : ¬(Divides p (factorial k)) :=
          prime_not_dvd_factorial_lt hp hk_lt
        -- From p | (C·k!) · (p-k)! and p ∤ (p-k)!, by Gauss: p | C·k!
        -- Need Coprime p (factorial (sub p k))
        have h_cop_sub : Coprime p (factorial (sub p k)) := by
          rcases @prime_coprime_or_dvd p (factorial (sub p k)) hp with h | h
          · exact absurd h h_not_dvd_sub
          · exact h
        have h_dvd_ck : Divides p (mul C(p, k) (factorial k)) :=
          coprime_dvd_of_dvd_mul h_cop_sub (mul_comm (mul C(p, k) (factorial k)) (factorial (sub p k)) ▸ h_dvd_prod)
        -- From p | C·k! and p ∤ k!, by Gauss: p | C(p,k)
        have h_cop_k : Coprime p (factorial k) := by
          rcases @prime_coprime_or_dvd p (factorial k) hp with h | h
          · exact absurd h h_not_dvd_k
          · exact h
        exact coprime_dvd_of_dvd_mul h_cop_k (mul_comm C(p, k) (factorial k) ▸ h_dvd_ck)


      /-!
      ## § 5. Modular arithmetic helpers
      -/

      /-- If `p ∣ x`, then `mod x p = 𝟘` (when `p ≠ 𝟘`). -/
      private theorem mod_eq_zero_of_dvd' {x p : ℕ₀} (hp : p ≠ 𝟘) (h : Divides p x) :
          mod x p = 𝟘 :=
        (mod_eq_zero_iff_dvd hp).mpr h

      /-- `pow 𝟘 p = 𝟘` for `p ≠ 𝟘`. -/
      private theorem pow_zero_eq_zero {p : ℕ₀} (hp : p ≠ 𝟘) : pow 𝟘 p = 𝟘 :=
        zero_pow hp

      /-- `pow 𝟙 n = 𝟙`. -/
      private theorem pow_one_base (n : ℕ₀) : pow 𝟙 n = 𝟙 := one_pow n


      /-!
      ## § 6. The key step: middle binomial terms vanish mod p

      We show that `finSum (fun k => binomTerm a 𝟙 p (σ k)) (sub p 𝟚)`
      is divisible by `p` when `p` is prime.
      -/

      /-- `p ∣ binomTerm a 𝟙 p k` for `0 < k < p` and `p` prime. -/
      private theorem dvd_binomTerm_middle {p a k : ℕ₀}
          (hp : Arith.Prime p) (hk_pos : lt₀ 𝟘 k) (hk_lt : lt₀ k p) :
          Divides p (binomTerm a 𝟙 p k) := by
        unfold binomTerm
        rw [pow_one_base, mul_one]
        -- binomTerm a 𝟙 p k = C(p,k) · a^k
        exact divides_mul_right (prime_dvd_binom hp hk_pos hk_lt)

      /-- `p ∣ finSum f n` if `p ∣ f k` for all `k ≤ n`. -/
      private theorem dvd_finSum {p : ℕ₀} {f : ℕ₀ → ℕ₀} {n : ℕ₀}
          (h : ∀ k : ℕ₀, le₀ k n → Divides p (f k)) : Divides p (finSum f n) := by
        induction n with
        | zero =>
          rw [finSum_zero]
          exact h 𝟘 (le_refl 𝟘)
        | succ n' ih =>
          rw [finSum_succ]
          exact divides_add
            (ih (fun k hk => h k (le_trans k n' (σ n') hk (lt_imp_le_wp (lt_succ_self n')))))
            (h (σ n') (le_refl (σ n')))


      /-!
      ## § 7. Fermat's Little Theorem
      -/

      /--
      ## Pequeño Teorema de Fermat
      Para todo primo p y todo a ∈ ℕ₀:
      a ^ p ≡ a [MOD p]
      -/
      theorem fermat_little_theorem (a p : ℕ₀) (hp : Arith.Prime p) :
         mod (pow a p) p = mod a p := by
        -- Inducción sobre a
        induction a with
        | zero =>
          -- 0^p = 0, y mod 0 p = 0 = mod 0 p
          rw [zero_pow (prime_ne_zero hp)]
        | succ a' ih =>
          -- (σ a')^p = (add a' 𝟙)^p
          have h_succ_eq : σ a' = add a' 𝟙 := (add_one a').symm
          rw [h_succ_eq]
          -- Binomio de Newton: (a' + 1)^p = Σ_{k=0}^{p} binomTerm a' 1 p k
          rw [newton_binom a' 𝟙 p]
          -- Expandir la suma: T(0) + Σ_{k=1}^{p} T(k)
          -- Necesitamos p ≥ 2
          have h_p_ge_2 := prime_ge_two hp
          -- p = σ p' para algún p'
          cases p with
          | zero => exact absurd rfl (prime_ne_zero hp)
          | succ p' =>
            -- p = σ p', y σ p' ≥ 2, así que p' ≥ 1
            have hp' : Arith.Prime (σ p') := hp
            -- finSum f (σ p') = f 𝟘 + finSum (f ∘ σ) p'
            rw [finSum_succ_left]
            -- T(a', 1, σp', 0) = 1^(σp') = 1
            rw [binomTerm_zero, pow_one_base]
            -- Ahora: mod (add 𝟙 (finSum (fun k => binomTerm a' 𝟙 (σ p') (σ k)) p')) (σ p')
            --      = mod (add a' 𝟙) (σ p')
            -- El último término: T(σp', σp', σp') = a'^(σp')
            -- finSum (σ·) p' = finSum (σ·) (τ p') + T(σp')
            -- p' = σ p'' para algún p'' (pues p' ≥ 1)
            cases p' with
            | zero =>
              -- p = 1, contradice Prime
              exact absurd (show (σ 𝟘 : ℕ₀) = 𝟙 from rfl) (prime_ne_one hp')
            | succ p'' =>
              -- p = σ(σ p''), p' = σ p''
              -- finSum g (σ p'') = finSum g p'' + g(σ p'')
              rw [finSum_succ]
              -- g(σ p'') = binomTerm a' 𝟙 (σ(σ p'')) (σ(σ p''))
              rw [binomTerm_self]
              -- Ahora: mod (add 𝟙 (add (finSum middle p'') (pow a' (σ(σ p''))))) (σ(σ p''))
              --      = mod (add a' 𝟙) (σ(σ p''))
              -- Los términos medios son divisibles por p = σ(σ p'')
              have h_p := σ (σ p'')
              -- Necesitamos que finSum (fun k => binomTerm a' 𝟙 (σ(σ p'')) (σ k)) p''
              -- es divisible por σ(σ p'')
              have h_middle_dvd : Divides (σ (σ p'')) (finSum (fun k => binomTerm a' 𝟙 (σ (σ p'')) (σ k)) p'') := by
                apply dvd_finSum
                intro k hk
                apply dvd_binomTerm_middle hp'
                · exact zero_lt_succ k
                · -- σ k < σ(σ p'') ← k ≤ p'' → σ k ≤ σ p'' < σ(σ p'')
                  have h_k_lt_sp'' : lt₀ k (σ p'') :=
                    match hk with
                    | Or.inl h_lt => lt_trans k p'' (σ p'') h_lt (lt_succ_self p'')
                    | Or.inr h_eq => h_eq ▸ lt_succ_self p''
                  exact (succ_lt_succ_iff k (σ p'')).mpr h_k_lt_sp''
              -- mod (something divisible by p) p = 0
              -- 𝟙 + (middle + a'^p) ≡ 𝟙 + (0 + a'^p) ≡ 1 + a'^p [MOD p]
              -- By IH: a'^p ≡ a' [MOD p]
              -- So: 1 + a'^p ≡ 1 + a' = σ a' = add a' 1 [MOD p]

              -- Rewrite using modular arithmetic
              -- LHS: mod (add 𝟙 (add middle (pow a' (σ(σ p''))))) (σ(σ p''))
              -- We know: middle ≡ 0 [MOD p]
              have h_mid_zero : mod (finSum (fun k => binomTerm a' 𝟙 (σ (σ p'')) (σ k)) p'') (σ (σ p'')) = 𝟘 :=
                (mod_eq_zero_iff_dvd (succ_neq_zero (σ p''))).mpr h_middle_dvd

              -- LHS = mod (add 𝟙 (add middle (pow a' p))) p
              -- Use add_mod to separate
              show mod (add 𝟙 (add (finSum (fun k => binomTerm a' 𝟙 (σ (σ p'')) (σ k)) p'') (pow a' (σ (σ p''))))) (σ (σ p''))
                 = mod (add a' 𝟙) (σ (σ p''))

              -- Rewrite via add_mod
              rw [add_mod 𝟙 (add (finSum _ p'') (pow a' (σ (σ p'')))) (σ (σ p''))]
              rw [add_mod (finSum _ p'') (pow a' (σ (σ p''))) (σ (σ p''))]
              rw [h_mid_zero, zero_add, mod_mod]

              -- Now LHS: mod (add (mod 𝟙 (σ(σ p''))) (mod (pow a' (σ(σ p''))) (σ(σ p'')))) (σ(σ p''))
              -- RHS: mod (add a' 𝟙) (σ(σ p''))
              rw [add_mod a' 𝟙 (σ (σ p'')), add_comm (mod a' (σ (σ p''))) (mod 𝟙 (σ (σ p''))), ih]

   end Fermat
end Peano
