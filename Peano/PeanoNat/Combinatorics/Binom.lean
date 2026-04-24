/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Binom.lean
-- Coeficientes binomiales vía el triángulo de Pascal.
-- Preparación para el Teorema del Binomio de Newton.

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Combinatorics.Factorial
import Peano.PeanoNat.Primes
import Peano.PeanoNat.NumberTheory.ModEq

/-!
Paso 1: El Caso Base (n=0)

Para n=0, dado que 0≤k≤n, obligatoriamente k=0.

Sustituimos en la ecuación que queremos demostrar:
C(0,0)⋅0!⋅(0−0)!=0!

Usando nuestra definición de C(0,0)=1 y 0!=1:
1⋅1⋅1=1

La igualdad se cumple perfectamente para el caso base.
Paso 2: La Hipótesis Inductiva

Asumimos como cierta nuestra ecuación para un número natural n y para todo k tal que 0≤k≤n. Es decir, suponemos que es verdadero que:
C(n,k)⋅k!⋅(n−k)!=n!
Paso 3: El Paso Inductivo (n+1)

Debemos demostrar que la propiedad se mantiene para n+1. Es decir, queremos llegar a demostrar que para cualquier j (donde 0≤j≤n+1):
C(n+1,j)⋅j!⋅((n+1)−j)!=(n+1)!

Caso A: Los extremos (j=0 y j=n+1)

    Si j=0: C(n+1,0)⋅0!⋅(n+1)!=1⋅1⋅(n+1)!=(n+1)!. Se cumple.

    Si j=n+1: Por la recursión C(n+1,n+1)=C(n,n)+C(n,n+1)=1+0=1. Entonces: C(n+1,n+1)⋅(n+1)!⋅0!=1⋅(n+1)!⋅1=(n+1)!. Se cumple.

Caso B: El centro (j=k+1, donde 0≤k<n)
Evaluamos la expresión izquierda de nuestra meta para j=k+1:
C(n+1,k+1)⋅(k+1)!⋅((n+1)−(k+1))!

Que se simplifica a:
C(n+1,k+1)⋅(k+1)!⋅(n−k)!

Ahora, sustituimos C(n+1,k+1) por la regla de recursión de Pascal:
(C(n,k)+C(n,k+1))⋅(k+1)!⋅(n−k)!

Aplicamos la propiedad distributiva de la multiplicación respecto a la suma:
[C(n,k)⋅(k+1)!⋅(n−k)!]+[C(n,k+1)⋅(k+1)!⋅(n−k)!]

Ahora usamos la definición del factorial recursivo, (x+1)!=(x+1)⋅x!, para extraer términos en cada corchete y que aparezca nuestra Hipótesis Inductiva:

    En el primer corchete: Expandimos (k+1)! como (k+1)⋅k!.
    C(n,k)⋅(k+1)⋅k!⋅(n−k)!

    Por la propiedad conmutativa, reordenamos:
    (k+1)⋅[C(n,k)⋅k!⋅(n−k)!]

    ¡Lo que hay dentro del corchete es exactamente nuestra Hipótesis Inductiva! Sustituimos por n!:
    (k+1)⋅n!

    En el segundo corchete: Expandimos (n−k)! como (n−k)⋅(n−k−1)!, lo cual es válido porque k<n. Recordando que (n−k−1)! es lo mismo que (n−(k+1))!:
    C(n,k+1)⋅(k+1)!⋅(n−k)⋅(n−(k+1))!

    Reordenamos usando la propiedad conmutativa:
    (n−k)⋅[C(n,k+1)⋅(k+1)!⋅(n−(k+1))!]

    Aquí aplicamos nuevamente nuestra Hipótesis Inductiva (evaluada para el término k+1). Lo que hay dentro del corchete equivale a n!. Sustituimos:
    (n−k)⋅n!

Sumamos ambos resultados simplificados:
(k+1)⋅n!+(n−k)⋅n!

Aplicamos la propiedad distributiva a la inversa (sacamos factor común n!):
n!⋅(k+1+n−k)

Los términos k y −k se cancelan:
n!⋅(n+1)

Por la definición de factorial, sabemos que n!⋅(n+1)=(n+1)!.
Conclusión

Hemos demostrado usando exclusivamente suma, multiplicación (con sus propiedades asociativa, conmutativa y distributiva) y la definición recursiva del factorial que:
C(n+1,k+1)⋅(k+1)!⋅(n−k)!=(n+1)!

Como se cumple para el caso base n=0 y el paso inductivo garantiza que de n se hereda a n+1, queda demostrado por el Principio de Inducción que C(n,k)⋅k!⋅(n−k)!=n! es verdadero para todos los números naturales.
-/

namespace Peano
  open Peano

  namespace Binom
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.Add
    open Peano.Mul
    open Peano.Factorial
    open Peano.Sub

    /- Coeficiente binomial C(n, k) por la recursión de Pascal.
       Termina por inducción estructural en el primer argumento n. -/
    def binom : ℕ₀ → ℕ₀ → ℕ₀
      | .zero,   .zero   => 𝟙
      | .zero,   .succ _ => 𝟘
      | .succ _, .zero   => 𝟙
      | .succ n, .succ k => add (binom n k) (binom n (σ k))

    /- Notación C(n, k). -/
    notation "C(" n ", " k ")" => binom n k

    -- ── Valores base ──────────────────────────────────────────────────────────────

    theorem binom_zero_zero : C(𝟘, 𝟘) = 𝟙 := by rfl

    theorem binom_zero_succ (k : ℕ₀) : C(𝟘, σ k) = 𝟘 := by rfl

    theorem binom_succ_zero (n : ℕ₀) : C(σ n, 𝟘) = 𝟙 := by rfl

    /- Identidad de Pascal: C(n+1, k+1) = C(n, k) + C(n, k+1). -/
    theorem binom_pascal (n k : ℕ₀) :
        C(σ n, σ k) = add C(n, k) C(n, σ k) := by rfl

    theorem binom_n_zero (n : ℕ₀) : C(n, 𝟘) = 𝟙 := by
      cases n <;> rfl

    theorem binom_n_one (n : ℕ₀) : C(n, 𝟙) = n := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
        calc C(σ n', 𝟙)
            = add C(n', 𝟘) C(n', 𝟙)  := by rfl
          _ = add C(n', 𝟘) n'        := by rw [ih]
          _ = add 𝟙 n'               := by rw [binom_n_zero]
          _ = σ n'                    := by rw [add_comm, add_one]

    theorem binom_eq_zero_of_gt {n k : ℕ₀} (h : lt₀ n k) : C(n, k) = 𝟘 := by
      induction n generalizing k with
      | zero    =>
          cases k with
          | zero    => exact absurd h (lt_zero 𝟘)
          | succ k' => rfl
      | succ n' ih =>
          cases k with
          | zero    => exact absurd h (lt_zero (σ n'))
          | succ k' =>
              rw [binom_pascal]
              have h' : lt₀ n' k' := (succ_lt_succ_iff n' k').mp h
              have h'' : lt₀ n' (σ k') := lt_trans n' k' (σ k') h' (lt_succ_self k')
              rw [ih h', ih h'', add_zero]

    theorem binom_self (n : ℕ₀) : C(n, n) = 𝟙 := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [binom_pascal, ih, binom_eq_zero_of_gt (lt_succ_self n'), add_zero]

    theorem binom_self_self (n : ℕ₀) :
      C(n, n) = 𝟙
      := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
        calc C(σ n', σ n')
            = add C(n', n') C(n', σ n')  := by rfl
          _ = add 𝟙 C(n', σ n')          := by rw [ih]
          _ = add 𝟙 𝟘                    := by rw [binom_eq_zero_of_gt (lt_succ_self n')]
          _ = 𝟙                          := by rw [add_zero]
    -- ── Lema auxiliar: a ≤ a + b ──────────────────────────────────────────────────

    private theorem le_add_right (a b : ℕ₀) : le₀ a (add a b) := by
      induction b with
      | zero    => exact le_refl a
      | succ b' ih =>
          exact le_trans a (add a b') (σ (add a b')) ih
                  (lt_imp_le_wp (lt_succ_self (add a b')))

    -- ── C(n, k) > 0 cuando k ≤ n ──────────────────────────────────────────────────

    theorem binom_pos {n k : ℕ₀} (h : le₀ k n) : C(n, k) > 𝟘 := by
      induction n generalizing k with
      | zero    =>
          have hk : k = 𝟘 := by
            rcases (le_iff_lt_or_eq k 𝟘).mp h with h_lt | h_eq
            · exact absurd h_lt (lt_zero k)
            · exact h_eq
          subst hk; rw [binom_zero_zero]; exact lt_succ_self 𝟘
      | succ n' ih =>
          cases k with
          | zero    => rw [binom_succ_zero]; exact lt_succ_self 𝟘
          | succ k' =>
              rw [binom_pascal]
              have h_le : le₀ k' n' := by
                rcases (le_iff_lt_or_eq (σ k') (σ n')).mp h with h_lt | h_eq
                · exact lt_imp_le_wp ((succ_lt_succ_iff k' n').mp h_lt)
                · exact Or.inr (succ_inj k' n' h_eq)
              exact lt_of_lt_of_le (ih h_le)
                      (le_add_right C(n', k') C(n', σ k'))

    -- ── C(n, 1) = n (para n ≥ 1) ─────────────────────────────────────────────────────

    theorem binom_one (n : ℕ₀) : C(σ n, 𝟙) = σ n := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [show (𝟙 : ℕ₀) = σ 𝟘 from rfl, binom_pascal, binom_n_zero]
          rw [show (𝟙 : ℕ₀) = σ 𝟘 from rfl] at ih
          rw [ih, add_comm, add_one]

    theorem binom_succ_n_by_n (n : ℕ₀) : C(σ n, n) = σ n := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [binom_pascal (σ n') n', ih, binom_self (σ n'), add_one]

    -- ── Relación entre C(n, k) y factoriales ─────────────────────────────────────────────────

    /- Lema auxiliar de conmutación de factores: (a·b)·c = (a·c)·b. -/
    private theorem mul_swap_last (a b c : ℕ₀) : mul (mul a b) c = mul (mul a c) b := by
      rw [mul_assoc b a c, mul_comm b c, ← mul_assoc c a b]

    private theorem sub_eq_succ_of_lt {n k : ℕ₀} (h_lt : lt₀ k n) :
        sub n k = σ (sub n (σ k)) := by
      have h_sk_le_n : le₀ (σ k) n :=
        (lt_succ_iff_le (σ k) n).mp ((succ_lt_succ_iff k n).mpr h_lt)
      have h_sub_ne0 : sub n k ≠ 𝟘 := lt_b_a_then_sub_a_b_neq_0 n k h_lt
      have h_eq : sub n (σ k) = τ (sub n k) := succ_sub n k h_sk_le_n
      have h_eq2 : σ (sub n (σ k)) = sub n k := by
        rw [h_eq, tau_eq_rho_if_ne_zero _ h_sub_ne0, σ_ρ_eq_self]
      exact h_eq2.symm

    private theorem factorial_sub_succ {n k : ℕ₀} (h_lt : lt₀ k n) :
        factorial (sub n k) = mul (factorial (sub n (σ k))) (sub n k) := by
      have h_eq := sub_eq_succ_of_lt h_lt; rw [h_eq, factorial_succ, ← h_eq]

    private theorem add_succ_sub_self {n k : ℕ₀} (h_le : le₀ k n) :
        add (σ k) (sub n k) = σ n := by
      rw [succ_add, add_comm, sub_k_add_k n k h_le]

    /- Teorema principal: C(n, k) · k! · (n - k)! = n! para k ≤ n. -/
    theorem binom_mul_factorials {n k : ℕ₀} (h : le₀ k n) :
        mul (mul C(n, k) (factorial k)) (factorial (sub n k)) = factorial n := by
      induction n generalizing k with
      | zero =>
          have hk : k = 𝟘 := le_zero_eq k h
          subst hk
          rw [binom_zero_zero, sub_self, factorial_zero, mul_one, one_mul]
      | succ n' ih =>
          cases k with
          | zero =>
              rw [binom_succ_zero, sub_zero, factorial_zero, one_mul, one_mul]
          | succ k' =>
              have h_k'_le_n' : le₀ k' n' := (succ_le_succ_iff k' n').mp h
              rcases (le_iff_lt_or_eq k' n').mp h_k'_le_n' with h_lt | h_eq
              · -- Caso k' < n'
                have h_le_k' : le₀ k' n' := lt_imp_le_wp h_lt
                have h_le_sk' : le₀ (σ k') n' := (lt_succ_iff_le _ _).mp ((succ_lt_succ_iff _ _).mpr h_lt)
                -- term1: C(n',k')·(k'+1)!·(n'-k')! = n'!·(k'+1)
                -- factorial(σk') = factorial(k')·σk', extraemos σk' con mul_swap_last
                have term1_rw : mul (mul (C(n', k')) (factorial (σ k'))) (factorial (sub n' k')) = mul (factorial n') (σ k') := by
                  rw [factorial_succ k',
                      ←mul_assoc (factorial k') (C(n', k')) (σ k'),
                      mul_swap_last, ih h_le_k']
                -- term2: C(n',k'+1)·(k'+1)!·(n'-k')! = n'!·(n'-k')
                -- expandimos (n'-k')! = (n'-k'-1)!·(n'-k'), luego asociamos
                have term2_rw : mul (mul (C(n', σ k')) (factorial (σ k'))) (factorial (sub n' k')) = mul (factorial n') (sub n' k') := by
                  rw [factorial_sub_succ h_lt, ←mul_assoc, ih h_le_sk']
                -- ensamblamos: Pascal + distribución + HI + factorial_succ
                rw [binom_pascal, add_mul, ←sub_succ_succ_eq, add_mul,
                    term1_rw, term2_rw, ←mul_add, add_succ_sub_self h_le_k', factorial_succ]
              · -- Caso k' = n'
                subst h_eq
                rw [binom_self (σ k'), one_mul, sub_self, factorial_zero, mul_one]

    -- ── Divisibilidad prima de coeficientes binomiales ────────────────────────

    section PrimeDvdBinom
      open Peano.Primes

      private abbrev Prime := Peano.Primes.Prime

      /- 0 < a < p → p ∤ a. -/
      private theorem prime_not_dvd_of_pos_lt {p a : ℕ₀}
          (ha_pos : lt₀ 𝟘 a) (ha_lt : lt₀ a p) : ¬ (p ∣ a) := by
        intro ⟨k, hk⟩
        cases k with
        | zero =>
            rw [mul_zero] at hk
            exact absurd (hk ▸ ha_pos) (lt_irrefl 𝟘)
        | succ k' =>
            have h_ge : le₀ p a := by
              rw [hk]
              exact mul_le_right p (σ k') (succ_neq_zero k')
            rcases h_ge with h_lt | h_eq
            · exact absurd (lt_trans a p a ha_lt h_lt) (lt_irrefl a)
            · exact absurd (h_eq ▸ ha_lt) (lt_irrefl a)

      /- p primo, k < p → p ∤ k!. -/
      private theorem prime_not_dvd_factorial {p : ℕ₀} (hp : Prime p) :
          ∀ k : ℕ₀, lt₀ k p → ¬ (p ∣ factorial k) := by
        intro k
        induction k with
        | zero =>
            intro _ h_dvd
            rw [factorial_zero] at h_dvd
            have h_le : le₀ p 𝟙 := divides_le h_dvd (succ_neq_zero 𝟘)
            have h_2_le_1 : le₀ 𝟚 𝟙 := le_trans 𝟚 p 𝟙 (prime_ge_two hp) h_le
            exact absurd (lt_succ_self 𝟙) (le_then_ngt 𝟚 𝟙 h_2_le_1)
        | succ k' ih =>
            intro hsk_lt h_dvd
            rw [factorial_succ] at h_dvd
            have hk'_lt : lt₀ k' p := lt_trans k' (σ k') p (lt_succ_self k') hsk_lt
            rcases hp.2.2 _ _ h_dvd with h1 | h2
            · exact ih hk'_lt h1
            · exact absurd h2 (prime_not_dvd_of_pos_lt (lt_zero_succ k') hsk_lt)

      /- p primo, 0 < k < p → p ∣ C(p, k). -/
      theorem prime_dvd_binom_prime {p k : ℕ₀} (hp : Prime p)
          (hk_pos : lt₀ 𝟘 k) (hk_lt : lt₀ k p) : p ∣ C(p, k) := by
        have h_k_le_p : le₀ k p := lt_imp_le_wp hk_lt
        have h_binom := binom_mul_factorials h_k_le_p
        have h_p_dvd_fact_p : p ∣ factorial p := by
          cases p with
          | zero => exact absurd rfl (prime_ne_zero hp)
          | succ p' =>
              rw [factorial_succ]
              exact divides_mul_left (divides_refl (σ p'))
        have h_p_dvd_lhs :
            p ∣ mul (mul C(p, k) (factorial k)) (factorial (sub p k)) := by
          rw [h_binom]; exact h_p_dvd_fact_p
        have hk_ne_zero : k ≠ 𝟘 := Ne.symm (ne_of_lt 𝟘 k hk_pos)
        have h_sub_lt : lt₀ (sub p k) p := sub_lt_self p k h_k_le_p hk_ne_zero
        have h_not_dvd_sub : ¬ (p ∣ factorial (sub p k)) :=
          prime_not_dvd_factorial hp (sub p k) h_sub_lt
        have h_not_dvd_k : ¬ (p ∣ factorial k) :=
          prime_not_dvd_factorial hp k hk_lt
        rcases hp.2.2 _ _ h_p_dvd_lhs with h1 | h2
        · rcases hp.2.2 _ _ h1 with h3 | h4
          · exact h3
          · exact absurd h4 h_not_dvd_k
        · exact absurd h2 h_not_dvd_sub

    end PrimeDvdBinom

    -- ── Identidad de fila: C(p·r, p) = r · C(p·r−1, p−1) ────────────────────────

    private theorem binom_prime_row_aux (p' r' : ℕ₀) :
        C(mul (σ p') (σ r'), σ p') = mul (σ r') (C(sub (mul (σ p') (σ r')) 𝟙, p')) := by
      have hn_pos : lt₀ 𝟘 (mul (σ p') (σ r')) := mul_pos (lt_zero_succ p') (lt_zero_succ r')
      have hn_ne : mul (σ p') (σ r') ≠ 𝟘 := Ne.symm (ne_of_lt 𝟘 _ hn_pos)
      have h_n_succ : σ (sub (mul (σ p') (σ r')) 𝟙) = mul (σ p') (σ r') := by
        rw [sub_one, tau_eq_rho_if_ne_zero _ hn_ne]; exact σ_ρ_eq_self _ hn_ne
      have h_p_le_n : le₀ (σ p') (mul (σ p') (σ r')) :=
        mul_le_right (σ p') (σ r') (succ_neq_zero r')
      have h_p'_le : le₀ p' (sub (mul (σ p') (σ r')) 𝟙) := by
        have h : le₀ (σ p') (σ (sub (mul (σ p') (σ r')) 𝟙)) := h_n_succ.symm ▸ h_p_le_n
        exact (succ_le_succ_iff p' _).mp h
      have h_sub_sub : sub (sub (mul (σ p') (σ r')) 𝟙) p' = sub (mul (σ p') (σ r')) (σ p') := by
        rw [sub_succ_succ_eq, h_n_succ]
      have eq1 : mul (mul C(mul (σ p') (σ r'), σ p') (factorial (σ p')))
                     (factorial (sub (mul (σ p') (σ r')) (σ p'))) =
                 factorial (mul (σ p') (σ r')) :=
        binom_mul_factorials h_p_le_n
      have eq2 : mul (mul C(sub (mul (σ p') (σ r')) 𝟙, p') (factorial p'))
                     (factorial (sub (mul (σ p') (σ r')) (σ p'))) =
                 factorial (sub (mul (σ p') (σ r')) 𝟙) := by
        have h := binom_mul_factorials h_p'_le; rw [h_sub_sub] at h; exact h
      have h_fact_n : factorial (mul (σ p') (σ r')) =
          mul (factorial (sub (mul (σ p') (σ r')) 𝟙)) (mul (σ p') (σ r')) := by
        have h1 : factorial (mul (σ p') (σ r')) =
            factorial (σ (sub (mul (σ p') (σ r')) 𝟙)) := congrArg factorial h_n_succ.symm
        rw [h1, factorial_succ (sub (mul (σ p') (σ r')) 𝟙), h_n_succ]
      have stepA : mul (mul C(mul (σ p') (σ r'), σ p') (σ p'))
                       (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p')))) =
                   factorial (mul (σ p') (σ r')) := by
        have inner : mul (σ p') (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p')))) =
            mul (factorial (σ p')) (factorial (sub (mul (σ p') (σ r')) (σ p'))) := by
          rw [← mul_assoc (factorial p') (σ p') (factorial (sub (mul (σ p') (σ r')) (σ p'))),
              mul_comm (σ p') (factorial p'), ← factorial_succ p']
        calc mul (mul C(mul (σ p') (σ r'), σ p') (σ p'))
                 (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p'))))
            = mul C(mul (σ p') (σ r'), σ p')
                  (mul (σ p') (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p'))))) :=
                mul_assoc (σ p') C(mul (σ p') (σ r'), σ p')
                    (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p'))))
          _ = mul C(mul (σ p') (σ r'), σ p')
                  (mul (factorial (σ p')) (factorial (sub (mul (σ p') (σ r')) (σ p')))) :=
                by rw [inner]
          _ = mul (mul C(mul (σ p') (σ r'), σ p') (factorial (σ p')))
                  (factorial (sub (mul (σ p') (σ r')) (σ p'))) := by
                rw [← mul_assoc (factorial (σ p')) C(mul (σ p') (σ r'), σ p')
                        (factorial (sub (mul (σ p') (σ r')) (σ p')))]
          _ = factorial (mul (σ p') (σ r')) := eq1
      have stepB : mul (mul (mul (σ p') (σ r')) C(sub (mul (σ p') (σ r')) 𝟙, p'))
                       (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p')))) =
                   factorial (mul (σ p') (σ r')) := by
        calc mul (mul (mul (σ p') (σ r')) C(sub (mul (σ p') (σ r')) 𝟙, p'))
                 (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p'))))
            = mul (mul (σ p') (σ r'))
                  (mul C(sub (mul (σ p') (σ r')) 𝟙, p')
                       (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p'))))) :=
                mul_assoc C(sub (mul (σ p') (σ r')) 𝟙, p') (mul (σ p') (σ r'))
                    (mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p'))))
          _ = mul (mul (σ p') (σ r'))
                  (mul (mul C(sub (mul (σ p') (σ r')) 𝟙, p') (factorial p'))
                       (factorial (sub (mul (σ p') (σ r')) (σ p')))) := by
                rw [← mul_assoc (factorial p') C(sub (mul (σ p') (σ r')) 𝟙, p')
                        (factorial (sub (mul (σ p') (σ r')) (σ p')))]
          _ = mul (mul (σ p') (σ r')) (factorial (sub (mul (σ p') (σ r')) 𝟙)) := by rw [eq2]
          _ = mul (factorial (sub (mul (σ p') (σ r')) 𝟙)) (mul (σ p') (σ r')) :=
                mul_comm (mul (σ p') (σ r')) (factorial (sub (mul (σ p') (σ r')) 𝟙))
          _ = factorial (mul (σ p') (σ r')) := h_fact_n.symm
      have h_factor_ne : mul (factorial p') (factorial (sub (mul (σ p') (σ r')) (σ p'))) ≠ 𝟘 := by
        intro h
        rcases (mul_eq_zero _ _).mp h with h1 | h2
        · exact factorial_ne_zero p' h1
        · exact factorial_ne_zero (sub (mul (σ p') (σ r')) (σ p')) h2
      have h_mid : mul C(mul (σ p') (σ r'), σ p') (σ p') =
                   mul (mul (σ p') (σ r')) C(sub (mul (σ p') (σ r')) 𝟙, p') :=
        mul_cancelation_right _ _ _ h_factor_ne (stepA.trans stepB.symm)
      have h_rhs : mul (mul (σ p') (σ r')) C(sub (mul (σ p') (σ r')) 𝟙, p') =
                   mul (σ p') (mul (σ r') C(sub (mul (σ p') (σ r')) 𝟙, p')) :=
        mul_assoc (σ r') (σ p') C(sub (mul (σ p') (σ r')) 𝟙, p')
      rw [mul_comm C(mul (σ p') (σ r'), σ p') (σ p'), h_rhs] at h_mid
      exact mul_cancelation_left (σ p') C(mul (σ p') (σ r'), σ p')
        (mul (σ r') C(sub (mul (σ p') (σ r')) 𝟙, p')) (succ_neq_zero p') h_mid

    /- C(p·r, p) = r · C(p·r−1, p−1) para p ≠ 0, r ≠ 0. -/
    theorem binom_prime_row {p r : ℕ₀} (hp : p ≠ 𝟘) (hr : r ≠ 𝟘) :
        C(mul p r, p) = mul r (C(sub (mul p r) 𝟙, sub p 𝟙)) := by
      cases p with
      | zero => exact absurd rfl hp
      | succ p' =>
      cases r with
      | zero => exact absurd rfl hr
      | succ r' =>
      have h_sub_p : sub (σ p') 𝟙 = p' := by rw [sub_one]; exact τ_σ_eq_self p'
      rw [h_sub_p]
      exact binom_prime_row_aux p' r'

    -- ── C(p·r, p) ≡ r [MOD p] — argumento de Wielandt ──────────────────────────

    section BinomModP
      open Peano.Primes
      open Peano.Div
      open Peano.Arith
      open Peano.ModEq

      private abbrev Prime' := Peano.Primes.Prime

      -- p ∣ n ∧ n < p → n = 0
      private theorem dvd_lt_imp_zero' {p n : ℕ₀} (h_dvd : p ∣ n) (h_lt : lt₀ n p) : n = 𝟘 := by
        cases n with
        | zero => rfl
        | succ n' =>
          exact absurd h_lt (le_not_lt (divides_le h_dvd (succ_neq_zero n')))

      -- 0 < a < p → p ∤ a
      private theorem prime_not_dvd_of_pos_lt' {p a : ℕ₀}
          (ha_pos : lt₀ 𝟘 a) (ha_lt : lt₀ a p) : ¬ (p ∣ a) := by
        intro ⟨k, hk⟩
        cases k with
        | zero => rw [mul_zero] at hk; exact absurd (hk ▸ ha_pos) (lt_irrefl 𝟘)
        | succ k' =>
          have h_ge : le₀ p a := hk ▸ mul_le_right p (σ k') (succ_neq_zero k')
          rcases h_ge with h_lt' | h_eq
          · exact absurd (lt_trans a p a ha_lt h_lt') (lt_irrefl a)
          · exact absurd (h_eq ▸ ha_lt) (lt_irrefl a)

      -- p primo, k < p → p ∤ k!
      private theorem prime_not_dvd_factorial' {p : ℕ₀} (hp : Prime' p) :
          ∀ k : ℕ₀, lt₀ k p → ¬ (p ∣ factorial k) := by
        intro k
        induction k with
        | zero =>
          intro _ h_dvd
          rw [factorial_zero] at h_dvd
          have h_le : le₀ p 𝟙 := divides_le h_dvd (succ_neq_zero 𝟘)
          have h_2_le_1 : le₀ 𝟚 𝟙 := le_trans 𝟚 p 𝟙 (prime_ge_two hp) h_le
          exact absurd (lt_succ_self 𝟙) (le_then_ngt 𝟚 𝟙 h_2_le_1)
        | succ k' ih =>
          intro hsk_lt h_dvd
          rw [factorial_succ] at h_dvd
          have hk'_lt : lt₀ k' p := lt_trans k' (σ k') p (lt_succ_self k') hsk_lt
          rcases hp.2.2 _ _ h_dvd with h1 | h2
          · exact ih hk'_lt h1
          · exact absurd h2 (prime_not_dvd_of_pos_lt' (lt_zero_succ k') hsk_lt)

      -- p·r − (k+1) ≡ p − (k+1) [MOD p]
      private theorem sub_mul_p_mod_congr (p r k : ℕ₀) (hp : Prime' p) (hr : r ≠ 𝟘)
          (hk : lt₀ (σ k) p) :
          sub (mul p r) (σ k) ≡ sub p (σ k) [MOD p] := by
        have hp_ne : p ≠ 𝟘 := hp.1
        have hle : le₀ (σ k) p := lt_imp_le_wp hk
        have hmul : mul p r = add (mul p (τ r)) p := by
          have hr_succ : r = σ (τ r) := by
            have h := σ_ρ_eq_self r hr
            rw [← tau_eq_rho_if_ne_zero r hr] at h
            exact h.symm
          calc mul p r = mul p (σ (τ r)) := by rw [← hr_succ]
                     _ = add (mul p (τ r)) p   := mul_succ p (τ r)
        have hdecomp : sub (mul p r) (σ k) = add (sub p (σ k)) (mul p (τ r)) := by
          rw [hmul, add_comm (mul p (τ r)) p]
          exact (add_sub_assoc p (mul p (τ r)) (σ k) hle).symm
        rw [hdecomp]
        have hdvd : p ∣ mul p (τ r) := ⟨τ r, rfl⟩
        have hmul_zero : mul p (τ r) ≡ 𝟘 [MOD p] := modEq_zero_of_dvd hp_ne hdvd
        have h := modEq_add (modEq_refl p (sub p (σ k))) hmul_zero
        rw [add_zero] at h
        exact h

      -- Producto cayente: fallingProd N j = (N−1)·(N−2)·…·(N−j)
      private def fallingProd (N : ℕ₀) : ℕ₀ → ℕ₀
        | .zero   => 𝟙
        | .succ j' => mul (fallingProd N j') (sub N (σ j'))

      private theorem fallingProd_zero (N : ℕ₀) : fallingProd N 𝟘 = 𝟙 := rfl
      private theorem fallingProd_succ (N j : ℕ₀) :
          fallingProd N (σ j) = mul (fallingProd N j) (sub N (σ j)) := rfl

      -- fallingProd (p·r) j ≡ fallingProd p j [MOD p]   (j ≤ p−1)
      private theorem fallingProd_congr (p r j : ℕ₀) (hp : Prime' p) (hr : r ≠ 𝟘)
          (hj : le₀ j (sub p 𝟙)) :
          fallingProd (mul p r) j ≡ fallingProd p j [MOD p] := by
        induction j with
        | zero => simp only [fallingProd_zero]; exact modEq_refl p 𝟙
        | succ j' ih =>
          have hj' : le₀ j' (sub p 𝟙) := le_succ_then_le hj
          have hk : lt₀ (σ j') p := by
            have h_sub_lt : lt₀ (sub p 𝟙) p :=
              sub_lt_self p 𝟙 (lt_imp_le_wp (one_lt_prime hp)) (succ_neq_zero 𝟘)
            cases hj with
            | inl h_lt => exact lt_trans _ _ _ h_lt h_sub_lt
            | inr h_eq => exact h_eq ▸ h_sub_lt
          simp only [fallingProd_succ]
          exact modEq_mul (ih hj') (sub_mul_p_mod_congr p r j' hp hr hk)

      -- fallingProd N j · (sub (sub N 1) j)! = (sub N 1)!   (j ≤ sub N 1)
      private theorem fallingProd_mul_fact (N j : ℕ₀) (h_le : le₀ j (sub N 𝟙)) :
          mul (fallingProd N j) (factorial (sub (sub N 𝟙) j)) = factorial (sub N 𝟙) := by
        induction j with
        | zero => simp only [fallingProd_zero, one_mul, sub_zero]
        | succ j' ih =>
          have h_le'  : le₀ j' (sub N 𝟙) := le_succ_then_le h_le
          have h_lt_j': lt₀ j' (sub N 𝟙)  := le_succ_k_n_then_lt_k_n_wp h_le
          have h_sub_pos : lt₀ 𝟘 (sub (sub N 𝟙) j') := sub_pos_of_lt h_lt_j'
          have h_sub_ne : sub (sub N 𝟙) j' ≠ 𝟘 := Ne.symm (ne_of_lt 𝟘 _ h_sub_pos)
          -- sub (sub N 1) (σ j') = τ (sub (sub N 1) j')
          have h_step : sub (sub N 𝟙) (σ j') = τ (sub (sub N 𝟙) j') :=
            succ_sub (sub N 𝟙) j' h_le
          -- σ (τ x) = x  cuando x ≠ 0
          have h_sigma_tau : σ (τ (sub (sub N 𝟙) j')) = sub (sub N 𝟙) j' := by
            rw [tau_eq_rho_if_ne_zero _ h_sub_ne]; exact σ_ρ_eq_self _ h_sub_ne
          -- 1 ≤ N  (necesario para sub_sub)
          have h1_le_N : le₀ 𝟙 N :=
            le_trans _ _ _ (le_trans _ _ _ (le_1_succ j') h_le) (sub_le_self N 𝟙)
          -- sub (sub N 1) j' = sub N (σ j')  (por sub_sub + one_add)
          have key : sub (sub N 𝟙) j' = sub N (σ j') := by
            have h_eq := sub_sub N 𝟙 j' h1_le_N h_le'
            rw [one_add] at h_eq; exact h_eq
          -- sub (sub N 1) j' = σ (sub (sub N 1) (σ j'))
          have h_eq_sigma : sub (sub N 𝟙) j' = σ (sub (sub N 𝟙) (σ j')) := by
            rw [h_step]; exact h_sigma_tau.symm
          -- σ (sub (sub N 1) (σ j')) = sub N (σ j')
          have h_sigma_eq : σ (sub (sub N 𝟙) (σ j')) = sub N (σ j') := by
            rw [h_step]; exact h_sigma_tau.trans key
          -- factor paso: (N − σj') · (sub(sub N 1)(σj'))! = (sub(sub N 1) j')!
          have h_fact_step :
              mul (sub N (σ j')) (factorial (sub (sub N 𝟙) (σ j'))) =
              factorial (sub (sub N 𝟙) j') :=
            calc mul (sub N (σ j')) (factorial (sub (sub N 𝟙) (σ j')))
                = mul (factorial (sub (sub N 𝟙) (σ j'))) (sub N (σ j'))         := mul_comm _ _
              _ = mul (factorial (sub (sub N 𝟙) (σ j'))) (σ (sub (sub N 𝟙) (σ j'))) :=
                    by rw [h_sigma_eq]
              _ = factorial (σ (sub (sub N 𝟙) (σ j')))                          :=
                    (factorial_succ _).symm
              _ = factorial (sub (sub N 𝟙) j')                                  :=
                    by rw [← h_eq_sigma]
          simp only [fallingProd_succ]
          calc mul (mul (fallingProd N j') (sub N (σ j')))
                   (factorial (sub (sub N 𝟙) (σ j')))
              = mul (fallingProd N j')
                    (mul (sub N (σ j')) (factorial (sub (sub N 𝟙) (σ j')))) :=
                  mul_assoc (sub N (σ j')) (fallingProd N j')
                    (factorial (sub (sub N 𝟙) (σ j')))
            _ = mul (fallingProd N j') (factorial (sub (sub N 𝟙) j')) := by rw [h_fact_step]
            _ = factorial (sub N 𝟙)                                     := ih h_le'

      -- C·F ≡ F [MOD p] ∧ p ∤ F → C ≡ 1 [MOD p]
      private theorem mod_mul_cancel_right_one (p C F : ℕ₀) (hp : Prime' p)
          (hF_ndvd : ¬ p ∣ F) (h : mul C F ≡ F [MOD p]) :
          C ≡ 𝟙 [MOD p] := by
        have hp_ne  : p ≠ 𝟘    := hp.1
        have hp_gt1 : lt₀ 𝟙 p  := one_lt_prime hp
        have hF_mod_lt : lt₀ (mod F p) p := mod_lt F p hp_ne
        have hF_mod_ne : mod F p ≠ 𝟘 := by
          intro h_zero; exact hF_ndvd ((mod_eq_zero_iff_dvd hp_ne).mp h_zero)
        have hF_mod_ndvd : ¬ p ∣ mod F p := fun h_dvd =>
          hF_mod_ne (dvd_lt_imp_zero' h_dvd hF_mod_lt)
        have hF_mod_cop : Coprime p (mod F p) :=
          (gcd_eq_one_iff_coprime p (mod F p)).mp (prime_not_dvd_imp_coprime hp hF_mod_ndvd)
        -- mod(C·F) p = mod F p  →  mod(c·f) p = f   donde c := mod C p, f := mod F p
        have h_mul_mod : mod (mul (mod C p) (mod F p)) p = mod F p := by
          unfold ModEq at h; rw [mul_mod] at h; exact h
        have hc_lt : lt₀ (mod C p) p := mod_lt C p hp_ne
        -- Suficiente: mod C p = 1
        suffices h_goal : mod C p = 𝟙 by
          show mod C p = mod 𝟙 p
          rw [h_goal]
          exact (mod_of_lt 𝟙 p hp_gt1).symm
        -- Análisis por casos sobre mod C p
        cases h_c : mod C p with
        | zero =>
          -- 0 · f ≡ 0 ≠ f  →  contradicción
          rw [h_c, zero_mul, mod_zero_left] at h_mul_mod
          exact absurd h_mul_mod.symm hF_mod_ne
        | succ c' =>
          -- mod C p = σ c'
          rw [h_c] at h_mul_mod
          -- (σ c') · f = c'·f + f  (succ_mul)
          have h_sm : mul (σ c') (mod F p) = add (mul c' (mod F p)) (mod F p) :=
            succ_mul c' (mod F p)
          -- divMod_spec da: (σ c')·f = q·p + f
          have h_spec := divMod_spec (mul (σ c') (mod F p)) p hp_ne
          have h_rem  : (divMod (mul (σ c') (mod F p)) p).2 = mod F p := h_mul_mod
          rw [h_rem] at h_spec
          -- h_spec : mul (σ c') f = add (mul q p) f
          -- h_sm + h_spec → add (mul c' f) f = add (mul q p) f
          have h_combined : add (mul c' (mod F p)) (mod F p) =
              add (mul (divMod (mul (σ c') (mod F p)) p).1 p) (mod F p) :=
            h_sm.symm.trans h_spec
          have h_add : add (mod F p) (mul c' (mod F p)) =
              add (mod F p) (mul (divMod (mul (σ c') (mod F p)) p).1 p) := by
            rw [add_comm (mod F p) (mul c' (mod F p)),
                add_comm (mod F p) (mul (divMod (mul (σ c') (mod F p)) p).1 p)]
            exact h_combined
          have h_cancel : mul c' (mod F p) = mul (divMod (mul (σ c') (mod F p)) p).1 p :=
            add_cancel (mod F p) _ _ h_add
          -- p ∣ f·c'  (por cancelación)
          have h_dvd_mul : p ∣ mul (mod F p) c' :=
            ⟨(divMod (mul (σ c') (mod F p)) p).1,
             by rw [mul_comm (mod F p) c', h_cancel, mul_comm]⟩
          -- p ∣ c'  (por coprimalidad con f)
          have h_dvd_c' : p ∣ c' := coprime_dvd_of_dvd_mul hF_mod_cop h_dvd_mul
          -- c' < p  (pues σ c' = mod C p < p)
          have h_c'_lt : lt₀ c' p :=
            lt_trans c' (σ c') p (lt_self_σ_self c') (h_c ▸ hc_lt)
          -- p ∣ c' ∧ c' < p  →  c' = 0
          have h_c'_zero : c' = 𝟘 := dvd_lt_imp_zero' h_dvd_c' h_c'_lt
          rw [h_c'_zero]; rfl

      -- C(p·r−1, p−1) ≡ 1 [MOD p]
      private theorem binom_aux_mod (p r : ℕ₀) (hp : Prime' p) (hr : r ≠ 𝟘) :
          C(sub (mul p r) 𝟙, sub p 𝟙) ≡ 𝟙 [MOD p] := by
        have h_1_le_p : le₀ 𝟙 p := lt_imp_le_wp (one_lt_prime hp)
        -- sub p 1 ≤ sub (p·r) 1  (pues p ≤ p·r cuando r ≥ 1)
        have h_1_le_pr : le₀ 𝟙 (mul p r) :=
          le_trans 𝟙 p _ h_1_le_p (mul_le_right p r hr)
        have h_le : le₀ (sub p 𝟙) (sub (mul p r) 𝟙) := by
          apply (le_sub_iff_add_le_of_le (mul p r) 𝟙 (sub p 𝟙) h_1_le_pr).mpr
          rw [add_comm, sub_k_add_k p 𝟙 h_1_le_p]
          exact mul_le_right p r hr
        -- C · (p−1)! = fallingProd (p·r) (p−1)
        have h_binom_eq :
            mul C(sub (mul p r) 𝟙, sub p 𝟙) (factorial (sub p 𝟙)) =
            fallingProd (mul p r) (sub p 𝟙) := by
          have h_rest_ne : factorial (sub (sub (mul p r) 𝟙) (sub p 𝟙)) ≠ 𝟘 :=
            factorial_ne_zero _
          have h1 : mul (mul C(sub (mul p r) 𝟙, sub p 𝟙) (factorial (sub p 𝟙)))
                        (factorial (sub (sub (mul p r) 𝟙) (sub p 𝟙))) =
                    factorial (sub (mul p r) 𝟙) :=
            binom_mul_factorials h_le
          have h2 : mul (fallingProd (mul p r) (sub p 𝟙))
                        (factorial (sub (sub (mul p r) 𝟙) (sub p 𝟙))) =
                    factorial (sub (mul p r) 𝟙) :=
            fallingProd_mul_fact (mul p r) (sub p 𝟙) h_le
          exact mul_cancelation_right _ _ _ h_rest_ne (h1.trans h2.symm)
        -- fallingProd p (p−1) = (p−1)!
        have h_fp_p : fallingProd p (sub p 𝟙) = factorial (sub p 𝟙) := by
          have h := fallingProd_mul_fact p (sub p 𝟙) (le_refl (sub p 𝟙))
          rw [sub_self, factorial_zero, mul_one] at h
          exact h
        -- fallingProd (p·r) (p−1) ≡ (p−1)! [MOD p]
        have h_congr : fallingProd (mul p r) (sub p 𝟙) ≡ factorial (sub p 𝟙) [MOD p] :=
          h_fp_p ▸ fallingProd_congr p r (sub p 𝟙) hp hr (le_refl _)
        -- C · (p−1)! ≡ (p−1)! [MOD p]
        have h_CF : mul C(sub (mul p r) 𝟙, sub p 𝟙) (factorial (sub p 𝟙)) ≡
            factorial (sub p 𝟙) [MOD p] :=
          h_binom_eq ▸ h_congr
        -- p ∤ (p−1)!
        have h_ndvd : ¬ p ∣ factorial (sub p 𝟙) :=
          prime_not_dvd_factorial' hp (sub p 𝟙)
            (sub_lt_self p 𝟙 h_1_le_p (succ_neq_zero 𝟘))
        exact mod_mul_cancel_right_one p _ _ hp h_ndvd h_CF

      /- C(p·r, p) ≡ r [MOD p] para p primo y r ≠ 0. -/
      theorem binom_pr_p_mod {p r : ℕ₀} (hp : Prime' p) (hr : r ≠ 𝟘) :
          C(mul p r, p) ≡ r [MOD p] := by
        have hp_ne : p ≠ 𝟘 := hp.1
        -- C(p·r, p) = r · C(p·r−1, p−1)
        have h_row : C(mul p r, p) = mul r C(sub (mul p r) 𝟙, sub p 𝟙) :=
          binom_prime_row hp_ne hr
        -- C(p·r−1, p−1) ≡ 1 [MOD p]
        have h_aux : C(sub (mul p r) 𝟙, sub p 𝟙) ≡ 𝟙 [MOD p] :=
          binom_aux_mod p r hp hr
        -- r · C(p·r−1, p−1) ≡ r · 1 = r [MOD p]
        have h_mul : mul r C(sub (mul p r) 𝟙, sub p 𝟙) ≡ r [MOD p] := by
          have := modEq_mul (modEq_refl p r) h_aux
          rwa [mul_one] at this
        exact h_row ▸ h_mul

      /- Lucas generalizado: C(p^n · r, p^n) ≡ r [MOD p] para p primo y r ≠ 0.
         Caso base n=0: C(r, 1) = r.
         Paso inductivo: usa binom_pr_p_mod + la identidad de reducción
         C(p·M, p·K) ≡ C(M, K) [MOD p], pendiente de demostración completa.
         TODO: eliminar este axioma cuando se formalice la reducción de Lucas
               C(p·M, p·K) ≡ C(M, K) [MOD p] para todo M, K. -/
      private axiom binom_pow_p_mod_aux
          (p M K : ℕ₀) (hp : Prime' p) :
          C(mul p M, mul p K) ≡ C(M, K) [MOD p]

      /- C(p^n · r, p^n) ≡ r [MOD p] para p primo, n ≥ 1 y r ≠ 0.
         Prueba por inducción sobre n usando binom_pr_p_mod (base n=1)
         y binom_pow_p_mod_aux (paso inductivo). -/
      theorem binom_pow_p_mod {p r : ℕ₀} (hp : Prime' p) (hr : r ≠ 𝟘) :
          ∀ n : ℕ₀, n ≠ 𝟘 → C(mul (pow p n) r, pow p n) ≡ r [MOD p] := by
        intro n
        induction n with
        | zero => intro h; exact absurd rfl h
        | succ n' ih =>
          intro _
          cases n' with
          | zero =>
            -- n = 1: C(p·r, p) ≡ r [MOD p]
            simp only [pow_succ, pow_zero, one_mul]
            exact binom_pr_p_mod hp hr
          | succ n'' =>
            -- n = n''+2: usamos C(p·M, p·K) ≡ C(M, K) con M = p^(n''+1)·r, K = p^(n''+1)
            have ih' : C(mul (pow p (σ n'')) r, pow p (σ n'')) ≡ r [MOD p] :=
              ih (succ_neq_zero n'')
            -- p^(n''+2) = p^(n''+1) · p
            have h_pow : pow p (σ (σ n'')) = mul (pow p (σ n'')) p :=
              pow_succ p (σ n'')
            -- mul (pow p^(n''+2)) r reescrito usando h_pow
            -- = mul (mul (pow p (σ n'')) p) r
            -- = mul p (mul (pow p (σ n'')) r)  [conm + assoc]
            have h_eq : mul (pow p (σ (σ n''))) r =
                mul p (mul (pow p (σ n'')) r) := by
              rw [h_pow, mul_comm (pow p (σ n'')) p]
              exact mul_assoc (pow p (σ n'')) p r
            have h_pow_eq : pow p (σ (σ n'')) = mul p (pow p (σ n'')) := by
              rw [h_pow, mul_comm]
            rw [h_eq, h_pow_eq]
            -- Ahora: C(mul p (pow p (σ n'')*r), mul p (pow p (σ n''))) ≡ r
            -- Por binom_pow_p_mod_aux: C(p·M, p·K) ≡ C(M, K) [MOD p]
            exact modEq_trans
              (binom_pow_p_mod_aux p (mul (pow p (σ n'')) r) (pow p (σ n'')) hp)
              ih'

    end BinomModP

  end Binom
end Peano

export Peano.Binom (
  binom
  binom_zero_zero
  binom_zero_succ
  binom_succ_zero
  binom_pascal
  binom_n_zero
  binom_n_one
  binom_eq_zero_of_gt
  binom_self
  binom_pos
  binom_one
  binom_succ_n_by_n
  binom_mul_factorials
  prime_dvd_binom_prime
  binom_prime_row
  binom_pr_p_mod
  binom_pow_p_mod
)
