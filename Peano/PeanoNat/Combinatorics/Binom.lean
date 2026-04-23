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
)
