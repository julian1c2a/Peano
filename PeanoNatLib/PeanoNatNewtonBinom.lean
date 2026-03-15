/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- PeanoNatLib/PeanoNatNewtonBinom.lean
-- Sumatorios finitos, Teorema del Binomio de Newton y crecimiento comparado.
-- REFERENCE.md: proyectar este archivo en la sección 17 de REFERENCE.md.

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatPow
import PeanoNatLib.PeanoNatFactorial
import PeanoNatLib.PeanoNatBinom

namespace Peano
  open Peano

  namespace NewtonBinom
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.Add
    open Peano.Sub
    open Peano.Mul
    open Peano.Pow
    open Peano.Factorial
    open Peano.Binom

    -- ── §1. Sumatorio finito ───────────────────────────────────────────────────

    /- `finSum f n` = Σ_{k=0}^{n} f(k).
       Computable. Terminado por recursión estructural en n. -/
    def finSum (f : ℕ₀ → ℕ₀) : ℕ₀ → ℕ₀
      | 𝟘   => f 𝟘
      | σ n => add (finSum f n) (f (σ n))

    /- Notación: `∑ k ≤ n, f k` = finSum (fun k => f k) n = Σ_{k=0}^{n} f(k).
       Uso: ∑ k ≤ n', C(n', k)  en lugar de  finSum (fun k => C(n', k)) n'. -/
    macro "∑ " k:ident " ≤ " n:term ", " f:term : term => `(finSum (fun $k => $f) $n)

    -- ── Propiedades básicas del sumatorio ─────────────────────────────────────

    theorem finSum_zero (f : ℕ₀ → ℕ₀) : finSum f 𝟘 = f 𝟘 := by rfl

    theorem finSum_succ (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum f (σ n) = add (finSum f n) (f (σ n)) := by rfl

    /- El sumatorio de la función cero es cero. -/
    theorem finSum_zero_fn (n : ℕ₀) : finSum (fun _ => 𝟘) n = 𝟘 := by
      induction n with
      | zero    => rfl
      | succ n' ih => rw [finSum_succ, ih, add_zero]

    /- Linealidad: Σ (f + g) = Σ f + Σ g. -/
    theorem finSum_add_fn (f g : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum (fun k => add (f k) (g k)) n = add (finSum f n) (finSum g n) := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          -- Objetivo tras rw ih: (A+B)+(C+D) = (A+C)+(B+D)  con A=ΣF, B=ΣG, C=f(σn'), D=g(σn')
          rw [finSum_succ, finSum_succ, finSum_succ, ih]
          rw [add_assoc, ← add_assoc (finSum f n'), add_comm (finSum g n'),
              add_assoc (finSum f n'), ← add_assoc]

    /- Factor constante: Σ (c · f) = c · Σ f. -/
    theorem finSum_mul_const (c : ℕ₀) (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum (fun k => mul c (f k)) n = mul c (finSum f n) := by
      induction n with
      | zero    => rfl
      | succ n' ih => rw [finSum_succ, finSum_succ, ih, mul_ldistr]

    /- Distribución a derecha: (Σ f) · c = Σ (f · c). -/
    theorem finSum_mul_const_right (c : ℕ₀) (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        mul (finSum f n) c = finSum (fun k => mul (f k) c) n := by
      induction n with
      | zero    => rfl
      | succ n' ih => rw [finSum_succ, finSum_succ, mul_rdistr, ← ih]

    /- Monotonía: si f ≤ g puntualmente entonces Σ f ≤ Σ g. -/
    theorem finSum_le_of_le (f g : ℕ₀ → ℕ₀) (h : ∀ k, Le (f k) (g k)) (n : ℕ₀) :
        Le (finSum f n) (finSum g n) := by
      induction n with
      | zero    => exact h 𝟘
      | succ n' ih =>
          rw [finSum_succ, finSum_succ]
          exact le_add_compat_wp ih (h (σ n'))

    /- Positividad: si f > 0 puntualmente entonces Σ f > 0. -/
    theorem finSum_pos (f : ℕ₀ → ℕ₀) (h : ∀ k, Lt 𝟘 (f k)) (n : ℕ₀) :
        Lt 𝟘 (finSum f n) := by
      induction n with
      | zero    => exact h 𝟘
      | succ n' ih =>
          rw [finSum_succ]
          exact lt_of_lt_of_le ih (le_self_add_r (finSum f n') (f (σ n')))

    /- La suma de una constante: Σ_{k=0}^{n} c = (n+1)·c. -/
    theorem finSum_const (c n : ℕ₀) :
        finSum (fun _ => c) n = mul (σ n) c := by
      induction n with
      | zero    => rw [finSum_zero]; exact (one_mul c).symm
      | succ n' ih =>
          rw [finSum_succ, ih, ← succ_mul]

    -- ── §1b. Desplazamiento e inversión de índice ─────────────────────────────

    /- Desplazamiento a la izquierda:
       Σ_{k=0}^{n+1} f(k) = f(0) + Σ_{k=0}^{n} f(k+1). -/
    theorem finSum_succ_left (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum f (σ n) = add (f 𝟘) (finSum (fun k => f (σ k)) n) := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [finSum_succ, ih, finSum_succ, ← add_assoc]

    /- Invariancia por inversión del índice:
       Σ_{k=0}^{n} f(k) = Σ_{k=0}^{n} f(n-k).
       Esto expresa que el sumatorio no depende del orden de recorrido. -/
    theorem finSum_reverse (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finSum f n = finSum (fun k => f (sub n k)) n := by
      induction n with
      | zero    => rw [finSum_zero, finSum_zero, sub_self]
      | succ n' ih =>
          rw [finSum_succ, ih,
              finSum_succ_left (fun k => f (sub (σ n') k)),
              sub_zero]
          -- Meta: add (finSum (fun k => f (sub n' k)) n') (f (σ n'))
          --     = add (f (σ n')) (finSum (fun k => f (sub (σ n') (σ k))) n')
          have h_fn : (fun k => f (sub (σ n') (σ k))) = (fun k => f (sub n' k)) := by
            funext k; rw [← sub_succ_succ_eq]
          rw [h_fn, add_comm]

    -- ── §2. Sumatorio de coeficientes binomiales ──────────────────────────────

    /- Suma de la fila n del triángulo de Pascal: Σ_{k=0}^{n} C(n,k) = 2^n.
       Prueba por inducción con la identidad de Pascal.
       ⚠️ sorry: la reindexación de la suma de k=0..n requiere un lema de desplazamiento
       de índice que involucra cuidadosa aritmética sobre la resta truncada. -/
    theorem sum_binom_eq_pow_two (n : ℕ₀) :
        finSum (fun k => C(n, k)) n = pow 𝟚 n := by
      induction n with
      | zero =>
          rw [finSum_zero, binom_zero_zero, pow_zero]
      | succ n' ih =>
          -- Objetivo: Σ_{k=0}^{n'+1} C(n'+1,k) = 2^(n'+1) = 2^n' · 2
          -- Ecuación clave: Σ C(n'+1,k) = Σ C(n',k-1) + Σ C(n',k)  (Pascal)
          -- Bordes: C(n',−1)=0 y C(n',n'+1)=0; resultado = 2·2^n' = 2^(n'+1).
          sorry  -- ⚠️ Reindexación compleja; esquema: Pascal + desplazamiento de índice.

    -- ── §3. Término del binomio de Newton ────────────────────────────────────

    /- Término k-ésimo del desarrollo binomial: C(n,k) · a^k · b^(n-k). -/
    def binomTerm (a b n k : ℕ₀) : ℕ₀ :=
      mul (mul C(n, k) (pow a k)) (pow b (sub n k))

    /- Valor en k=0: C(n,0)·a^0·b^n = b^n. -/
    theorem binomTerm_zero (a b n : ℕ₀) :
        binomTerm a b n 𝟘 = pow b n := by
      unfold binomTerm
      rw [binom_n_zero, pow_zero, sub_zero, one_mul, one_mul]

    /- Valor en k=n: C(n,n)·a^n·b^0 = a^n. -/
    theorem binomTerm_self (a b n : ℕ₀) :
        binomTerm a b n n = pow a n := by
      unfold binomTerm
      rw [binom_self, sub_self, pow_zero, mul_one, one_mul]

    /- Auxiliar: (a·b)·c = (a·c)·b. -/
    private theorem mul_swap_last' (a b c : ℕ₀) : mul (mul a b) c = mul (mul a c) b := by
      rw [mul_assoc b a c, mul_comm b c, ← mul_assoc c a b]

    /- Relación de Pascal en términos del binomio:
       T(n+1, k+1) = T(n,k)·a + T(n,k+1)·b  cuando k+1 ≤ n+1. -/
    private theorem binomTerm_pascal_step (a b n k : ℕ₀) :
        binomTerm a b (σ n) (σ k) =
        add (mul (binomTerm a b n k) a) (mul (binomTerm a b n (σ k)) b) := by
      unfold binomTerm
      rw [binom_pascal, ← sub_succ_succ_eq, pow_succ]
      -- Meta: mul (mul (add C(n,k) C(n,σk)) (mul (pow a k) a)) (pow b (sub n k))
      --     = add (mul (mul (mul C(n,k) (pow a k)) (pow b (sub n k))) a)
      --           (mul (mul (mul C(n,σk) (mul (pow a k) a)) (pow b (sub n (σk)))) b)
      by_cases h : Le (σ k) n
      · -- Caso σk ≤ n: sub n k = σ(sub n (σk)), b^(n-k) = b^(n-k-1) · b
        have h_sub_eq : sub n k = σ (sub n (σ k)) :=
          (sub_succ_succ_eq n k).trans (sub_succ n (σ k) h)
        rw [h_sub_eq, pow_succ]
        -- LHS: (C1+C2)·(A·a)·(B·b)  RHS: C1·A·(B·b)·a + C2·(A·a)·B·b
        rw [mul_rdistr, mul_rdistr]
        congr 1
        · -- C1·(A·a)·(B·b) = (C1·A)·(B·b)·a
          rw [← mul_assoc (pow a k) C(n, k) a,
              mul_swap_last' (mul C(n, k) (pow a k)) a (mul (pow b (sub n (σ k))) b)]
        · -- C2·(A·a)·(B·b) = (C2·(A·a))·B·b
          rw [← mul_assoc (pow b (sub n (σ k))) (mul C(n, σ k) (mul (pow a k) a)) b]
      · -- Caso ¬(σk ≤ n): C(n, σk) = 0, todo el segundo sumando desaparece
        have h_lt : Lt n (σ k) := nle_then_gt_wp h
        rw [binom_eq_zero_of_gt h_lt, add_zero, zero_mul, zero_mul, zero_mul, add_zero]
        -- Meta: C(n,k)·(A·a)·B_k = (C(n,k)·A)·B_k·a
        rw [← mul_assoc (pow a k) C(n, k) a,
            mul_swap_last' (mul C(n, k) (pow a k)) a (pow b (sub n k))]

    /- Teorema del Binomio de Newton:
       (a + b)^n = Σ_{k=0}^{n} C(n,k) · a^k · b^(n-k).

       Demostración por inducción sobre n:
         Base: (a+b)^0 = 1 = C(0,0)·a^0·b^0 = T(a,b,0,0).
         Paso: (a+b)^(n+1) = (a+b)^n · (a+b)
                            = Σ T(a,b,n,k) · (a+b)
                            = Σ T(a,b,n,k)·a + Σ T(a,b,n,k)·b
       La reindexación de ambas sumas y la aplicación de Pascal producen
       Σ_{k=0}^{n+1} T(a,b,n+1,k).
       ⚠️ sorry: la convolución de índices requiere `binomTerm_pascal_step`
       y lemas de desplazamiento de suma que dependen de la resta truncada. -/
    theorem newton_binom (a b n : ℕ₀) :
        pow (add a b) n = finSum (binomTerm a b n) n := by
      induction n with
      | zero =>
          rw [pow_zero, finSum_zero, binomTerm_zero, pow_zero]
      | succ n' ih =>
          rw [pow_succ, ih, mul_ldistr]
          sorry  -- ⚠️ Convolución de sumatorios + Pascal

    -- ── §4. Crecimiento comparado: (n+k)^m < n^(m+k) ─────────────────────────

    /- Lema: n^(m+k) = n^m · n^k. -/
    theorem pow_add_split (n m k : ℕ₀) :
        pow n (add m k) = mul (pow n m) (pow n k) :=
      pow_add_eq_mul_pow n m k

    /- Lema auxiliar: Para n ≥ 2 y k ≥ 1: (n+k)^m < n^m · n^k cuando n^k > (n+k)^m / n^m.
       La prueba formal requiere establecer que n^k crece geométricamente y (n+k)^m polinomialmente.
       ⚠️ sorry: requiere lemas de acotación polinomial vs exponencial. -/
    private theorem poly_vs_exp_bound (n m : ℕ₀) (hn : Le 𝟚 n) :
        ∀ k : ℕ₀, Le 𝟙 k →
          Lt (pow (add n k) m) (mul (pow n m) (pow n k)) := by
      intro k hk
      induction k with
      | zero => exact absurd hk (not_succ_le_zero 𝟘)
      | succ k' _ih =>
          sorry  -- ⚠️ Inducción: (n+k'+1)^m < n^m · n^(k'+1)

    /- Teorema de crecimiento: ∃ n m, ∀ k ≥ 1, (n+k)^m < n^(m+k).

       Tomamos n=4, m=2. Verificación:
         n^(m+k) = 4^(2+k) = 16 · 4^k  (crece exponencialmente)
         (n+k)^m = (4+k)^2             (crece polinomialmente)
       Para k=1: 25 < 64; para k=2: 36 < 256; en general 16·4^k >> (4+k)^2.

       Reformulación: (n+k)^m < n^m · n^k  (por pow_add_split)
       que es `poly_vs_exp_bound n m hn`. -/
    theorem exists_nm_growth :
        ∃ n m : ℕ₀, ∀ k : ℕ₀, Le 𝟙 k →
          Lt (pow (add n k) m) (pow n (add m k)) := by
      refine ⟨σ (σ (σ (σ 𝟘))), σ (σ 𝟘), fun k hk => ?_⟩  -- n = 4, m = 2
      rw [pow_add_split]
      exact poly_vs_exp_bound (σ (σ (σ (σ 𝟘)))) (σ (σ 𝟘))
              (le_trans 𝟚 (σ 𝟚) (σ (σ 𝟚)) (le_succ_self 𝟚) (le_succ_self (σ 𝟚))) k hk

  end NewtonBinom
end Peano

export Peano.NewtonBinom (
  finSum
  finSum_zero
  finSum_succ
  finSum_zero_fn
  finSum_add_fn
  finSum_mul_const
  finSum_mul_const_right
  finSum_le_of_le
  finSum_pos
  finSum_const
  finSum_succ_left
  finSum_reverse
  sum_binom_eq_pow_two
  binomTerm
  binomTerm_zero
  binomTerm_self
  newton_binom
  pow_add_split
  exists_nm_growth
)
