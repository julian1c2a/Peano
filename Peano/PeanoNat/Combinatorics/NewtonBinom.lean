/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/NewtonBinom.lean
-- Teorema del Binomio de Newton y crecimiento comparado.
-- Depende de Summation.lean para finSum (∑).
-- REFERENCE.md: proyectar este archivo en la sección 17 de REFERENCE.md.

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Combinatorics.Factorial
import Peano.PeanoNat.Combinatorics.Binom
import Peano.PeanoNat.Combinatorics.Summation

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
    open Peano.Summation

    -- ── §1. Sumatorio de coeficientes binomiales ──────────────────────────────

    /- Suma de la fila n del triángulo de Pascal: Σ_{k=0}^{n} C(n,k) = 2^n.
       Prueba por inducción con la identidad de Pascal.
    -/
    theorem sum_binom_eq_pow_two (n : ℕ₀) :
        finSum (fun k => C(n, k)) n = pow 𝟚 n := by
      induction n with
      | zero =>
          rw [finSum_zero, binom_zero_zero, pow_zero]
      | succ n' ih =>
          -- Paso 1: desplazar el sumatorio por la izquierda
          rw [finSum_succ_left, binom_succ_zero]
          -- Meta: add 𝟙 (finSum (fun k => C(σ n', σ k)) n') = pow 𝟚 (σ n')
          -- Paso 2: Pascal → C(σn', σk) = C(n',k) + C(n', σk)
          have h_pascal_fn : finSum (fun k => C(σ n', σ k)) n' =
              add (finSum (fun k => C(n', k)) n') (finSum (fun k => C(n', σ k)) n') :=
            finSum_add_fn (fun k => C(n', k)) (fun k => C(n', σ k)) n'
          rw [h_pascal_fn, ih]
          -- Meta: add 𝟙 (add (pow 𝟚 n') (finSum (fun k => C(n', σ k)) n')) = pow 𝟚 (σ n')
          -- Paso 3: la fila n' extendida hasta σn' da pow 𝟚 n' = 1 + Σ C(n', σk)
          have hss : finSum (fun k => C(n', k)) (σ n') = pow 𝟚 n' := by
            rw [finSum_succ, binom_eq_zero_of_gt (lt_succ_self n'), add_zero, ih]
          have h_shift : pow 𝟚 n' = add 𝟙 (finSum (fun k => C(n', σ k)) n') := by
            rw [← hss, finSum_succ_left, binom_n_zero]
          -- Paso 4: álgebra  1 + (P + X) = P + P  con  P = 1 + X
          rw [add_comm (pow 𝟚 n'), add_assoc, ← h_shift, ← mul_two, ← pow_succ]

    -- ── §2. Término del binomio de Newton ────────────────────────────────────

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
        rw [add_mul, add_mul]
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
    -/
    theorem newton_binom (a b n : ℕ₀) :
        pow (add a b) n = finSum (binomTerm a b n) n := by
      induction n with
      | zero =>
          rw [pow_zero, finSum_zero, binomTerm_zero, pow_zero]
      | succ n' ih =>
          rw [pow_succ, ih, mul_add]
          -- Meta: add (mul (finSum (binomTerm a b n') n') a)
          --           (mul (finSum (binomTerm a b n') n') b)
          --     = finSum (binomTerm a b (σ n')) (σ n')

          -- Auxiliar 1: T(n', σn') = 0  (C(n', σn') = 0)
          have h_zero : binomTerm a b n' (σ n') = 𝟘 := by
            unfold binomTerm
            rw [binom_eq_zero_of_gt (lt_succ_self n'), zero_mul, zero_mul]

          -- Auxiliar 2: Σ_{k=0}^{n'} T(n',k) = b^{n'} + Σ_{k=0}^{n'} T(n',σk)
          --   Prueba: finSum (σ n') = T(n',0) + Σ T(n',σk)  (por finSum_succ_left)
          --           finSum (σ n') = finSum (n') + T(n',σn') = finSum (n') + 0
          have h_shift : finSum (binomTerm a b n') n' =
              add (pow b n') (finSum (fun k => binomTerm a b n' (σ k)) n') := by
            have h1 := finSum_succ_left (binomTerm a b n') n'
            rw [binomTerm_zero] at h1
            rw [← h1, finSum_succ, h_zero, add_zero]

          -- Auxiliar 3: Σ (T(n',k)·b) = b^{σn'} + Σ (T(n',σk)·b)
          have h_b_sum : finSum (fun k => mul (binomTerm a b n' k) b) n' =
              add (pow b (σ n')) (finSum (fun k => mul (binomTerm a b n' (σ k)) b) n') := by
            rw [← finSum_mul_const_right, h_shift, add_mul,
                finSum_mul_const_right b (fun k => binomTerm a b n' (σ k)) n', ← pow_succ]

          -- Paso: expandir (Σ T)·a y (Σ T)·b como sumatorios
          rw [finSum_mul_const_right, finSum_mul_const_right]
          -- Expandir el RHS: T(σn',0) = b^{σn'},  luego Pascal en índices interiores
          rw [finSum_succ_left (binomTerm a b (σ n')) n', binomTerm_zero]
          have h_pascal : (fun k => binomTerm a b (σ n') (σ k)) =
                          (fun k => add (mul (binomTerm a b n' k) a)
                                        (mul (binomTerm a b n' (σ k)) b)) :=
            funext (fun k => binomTerm_pascal_step a b n' k)
          rw [h_pascal, finSum_add_fn, h_b_sum]
          -- Meta: add X (add Y Z) = add Y (add X Z)
          --   con X = Σ(T·a), Y = b^{σn'}, Z = Σ(T·b desplazado)
          rw [add_assoc,
              add_comm (finSum (fun k => mul (binomTerm a b n' k) a) n') (pow b (σ n')),
              ← add_assoc]

    -- ── §3. Crecimiento comparado: (n+k)^m < n^(m+k) ─────────────────────────

    /- Lema: n^(m+k) = n^m · n^k. -/
    theorem pow_add_split (n m k : ℕ₀) :
        pow n (add m k) = mul (pow n m) (pow n k) :=
      pow_add_eq_mul_pow n m k

    /- Lema clave: si X < Y entonces σX < Y + Y.
       Prueba: σX < σY ≤ Y+Y, pues Y > 0 implica σY ≤ Y+Y. -/
    private theorem lt_add_double_of_lt_of_pos {X Y : ℕ₀}
        (h_lt : Lt X Y) (h_pos : Lt 𝟘 Y) :
        Lt (σ X) (add Y Y) := by
      have h_sX_lt_sY : Lt (σ X) (σ Y) := (succ_lt_succ_iff X Y).mpr h_lt
      have h_Y_ne_0 : Y ≠ 𝟘 := by
        intro h; exact absurd (h ▸ h_pos) (lt_irrefl 𝟘)
      have h_lt_Y_addYY : Lt Y (add Y Y) := lt_self_add_r Y Y h_Y_ne_0
      exact lt_of_lt_of_le h_sX_lt_sY (lt_nm_then_le_nm_wp h_lt_Y_addYY)

    /- Teorema de crecimiento: ∃ n m, ∀ k ≥ 1, (n+k)^m < n^(m+k).

       Tomamos n=2, m=1. Verificación: (2+k)^1 = 2+k  y  2^(1+k) = 2·2^k.
       Prueba: 2+k < 2·2^k para k ≥ 1.
         Base k=1: 3 < 4.
         Paso k → k+1: 2+(k+1) = σ(2+k) < 2·2^k + 2·2^k = 2·2^(k+1)
           pues 2+k < 2·2^k (HI) y 2·2^k > 0. -/
    theorem exists_nm_growth :
        ∃ n m : ℕ₀, ∀ k : ℕ₀, Le 𝟙 k →
          Lt (pow (add n k) m) (pow n (add m k)) := by
      refine ⟨𝟚, 𝟙, fun k hk => ?_⟩  -- n = 2, m = 1
      rw [pow_add_split, pow_one, pow_one]
      -- Meta: Lt (add 𝟚 k) (mul 𝟚 (pow 𝟚 k))
      induction k with
      | zero => exact absurd hk (not_succ_le_zero 𝟘)
      | succ k' ih =>
        cases k' with
        | zero =>
          -- k = 1: Lt 3 (mul 𝟚 𝟚) = Lt 3 4
          rw [pow_succ, pow_zero, one_mul, mul_two]
          exact lt_succ_self (σ 𝟚)
        | succ k'' =>
          -- k = σ(σ k''), HI: Le 𝟙 (σ k'') → Lt (add 𝟚 (σ k'')) (mul 𝟚 (pow 𝟚 (σ k'')))
          have h_le_1_sk : Le 𝟙 (σ k'') := succ_le_succ_if_wp (zero_le k'')
          have ih_k := ih h_le_1_sk
          rw [add_succ, pow_succ, mul_two (pow 𝟚 (σ k'')), mul_add]
          -- Meta: Lt (σ(add 𝟚 (σ k''))) (add (mul 𝟚 (pow 𝟚 (σ k''))) (mul 𝟚 (pow 𝟚 (σ k''))))
          have h_pow_pos : Lt 𝟘 (pow 𝟚 (σ k'')) :=
            pow_gt (lt_trans 𝟘 𝟙 𝟚 (lt_succ_self 𝟘) (lt_succ_self 𝟙)) (zero_lt_succ k'')
          have h_Y_pos : Lt 𝟘 (mul 𝟚 (pow 𝟚 (σ k''))) :=
            mul_pos (lt_trans 𝟘 𝟙 𝟚 (lt_succ_self 𝟘) (lt_succ_self 𝟙)) h_pow_pos
          exact lt_add_double_of_lt_of_pos ih_k h_Y_pos

  end NewtonBinom
end Peano

export Peano.NewtonBinom (
  sum_binom_eq_pow_two
  binomTerm
  binomTerm_zero
  binomTerm_self
  newton_binom
  pow_add_split
  exists_nm_growth
)
