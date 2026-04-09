/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Product.lean
-- Operador grande productorio: producto de listas y productorio finito sobre rangos.
--
-- § 1. Producto de listas (product_list)
-- § 2. Productorio finito (finProd): Π_{k=0}^{n} f(k)
-- § 3. Propiedades básicas del productorio
-- § 4. Productorio de factorización (product_factorization)

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.Mul
import Peano.PeanoNat.FSet
import Peano.PeanoNat.Combinatorics.Pow


namespace Peano
  open Peano

  namespace Product
    open Peano.Axioms
    open Peano.Mul

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Producto de listas (product_list)
    -- ══════════════════════════════════════════════════════════════════

    /- `product_list l` = Π de los elementos de la lista l.
       Identidad: 𝟙 (neutro de mul). -/
    def product_list : List ℕ₀ → ℕ₀
      | []       => 𝟙
      | p :: ps => mul p (product_list ps)

    @[simp] theorem product_nil : product_list [] = 𝟙 := rfl

    @[simp] theorem product_cons (p : ℕ₀) (ps : List ℕ₀) :
        product_list (p :: ps) = mul p (product_list ps) := rfl

    theorem product_append (l1 l2 : List ℕ₀) :
        product_list (l1 ++ l2) =
          mul (product_list l1) (product_list l2) := by
      induction l1 with
      | nil => simp [one_mul]
      | cons p ps ih => simp [ih, mul_assoc]

    theorem product_list_singleton (x : ℕ₀) :
        product_list [x] = x := by
      simp [mul_one]

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. Productorio finito (finProd): Π_{k=0}^{n} f(k)
    -- ══════════════════════════════════════════════════════════════════

    /- `finProd f n` = Π_{k=0}^{n} f(k).
       Computable. Terminado por recursión estructural en n. -/
    def finProd (f : ℕ₀ → ℕ₀) : ℕ₀ → ℕ₀
      | 𝟘   => f 𝟘
      | σ n => mul (finProd f n) (f (σ n))

    /- Notación: `∏ k ≤ n, f k` = finProd (fun k => f k) n = Π_{k=0}^{n} f(k). -/
    macro "∏ " k:ident " ≤ " n:term ", " f:term : term => `(finProd (fun $k => $f) $n)

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Propiedades básicas del productorio
    -- ══════════════════════════════════════════════════════════════════

    theorem finProd_zero (f : ℕ₀ → ℕ₀) : finProd f 𝟘 = f 𝟘 := by rfl

    theorem finProd_succ (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finProd f (σ n) = mul (finProd f n) (f (σ n)) := by rfl

    /- El productorio de la función uno es uno. -/
    theorem finProd_one_fn (n : ℕ₀) : finProd (fun _ => 𝟙) n = 𝟙 := by
      induction n with
      | zero    => rfl
      | succ n' ih => rw [finProd_succ, ih, mul_one]

    /- Si todos los factores son 𝟘, el productorio es 𝟘. -/
    theorem finProd_zero_fn (n : ℕ₀) : finProd (fun _ => 𝟘) n = 𝟘 := by
      induction n with
      | zero    => rfl
      | succ n' ih => rw [finProd_succ, ih, zero_mul]

    /- Desplazamiento a la izquierda:
       Π_{k=0}^{n+1} f(k) = f(0) · Π_{k=0}^{n} f(k+1). -/
    theorem finProd_succ_left (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
        finProd f (σ n) = mul (f 𝟘) (finProd (fun k => f (σ k)) n) := by
      induction n with
      | zero    => rfl
      | succ n' ih =>
          rw [finProd_succ, ih, finProd_succ, ← mul_assoc]

  end Product
end Peano

namespace Peano
  open Peano

  namespace Factorization
    open Peano.Axioms
    open Peano.Mul
    open Peano.Product
    open Peano.Pow
    open Peano.FSet

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Productorio de factorización (product_factorization)
    -- ══════════════════════════════════════════════════════════════════

    /-- El producto de una lista de ℕ₀ todos distintos de cero es distinto de cero. -/
    private theorem product_list_ne_zero {l : List ℕ₀}
        (h : ∀ x, x ∈ l → x ≠ 𝟘) :
        product_list l ≠ 𝟘 := by
      induction l with
      | nil => simp; exact succ_neq_zero 𝟘
      | cons a as ih =>
        simp
        exact eq_zero_of_mul_eq_zero
          (h a (List.mem_cons.mpr (Or.inl rfl)))
          (ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx))))

    open Peano.StrictOrder in
    /-- Calcula p^e como elemento de ℕ₂ a partir de un par (base ≥ 2, exponente ≥ 1).
        Es ℕ₂ porque p ≥ 2 y e ≥ 1 implican p^e ≥ 2. -/
    def factorValue (pe : ℕ₂ × ℕ₁) : ℕ₂ :=
      let p := pe.1        -- : ℕ₂
      let e := pe.2        -- : ℕ₁
      let val := pow p.val.val e.val   -- : ℕ₀
      -- val ≠ 𝟘
      have h_ne_zero : val ≠ 𝟘 := pow_ne_zero p.val.2 e.val
      -- Lt 𝟙 p.val.val  (p ≥ 2 → p.val.val > 1)
      have h_p_gt_1 : Lt 𝟙 p.val.val :=
        neq_01_then_gt_1 p.val.val ⟨p.val.2, p.2⟩
      -- e.val ≠ 𝟘  (e ≥ 1)
      have h_e_ne_zero : e.val ≠ 𝟘 := e.2
      -- Lt 𝟙 val
      have h_gt_1 : Lt 𝟙 val := one_lt_pow h_p_gt_1 h_e_ne_zero
      -- val ≠ 𝟙
      have h_ne_one : val ≠ σ 𝟘 := Ne.symm (ne_of_lt 𝟙 val h_gt_1)
      Subtype.mk (Subtype.mk val h_ne_zero) h_ne_one

    /-- El valor subyacente en ℕ₀ de factorValue. -/
    theorem factorValue_val (pe : ℕ₂ × ℕ₁) :
        (factorValue pe).val.val = pow pe.1.val.val pe.2.val :=
      rfl

    /-- Producto de una factorización: multiplica p₁^e₁ ⋅ p₂^e₂ ⋅ … ⋅ pₖ^eₖ.
        Devuelve un ℕ₁ (≥ 1): el producto vacío es 1, y factores ≥ 2 mantienen positividad. -/
    def product_factorization (s : FactFSet) : ℕ₁ :=
      let vals := List.map (fun pe => (factorValue pe).val.val) s.elems
      have h : product_list vals ≠ 𝟘 := by
        apply product_list_ne_zero
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨pe, _, rfl⟩ := hx
        exact (factorValue pe).val.2
      Subtype.mk (product_list vals) h

    /-- El valor subyacente en ℕ₀ de product_factorization. -/
    theorem product_factorization_val (s : FactFSet) :
        (product_factorization s).val =
          product_list (List.map (fun pe => (factorValue pe).val.val) s.elems) :=
      rfl

    theorem product_factorization_empty :
        (product_factorization FactFSet.empty).val = 𝟙 := by
      rfl

    theorem product_factorization_singleton (pe : ℕ₂ × ℕ₁) :
        (product_factorization (FactFSet.singleton pe)).val =
          pow pe.1.val.val pe.2.val := by
      show mul (pow pe.1.val.val pe.2.val) 𝟙 = pow pe.1.val.val pe.2.val
      exact mul_one _

  end Factorization
end Peano

export Peano.Product (
  product_list
  product_nil
  product_cons
  product_append
  product_list_singleton
  finProd
  finProd_zero
  finProd_succ
  finProd_one_fn
  finProd_zero_fn
  finProd_succ_left
)

export Peano.Factorization (
  factorValue
  product_factorization
  product_factorization_empty
  product_factorization_singleton
)
