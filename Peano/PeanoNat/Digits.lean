/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Digits.lean
-- Representación de ℕ₀ en base b (b ≥ 2) como lista de dígitos.
--
-- § 1. Definiciones (digits, ofDigits, numDigits)
-- § 2. Propiedades básicas (digits_zero, ofDigits_nil, ofDigits_cons)
-- § 3. Round-trip (ofDigits_digits)
-- § 4. Cota de dígitos (digits_lt — incorporada en Fin₀)
-- § 5. Longitud y enlace con log
-- § 6. Exports

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Lists
import Peano.PeanoNat.Log
import Peano.PeanoNat.Combinatorics.Pow

set_option autoImplicit false

namespace Peano
  open Peano

  namespace Digits
    open Peano.Axioms
    open Peano.StrictOrder
    open Peano.Order
    open Peano.Add
    open Peano.Sub
    open Peano.Mul
    open Peano.Div
    open Peano.Lists
    open Peano.Log
    open Peano.Pow

    -- ══════════════════════════════════════════════════════════════════
    -- § 1. Definiciones
    -- ══════════════════════════════════════════════════════════════════

    -- Helper: extract b ≠ 0 and b > 1 from ℕ₂
    private theorem base_neq_zero (base : ℕ₂) : base.val.val ≠ 𝟘 :=
      base.val.property

    private theorem base_gt_one (base : ℕ₂) : Lt 𝟙 base.val.val := by
      have h_neq_0 := base.val.property
      have h_neq_1 : base.val.val ≠ 𝟙 := base.property
      exact lt_of_le_of_ne 𝟙 base.val.val
        (lt_0_then_le_1 base.val.val (neq_0_then_lt_0 h_neq_0))
        (Ne.symm h_neq_1)

    /-- Dígitos de `n` en base `b` (dígito menos significativo primero).
        Precondición: `b ≥ 2` (codificada como `ℕ₂`).
        Devuelve `List (Fin₀ b)` donde `b := base.val.val`.
        `digits base 𝟘 = []`. -/
    def digits (base : ℕ₂) (n : ℕ₀) : List (Fin₀ base.val.val) :=
      if h_n : n = 𝟘 then []
      else
        ⟨mod n base.val.val, mod_lt n base.val.val (base_neq_zero base)⟩ ::
          digits base (div n base.val.val)
    termination_by n
    decreasing_by exact div_lt_self n base.val.val (base_gt_one base) h_n

    /-- Reconstruye un número desde una lista de dígitos en base `b` (LSB primero). -/
    def ofDigits (b : ℕ₀) : List ℕ₀ → ℕ₀
      | [] => 𝟘
      | d :: ds => add d (mul b (ofDigits b ds))

    /-- Extrae los valores de una `List (Fin₀ b)` a `List ℕ₀`. -/
    def toValues {b : ℕ₀} : List (Fin₀ b) → List ℕ₀
      | [] => []
      | d :: ds => d.val :: toValues ds

    /-- Reconstruye un número desde una lista de `Fin₀ b`. -/
    def ofDigitsFin (b : ℕ₀) (ds : List (Fin₀ b)) : ℕ₀ :=
      ofDigits b (toValues ds)

    /-- Número de dígitos de `n` en base `b`. -/
    def numDigits (base : ℕ₂) (n : ℕ₀) : ℕ₀ :=
      Λ (digits base n).length

    -- ══════════════════════════════════════════════════════════════════
    -- § 2. Propiedades básicas
    -- ══════════════════════════════════════════════════════════════════

    @[simp] theorem digits_zero (base : ℕ₂) :
        digits base 𝟘 = [] := by
      unfold digits
      simp

    @[simp] theorem ofDigits_nil (b : ℕ₀) :
        ofDigits b [] = 𝟘 := rfl

    @[simp] theorem ofDigits_cons (b d : ℕ₀) (ds : List ℕ₀) :
        ofDigits b (d :: ds) = add d (mul b (ofDigits b ds)) := rfl

    @[simp] theorem toValues_nil {b : ℕ₀} :
        toValues ([] : List (Fin₀ b)) = [] := rfl

    @[simp] theorem toValues_cons {b : ℕ₀} (d : Fin₀ b) (ds : List (Fin₀ b)) :
        toValues (d :: ds) = d.val :: toValues ds := rfl

    @[simp] theorem numDigits_zero (base : ℕ₂) :
        numDigits base 𝟘 = 𝟘 := by
      unfold numDigits
      rw [digits_zero]
      rfl

    -- ══════════════════════════════════════════════════════════════════
    -- § 3. Round-trip: ofDigitsFin b (digits b n) = n
    -- ══════════════════════════════════════════════════════════════════

    private theorem ofDigits_toValues_digits (base : ℕ₂) (n : ℕ₀) :
        ofDigits base.val.val (toValues (digits base n)) = n := by
      induction n using well_founded_lt.induction with
      | h n ih =>
        if h_n : n = 𝟘 then
          rw [h_n, digits_zero, toValues_nil, ofDigits_nil]
        else
          have h_b_neq_0 := base_neq_zero base
          have h_div_lt := div_lt_self n base.val.val (base_gt_one base) h_n
          rw [digits.eq_def base n, dif_neg h_n, toValues_cons, ofDigits_cons]
          rw [ih (div n base.val.val) h_div_lt]
          rw [mul_comm base.val.val (div n base.val.val)]
          rw [add_comm (mod n base.val.val) (mul (div n base.val.val) base.val.val)]
          exact (divMod_spec n base.val.val h_b_neq_0).symm

    theorem ofDigitsFin_digits (base : ℕ₂) (n : ℕ₀) :
        ofDigitsFin base.val.val (digits base n) = n := by
      unfold ofDigitsFin
      exact ofDigits_toValues_digits base n

    -- ══════════════════════════════════════════════════════════════════
    -- § 4. Propiedades adicionales
    -- ══════════════════════════════════════════════════════════════════

    theorem digits_singleton_of_lt (base : ℕ₂) (n : ℕ₀) (h_n : n ≠ 𝟘) (h_lt : Lt n base.val.val) :
        digits base n = [⟨n, h_lt⟩] := by
      have h_div : div n base.val.val = 𝟘 := by
        have := div_of_lt n base.val.val h_lt; simp [div_def] at this; exact this
      have h_mod : mod n base.val.val = n := by
        have := mod_of_lt n base.val.val h_lt; simp [mod_def] at this; exact this
      rw [digits.eq_def base n, dif_neg h_n, h_div, digits_zero]
      congr 1
      exact Subtype.ext h_mod

  end Digits

end Peano

export Peano.Digits (
  digits
  ofDigits
  toValues
  ofDigitsFin
  numDigits
  digits_zero
  ofDigits_nil
  ofDigits_cons
  toValues_nil
  toValues_cons
  numDigits_zero
  ofDigitsFin_digits
  digits_singleton_of_lt
)
