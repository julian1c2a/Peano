-- test_gcd1.lean
-- Ejemplos de uso de gcd₁ con ℕ₁ (números naturales positivos)

import Init.Classical
import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatDiv
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatArith

open Peano
open Peano.Axioms
open Peano.Order
open Peano.StrictOrder
open Peano.Add
open Peano.Sub
open Peano.Div
open Peano.MaxMin
open Peano.Mul
open Peano.Div
open Peano.Arith

-- Ejemplos de construcción de valores ℕ₁
def doce₁ : ℕ₁ := ⟨Λ 12, by decide⟩
def ocho₁ : ℕ₁ := ⟨Λ 8, by decide⟩
def cien₁ : ℕ₁ := ⟨Λ 100, by decide⟩
def treintaycinco₁ : ℕ₁ := ⟨Λ 35, by decide⟩
def cinco₁ : ℕ₁ := ⟨Λ 5, by decide⟩
def siete₁ : ℕ₁ := ⟨Λ 7, by decide⟩

-- Calcular gcd con ℕ₁
#eval Ψ (gcd₁ doce₁ ocho₁).val          -- Debería dar 4
#eval Ψ (gcd₁ cien₁ treintaycinco₁).val  -- Debería dar 5
#eval Ψ (gcd₁ siete₁ cinco₁).val         -- Debería dar 1 (coprimos)

-- Ejemplo de divisibilidad en ℕ₁
def cuatro₁ : ℕ₁ := ⟨Λ 4, by decide⟩

-- Verificar que 4 divide a 12
example : cuatro₁ ∣₁ doce₁ := by
  unfold Divides₁ Divides
  exact ⟨Λ 3, by decide⟩

-- Verificar reflexividad
example : doce₁ ∣₁ doce₁ := divides₁_refl doce₁

-- Comentarios sobre las ventajas de usar ℕ₁:
-- 1. No necesitamos manejar el caso especial de gcd(a, 0)
-- 2. El resultado siempre es un número positivo (ℕ₁)
-- 3. Las demostraciones pueden ser más simples sin el caso cero
-- 4. Es más natural para teoría de números donde típicamente trabajamos con enteros positivos
