/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean
-- Teoremas de Sylow para grupos finitos.
--
-- § 1. p-subgrupos y p-subgrupos de Sylow
-- § 2. Primer teorema de Sylow (existencia)
-- § 3. Segundo teorema de Sylow (conjugación)
-- § 4. Tercer teorema de Sylow (número de p-subgrupos de Sylow)
--
-- Prerrequisitos:
--   * Cosets.lean (Lema de Lagrange)
--   * Action.lean (Teorema Órbita–Estabilizador, Ecuación de Clases)

import Peano.PeanoNat
import Peano.PeanoNat.Arith
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets
import Peano.PeanoNat.Combinatorics.GroupTheory.Action

set_option autoImplicit false

namespace Peano
  namespace GroupTheory

    open Peano.FSet
    open Peano.FSetFunction
    open Peano.Group
    open Peano.Arith

    /-!
    # § 1. p-subgrupos
    -/

    /-- `p` divide `|H|` en sentido ℕ₀: `∃ k, |H| = p · k`. -/
    def dvd_card (p : ℕ₀) (H : ℕ₀FSet) : Prop :=
      ∃ k : ℕ₀, Mul.mul p k = H.card

    /-- `p^k` divide `|H|`. -/
    def pow_dvd_card (p k : ℕ₀) (H : ℕ₀FSet) : Prop :=
      ∃ m : ℕ₀, Mul.mul (p ^ k) m = H.card

    /-- Un `p`-subgrupo de `G` es un subgrupo cuyo orden es una potencia de `p`. -/
    def isPSubgroup (G : FinGroup) (H : Subgroup G) (p : ℕ₀) : Prop :=
      ∃ k : ℕ₀, H.carrier.card = p ^ k

    /-- `p^n` es la mayor potencia de `p` que divide `|G|`
        (es decir, `p^n | |G|` pero `p^(n+1) ∤ |G|`). -/
    def isSylowExponent (G : FinGroup) (p n : ℕ₀) : Prop :=
      pow_dvd_card p n G.carrier ∧ ¬ pow_dvd_card p (σ n) G.carrier

    /-- Un subgrupo de Sylow `p` de `G` es un `p`-subgrupo de orden `p^n`
        donde `p^n` es la mayor potencia de `p` que divide `|G|`. -/
    def isSylowSubgroup (G : FinGroup) (H : Subgroup G) (p : ℕ₀) : Prop :=
      ∃ n, isSylowExponent G p n ∧ H.carrier.card = p ^ n

    /-!
    # § 2. Primer Teorema de Sylow (existencia)

    Si `p` es primo y `p^n | |G|`, entonces `G` tiene un subgrupo de orden `p^n`.
    En particular, `G` tiene un subgrupo de Sylow para cada primo `p | |G|`.
    -/

    /-- Paso 1 (Cauchy mínimo): si `p` primo divide `|G|`, existe
        un subgrupo de `G` de orden `p`. -/
    axiom cauchy_minimal_axiom (G : FinGroup) (p : ℕ₀)
        (hp : Prime p) (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :
        ∃ K : Subgroup G, K.carrier.card = p

    theorem cauchy_minimal (G : FinGroup) (p : ℕ₀)
        (hp : Prime p) (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :
        ∃ K : Subgroup G, K.carrier.card = p :=
      cauchy_minimal_axiom G p hp hdvd

    /-- Paso 2 (elevación inductiva): asumiendo Cauchy mínimo,
        construir subgrupos de orden `p^(m+1)` cuando `p^(m+1) | |G|`. -/
    theorem sylow_lift_from_cauchy
        (hC : ∀ (G0 : FinGroup) (p0 : ℕ₀), Prime p0 →
          (∃ t : ℕ₀, Mul.mul p0 t = G0.carrier.card) →
          ∃ K : Subgroup G0, K.carrier.card = p0)
        (G : FinGroup) (p m : ℕ₀)
        (hp : Prime p) (hpow : pow_dvd_card p (σ m) G.carrier) :
        ∃ H : Subgroup G, H.carrier.card = p ^ (σ m) := by
      have _ := hC
      have _ := hp
      have _ := hpow
      sorry

    /-- **Primer Teorema de Sylow**: existencia de p-subgrupos. -/
    theorem sylow_first (G : FinGroup) (p n : ℕ₀)
        (hp : Prime p)
        (hdvd : pow_dvd_card p n G.carrier) :
        ∃ H : Subgroup G, H.carrier.card = p ^ n := by
      cases n with
      | zero =>
          refine ⟨trivialSubgroup G, ?_⟩
          have hcard : (trivialSubgroup G).carrier.card = 𝟙 := by rfl
          have hpow : p ^ 𝟘 = 𝟙 := Peano.Pow.pow_zero p
          exact hcard.trans hpow.symm
      | succ n' =>
          exact sylow_lift_from_cauchy cauchy_minimal G p n' hp hdvd

    /-!
    # § 3. Segundo Teorema de Sylow (conjugación)

    Todos los subgrupos de Sylow `p` de `G` son conjugados entre sí.
    -/

    /-- **Segundo Teorema de Sylow**: conjugación de p-subgrupos. -/
    theorem sylow_second (G : FinGroup) (p : ℕ₀)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p) (hK : isSylowSubgroup G K p) :
        ∃ g, g ∈ G.carrier.elems ∧
          ∀ x, x ∈ K.carrier.elems ↔
            ∃ h, h ∈ H.carrier.elems ∧ G.op (G.op g h) (G.inv g) = x :=
      sorry  -- acción de H sobre G/K por multiplicación izquierda, conteo mod p

    /-!
    # § 4. Tercer Teorema de Sylow (número de subgrupos de Sylow)

    El número `n_p` de subgrupos de Sylow `p` satisface:
    - `n_p ≡ 1 (mod p)`
    - `n_p | [G : H]` donde `H` es cualquier subgrupo de Sylow `p`.
    -/

    /-- **Tercer Teorema de Sylow**: n_p ≡ 1 mod p y n_p | [G:H]. -/
    theorem sylow_third (G : FinGroup) (p : ℕ₀)
        (hp : Prime p)
        (sylows : List (Subgroup G))
        (h_all_sylow : ∀ H ∈ sylows, isSylowSubgroup G H p)
        (h_all_included : ∀ H : Subgroup G, isSylowSubgroup G H p → H ∈ sylows) :
        -- n_p ≡ 1 (mod p)
        (∃ k : ℕ₀, lengthₚ sylows = Peano.Add.add (Peano.Mul.mul p k) 𝟙) ∧
        -- n_p | |G|/p^n
        (∀ H ∈ sylows, ∃ k : ℕ₀, Mul.mul (lengthₚ sylows) k = G.carrier.card) :=
      sorry  -- acción por conjugación + Sylow II + conteo mod p

  end GroupTheory
end Peano
