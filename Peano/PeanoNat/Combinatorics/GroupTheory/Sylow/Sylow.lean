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
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets
import Peano.PeanoNat.Combinatorics.GroupTheory.Action

set_option autoImplicit false

namespace Peano
  namespace GroupTheory

    open Peano.FSet
    open Peano.FSetFunction
    open Peano.Group

    /-!
    # § 1. p-subgrupos
    -/

    /-- `p` divide `|H|` en sentido ℕ₀: `∃ k, |H| = p · k`. -/
    def dvd_card (p : ℕ₀) (H : ℕ₀FSet) : Prop :=
      ∃ k : ℕ₀, Mul.mul p k = H.card

    /-- `p^k` divide `|H|`. -/
    def pow_dvd_card (p k : ℕ₀) (H : ℕ₀FSet) : Prop :=
      ∃ m : ℕ₀, Mul.mul (Pow.pow p k) m = H.card

    /-- Un `p`-subgrupo de `G` es un subgrupo cuyo orden es una potencia de `p`. -/
    def isPSubgroup (G : FinGroup) (H : Subgroup G) (p : ℕ₀) : Prop :=
      ∃ k : ℕ₀, H.carrier.card = Pow.pow p k

    /-- `p^n` es la mayor potencia de `p` que divide `|G|`
        (es decir, `p^n | |G|` pero `p^(n+1) ∤ |G|`). -/
    def isSylowExponent (G : FinGroup) (p n : ℕ₀) : Prop :=
      pow_dvd_card p n G.carrier ∧ ¬ pow_dvd_card p (Nat.succ n) G.carrier

    /-- Un subgrupo de Sylow `p` de `G` es un `p`-subgrupo de orden `p^n`
        donde `p^n` es la mayor potencia de `p` que divide `|G|`. -/
    def isSylowSubgroup (G : FinGroup) (H : Subgroup G) (p : ℕ₀) : Prop :=
      ∃ n, isSylowExponent G p n ∧ H.carrier.card = Pow.pow p n

    /-!
    # § 2. Primer Teorema de Sylow (existencia)

    Si `p` es primo y `p^n | |G|`, entonces `G` tiene un subgrupo de orden `p^n`.
    En particular, `G` tiene un subgrupo de Sylow para cada primo `p | |G|`.
    -/

    /-- **Primer Teorema de Sylow** (enunciado).
        Para cada primo `p` y cada `n` tal que `p^n | |G|`,
        existe un subgrupo `H ≤ G` con `|H| = p^n`. -/
    theorem sylow_first (G : FinGroup) (p n : ℕ₀)
        (hp : sorry)   -- p es primo
        (hdvd : pow_dvd_card p n G.carrier) :
        ∃ H : Subgroup G, H.carrier.card = Pow.pow p n :=
      sorry
      -- Prueba estándar: inducción sobre |G| usando la ecuación de clases.
      -- Caso base: |G| = 1 (trivial).
      -- Paso inductivo:
      --   si p | |Z(G)|: usar que Z(G) es abeliano y encontrar H ≤ Z(G) de orden p,
      --     luego inducción en G/H.
      --   si p ∤ |Z(G)|: la ecuación de clases da un centralizador C_G(x) con [G:C_G(x)] no div. p,
      --     luego inducción en C_G(x).

    /-!
    # § 3. Segundo Teorema de Sylow (conjugación)

    Todos los subgrupos de Sylow `p` de `G` son conjugados entre sí.
    -/

    /-- **Segundo Teorema de Sylow** (enunciado).
        Si `H` y `K` son subgrupos de Sylow `p` de `G`, entonces
        existe `g ∈ G` tal que `K = g H g⁻¹`. -/
    theorem sylow_second (G : FinGroup) (p : ℕ₀)
        (H K : Subgroup G)
        (hH : isSylowSubgroup G H p) (hK : isSylowSubgroup G K p) :
        ∃ g, g ∈ G.carrier.elems ∧
          ∀ x, x ∈ K.carrier.elems ↔
            ∃ h, h ∈ H.carrier.elems ∧ G.op (G.op g h) (G.inv g) = x :=
      sorry
      -- Prueba: hacer actuar H sobre G/K por multiplicación izquierda,
      -- contar órbitas módulo p; hay exactamente una órbita fija.

    /-!
    # § 4. Tercer Teorema de Sylow (número de subgrupos de Sylow)

    El número `n_p` de subgrupos de Sylow `p` satisface:
    - `n_p ≡ 1 (mod p)`
    - `n_p | [G : H]` donde `H` es cualquier subgrupo de Sylow `p`.
    -/

    /-- **Tercer Teorema de Sylow** (enunciado).
        El número de subgrupos de Sylow `p` es ≡ 1 mod p y divide a `[G:H]`. -/
    theorem sylow_third (G : FinGroup) (p : ℕ₀)
        (hp : sorry) -- p primo
        (sylows : List (Subgroup G))
        (h_all_sylow : ∀ H ∈ sylows, isSylowSubgroup G H p)
        (h_all_included : ∀ H : Subgroup G, isSylowSubgroup G H p → H ∈ sylows) :
        -- n_p ≡ 1 (mod p)
        (∃ k : ℕ₀, (sylows.length : ℕ₀) = Nat.add (Mul.mul p k) 1) ∧
        -- n_p | |G|/p^n
        (∀ H ∈ sylows, ∃ k : ℕ₀, Mul.mul (sylows.length : ℕ₀) k = G.carrier.card) :=
      sorry
      -- Prueba: hacer actuar G sobre el conjunto de subgrupos de Sylow por conjugación.
      -- Hay una sola órbita (Sylow II), luego n_p | |G|/p^n.
      -- Para n_p ≡ 1 mod p: hacer actuar H sobre el conjunto de subgrupos de Sylow;
      -- H es el único punto fijo.

  end GroupTheory
end Peano
