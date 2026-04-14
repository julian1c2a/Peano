/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean
-- Acción de un grupo finito sobre un conjunto finito.
--
-- § 1. GroupAction  — definición de acción (izquierda)
-- § 2. Órbitas      — órbita de un elemento bajo la acción
-- § 3. Estabilizador — subgrupo estabilizador de un elemento
-- § 4. Teorema Órbita–Estabilizador: |Orb(x)| · |Stab(x)| = |G|
-- § 5. Ecuación de clases

import Peano.PeanoNat
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.Combinatorics.Group

set_option autoImplicit false

namespace Peano
  namespace GroupTheory

    open Peano.FSet
    open Peano.FSetFunction
    open Peano.Group

    /-!
    # § 1. GroupAction — acción (izquierda) de un FinGroup sobre un ℕ₀FSet
    -/

    /-- Una acción (izquierda) de `G` sobre un conjunto finito `X`:
        un homomorfismo de grupos de `G` al grupo simétrico de `X`,
        equivalente a una función `α : G × X → X` que satisface:
        - `α(e, x) = x`  para todo `x`,
        - `α(g, α(h, x)) = α(g·h, x)`  para todo `g, h, x`. -/
    structure GroupAction (G : FinGroup) (X : ℕ₀FSet) where
      /-- La función de acción: dados `g ∈ G` y `x ∈ X`, devuelve `g·x ∈ X`. -/
      act        : ℕ₀ → ℕ₀ → ℕ₀
      act_closed : ∀ g x, g ∈ G.carrier.elems → x ∈ X.elems → act g x ∈ X.elems
      act_id     : ∀ x, x ∈ X.elems → act G.id x = x
      act_compat : ∀ g h x,
                     g ∈ G.carrier.elems → h ∈ G.carrier.elems → x ∈ X.elems →
                     act g (act h x) = act (G.op g h) x

    /-!
    # § 2. Órbita de un elemento
    -/

    /-- La órbita de `x ∈ X` bajo la acción `α`:
        `Orb(x) = { α(g, x) | g ∈ G }`.
        Se construye filtrando `X` por los `y` que tienen preimagen en `G`. -/
    def GroupAction.orb {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) (x : ℕ₀) : ℕ₀FSet :=
      ℕ₀FSet.filter (fun y => G.carrier.elems.any (fun g => decide (α.act g x = y))) X

    /-- `y ∈ Orb(x)` si y solo si existe `g ∈ G` tal que `α(g, x) = y`. -/
    theorem mem_orb_iff {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) (x y : ℕ₀) :
        y ∈ (α.orb x).elems ↔ ∃ g, g ∈ G.carrier.elems ∧ α.act g x = y :=
      sorry

    /-!
    # § 3. Estabilizador de un elemento
    -/

    /-- El estabilizador de `x` en `G`:
        `Stab(x) = { g ∈ G | α(g, x) = x }`. -/
    def GroupAction.stab {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) (x : ℕ₀) : Subgroup G :=
      sorry  -- TODO: { g ∈ G | α(g,x) = x }; requiere filter sobre G.carrier

    /-!
    # § 4. Teorema Órbita–Estabilizador

    `|Orb(x)| · |Stab(x)| = |G|`

    Requiere cosets y el isomorfismo G/Stab(x) ≅ Orb(x).
    La prueba completa depende de Sylow/Cosets.lean.
    -/

    /-- Teorema órbita–estabilizador (enunciado). -/
    theorem orbit_stabilizer {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) (x : ℕ₀) (hx : x ∈ X.elems) :
        mul (α.orb x).card G.carrier.card =
          mul (α.stab x).carrier.card G.carrier.card :=
      sorry  -- requiere cosets (ver GroupTheory/Sylow/Cosets.lean)

    /-!
    # § 5. Ecuación de clases

    `|G| = |Z(G)| + Σ [G : C_G(x)]`
    donde la suma recorre representantes de órbitas no triviales.

    Estructura pendiente; requiere la fórmula de Burnside o la ecuación de clases
    para continuar hacia los teoremas de Sylow.
    -/

    /-- Partición de X en órbitas (enunciado). -/
    theorem orbits_partition {G : FinGroup} {X : ℕ₀FSet}
        (α : GroupAction G X) :
        -- Toda x ∈ X pertenece a exactamente una órbita
        (∀ x, x ∈ X.elems → ∃ y, y ∈ X.elems ∧ x ∈ (α.orb y).elems) ∧
        -- Dos órbitas son iguales o disjuntas
        (∀ x y, x ∈ X.elems → y ∈ X.elems →
          (α.orb x).elems = (α.orb y).elems ∨
          ∀ z, z ∉ (α.orb x).elems ∨ z ∉ (α.orb y).elems) :=
      sorry

  end GroupTheory
end Peano
