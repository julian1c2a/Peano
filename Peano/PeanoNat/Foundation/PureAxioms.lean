/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Foundation/PureAxioms.lean
--
-- Declara el sistema de Peano puramente axiomático (6 private axiom de Lean 4)
-- y demuestra la paridad formal con ℕ₀:
--
--   pa_parity : ∃! f : PeanoMorphism ℕ₀_PeanoSystem PurePA, isPeanoIso ... f
--
-- Estrategia para derivar prim_rec de ind_pa (sin un 7º axioma):
--   1. Definir φ : ℕ₀ → ℕ₀_pa por recursión estructural en ℕ₀ (computable).
--   2. Demostrar que φ es biyectiva usando ind_pa.
--   3. Construir ψ : ℕ₀_pa → ℕ₀ como inversa clásica (no computable).
--   4. Derivar prim_rec transportando ℕ₀_rec a través de ψ.
--
-- Nombres exportados: PurePA, pa_parity.
-- Los 6 axiom y toda la maquinaria auxiliar son private.

import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.Prelim.Classical
import Peano.PeanoNat.Foundation.PeanoSystem
import Peano.PeanoNat.Foundation.Initiality

namespace Peano
  open Peano
  open Peano.Axioms

  namespace PureAxioms
    open PureAxioms
    open Peano.PeanoSystem
    open Peano.Initiality

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 1. Los seis axiomas de Peano como `private axiom` de Lean 4
  --
  -- Uso de `private`: los nombres ℕ₀_pa, zero_pa, … no son accesibles fuera
  -- de este archivo. El único punto de acceso externo es PurePA : PeanoSystem.
  -- Esto preserva la computabilidad del resto del proyecto: ningún otro módulo
  -- puede usar ℕ₀_pa directamente.
  -- ─────────────────────────────────────────────────────────────────────────

  /-- El tipo de los naturales puramente axiomático (sin reglas de cómputo). -/
  private axiom ℕ₀_pa : Type 0

  /-- El elemento cero. -/
  private axiom zero_pa : ℕ₀_pa

  /-- El sucesor. -/
  private axiom succ_pa : ℕ₀_pa → ℕ₀_pa

  /-- Axioma 4 de Peano: el sucesor es inyectivo. -/
  private axiom succ_inj_pa : ∀ m n : ℕ₀_pa, succ_pa m = succ_pa n → m = n

  /-- Axioma 3 de Peano: cero no es sucesor de ningún natural. -/
  private axiom zero_ne_succ_pa : ∀ n : ℕ₀_pa, zero_pa ≠ succ_pa n

  /-- Axioma de inducción: el principio de inducción matemática sobre ℕ₀_pa. -/
  private axiom ind_pa : ∀ P : ℕ₀_pa → Prop,
      P zero_pa → (∀ n, P n → P (succ_pa n)) → ∀ n, P n

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 2. El morfismo canónico φ : ℕ₀ → ℕ₀_pa
  --
  -- Computable: definido por recursión estructural en el tipo inductivo ℕ₀.
  -- No requiere ningún axioma adicional más allá del pattern matching de Lean.
  -- ─────────────────────────────────────────────────────────────────────────

  /-- El morfismo de álgebras ℕ₀ → ℕ₀_pa.
      Marcado `noncomputable` porque su codominio ℕ₀_pa es un `axiom` opaco.
      La función es estructuralmente computable (recursión en ℕ₀), pero el
      generador de código de Lean no puede compilar valores de tipo ℕ₀_pa. -/
  private noncomputable def φ : ℕ₀ → ℕ₀_pa
    | .zero   => zero_pa
    | .succ n => succ_pa (φ n)

  private theorem φ_zero : φ 𝟘 = zero_pa := rfl

  private theorem φ_succ (n : ℕ₀) : φ (σ n) = succ_pa (φ n) := rfl

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 3. φ es inyectiva
  -- ─────────────────────────────────────────────────────────────────────────

  private theorem φ_inj : ∀ m n : ℕ₀, φ m = φ n → m = n := by
    intro m
    induction m with
    | zero =>
      intro n heq
      cases n with
      | zero  => rfl
      | succ n' =>
        -- heq : zero_pa = succ_pa (φ n'), contradice zero_ne_succ_pa
        exact absurd heq (zero_ne_succ_pa (φ n'))
    | succ m' ih =>
      intro n heq
      cases n with
      | zero =>
        -- heq : succ_pa (φ m') = zero_pa, contradice zero_ne_succ_pa
        exact absurd heq.symm (zero_ne_succ_pa (φ m'))
      | succ n' =>
        -- heq : succ_pa (φ m') = succ_pa (φ n')
        -- Por succ_inj_pa: φ m' = φ n', luego por ih: m' = n'
        congr 1
        exact ih n' (succ_inj_pa _ _ heq)

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 4. φ es sobreyectiva  (por ind_pa)
  -- ─────────────────────────────────────────────────────────────────────────

  private theorem φ_surj (m : ℕ₀_pa) : ∃ n : ℕ₀, φ n = m :=
    ind_pa (fun m => ∃ n : ℕ₀, φ n = m)
      ⟨𝟘, rfl⟩
      (fun m' ⟨n, hn⟩ => ⟨σ n, show φ (σ n) = succ_pa m' by rw [φ_succ n, hn]⟩)
      m

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 5. La inversa ψ : ℕ₀_pa → ℕ₀   (no computable, por elección clásica)
  --
  -- Como φ es inyectiva y sobreyectiva, cada m : ℕ₀_pa tiene un único
  -- preimagen. Peano.choose selecciona ese preimagen de forma no computable.
  -- ─────────────────────────────────────────────────────────────────────────

  /-- Inversa derecha de φ, construida por elección clásica sobre la sobreyectividad. -/
  private noncomputable def ψ (m : ℕ₀_pa) : ℕ₀ :=
    Peano.choose (φ_surj m)

  /-- φ ∘ ψ = id : la especificación de la elección clásica. -/
  private theorem φ_ψ (m : ℕ₀_pa) : φ (ψ m) = m :=
    Peano.choose_spec (φ_surj m)

  /-- ψ preserva cero: ψ zero_pa = 𝟘. -/
  private theorem ψ_zero : ψ zero_pa = 𝟘 := by
    apply φ_inj
    -- Objetivo: φ (ψ zero_pa) = φ 𝟘
    rw [φ_ψ zero_pa]
    -- Objetivo: zero_pa = φ 𝟘   (= zero_pa por def. de φ)
    rfl

  /-- ψ preserva sucesor: ψ (succ_pa m) = σ (ψ m). -/
  private theorem ψ_succ (m : ℕ₀_pa) : ψ (succ_pa m) = σ (ψ m) := by
    apply φ_inj
    -- Objetivo: φ (ψ (succ_pa m)) = φ (σ (ψ m))
    rw [φ_ψ (succ_pa m)]
    -- Objetivo: succ_pa m = φ (σ (ψ m))
    rw [φ_succ (ψ m)]
    -- Objetivo: succ_pa m = succ_pa (φ (ψ m))
    rw [φ_ψ m]

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 6. Función de recursión local sobre ℕ₀
  --
  -- Redefinida localmente para evitar depender del `private` de Initiality.lean.
  -- Es la misma construcción que ℕ₀_rec_fn allí.
  -- ─────────────────────────────────────────────────────────────────────────

  /-- Función recursiva canónica sobre el tipo inductivo ℕ₀. -/
  private def ℕ₀_rec_aux {A : Type 0} (a : A) (f : A → A) : ℕ₀ → A
    | .zero   => a
    | .succ n => f (ℕ₀_rec_aux a f n)

  private theorem ℕ₀_rec_aux_zero {A : Type 0} (a : A) (f : A → A) :
      ℕ₀_rec_aux a f 𝟘 = a := rfl

  private theorem ℕ₀_rec_aux_succ {A : Type 0} (a : A) (f : A → A) (n : ℕ₀) :
      ℕ₀_rec_aux a f (σ n) = f (ℕ₀_rec_aux a f n) := rfl

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 7. Principio de recursión primitiva para ℕ₀_pa
  --
  -- Derivado sin axioma adicional: se transporta ℕ₀_rec_aux a través de ψ.
  --
  -- Existencia:  h := ℕ₀_rec_aux a f ∘ ψ  satisface las ecuaciones de recursión
  --              porque ψ preserva zero y succ  (§ 5) y ℕ₀_rec_aux las satisface
  --              en ℕ₀ por construcción.
  -- Unicidad:    cualquier dos soluciones coinciden por ind_pa punto a punto.
  -- ─────────────────────────────────────────────────────────────────────────

  private theorem pa_prim_rec {A : Type 0} (a : A) (f : A → A) :
      ExistsUnique (fun h : ℕ₀_pa → A => h zero_pa = a ∧ ∀ n, h (succ_pa n) = f (h n)) := by
    -- Función candidata
    let h : ℕ₀_pa → A := fun m => ℕ₀_rec_aux a f (ψ m)
    -- h preserva cero
    have h_zero : h zero_pa = a := by
      show ℕ₀_rec_aux a f (ψ zero_pa) = a
      rw [ψ_zero, ℕ₀_rec_aux_zero]
    -- h preserva sucesor
    have h_succ : ∀ n, h (succ_pa n) = f (h n) := fun n => by
      show ℕ₀_rec_aux a f (ψ (succ_pa n)) = f (ℕ₀_rec_aux a f (ψ n))
      rw [ψ_succ n, ℕ₀_rec_aux_succ]
    -- Existencia y unicidad
    refine ⟨h, ⟨h_zero, h_succ⟩, ?_⟩
    intro h' ⟨h'_zero, h'_succ⟩
    -- Cualquier solución h' coincide con h en todos los puntos (por ind_pa)
    funext m
    have key : ∀ n : ℕ₀_pa, h' n = h n :=
      ind_pa (fun n => h' n = h n)
        (h'_zero.trans h_zero.symm)
        (fun n ih => by
          show h' (succ_pa n) = h (succ_pa n)
          rw [h'_succ n, h_succ n, ih])
    exact key m

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 8. PurePA : PeanoSystem
  --
  -- Los seis axiom forman exactamente la estructura PeanoSystem.
  -- prim_rec no es un axioma adicional: se deriva de ind_pa (§ 7).
  -- ─────────────────────────────────────────────────────────────────────────

  /-- El sistema de Peano puramente axiomático.
      Marcado `noncomputable` porque sus campos usan axioms opacos (ℕ₀_pa, zero_pa, succ_pa).
      Toda su teoría (suma, multiplicación, primos, Sylow…) es derivable
      a través del isomorfismo `pa_parity`. -/
  noncomputable def PurePA : PeanoSystem where
    N        := ℕ₀_pa
    zero     := zero_pa
    succ     := succ_pa
    inj      := succ_inj_pa
    discr    := zero_ne_succ_pa
    ind      := ind_pa
    prim_rec := pa_prim_rec

  -- ─────────────────────────────────────────────────────────────────────────
  -- § 9. El teorema de paridad
  --
  -- Consecuencia inmediata de peano_unique (Initiality.lean).
  -- El isomorfismo canónico es:
  --   · ℕ₀ → ℕ₀_pa : n ↦ φ n  = ℕ₀_to PurePA n
  --   · ℕ₀_pa → ℕ₀ : m ↦ ψ m  = morph_fn PurePA ℕ₀_PeanoSystem m
  --
  -- Todo teorema demostrado sobre ℕ₀_PeanoSystem se transporta a PurePA
  -- y viceversa mediante este isomorfismo único.
  -- ─────────────────────────────────────────────────────────────────────────

  /-- **Paridad formal**: existe un único isomorfismo entre el tipo inductivo ℕ₀
      y el sistema axiomático puro ℕ₀_pa.

      Interpretación: los axiomas de Peano declarados con `axiom` de Lean 4 y
      el tipo inductivo `ℕ₀` son el mismo objeto matemático, distinguibles
      únicamente en su contenido computacional (ℕ₀ reduce; ℕ₀_pa no).

      Corolario implícito: ω (los naturales de von Neumann en ZFC) satisface
      los axiomas de Peano y es, por lo tanto, isomorfo a ℕ₀ mediante el mismo
      mecanismo — la cadena ω ≅ PurePA ≅ ℕ₀ es una instancia de peano_unique. -/
  theorem pa_parity :
      ExistsUnique (fun f : PeanoMorphism ℕ₀_PeanoSystem PurePA =>
        isPeanoIso ℕ₀_PeanoSystem PurePA f) :=
    peano_unique ℕ₀_PeanoSystem PurePA

  end PureAxioms

end Peano

export Peano.PureAxioms (
  PurePA
  pa_parity
)
