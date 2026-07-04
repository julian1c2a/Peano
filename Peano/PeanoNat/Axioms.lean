/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatAxioms.lean

import Peano.PeanoNat

namespace Peano
    open Peano
    -- set_option trace.Meta.Tactic.simp true

  -- notation "σ" n:max => ℕ₀.succ n
  -- notation "𝟘" => ℕ₀.zero
  namespace Axioms
      open Axioms

  def isZero : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | .zero   => True
      | .succ _ => False

  def isSucc : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | .zero => False
      | .succ _ => True

  def returnBranch : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | .zero   => isZero n
      | .succ _ => isSucc n

  theorem noConfusion (n: ℕ₀) :
    (isZero n → ¬ isSucc n) ∧ (isSucc n → ¬ isZero n)
      := by
    constructor
    · intro h_isZero_n h_isSucc_n
      cases n with
      | zero =>
        unfold isSucc at h_isSucc_n
        contradiction
      | succ k =>
        unfold isZero at h_isZero_n
        contradiction
    · intro h_isSucc_n h_isZero_n
      cases n with
      | zero =>
        unfold isSucc at h_isSucc_n
        contradiction
      | succ k =>
        unfold isZero at h_isZero_n
        contradiction

  /--!
      EL SIGUIENTE AXIOMA SE DA POR QUE IS_ZERO INDICA
      QUE ES UNA RAMA DEL CONSTRUCTOR DE PEANONAT
     !-/
  theorem isNat_zero :
      isZero 𝟘 := by
        unfold isZero
        trivial


  /--!
      EL SIGUIENTE AXIOMA SE DA POR QUE IS_SUCC INDICA
      QUE ES UNA RAMA DEL CONSTRUCTOR DE PEANONAT
     !-/
  theorem isNat_succ(n : ℕ₀) :
      isSucc (σ n) := by
        unfold isSucc
        trivial


  /--!
  EL AXIOMA DE PEANO DE EXISTENCIA DEL CERO
  COMO NÚMERO NATURAL ESTÁ ASEGURADO POR LA CONSTRUCCIÓN
  DEL TIPO PEANONAT (BRAZO UNO DEL TIPO INDUCTIVO,
  EXPLÍCITO EN LA DEFINICIÓN DEL TIPO)


  --- TEOREMAS ACERCA DE LA FUNCIÓN SUCESOR Y LA CONSTANTE ZERO
  ---

  !-/

  theorem cero_neq_succ:
      ∀ (n : ℕ₀), 𝟘 ≠ σ n
        := by
          intro n -- Introducir n aquí
          cases n with
          | zero =>
              apply ℕ₀.noConfusion
          | succ n' =>
              apply ℕ₀.noConfusion

  theorem zero_ne_succ :
          ∀ (k : ℕ₀), 𝟘 ≠ σ k
              := by
                  intro k
                  intro h_eq_contra
                  exact ℕ₀.noConfusion h_eq_contra

  /--!
      ESTOS DOS TEOREMAS  QUE SE MUESTRAN A CONTINUACIÓN DICEN EL
      AXIOMA DE PEANO
          σ ES UNA FUNCIÓN EN EL SENTIDO MATEMÁTICO MODERNO.

      QUE UNA FUNCIÓN (PORQUE TODO SON FUNCIONES EN LEAN4) TENGA
      RETORNOS CONCRETOS PARA CADA ENTRADA (TENGA IMAGEN) ES UN
      TEOREMA EN LEAN4, HABRÍA QUE HACER EXPLÍCITAMENTE ALGUNA
      FUNCIÓN DE TIPO PARCIAL, NO TOTAL, PARA QUE NO OCURRIERA
      ASÍ
     !-/
  theorem succ_isNat:
      ∀ (n : ℕ₀), ∃ (k : ℕ₀), k = σ n
          := by
              intro n
              exists σ n

  /--!
      LA UNICIDAD EN LA IMAGEN DE LA FUNCIÓN SUCESIÓN ES UN TEOREMA
      PORQUE EN LEAN4 TODAS SON FUNCIONES DETERMINISTAS, Y POR LO
      TANTO SIEMPRE VAN A DAR EL MISMO RESULTADO CON ENTRADAS IGUALES
      (NO SE PUEDE HACER UNA FUNCIÓN QUE NO SEA DETERMINISTA)
     !-/
  theorem succ_congr(n m: ℕ₀) :
      n = m → σ n = σ m
          := by
              intro h_eq
              calc
                σ n = σ n   := by rfl
                _   = σ m   := by rw [h_eq]

  /--!
      ESTE TEOREMA QUE SE MUESTRAN A CONTINUACIÓN ES EL
      AXIOMA DE PEANO
          σ ES UNA FUNCIÓN INYECTIVA.

      POR LA FORMA DE LOS TIPOS INDUCTIVO NOS LEAN4 ASEGURA QUE LOS BRAZOS DEL MATCH SON VALORES DISTINTOS DEL TIPO, Y LAS FUNCIONES EN LOS BRAZOS SON INYECTIVAS PARA SEGUIR PRODUCIENDO VALORES DIFERENTES.
     !-/
  theorem succ_injective(n m : ℕ₀):
      σ n = σ m → n = m
          := by
              intro h_eq
              injection h_eq with h_n_eq_m

  def succ_inj(n m : ℕ₀) := succ_injective n m

  theorem succ_inj_wp {n m : ℕ₀} (h_neq: ¬ n = m) :
      σ n ≠ σ m
          := by
      intro h_eq
      exact absurd (succ_inj n m h_eq) h_neq

  theorem succ_inj_neg :
      ∀ n m : ℕ₀, σ n ≠ σ m → n ≠ m :=
          fun n m h_neq_succ h_eq =>
              have h_succ_eq : σ n = σ m
                  := congrArg ℕ₀.succ h_eq
              absurd h_succ_eq h_neq_succ

  theorem succ_inj_pos_wp {n m : ℕ₀} (h_succeq: σ n = σ m) :
      n = m
          := by
      exact succ_injective n m h_succeq

  /--!
      AXIOMA DE PEANO:
          0 NO ES SUCESOR DE NINGÚN NÚMERO NATURAL.

      EN LEAN4 ESTO VIENE DADO POR EL CONSTRUCTOR QUE TIENE LA PROPIEDAD NOCONFUSION
     !-/
  theorem succ_neq_zero (n : ℕ₀) :
      σ n ≠ 𝟘
          := by
              intro h_eq
              apply ℕ₀.noConfusion h_eq

  theorem AXIOM_zero_notin_ima_succ :
      ∀ (n : ℕ₀), 𝟘 ≠ σ n
          := by
              intro n
              symm
              apply succ_neq_zero

  /--!
      EL ÚLTIMO AXIOMA DE LA FUNCIÓN SUCESOR
      ES LA PROPIEDAD DE INDUCCIÓN SOBRE CUALQUIER
      PROPIEDAD P.
      EN LEAN4 ESTO VIENE DADO POR EL TIPO INDUCTIVO
      QUE TIENE LA PROPIEDAD NOCONFUSION
     !-/
  theorem induction_principle
      (P : ℕ₀ -> Prop)
      (h_0 : P 𝟘)
      (h_succ : ∀ n, P n → P (σ n)) :
      ∀ n, P n
          := by
              intro n
              induction n with
              | zero =>
                  exact h_0
              | succ k ih =>
                  exact h_succ k ih

  def BIs_zero : ℕ₀ -> Bool :=
    fun n =>
      match n with
      | .zero   => true
      | .succ _ => false

  def BIs_succ : ℕ₀ -> Bool :=
    fun n =>
      match n with
      | .zero   => false
      | .succ _ => true

  def category_by_constructor (n : ℕ₀) : ℕ₀ -> Prop :=
    match n with
    | .zero   => isZero
    | .succ _ => isSucc

  theorem neq_succ (k : ℕ₀) : k ≠ σ k := by
    induction k with
    | zero =>
      intro h_eq_zero_succ_zero
      exact succ_neq_zero 𝟘 h_eq_zero_succ_zero.symm
    | succ k' ih_k' =>
      intro h_eq_succ_k_succ_succ_k
      have h_k_eq_succ_k : k' = σ k' := succ_injective k' (σ k') h_eq_succ_k_succ_succ_k
      exact ih_k' h_k_eq_succ_k

  theorem isZero_or_isSucc (n : ℕ₀) :
      isZero n ∨ isSucc n
          := by
              cases n with
              | zero =>
                  unfold isZero
                  dsimp
                  unfold isSucc
                  dsimp
                  rw [true_or]
                  trivial
              | succ a =>
                  unfold isZero
                  dsimp
                  unfold isSucc
                  dsimp
                  rw [or_true]
                  trivial

  theorem isZero_xor_isSucc (n : ℕ₀) :
      (isZero n ∧ ¬isSucc n) ∨ (¬isZero n ∧ isSucc n)
          := by
              cases n with
              | zero =>
                  unfold isZero isSucc
                  dsimp
                  rw [not_false_eq_true]
                  rw [and_self]
                  rw [not_true_eq_false]
                  rw [and_self]
                  rw [or_false]
                  trivial
              | succ a =>
                  unfold isZero isSucc
                  dsimp
                  rw [not_true_eq_false]
                  rw [and_self]
                  rw [not_false_eq_true]
                  rw [and_self]
                  rw [or_true]
                  trivial

  theorem Λ_inj (n m : Nat) :
    Λ n = Λ m → n = m := by
      induction n generalizing m with
      | zero =>
        intro h_eq
        cases m with
        | zero =>
          rfl
        | succ m' =>
          exact ℕ₀.noConfusion h_eq
      | succ k ih =>
        intro h_eq
        cases m with
        | zero =>
          exact ℕ₀.noConfusion h_eq
        | succ m' =>
          injection h_eq with h_Λk_eq_Λm'
          have h_k_eq_m' : k = m' := ih m' h_Λk_eq_Λm'
          exact congrArg Nat.succ h_k_eq_m'

  theorem Ψ_inj (n m : ℕ₀) :
    (Ψ n) = (Ψ m) → n = m
      := by
      induction n generalizing m with
      | zero =>
        intro h_eq
        cases m with
        | zero =>
          rfl
        | succ m' =>
          exact Nat.noConfusion h_eq
      | succ k ih =>
        intro h_eq
        cases m with
        | zero =>
          exact Nat.noConfusion h_eq
        | succ m' =>
          injection h_eq with h_Ψk_eq_Ψm'
          have h_k_eq_m' : k = m' := ih m' h_Ψk_eq_Ψm'
          exact congrArg ℕ₀.succ h_k_eq_m'

  theorem Λ_surj (k : ℕ₀) :
    k = Λ (Ψ k)
    := by
        induction k with
        | zero =>
          calc
            𝟘 = 𝟘 := rfl
            _ = Λ (Ψ 𝟘) := rfl
        | succ k ih =>
          calc
            σ k = σ (Λ (Ψ k))       := congrArg ℕ₀.succ ih
            _   = Λ (Nat.succ (Ψ k))  := rfl
            _   = Λ (Ψ (σ k))       := rfl

  theorem Λ_bij (n m : Nat) (k : ℕ₀) :
    (Λ n = Λ m ↔ n = m) ∧ (k = Λ (Ψ k))
    := by
        constructor
        · -- Prueba de (Λ n = Λ m ↔ n = m)
          apply Iff.intro
          · -- Prueba de (Λ n = Λ m → n = m)
            intro h_eq
            apply Λ_inj
            exact h_eq
          · -- Prueba de (n = m → Λ n = Λ m)
            intro h_eq
            rw [h_eq]
        · -- Prueba de (k = Λ (Ψ k))
          apply Λ_surj

  theorem Ψ_surj (n : Nat) :
    n = Ψ (Λ n)
    := by
        induction n with
        | zero =>
          calc
            0 = 0 := by rfl
            _ = Ψ (Λ 0) := by rfl
        | succ k ih =>
          calc
            Nat.succ k = Nat.succ (Ψ (Λ k))
                := congrArg Nat.succ ih
            _          = Ψ (σ (Λ k))
                := by rfl
            _          = Ψ (Λ (Nat.succ k))
                := by rfl

  theorem Ψ_bij (n m : ℕ₀) (k : Nat) :
    (Ψ n = Ψ m ↔ n = m) ∧ (k = Ψ (Λ k))
    := by
        constructor
        · -- Prueba de (Ψ n = Ψ m ↔ n = m)
          apply Iff.intro
          · -- Prueba de (Ψ n = Ψ m → n = m)
            intro h_eq
            apply Ψ_inj
            exact h_eq
          · -- Prueba de (n = m → Ψ n = Ψ m)
            intro h_eq
            rw [h_eq]
        · -- Prueba de (k = Ψ (Λ k))
          apply Ψ_surj

  theorem comp_Λ_eq_Ψ :
    comp (Λ : Nat -> ℕ₀) (Ψ : ℕ₀ -> Nat)
        := by
        intro n
        induction n with
        | zero =>
          calc
            Ψ (Λ 0) = Ψ 𝟘 := by rfl
            _ = 0 := by rfl
        | succ k ih =>
          calc
            Ψ (Λ (Nat.succ k)) = Ψ (σ (Λ k)) := by rfl
            _ = Nat.succ (Ψ (Λ k)) := by rfl
            _ = Nat.succ k := by rw [ih]

  theorem comp_Ψ_eq_Λ :
    comp (Ψ : ℕ₀ -> Nat) (Λ : Nat -> ℕ₀)
        := by
        intro n
        induction n with
        | zero =>
          calc
            Λ (Ψ 𝟘) = Λ 0 := by rfl
            _ = 𝟘 := by rfl
        | succ k ih =>
          calc
            Λ (Ψ (σ k)) = σ (Λ (Ψ k)) := by rfl
            _ = σ k := by rw [ih]

  theorem eqFn_induction {α} (f : ℕ₀ -> α)(g : ℕ₀ -> α) :
    (
      (f 𝟘 = g 𝟘)
      ∧
      (
        ∀ (n: ℕ₀),
        (f n = g n) → (f (σ n) = g (σ n))
      )
    ) → (eqFn f g) := by
            intro h
            let h_0 := h.left
            let h_step := h.right
            intro n
            induction n with
            | zero =>
                exact h_0
            | succ k ih =>
                exact h_step k ih

  /--!
      LA SIGUIENTE ES UNA PRUEBA DE CONCEPTO (UN ENSAYO)
      DE COMO UTILIZAR EqFun Y EqFun_induction
     !-/
    theorem id_eq_id_lambda:
      eqFn id (λ (n : ℕ₀) => n)
          :=  by
              intro n
              rfl

  /--!
      LA IGUALDAD DE FUNCIONES ES UNA RELACIÓN DE EQUIVALENCIA
      (REFLEXIVA, SIMÉRICA Y TRANSITIVA)
     !-/
  theorem eqFn_refl {α} (f : ℕ₀ -> α) :
    eqFn f f := by
        intro n
        rfl

  theorem eqFn_symm {α} (f : ℕ₀ -> α)(g : ℕ₀ -> α) :
    eqFn f g → eqFn g f := by
        intro h n
        exact (h n).symm

  theorem eqFn_trans {α}
    (f : ℕ₀ -> α)
    (g : ℕ₀ -> α)
    (h : ℕ₀ -> α) :
    eqFn f g → eqFn g h → eqFn f h := by
        intro h_fg h_gh n
        exact (h_fg n).trans (h_gh n)

  /--! Dada la prueba que n ≠ 0, pred n = pred_checked n h_n_neq_0 -/
  theorem ρ_eq_τ
          (n : ℕ₀)
          (h_n_neq_0 : n ≠ 𝟘) :
      ρ n h_n_neq_0 = τ n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem τ_σ_eq_self (n : ℕ₀) :
      τ (σ n) = n
          := by
              unfold τ
              rfl

  theorem ρ_σ_eq_self
      (n : ℕ₀ )
      {h_succ_n_neq_0 : σ n ≠ 𝟘} :
      ρ (σ n) h_succ_n_neq_0 = n
          := by
              unfold ρ
              rfl

  theorem σ_ρ_eq_self(n: ℕ₀) (h_neq_0 : n ≠ 𝟘):
      σ (ρ n h_neq_0) = n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem τ_σ_eq_self_forall:
      ∀ (n : ℕ₀), τ (σ n) = n
              := by
                  intros n
                  unfold τ
                  rfl

  theorem σ_ρ_eq_id_pos_elem (n: ℕ₀) (n_neq_0: n ≠ 𝟘):
      σ (ρ n n_neq_0) = n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem σ_τ_eq_id_pos :
      ∀ (n : ℕ₀) (h : n ≠ 𝟘), σ (ρ n h) = n
          := by
              intros n h
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem σ_τ_eq_id_pos_forall {n : ℕ₀} (h : n ≠ 𝟘) :
      σ (ρ n h) = n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem ΨΛ (n: Nat) :
      Ψ (Λ n) = n
          := by
              induction n with
              | zero =>
                calc
                  Ψ (Λ Nat.zero) = Ψ 𝟘 := by rfl
                  _ = 0 := by rfl
              | succ k' ih =>
                unfold Λ Ψ
                dsimp
                rw [ih]

  theorem ΨΛ_eq_id :
      eqFnNat (Ψ ∘ Λ) idNat
          := by
              intro n
              exact ΨΛ   n

    theorem ΛΨ (n : ℕ₀) :
      Λ (Ψ n) = n
    := by
        induction n with
        | zero =>
          calc
            Λ (Ψ 𝟘) = Λ 0 := by rfl
            _ = 𝟘 := by rfl
        | succ k ih =>
          calc
            Λ (Ψ (σ k)) = σ (Λ (Ψ k)) := by rfl
            _ = σ k := by rw [ih]

    theorem Λψ_eq_id :
      eqFn (Λ ∘ Ψ) id
          := by
              intro n
              exact ΛΨ n

    theorem Ψ_σ_eq_σ_Λ (n : ℕ₀) :
      Ψ (σ n) = Nat.succ (Ψ n)
          := by
            induction n with
            | zero =>
              calc
                Ψ (σ 𝟘) = Ψ (σ 𝟘) := by rfl
                _ = Nat.succ (Ψ 𝟘) := by rfl
            | succ k' ih =>
              calc
                Ψ (σ (σ k')) = Ψ (σ (σ k')) := by rfl
                _ = Nat.succ (Ψ (σ k')) := by rfl
                _ = Nat.succ (Nat.succ (Ψ k')) := by rw [ih]

    theorem Ψ_σ_eq_σ_Λ_eqfn:
      eqFn ( Ψ ∘ ℕ₀.succ ) ( Nat.succ ∘ Ψ )
          := by
              intro n
              exact Ψ_σ_eq_σ_Λ n

    theorem Λ_σ_eq_σ_Ψ (n : Nat) :
      Λ (Nat.succ n) = σ (Λ n)
          := by
          induction n with
          | zero =>
            calc
              Λ (Nat.succ 0) = σ (Λ 0) := by rfl
          | succ k ih =>
            calc
              Λ (Nat.succ (Nat.succ k)) =
                  σ (Λ (Nat.succ k)) := by rfl
              _ = σ (σ (Λ k)) := by rw[ih]

        theorem Λ_σ_eq_σ_Ψ_eqfn:
          eqFnNat (Λ ∘ Nat.succ) (ℕ₀.succ ∘ Λ)
              := by
                  intro n
                  exact Λ_σ_eq_σ_Ψ n

        theorem Ψ_τ_eq_τ_Λ (n : ℕ₀) :
          Ψ (τ n) = Nat.pred (Ψ n)
              := by
                induction n with
                | zero =>
                  calc
                    Ψ (τ 𝟘) = Ψ (τ 𝟘) := by rfl
                    _ = Nat.pred (Ψ 𝟘) := by rfl
                | succ k' ih =>
                  calc
                    Ψ (τ (σ k')) = Ψ k'
                        := by simp only [τ_σ_eq_self]
                    _ = Nat.pred (Nat.succ (Ψ k'))
                        := by rw [Nat.pred_succ (Ψ k')]
                    _ = Nat.pred (Ψ (σ k'))
                        := by rw [Ψ_σ_eq_σ_Λ k']

        theorem Ψ_τ_eq_τ_Λ_eqfn:
          eqFn ( Ψ ∘ τ ) ( Nat.pred ∘ Ψ )
              := by
                  intro n
                  exact Ψ_τ_eq_τ_Λ n

        theorem Λ_τ_eq_τ_Ψ (n : Nat) :
          Λ (Nat.pred n) = τ (Λ n)
              := by
                induction n with
                | zero =>
                  calc
                    Λ (Nat.pred 0) = Λ (Nat.pred 0)
                        := by rfl
                    _ = τ 𝟘
                        := by rfl
                | succ k ih =>
                  calc
                    Λ (Nat.pred (Nat.succ k)) =
                        Λ k := by rfl
                    _ = τ (Λ (Nat.succ k))
                        := by
                            simp only [
                              Λ_σ_eq_σ_Ψ k,
                              τ_σ_eq_self
                            ]

  theorem isomorph_0_Λ : Λ 0 = 𝟘 := rfl
  theorem isomorph_0_Ψ : Ψ 𝟘 = 0 := rfl

  theorem isomorph_σ_Λ (n : Nat) :
    Λ (Nat.succ n) = σ (Λ n)
    := by
      rw [Λ_σ_eq_σ_Ψ n]

  theorem isomorph_σ_Ψ (n : ℕ₀) :
    Ψ (σ n) = Nat.succ (Ψ n)
    := by
      rw [Ψ_σ_eq_σ_Λ n]

  theorem isomorph_τ_Λ (n : Nat) :
    Λ (Nat.pred n) = τ (Λ n)
    := by
      rw [Λ_τ_eq_τ_Ψ n]

  theorem isomorph_τ_Ψ (n : ℕ₀) :
    Ψ (τ n) = Nat.pred (Ψ n)
    := by
      rw [Ψ_τ_eq_τ_Λ n]

  -- Lemas auxiliares para la preservación de ρ
  theorem Λ_eq_zero_iff_eq_zero (n : Nat) : Λ n = 𝟘 ↔ n = 0 := by
    constructor
    · intro h_Λn_eq_zero
      cases n with
      | zero => rfl
      | succ k =>
        exfalso
        exact succ_neq_zero (Λ k) (h_Λn_eq_zero ▸ Λ_σ_eq_σ_Ψ k)
    · intro h_n_eq_zero
      rw [h_n_eq_zero]
      rfl

  theorem Λ_neq_zero_iff_neq_zero (n : Nat) :
      Λ n ≠ 𝟘 ↔ n ≠ 0
          := by
              simp [Λ_eq_zero_iff_eq_zero]

  theorem Ψ_eq_zero_iff_eq_zero (n : ℕ₀) :
      Ψ n = 0 ↔ n = 𝟘
          := by
    constructor
    · intro h_Ψn_eq_zero
      cases n with
      | zero =>
        rfl
      | succ k =>
        exfalso
        exact Nat.noConfusion (h_Ψn_eq_zero ▸ Ψ_σ_eq_σ_Λ k)
    · intro h_n_eq_zero
      rw [h_n_eq_zero]
      rfl

  theorem Ψ_neq_zero_iff_neq_zero (n : ℕ₀) :
      Ψ n ≠ 0 ↔ n ≠ 𝟘
          := by
              simp [Ψ_eq_zero_iff_eq_zero]

  -- Teoremas de preservación para ρ
  theorem isomorph_ρ_Ψ (n : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) :
    Ψ (ρ n h_n_neq_0) = Nat.pred (Ψ n) := by
    rw [ρ_eq_τ n h_n_neq_0]
    exact Ψ_τ_eq_τ_Λ n

  theorem isomorph_Λ_ρ (n : Nat) (h_n_neq_0 : n ≠ 0) :
    ρ (Λ n) ((Λ_neq_zero_iff_neq_zero n).mpr h_n_neq_0) = Λ (Nat.pred n)
      := by
    rw [ρ_eq_τ (Λ n) ((Λ_neq_zero_iff_neq_zero n).mpr h_n_neq_0)]
    rw [← Λ_τ_eq_τ_Ψ n]

  theorem tau_eq_rho_if_ne_zero (k : ℕ₀) (hk_ne_zero : k ≠ 𝟘) :
    τ k = ρ k hk_ne_zero
      := by
      cases k with
      | zero => exfalso; exact hk_ne_zero rfl
      | succ k' => simp [τ, ρ]


  end Axioms
end Peano

export Peano.Axioms (
  Λ_inj Λ_surj Λ_bij
  Ψ_inj Ψ_surj Ψ_bij
  isZero
  isSucc
  returnBranch
  isNat_zero
  isNat_succ
  zero_ne_succ
  succ_isNat
  succ_congr
  succ_injective
  succ_inj_neg
  AXIOM_zero_notin_ima_succ
  induction_principle
  BIs_zero BIs_succ
  category_by_constructor
  neq_succ
  isZero_or_isSucc
  isZero_xor_isSucc
  eqFn_refl eqFn_symm eqFn_trans
  eqFn_induction
  comp_Λ_eq_Ψ comp_Ψ_eq_Λ
  id_eq_id_lambda
  τ_σ_eq_self
  σ_ρ_eq_self
  σ_τ_eq_id_pos
  σ_ρ_eq_id_pos_elem
  ΨΛ ΛΨ
  Ψ_σ_eq_σ_Λ
  Λ_σ_eq_σ_Ψ
  Ψ_τ_eq_τ_Λ
  Λ_τ_eq_τ_Ψ
  isomorph_0_Λ
  isomorph_0_Ψ
  isomorph_σ_Λ
  isomorph_σ_Ψ
  isomorph_τ_Λ
  isomorph_τ_Ψ
  isomorph_ρ_Ψ
  isomorph_Λ_ρ
  tau_eq_rho_if_ne_zero
  succ_inj_wp
  succ_inj_pos_wp
)
