# Desarrollo de Números Naturales de Peano (`Peano.lean`)

Este documento resume las definiciones y teoremas fundamentales implementados en los modulos principales del proyecto, con `Peano.lean` como punto de entrada. La biblioteca construye los naturales desde los axiomas de Peano, define subtipos como los naturales positivos, y establece propiedades de las relaciones de orden (`<`, `≤`) y operaciones aritmeticas basicas (`+`, `*`).

Desde la parte aritmetica adicional se incluye el modulo `PeanoNatLib/PeanoNatArith.lean`, que define divisibilidad, listas finitas de divisores y conjuntos inductivos de multiplos.

## Indice rapido

- [Desarrollo de Números Naturales de Peano (`Peano.lean`)](#desarrollo-de-números-naturales-de-peano-peanolean)
  - [Indice rapido](#indice-rapido)
  - [Modulos principales](#modulos-principales)
  - [1. Tipo Inductivo Base: `PeanoNat`](#1-tipo-inductivo-base-peanonat)
  - [4. Definiciones Booleanas y Proposicionales Auxiliares de Orden](#4-definiciones-booleanas-y-proposicionales-auxiliares-de-orden)
  - [5. Relación de Orden No Estricto: Le (≤)](#5-relación-de-orden-no-estricto-le-)
  - [6. Operaciones Aritméticas](#6-operaciones-aritméticas)
    - [6.1. Adición (add, +)](#61-adición-add-)
    - [6.2. Multiplicación (mul, \*)](#62-multiplicación-mul-)
  - [7. Otros Teoremas Notables](#7-otros-teoremas-notables)

## Modulos principales

- [Peano.lean](Peano.lean): punto de entrada y re-export de toda la biblioteca.
- [PeanoNatLib/PeanoNatLib.lean](PeanoNatLib/PeanoNatLib.lean): definiciones base (`ℕ₀`, `Λ`, `Ψ`, notaciones basicas).
- [PeanoNatLib/PeanoNatAxioms.lean](PeanoNatLib/PeanoNatAxioms.lean): axiomas y resultados estructurales de Peano.
- [PeanoNatLib/PeanoNatOrder.lean](PeanoNatLib/PeanoNatOrder.lean) y [PeanoNatLib/PeanoNatStrictOrder.lean](PeanoNatLib/PeanoNatStrictOrder.lean): orden no estricto y estricto.
- [PeanoNatLib/PeanoNatAdd.lean](PeanoNatLib/PeanoNatAdd.lean), [PeanoNatLib/PeanoNatMul.lean](PeanoNatLib/PeanoNatMul.lean), [PeanoNatLib/PeanoNatSub.lean](PeanoNatLib/PeanoNatSub.lean), [PeanoNatLib/PeanoNatDiv.lean](PeanoNatLib/PeanoNatDiv.lean): operaciones aritmeticas y propiedades.
- [PeanoNatLib/PeanoNatMaxMin.lean](PeanoNatLib/PeanoNatMaxMin.lean): maximos/minimos y lemas asociados.
- [PeanoNatLib/PeanoNatWellFounded.lean](PeanoNatLib/PeanoNatWellFounded.lean): herramientas de bien fundado y terminacion.
- [PeanoNatLib/PeanoNatArith.lean](PeanoNatLib/PeanoNatArith.lean): divisibilidad, divisores finitos y multiplos inductivos.

## 1. Tipo Inductivo Base: `PeanoNat`

Los números naturales, incluyendo el cero, se definen inductivamente:

```lean

inductive PeanoNat : Type where
  | zero : PeanoNat
  | succ : PeanoNat -> PeanoNat
  deriving Repr, DecidableEq

Dentro del namespace PeanoNat:

### 1.1. Definiciones Numéricas Básicas

def one : PeanoNat := succ zero
def two : PeanoNat := succ one
-- ... (hasta sixteen) ...

def pred (n : PeanoNat) : PeanoNat

### 1.2. Teoremas Fundamentales de PeanoNat y succ

@[simp] theorem pred_succ_eq_self (n : PeanoNat) : pred (succ n) = n
@[simp] theorem succ_neq_zero (m : PeanoNat) : succ m ≠ zero
theorem neq_succ (k : PeanoNat) : k ≠ succ k
theorem succ_uni_th : ∀ n m: PeanoNat, n = m → succ n = succ m
theorem succ_fun_th : ∀ n: PeanoNat, ∃ m: PeanoNat, m = succ n
theorem succ_inj_th : ∀ n m : PeanoNat, succ n = succ m → n = m
theorem succ_inj_neg_th : ∀ n m : PeanoNat, succ n ≠ succ m → n ≠ m
theorem neq_zero_then_succ (n : PeanoNat) : n ≠ zero → ∃ k, n = succ k
theorem full_induction (P : PeanoNat → Prop) (h_P_zero : P zero) (h_P_succ : ∀ n, P n → P (succ n)) (n_target : PeanoNat) : P n_target

### 1.3. Predicados is_zero e is_succ

def is_zero (n: PeanoNat): Prop := n = zero

instance is_zero_inst_decidable (n : PeanoNat) : Decidable (is_zero n)

def is_succ (n: PeanoNat): Prop := ∃ k, n = succ k

instance is_succ_inst_decidable (n : PeanoNat) : Decidable (is_succ n)

theorem no_confu (n: PeanoNat) : (is_zero n → ¬ is_succ n) ∧ (is_succ n → ¬ is_zero n)

## 2. Subtipos de PeanoNat

### 2.1. PosPeanoNat (Naturales Positivos)

Números naturales n tales que n ≠ zero.

def PosPeanoNat := { n : PeanoNat // n ≠ zero }

Definiciones en namespace PosPeanoNat:

def one : PosPeanoNat
def two : PosPeanoNat
def pred (p : PosPeanoNat) : PeanoNat
def succ (p : PosPeanoNat) : PosPeanoNat

### 2.2. FacPeanoNat (Naturales > 1)

Números positivos n tales que n ≠ PosPeanoNat.one.

def FacPeanoNat := { n : PosPeanoNat // n ≠ one }

Definiciones en namespace PosPeanoNat.FacPeanoNat:

theorem one_neq_two_prop : PosPeanoNat.one ≠ PosPeanoNat.two

def two : FacPeanoNat

## 3. Relación de Orden Estricto

Definición de `Lt` y notación:

```lean
def Lt (n m : PeanoNat) : Prop :=
  match n, m with
  | zero, zero       => False
  | zero, succ _     => True
  | succ _, zero     => False
  | succ n', succ m' => Lt n' m'

infix:50 "<" => Lt
instance lt_decidable : ∀ (n m : PeanoNat), Decidable (n < m)
```

Teoremas sobre Lt:

@[simp] theorem not_lt_zero_self : ¬ (zero < zero)
@[simp] theorem not_succ_lt_zero (n: PeanoNat): ¬(succ n < zero)
@[simp] theorem lt_zero_succ (m: PeanoNat): zero < succ m
theorem zero_is_the_minor (n: PeanoNat): n < zero → False
theorem lt_n_succ_n (n: PeanoNat): n < succ n
theorem lt_not_refl (n : PeanoNat) : ¬(n < n)
theorem lt_n_m_then_neq_n_m (n m: PeanoNat): n < m → n ≠ m
theorem trichotomy (n m : PeanoNat) : n < m ∨ n = m ∨ m < n
theorem lt_succ (n m : PeanoNat) : Lt n m → Lt n (succ m)
theorem lt_not_symm (n m: PeanoNat) : (n < m) → ¬(m < n)
theorem lt_trans {n m k : PeanoNat} (h1 : Lt n m) (h2 : Lt m k) : Lt n k
theorem lt_n_m_then_exists_k_eq_succ_k_m (n m: PeanoNat) :
  n < m → (succ n = m) ∨ (∃ k_ex: PeanoNat, n < k_ex ∧ succ k_ex = m)

## 4. Definiciones Booleanas y Proposicionales Auxiliares de Orden

```lean
def BTrichotomy (n m : PeanoNat) : Bool
def PropTrichotomy (n m : PeanoNat) : Prop
def BLe (n m : PeanoNat) : Bool
```

## 5. Relación de Orden No Estricto: Le (≤)

Definición de `Le` y notación:

```lean
def Le : PeanoNat -> PeanoNat -> Prop where
  | strict_lt {n m : PeanoNat} (h : Lt n m) : Le n m
  | refl_le {n : PeanoNat} : Le n n

infix:50 "<=" => Le
infix:50 "≤"  => Le

instance le_decidable : ∀ (n m : PeanoNat), Decidable (n <= m)
```

Teoremas sobre Le:

theorem le_zero_zero : Le zero zero
theorem le_if_eq (n m : PeanoNat) : n = m → Le n m
theorem le_if_lt (n m : PeanoNat) : n < m → Le n m
theorem le_succ (n m : PeanoNat) : Le n m → Le n (succ m) -- Nota: Este es Le n m → Le n (succ m), no Le (succ n) (succ m)
theorem ble_then_le (n m : PeanoNat) : (BLe n m = true) →  (n <= m)
theorem le_of_succ_le_succ {n m : PeanoNat} (h_succ_n_le_succ_m : Le (succ n) (succ m)) : Le n m
theorem le_then_ble (n m : PeanoNat) : (n <= m)  → (BLe n m = true)
theorem ble_iff_le (n m : PeanoNat) : (BLe n m = true) ↔ (n <= m)
theorem le_refl (n : PeanoNat) : Le n n
theorem le_succ_self (n : PeanoNat) : Le n (succ n)
theorem le_succ_succ (n m : PeanoNat) : Le n m → Le (succ n) (succ m) -- Este es el que usualmente se llama le_succ
theorem le_then_eq_xor_lt (n m : PeanoNat) : Le n m → n = m ∨ n < m
theorem le_trans {n m k : PeanoNat} (h1 : Le n m) (h2 : Le m k) : Le n k
theorem le_zero (n : PeanoNat) : Le zero n
theorem le_n_zero_eq_zero (n : PeanoNat) (h_n_le_zero : Le n zero) : n = zero
theorem le_antisymm {n m : PeanoNat} (h1 : Le n m) (h2 : Le m n) : n = m
theorem le_lt_succ (n m : PeanoNat) : Le n m → Lt n (succ m)
theorem lt_le_succ (n m : PeanoNat) : Lt n m → Le n m

## 6. Operaciones Aritméticas

### 6.1. Adición (add, +)

```lean
def add (n m : PeanoNat) : PeanoNat
infix:65 "+" => add -- Nota: el infix original era 50, la suma suele tener mayor precedencia
```

Teoremas sobre add:

theorem add_zero (n : PeanoNat) : add n zero = n
theorem zero_add (n : PeanoNat) : add zero n = n
theorem add_one (n : PeanoNat) : add n one = succ n
theorem one_add (n : PeanoNat) : add one n = succ n
theorem add_succ (n m : PeanoNat) : add n (succ m) = succ (add n m)
theorem succ_add (n m : PeanoNat) : add (succ n) m = succ (add n m)
theorem add_comm (n m : PeanoNat) : add n m = add m n
theorem add_assoc (n m k : PeanoNat) : add n (add m k) = add (add n m) k
theorem add_le (a b c : PeanoNat) : Le a b → Le a (add b c)
theorem add_lt (n m k : PeanoNat) : Lt n m → Lt n (add m k)
theorem add_cancelation (n m k : PeanoNat) : add n m = add n k → m = k
theorem cancelation_add (n m k : PeanoNat) : add m n = add k n → m = k
theorem add_lt_cancelation (n m k : PeanoNat) : add n m < add n k → m < k
theorem add_le_cancelation (n m k : PeanoNat) : Le (add n m) (add n k) → Le m k
theorem add_eq_zero_iff (a b : PeanoNat) : add a b = zero ↔ a = zero ∧ b = zero
theorem le_iff_exists_add (a b : PeanoNat) : Le a b ↔ ∃ p, b = add a p
theorem lt_iff_exists_add_succ (a b : PeanoNat) : Lt a b ↔ ∃ p, b = add a (succ p)

### 6.2. Multiplicación (mul, *)

```lean
def mul (n m : PeanoNat) : PeanoNat
infix:70 "*" => mul
```

Teoremas sobre mul:

theorem mul_zero (n : PeanoNat) : mul n zero = zero
theorem zero_mul (n : PeanoNat) : mul zero n = zero
theorem succ_mul (n m : PeanoNat) : mul (succ n) m = add (mul n m) m
theorem mul_succ (n m : PeanoNat) : mul n (succ m) = add (mul n m) n
theorem mul_one (n : PeanoNat) : mul n one = n
theorem one_mul (m : PeanoNat) : mul one m = m
theorem mul_two (n : PeanoNat): mul n two = add n n
theorem mul_comm (n m : PeanoNat) : mul n m = mul m n
theorem two_mul (m : PeanoNat) : mul two m = add m m
theorem mul_ldistr (m n k : PeanoNat) : mul m (add n k) = add (mul m n) (mul m k)
theorem mul_rdistr (m n k : PeanoNat) : mul (add m n) k = add (mul m k) (mul n k)
theorem mul_cancelation (n m k : PeanoNat) : n ≠ zero → (mul n m = mul n k → m = k)
theorem mul_assoc (n m k : PeanoNat) : mul (mul m n) k = mul m (mul n k) -- Nota: Este es mul (mul n m) k = mul n (mul m k)

## 7. Otros Teoremas Notables

def EqDef (f g : PeanoNat → PeanoNat) : Prop := ∀ x, f x = g x

theorem eq_of_eq_on_induct (f g : PeanoNat → PeanoNat)
    (h_conj : (f zero = g zero) ∧ (∀ n, f n = g n → f (succ n) = g (succ n))) : EqDef f g

theorem neq_then_lt (n m : PeanoNat) : n ≠ m → (n < m) ∨ (m < n)
theorem lt_then_neq (n m : PeanoNat) : n < m → n ≠ m -- Este es el mismo que lt_n_m_then_neq_n_m

theorem not_exists_maximum : ¬(∃ k : PeanoNat, ∀ m : PeanoNat, m < k)
