# Referencia Técnica — Proyecto Peano

**Última actualización:** 2026-04-20
**Autor**: Julián Calderón Almendros

> Documentación técnica de referencia para IA y desarrolladores Lean 4. **No** es documentación de usuario final.
> Contiene únicamente lo que está demostrado o construido en los archivos `.lean` (requisito 8).
> **Proyectar** un `.lean` en este archivo = actualizar las secciones correspondientes con todo lo exportable (no privado).

---

## 0. Estructura del Proyecto (requisitos 1–3)

### 0.1. Módulos `.lean`

> 52 build jobs · 2 sorry (Sylow.lean) · 0 errores · Lean 4 v4.29.0 · *Actualizado: 2026-04-23*

| Módulo (ruta) | Namespace | Depende de | Dependido por |
|---|---|---|---|
| `Peano.lean` | — | todos los módulos de `Peano/` | — |
| **Prelim** | | | |
| `Peano/Prelim.lean` | `Peano` | `Prelim/ExistsUnique`, `Prelim/Classical` | `PeanoNat` y todos los siguientes |
| `Peano/Prelim/ExistsUnique.lean` | `Peano` | — | `Prelim`, `Classical` |
| `Peano/Prelim/Classical.lean` | `Peano` | `ExistsUnique`, `Init.Classical` | `Prelim` |
| **Core aritmético** | | | |
| `Peano/PeanoNat.lean` | `Peano` | `Prelim` | todos los de `PeanoNat/` |
| `Peano/PeanoNat/Axioms.lean` | `Peano.Axioms` | `PeanoNat` | `StrictOrder` y descendientes |
| `Peano/PeanoNat/StrictOrder.lean` | `Peano.StrictOrder` | `PeanoNat`, `Axioms` | `Order` y descendientes |
| `Peano/PeanoNat/Order.lean` | `Peano.Order` | `…StrictOrder` | `Lattice` y descendientes |
| `Peano/PeanoNat/Tuple.lean` | `Peano` | `PeanoNat`, `StrictOrder` | — |
| `Peano/PeanoNat/Lattice.lean` | `Peano.Lattice` | `…Order` | `WellFounded` y descendientes |
| `Peano/PeanoNat/WellFounded.lean` | `Peano.WellFounded` | `…Lattice` | `Add` y descendientes |
| `Peano/PeanoNat/Add.lean` | `Peano.Add` | `…WellFounded` | `Sub` y descendientes |
| `Peano/PeanoNat/Sub.lean` | `Peano.Sub` | `…Add` | `Mul` y descendientes |
| `Peano/PeanoNat/Mul.lean` | `Peano.Mul` | `…Sub` | `Div` y descendientes |
| `Peano/PeanoNat/Div.lean` | `Peano.Div` | `…Mul` | `Arith`, `Pow` y descendientes |
| `Peano/PeanoNat/Arith.lean` | `Peano.Arith` | todos los anteriores | `Primes`, `NumberTheory/*` |
| `Peano/PeanoNat/Primes.lean` | `Peano.Primes` | `Arith` | `NumberTheory/*` |
| `Peano/PeanoNat/NumberSets.lean` | `Peano` | `PeanoNat` | — |
| `Peano/PeanoNat/Decidable.lean` | — (reexport) | `Order` | — |
| `Peano/PeanoNat/Isomorph.lean` | — (reexport) | `Arith` | — |
| **Representaciones** | | | |
| `Peano/PeanoNat/Digits.lean` | `Peano.Digits` | `Div`, `Pow`, `Log` | — |
| `Peano/PeanoNat/Log.lean` | `Peano.Log` | `Div`, `Pow` | `Digits` |
| `Peano/PeanoNat/Sqrt.lean` | `Peano.Sqrt` | `Mul`, `Sub`, `Pow` | — |
| `Peano/PeanoNat/Pairing.lean` | `Peano.Pairing` | `Div`, `Sqrt` | — |
| **Combinatoria** | | | |
| `Peano/PeanoNat/Combinatorics/Pow.lean` | `Peano.Pow` | `Mul`, `Div` | `NewtonBinom`, `Log`, `Sqrt`, `Digits` |
| `Peano/PeanoNat/Combinatorics/Factorial.lean` | `Peano.Factorial` | `Add`, `Mul` | `Binom`, `NewtonBinom` |
| `Peano/PeanoNat/Combinatorics/Binom.lean` | `Peano.Binom` | `Mul`, `Sub`, `Factorial` | `NewtonBinom` |
| `Peano/PeanoNat/Combinatorics/NewtonBinom.lean` | `Peano.NewtonBinom` | `Pow`, `Factorial`, `Binom`, `Summation` | — |
| `Peano/PeanoNat/Combinatorics/Summation.lean` | `Peano.Summation` | `Add`, `Mul` | `NewtonBinom`, `Product` |
| `Peano/PeanoNat/Combinatorics/Product.lean` | `Peano.Product` | `Mul`, `Summation` | `Totient` |
| `Peano/PeanoNat/Combinatorics/Fibonacci.lean` | `Peano.Fibonacci` | `Add` | — |
| `Peano/PeanoNat/Combinatorics/Counting.lean` | `Peano.Counting` | `FSet`, `Primes` | — |
| **Listas y conjuntos finitos** | | | |
| `Peano/PeanoNat/ListsAndSets/List.lean` | `Peano.List` | `PeanoNat` | `ListList`, `FSet` |
| `Peano/PeanoNat/ListsAndSets/ListList.lean` | `Peano.ListList` | `List` | — |
| `Peano/PeanoNat/ListsAndSets/FSet.lean` | `Peano.FSet` | `List`, `Add` | `FSetFSet`, `FSetFunction`, `Counting`, `Group` |
| `Peano/PeanoNat/ListsAndSets/FSetFSet.lean` | `Peano.FSetFSet` | `FSet` | — |
| `Peano/PeanoNat/ListsAndSets/FSetFunction.lean` | `Peano.FSetFunction` | `FSet`, `List`, `Mul` | `Perm`, `Group` |
| **Teoría de números** | | | |
| `Peano/PeanoNat/NumberTheory/ModEq.lean` | `Peano.ModEq` | `Arith`, `Primes` | `Totient`, `CRT`, `Fermat` |
| `Peano/PeanoNat/NumberTheory/Totient.lean` | `Peano.Totient` | `ModEq`, `Product`, `FSet` | `Fermat` |
| `Peano/PeanoNat/NumberTheory/ChineseRemainder.lean` | `Peano.CRT` | `ModEq`, `Arith` | — |
| `Peano/PeanoNat/NumberTheory/Fermat.lean` | `Peano.Fermat` | `ModEq`, `Totient`, `Primes` | — |
| **Teoría de grupos finitos** *(6 sorry)* | | | |
| `Peano/PeanoNat/Combinatorics/Perm.lean` | `Peano.Perm` | `FSetFunction` | `Group`, `Sign` |
| `Peano/PeanoNat/Combinatorics/Group.lean` | `Peano.Group` | `FSet`, `Perm` | `Orbit`, `Action` |
| `Peano/PeanoNat/Combinatorics/Sign.lean` | `Peano.Sign` | `Perm` | — |
| `Peano/PeanoNat/Combinatorics/Orbit.lean` | `Peano.Orbit` | `Group`, `FSet` | `Action` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean` | `Peano.Action` | `Group`, `Orbit` | `Cosets`, `Sylow` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean` | `Peano.Cosets` | `Action`, `Group` | `Sylow` |
| `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean` | `Peano.Sylow` | `Cosets`, `Action` | — |
| **Verificación** | | | |
| `Peano/ConstructiveCheck.lean` | — | `Prelim` | — |

### 0.2. Espacios de nombres y relaciones (requisito 3)

| Namespace | Módulo | Sub-namespace de |
|---|---|---|
| `Peano` | `Prelim.lean`, `PeanoNat.lean`, `Tuple`, `NumberSets` | — (raíz) |
| `Peano.Axioms` | `Axioms.lean` | `Peano` |
| `Peano.StrictOrder` | `StrictOrder.lean` | `Peano` |
| `Peano.Order` | `Order.lean` | `Peano` |
| `Peano.Lattice` | `Lattice.lean` | `Peano` |
| `Peano.WellFounded` | `WellFounded.lean` | `Peano` |
| `Peano.Add` | `Add.lean` | `Peano` |
| `Peano.Sub` | `Sub.lean` | `Peano` |
| `Peano.Mul` | `Mul.lean` | `Peano` |
| `Peano.Div` | `Div.lean` | `Peano` |
| `Peano.Arith` | `Arith.lean` | `Peano` |
| `Peano.Primes` | `Primes.lean` | `Peano` |
| `Peano.Digits` | `Digits.lean` | `Peano` |
| `Peano.Log` | `Log.lean` | `Peano` |
| `Peano.Sqrt` | `Sqrt.lean` | `Peano` |
| `Peano.Pairing` | `Pairing.lean` | `Peano` |
| `Peano.Pow` | `Combinatorics/Pow.lean` | `Peano` |
| `Peano.Factorial` | `Combinatorics/Factorial.lean` | `Peano` |
| `Peano.Binom` | `Combinatorics/Binom.lean` | `Peano` |
| `Peano.NewtonBinom` | `Combinatorics/NewtonBinom.lean` | `Peano` |
| `Peano.Summation` | `Combinatorics/Summation.lean` | `Peano` |
| `Peano.Product` | `Combinatorics/Product.lean` | `Peano` |
| `Peano.Fibonacci` | `Combinatorics/Fibonacci.lean` | `Peano` |
| `Peano.Counting` | `Combinatorics/Counting.lean` | `Peano` |
| `Peano.List` | `ListsAndSets/List.lean` | `Peano` |
| `Peano.ListList` | `ListsAndSets/ListList.lean` | `Peano` |
| `Peano.FSet` | `ListsAndSets/FSet.lean` | `Peano` |
| `Peano.FSetFSet` | `ListsAndSets/FSetFSet.lean` | `Peano` |
| `Peano.FSetFunction` | `ListsAndSets/FSetFunction.lean` | `Peano` |
| `Peano.ModEq` | `NumberTheory/ModEq.lean` | `Peano` |
| `Peano.Totient` | `NumberTheory/Totient.lean` | `Peano` |
| `Peano.CRT` | `NumberTheory/ChineseRemainder.lean` | `Peano` |
| `Peano.Fermat` | `NumberTheory/Fermat.lean` | `Peano` |
| `Peano.Perm` | `Combinatorics/Perm.lean` | `Peano` |
| `Peano.Group` | `Combinatorics/Group.lean` | `Peano` |
| `Peano.Sign` | `Combinatorics/Sign.lean` | `Peano` |
| `Peano.Orbit` | `Combinatorics/Orbit.lean` | `Peano` |
| `Peano.Action` | `GroupTheory/Action.lean` | `Peano` |
| `Peano.Cosets` | `GroupTheory/Sylow/Cosets.lean` | `Peano` |
| `Peano.Sylow` | `GroupTheory/Sylow/Sylow.lean` | `Peano` |

### 0.3. Notaciones registradas (requisito 4.4)

| Símbolo | Tipo | Prioridad | Namespace | Módulo |
|---|---|---|---|---|
| `σ n` | prefijo | `max` | `Peano` | `PeanoNat.lean` |
| `𝟘` | constante | — | `Peano` | `PeanoNat.lean` |
| `𝟙` | constante | — | `Peano` | `PeanoNat.lean` |
| `𝟚` | constante | — | `Peano` | `PeanoNat.lean` |
| `𝟛` | constante | — | `Peano` | `PeanoNat.lean` |
| `∃¹ x, p x` | macro cuantificador (4 variantes) | — | `Peano` | `Prelim.lean` |
| `⟨⟩` | tupla vacía | — | `Peano` | `PeanoNat.lean` |
| `⟨x⟩` | tupla singleton | — | `Peano` | `PeanoNat.lean` |
| `n + m` | infijo, instancia `Add ℕ₀` | ~65 | `Peano.Add` | `Add.lean` |
| `a +l b` | infijo | — | `Peano.Add` | `Add.lean` |
| `n - m` | infijo | 65 | `Peano.Sub` | `Sub.lean` |
| `n -( h ) m` | notación con prueba | 65 | `Peano.Sub` | `Sub.lean` |
| `n * m` | infijo | 70 | `Peano.Mul` | `Mul.lean` |
| `a / b` | instancia `Div ℕ₀` | — | `Peano.Div` | `Div.lean` |
| `a % b` | instancia `Mod ℕ₀` | — | `Peano.Div` | `Div.lean` |
| `n < m` | instancia `LT ℕ₀` | — | `Peano.StrictOrder` | `StrictOrder.lean` |
| `n ≤ m` | instancia `LE ℕ₀` | — | `Peano.Order` | `Order.lean` |
| `a ∣ b` | infijo | 50 | `Peano.Arith` | `Arith.lean` |
| `a ∤ b` | notación negación | 50 | `Peano.Arith` | `Arith.lean` |
| `a ∣₁ b` | infijo | 50 | `Peano.Arith` | `Arith.lean` |
| `n ^ m` | infijo | 80 | `Peano.Pow` | `Combinatorics/Pow.lean` |
| `C(n, k)` | notación combinatoria | — | `Peano.Binom` | `Combinatorics/Binom.lean` |
| `∑ k ≤ n, f` | macro sumatorio | — | `Peano.Summation` | `Combinatorics/Summation.lean` |
| `a ≡ b [MOD n]` | notación congruencia | 50 | `Peano.ModEq` | `NumberTheory/ModEq.lean` |
| `{[a, b, c]}` | macro FSet literal | — | `Peano.FSet` | `ListsAndSets/FSet.lean` |
| `{[x \| p]}` | macro FSet comprensión | — | `Peano.FSet` | `ListsAndSets/FSet.lean` |

---

## 1. Prelim.lean — `namespace Peano`

*Dependencias: `Init.Classical`*

Infraestructura compartida: existencia única y operador de elección clásica. No depende de `ℕ₀`.

### 1.1. Definiciones

**[D1.1]** `ExistsUnique`

- **Lean4:** `def ExistsUnique {α : Type} (p : α → Prop) : Prop := ∃ x, (p x ∧ ∀ y, p y → y = x)`
- **Matemática:** ∃¹x ∈ α, p(x)  ⟺  ∃x, (p(x) ∧ ∀y, p(y) ⇒ y = x)
- **Computable:** No (Prop)
- **Notación:** `∃¹ x, p x` | `∃¹ (x), p x` | `∃¹ (x : T), p x` | `∃¹ x : T, p x` — macro, 4 variantes

**[D1.2]** `choose` (elección clásica)

- **Lean4:** `noncomputable def choose {α : Type} {p : α → Prop} (h : ∃ x, p x) : α`
- **Matemática:** Operador ε: dado ∃x, p(x), elige un testigo
- **Computable:** No (noncomputable; usa `Classical.indefiniteDescription`)
- **Dependencias:** `Init.Classical`

**[D1.3]** `ExistsUnique.exists`

- **Lean4:** `def ExistsUnique.exists {α : Type} {p : α → Prop} (h : ExistsUnique p) : ∃ x, p x`
- **Computable:** Sí

**[D1.4]** `choose_unique`

- **Lean4:** `noncomputable def choose_unique {α : Type} {p : α → Prop} (h : ExistsUnique p) : α`
- **Matemática:** Elección del único testigo de ∃¹x, p(x)
- **Computable:** No
- **Dependencias:** `choose`, `ExistsUnique.exists`

### 1.2. Teoremas

**[T1.1]** `choose_spec`

- **Lean4:** `theorem choose_spec {α : Type} {p : α → Prop} (h : ∃ x, p x) : p (choose h)`
- **Matemática:** p(ε x, p(x))
- **Dependencias:** `choose`

**[T1.2]** `choose_spec_unique`

- **Lean4:** `theorem choose_spec_unique {α : Type} {p : α → Prop} (h : ExistsUnique p) : p (choose_unique h)`
- **Matemática:** El único testigo elegido satisface p
- **Dependencias:** `choose_unique`, `choose_spec`

**[T1.3]** `choose_uniq`

- **Lean4:** `theorem choose_uniq {α : Type} {p : α → Prop} (h : ExistsUnique p) {y : α} (hy : p y) : y = choose_unique h`
- **Matemática:** p(y) ⇒ y = choose_unique(h)
- **Dependencias:** `choose_unique`, `choose_spec_unique`, `ExistsUnique`

---

## 2. PeanoNat.lean — `namespace Peano`

*Dependencias: `Prelim`*

Tipo inductivo básico `ℕ₀`, subtipos, isomorfismo con `Nat`, tuplas.

### 2.1. Definiciones

**[D2.1]** `ℕ₀`

- **Lean4:**

  ```
  inductive ℕ₀ : Type
    | zero : ℕ₀
    | succ : ℕ₀ → ℕ₀
    deriving Repr, BEq, DecidableEq
  ```

- **Matemática:** Tipo inductivo libre con constructores 0 y σ: ℕ₀ → ℕ₀
- **Computable:** Sí
- **Notación:** `𝟘` → `ℕ₀.zero`; `σ n` → `ℕ₀.succ n` (prefijo, prioridad `max`)

**[D2.2]** `ℕ₁`

- **Lean4:** `def ℕ₁ : Type := {n : ℕ₀ // n ≠ ℕ₀.zero}`
- **Matemática:** ℕ₁ = {n ∈ ℕ₀ | n ≠ 0}
- **Computable:** Sí

**[D2.3]** `ℕ₂`

- **Lean4:** `def ℕ₂ : Type := {n : ℕ₁ // n.val ≠ ℕ₀.succ ℕ₀.zero}`
- **Matemática:** ℕ₂ = {n ∈ ℕ₁ | n ≠ 1}
- **Computable:** Sí

**[D2.4]** Constantes numéricas

- **Lean4:**

  ```
  def cero  : ℕ₀ := ℕ₀.zero    -- notación: 𝟘
  def one   : ℕ₀ := σ 𝟘         -- notación: 𝟙
  def two   : ℕ₀ := σ one       -- notación: 𝟚
  def three : ℕ₀ := σ two       -- notación: 𝟛
  ```

- **Matemática:** 0, 1 = σ(0), 2 = σ(1), 3 = σ(2)
- **Computable:** Sí

**[D2.5]** Funciones auxiliares de igualdad funcional

- **Lean4:**

  ```
  def idℕ₀   (n : ℕ₀) : ℕ₀
  def idNat  (n : Nat) : Nat
  def eqFnGen {α β} (f g : α → β)       : Prop  -- ∀ x, f x = g x
  def comp    {α β} (f : α→β) (g : β→α) : Prop  -- ∀ x, g(f x) = x
  def eqFn    {α}   (f g : ℕ₀ → α)      : Prop
  def eqFn2   {α}   (f g : ℕ₀×ℕ₀ → α)   : Prop
  def eqFnNat {α}   (f g : Nat → α)     : Prop
  ```

- **Computable:** Sí (identidades y definiciones proposicionales)

**[D2.6]** `Λ` y `Ψ` (isomorfismo con `Nat`)

- **Lean4:**

  ```
  def Λ (n : Nat) : ℕ₀   -- Nat.zero ↦ 𝟘, Nat.succ k ↦ σ(Λ k)
  def Ψ (n : ℕ₀)  : Nat   -- ℕ₀.zero ↦ 0, ℕ₀.succ k ↦ Nat.succ (Ψ k)
  ```

- **Matemática:** Λ: ℕ → ℕ₀, Ψ: ℕ₀ → ℕ; isomorfismo de semiestructuras
- **Computable:** Sí (ambos)

**[D2.7]** `τ` (predecesor truncado)

- **Lean4:**

  ```
  def τ (n : ℕ₀) : ℕ₀ :=
    match n with
    | ℕ₀.zero => 𝟘
    | ℕ₀.succ k => k
  ```

- **Matemática:** τ(0) = 0; τ(σ n) = n  (predecesor truncado)
- **Computable:** Sí

**[D2.8]** `ρ` (predecesor verificado)

- **Lean4:**

  ```
  def ρ (n : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) : ℕ₀ :=
    match n with
    | ℕ₀.zero => False.elim (h_n_neq_0 rfl)
    | ℕ₀.succ k => k
  ```

- **Matemática:** ρ(n, n≠0) = predecesor de n (con prueba n ≠ 0)
- **Computable:** Sí

### 2.2. Instancias

- `Coe Nat ℕ₀` (coerción vía `Λ`)

---

## 2.bis. Tuple.lean — `namespace Peano`

*Dependencias: `PeanoNat`, `StrictOrder`*

Tuplas de naturales de Peano de longitud finita.

### 2.bis.1. Definiciones

**[D2b.1]** `Tuple` (tuplas de dimensión finita)

- **Lean4:**

  ```
  def Tuple : ℕ₀ → Type
    | 𝟘 => Unit
    | σ n => ℕ₀ × Tuple n
  ```

- **Matemática:** Tuple(0) = Unit; Tuple(σ n) = ℕ₀ × Tuple(n)
- **Computable:** Sí

**[D2b.2]** Operaciones sobre tuplas

- **Lean4:**

  ```
  def emptyTuple : Tuple 𝟘 := ()
  def consTuple {n : ℕ₀} (x : ℕ₀) (xs : Tuple n) : Tuple (σ n) := (x, xs)
  def headTuple {n : ℕ₀} (t : Tuple (σ n)) : ℕ₀ := t.1
  def tailTuple {n : ℕ₀} (t : Tuple (σ n)) : Tuple n := t.2
  def mkTuple : (n : ℕ₀) → (f : ℕ₀ → ℕ₀) → Tuple n
  ```

- **Matemática:** Constructor vacío, cons, proyecciones cabeza/cola, construcción desde función
- **Computable:** Sí

**[D2b.3]** Orden lexicográfico

- **Lean4:**

  ```
  def lexLt {n : ℕ₀} : Tuple n → Tuple n → Prop
  def lexLe {n : ℕ₀} : Tuple n → Tuple n → Prop
  ```

- **Matemática:** Orden lexicográfico estricto y no estricto.
- **Computable:** No (Prop).

### 2.bis.2. Instancias

- `tupleDecEq : (n : ℕ₀) → DecidableEq (Tuple n)`
- `tupleRepr : (n : ℕ₀) → Repr (Tuple n)`
- `instLTTuple {n : ℕ₀} : LT (Tuple n)`
- `instLETuple {n : ℕ₀} : LE (Tuple n)`
- `instDecidableRelLtTuple {n : ℕ₀} : DecidableRel (@lexLt n)`
- `instDecidableRelLeTuple {n : ℕ₀} : DecidableRel (@lexLe n)`

### 2.bis.3. Notaciones

| Símbolo | Expansión |
|---|---|
| `⟨⟩` | `emptyTuple` |
| `⟨x⟩` | `consTuple x emptyTuple` |

---

## 3. Axioms.lean — `namespace Peano.Axioms`

*Dependencias: `PeanoNat`*

Los axiomas de Peano se demuestran como teoremas a partir de la estructura inductiva de `ℕ₀`.

### 3.1. Definiciones auxiliares

**[D3.1]** `isZero`, `isSucc`, `returnBranch`

- **Lean4:**

  ```
  def isZero      : ℕ₀ → Prop   -- True iff n = 𝟘
  def isSucc      : ℕ₀ → Prop   -- True iff ∃k, n = σ k
  def returnBranch : ℕ₀ → Prop   -- isZero | isSucc según constructor
  ```

- **Computable:** No (Prop)

**[D3.2]** `succ_inj` (alias)

- **Lean4:** `def succ_inj (n m : ℕ₀) := succ_injective n m`
- **Computable:** No (Prop → Prop)

**[D3.3]** `BIs_zero`, `BIs_succ` (contrapartes booleanas)

- **Lean4:**

  ```
  def BIs_zero : ℕ₀ → Bool
  def BIs_succ : ℕ₀ → Bool
  ```

- **Computable:** Sí

**[D3.4]** `category_by_constructor`

- **Lean4:** `def category_by_constructor (n : ℕ₀) : ℕ₀ → Prop`
- **Computable:** No (Prop)

### 3.2. Axiomas (demostrados como teoremas)

**[A1]** `isNat_zero`

- **Lean4:** `theorem isNat_zero : isZero 𝟘`
- **Matemática:** isZero(0)

**[A2]** `isNat_succ`

- **Lean4:** `theorem isNat_succ (n : ℕ₀) : isSucc (σ n)`
- **Matemática:** ∀n ∈ ℕ₀, isSucc(σ n)

**[A3]** `cero_neq_succ` / `zero_ne_succ`

- **Lean4:** `theorem cero_neq_succ (n : ℕ₀) : 𝟘 ≠ σ n`
- **Lean4:** `theorem zero_ne_succ : ∀ (n : ℕ₀), 𝟘 ≠ σ n`
- **Matemática:** ∀n ∈ ℕ₀, 0 ≠ σ(n)

**[A4]** `AXIOM_zero_notin_ima_succ`

- **Lean4:** `theorem AXIOM_zero_notin_ima_succ : ∀ (n : ℕ₀), 𝟘 ≠ σ n`
- **Matemática:** 0 ∉ Im(σ)

**[A5]** `succ_isNat`

- **Lean4:** `theorem succ_isNat : ∀ (n : ℕ₀), ∃ (k : ℕ₀), k = σ n`
- **Matemática:** ∀n ∈ ℕ₀, ∃k ∈ ℕ₀, k = σ(n)

**[A6]** `succ_congr`

- **Lean4:** `theorem succ_congr (n m : ℕ₀) : n = m → σ n = σ m`
- **Matemática:** n = m ⇒ σ(n) = σ(m)  (univocidad de σ)

**[A7]** `succ_injective`

- **Lean4:** `theorem succ_injective (n m : ℕ₀) : σ n = σ m → n = m`
- **Matemática:** σ(n) = σ(m) ⇒ n = m  (inyectividad de σ)

**[A8]** `induction_principle`

- **Lean4:**

  ```
  theorem induction_principle
      (P : ℕ₀ → Prop) (h_0 : P 𝟘)
      (h_succ : ∀ n, P n → P (σ n)) : ∀ n, P n
  ```

- **Matemática:** P(0) ∧ (∀n, P(n) ⇒ P(σ n)) ⇒ ∀n ∈ ℕ₀, P(n)

### 3.3. Teoremas auxiliares exportados

**[T3.1]** `noConfusion`

- **Lean4:** `theorem noConfusion (n : ℕ₀) : (isZero n → ¬ isSucc n) ∧ (isSucc n → ¬ isZero n)`
- **Matemática:** isZero(n) e isSucc(n) son mutuamente excluyentes

**[T3.2]** `succ_neq_zero`

- **Lean4:** `theorem succ_neq_zero (n : ℕ₀) : σ n ≠ 𝟘`
- **Matemática:** ∀n ∈ ℕ₀, σ(n) ≠ 0

**[T3.3]** `succ_inj_wp`

- **Lean4:** `theorem succ_inj_wp {n m : ℕ₀} (h_neq : ¬ n = m) : σ n ≠ σ m`
- **Matemática:** n ≠ m ⇒ σ(n) ≠ σ(m)

**[T3.4]** `succ_inj_neg`

- **Lean4:** `theorem succ_inj_neg : ∀ n m : ℕ₀, σ n ≠ σ m → n ≠ m`
- **Matemática:** σ(n) ≠ σ(m) ⇒ n ≠ m

**[T3.5]** `succ_inj_pos_wp`

- **Lean4:** `theorem succ_inj_pos_wp {n m : ℕ₀} (h_succeq : σ n = σ m) : n = m`
- **Matemática:** σ(n) = σ(m) ⇒ n = m

**[T3.6]** `neq_succ`

- **Lean4:** `theorem neq_succ (k : ℕ₀) : k ≠ σ k`
- **Matemática:** ∀k ∈ ℕ₀, k ≠ σ(k)

**[T3.7]** `isZero_or_isSucc`

- **Lean4:** `theorem isZero_or_isSucc (n : ℕ₀) : isZero n ∨ isSucc n`
- **Matemática:** ∀n ∈ ℕ₀, isZero(n) ∨ isSucc(n)

**[T3.8]** `isZero_xor_isSucc`

- **Lean4:** `theorem isZero_xor_isSucc (n : ℕ₀) : (isZero n ∧ ¬isSucc n) ∨ (isSucc n ∧ ¬isZero n)`
- **Matemática:** ∀n ∈ ℕ₀, isZero(n) ⊕ isSucc(n)

### 3.4. Isomorfismo Λ/Ψ — inyectividad, biyección, composición

**[T3.9]** `Λ_inj`

- **Lean4:** `theorem Λ_inj (n m : Nat) : Λ n = Λ m → n = m`
- **Matemática:** Λ es inyectiva

**[T3.10]** `Ψ_inj`

- **Lean4:** `theorem Ψ_inj (n m : ℕ₀) : Ψ n = Ψ m → n = m`
- **Matemática:** Ψ es inyectiva

**[T3.11]** `Λ_surj`

- **Lean4:** `theorem Λ_surj (k : ℕ₀) : ∃ n : Nat, Λ n = k`
- **Matemática:** Λ es sobreyectiva

**[T3.12]** `Λ_bij`

- **Lean4:** `theorem Λ_bij (n m : Nat) (k : ℕ₀) : (Λ n = Λ m → n = m) ∧ (∃ j, Λ j = k)`
- **Matemática:** Λ es biyectiva

**[T3.13]** `Ψ_surj`

- **Lean4:** `theorem Ψ_surj (n : Nat) : ∃ k : ℕ₀, Ψ k = n`
- **Matemática:** Ψ es sobreyectiva

**[T3.14]** `Ψ_bij`

- **Lean4:** `theorem Ψ_bij (n m : ℕ₀) (k : Nat) : (Ψ n = Ψ m → n = m) ∧ (∃ j, Ψ j = k)`
- **Matemática:** Ψ es biyectiva

**[T3.15]** `comp_Λ_eq_Ψ` / `comp_Ψ_eq_Λ`

- **Lean4:** `theorem comp_Λ_eq_Ψ : comp Λ Ψ` / `theorem comp_Ψ_eq_Λ : comp Ψ Λ`
- **Matemática:** Ψ ∘ Λ = id_ℕ;  Λ ∘ Ψ = id_ℕ₀

**[T3.16]** `ΨΛ` / `ΛΨ`

- **Lean4:** `theorem ΨΛ (n : Nat) : Ψ (Λ n) = n` / `theorem ΛΨ (n : ℕ₀) : Λ (Ψ n) = n`
- **Matemática:** Ψ(Λ(n)) = n;  Λ(Ψ(n)) = n

### 3.5. Conmutación σ/τ/ρ con isomorfismos

**[T3.17]** `isomorph_0_Λ` / `isomorph_0_Ψ`

- **Lean4:** `theorem isomorph_0_Λ : Λ 0 = 𝟘` / `theorem isomorph_0_Ψ : Ψ 𝟘 = 0`

**[T3.18]** `isomorph_σ_Λ` / `isomorph_σ_Ψ`

- **Lean4:** `theorem isomorph_σ_Λ (n : Nat) : Λ (Nat.succ n) = σ (Λ n)` / `theorem isomorph_σ_Ψ (n : ℕ₀) : Ψ (σ n) = Nat.succ (Ψ n)`

**[T3.19]** `isomorph_τ_Λ` / `isomorph_τ_Ψ`

- **Lean4:** `theorem isomorph_τ_Λ (n : Nat) : τ (Λ n) = Λ (Nat.pred n)` / `theorem isomorph_τ_Ψ (n : ℕ₀) : Nat.pred (Ψ n) = Ψ (τ n)`

**[T3.20]** `isomorph_ρ_Ψ` / `isomorph_Λ_ρ`

- **Lean4:** `theorem isomorph_ρ_Ψ (n : ℕ₀) (h : n ≠ 𝟘) : Nat.pred (Ψ n) = Ψ (ρ n h)` / `theorem isomorph_Λ_ρ (n : Nat) (h : n ≠ 0) : Λ (Nat.pred n) = ρ (Λ n) ...`

**[T3.21]** `tau_eq_rho_if_ne_zero`

- **Lean4:** `theorem tau_eq_rho_if_ne_zero (k : ℕ₀) (hk : k ≠ 𝟘) : τ k = ρ k hk`
- **Matemática:** k ≠ 0 ⇒ τ(k) = ρ(k)

### 3.6. Inversión σ/τ/ρ

**[T3.22]** `τ_σ_eq_self`

- **Lean4:** `theorem τ_σ_eq_self (n : ℕ₀) : τ (σ n) = n`
- **Matemática:** τ(σ(n)) = n

**[T3.23]** `ρ_σ_eq_self`

- **Lean4:** `theorem ρ_σ_eq_self (n : ℕ₀) (h : σ n ≠ 𝟘) : ρ (σ n) h = n`
- **Matemática:** ρ(σ(n)) = n

**[T3.24]** `σ_ρ_eq_self`

- **Lean4:** `theorem σ_ρ_eq_self (n : ℕ₀) (h : n ≠ 𝟘) : σ (ρ n h) = n`
- **Matemática:** n ≠ 0 ⇒ σ(ρ(n)) = n

**[T3.25]** `σ_τ_eq_id_pos`

- **Lean4:** `theorem σ_τ_eq_id_pos : ∀ n : ℕ₀, n ≠ 𝟘 → σ (τ n) = n`
- **Matemática:** n ≠ 0 ⇒ σ(τ(n)) = n

### 3.7. Igualdad funcional

**[T3.26]** `eqFn_induction`

- **Lean4:** `theorem eqFn_induction {α} (f g : ℕ₀ → α) : f 𝟘 = g 𝟘 → (∀ n, f n = g n → f (σ n) = g (σ n)) → eqFn f g`
- **Matemática:** Principio de inducción para igualdad funcional

**[T3.27]** `eqFn_refl` / `eqFn_symm` / `eqFn_trans`

- **Lean4:** Reflexividad, simetría y transitividad de `eqFn`

---

## 4. StrictOrder.lean — `namespace Peano.StrictOrder`

*Dependencias: `PeanoNat`, `Axioms`*

### 4.1. Definiciones

**[D4.1]** `Lt`

- **Lean4:**

  ```
  def Lt (n m : ℕ₀) : Prop :=
    match n, m with
    | _,      ℕ₀.zero => False
    | ℕ₀.zero, σ _   => True
    | σ n',    σ m'  => Lt n' m'
  ```

- **Matemática:** Lt(n, 0) = ⊥;  Lt(0, σm) = ⊤;  Lt(σn, σm) = Lt(n, m)
- **Computable:** No (Prop); par booleano: `blt`
- **Terminado por:** recursión estructural sobre ambos argumentos
- **Notación:** `n < m` (instancia `LT ℕ₀`)

**[D4.2]** `blt` (par booleano de `Lt`)

- **Lean4:** `def blt (n m : ℕ₀) : Bool` — recursión análoga a `Lt`
- **Computable:** Sí

**[D4.3]** `Gt`

- **Lean4:**

  ```
  def Gt (n m : ℕ₀) : Prop :=
    match n, m with
    | ℕ₀.zero, _      => False
    | σ _,  ℕ₀.zero   => True
    | σ n',  σ m'     => Gt n' m'
  ```

- **Matemática:** Gt(n, m) ⟺ Lt(m, n)
- **Computable:** No; par booleano: `bgt`

**[D4.4]** `bgt` (par booleano de `Gt`)

- **Lean4:** `def bgt (n m : ℕ₀) : Bool` — recursión análoga
- **Computable:** Sí

**[D4.5]** Instancias de decisión y clase de orden

- **Lean4:**

  ```
  instance : LT ℕ₀ := ⟨Lt⟩
  instance decidableLt (n m : ℕ₀) : Decidable (Lt n m)
  instance decidableGt (n m : ℕ₀) : Decidable (Gt n m)
  ```

### 4.2. Teoremas principales (orden estricto total)

**[T4.1]** `lt_irrefl`

- **Lean4:** `theorem lt_irrefl (n : ℕ₀) : ¬(Lt n n)`
- **Matemática:** ∀n ∈ ℕ₀, ¬(n < n)

**[T4.2]** `lt_asymm`

- **Lean4:** `theorem lt_asymm (n m : ℕ₀) : Lt n m → ¬(Lt m n)`
- **Matemática:** n < m ⇒ ¬(m < n)

**[T4.3]** `lt_trans`

- **Lean4:** `theorem lt_trans (a b c : ℕ₀) : Lt a b → Lt b c → Lt a c`
- **Matemática:** a < b ∧ b < c ⇒ a < c

**[T4.4]** `trichotomy`

- **Lean4:** `theorem trichotomy (n m : ℕ₀) : (Lt n m) ∨ (n = m) ∨ (Lt m n)`
- **Matemática:** ∀n, m ∈ ℕ₀, n < m ∨ n = m ∨ m < n

**[T4.5]** `strong_trichotomy`

- **Lean4:** `theorem strong_trichotomy (n m : ℕ₀) : (Lt n m ∧ ¬(n = m) ∧ ¬(Lt m n)) ∨ (n = m ∧ ¬(Lt n m) ∧ ¬(Lt m n)) ∨ (Lt m n ∧ ¬(n = m) ∧ ¬(Lt n m))`
- **Matemática:** Tricotomía mutuamente excluyente

**[T4.6]** `lt_iff_lt_σ_σ`

- **Lean4:** `theorem lt_iff_lt_σ_σ (n m : ℕ₀) : Lt n m ↔ Lt (σ n) (σ m)`
- **Matemática:** n < m ⟺ σ(n) < σ(m)

**[T4.7]** `lt_iff_lt_τ_τ`

- **Lean4:** `theorem lt_iff_lt_τ_τ ...`
- **Matemática:** n < m ⟺ τ(n) < τ(m) (con condiciones)

**[T4.8]** `lt_zero` / `nlt_n_0`

- **Lean4:** `theorem lt_zero (n : ℕ₀) : ¬ Lt n 𝟘` / `theorem nlt_n_0 (n : ℕ₀) : ¬ Lt n 𝟘`
- **Matemática:** ∀n ∈ ℕ₀, ¬(n < 0)

**[T4.9]** `lt_succ_self`

- **Lean4:** `theorem lt_succ_self (n : ℕ₀) : Lt n (σ n)`
- **Matemática:** ∀n ∈ ℕ₀, n < σ(n)

**[T4.10]** `lt_then_lt_succ`

- **Lean4:** `theorem lt_then_lt_succ (n m : ℕ₀) : Lt n m → Lt n (σ m)`
- **Matemática:** n < m ⇒ n < σ(m)

**[T4.11]** `pos_of_ne_zero`

- **Lean4:** `theorem pos_of_ne_zero (n : ℕ₀) (h : n ≠ 𝟘) : Lt 𝟘 n`
- **Matemática:** n ≠ 0 ⇒ 0 < n

**[T4.12]** `zero_lt_succ`

- **Lean4:** `theorem zero_lt_succ (n : ℕ₀) : Lt 𝟘 (σ n)`
- **Matemática:** ∀n ∈ ℕ₀, 0 < σ(n)

**[T4.13]** `ne_of_lt`

- **Lean4:** `theorem ne_of_lt {n m : ℕ₀} : Lt n m → n ≠ m`

**[T4.14]** `lt_equiv_exists_σ`

- **Lean4:** `theorem lt_equiv_exists_σ (a b : ℕ₀) : Lt a b ↔ ∃ k, b = σ (add a k)`
- **Matemática:** a < b ⟺ ∃k, b = σ(a + k)

**[T4.15]** `succ_lt_succ_iff`

- **Lean4:** `theorem succ_lt_succ_iff {n m : ℕ₀} : Lt (σ n) (σ m) ↔ Lt n m`
- **Matemática:** σ(n) < σ(m) ⟺ n < m

**[T4.16]** `blt_iff_Lt` / `bgt_iff_Gt`

- **Lean4:** `theorem blt_iff_Lt (n m : ℕ₀) : blt n m = true ↔ Lt n m` / `theorem bgt_iff_Gt (n m : ℕ₀) : bgt n m = true ↔ Gt n m`
- **Matemática:** Equivalencia booleano ↔ proposición

**[T4.17]** `isomorph_Λ_lt` / `isomorph_Ψ_lt`

- **Lean4:** `theorem isomorph_Λ_lt (a b : Nat) : a < b ↔ Lt (Λ a) (Λ b)` / `theorem isomorph_Ψ_lt (a b : ℕ₀) : Lt a b ↔ Ψ a < Ψ b`
- **Matemática:** Preservación del orden estricto por Λ y Ψ

**[T4.18]** Teoremas adicionales exportados

`lt_then_lt_succ_wp`, `nlt_self`, `nlt_n_0_false`, `neq_then_lt_or_gt`, `lt_nor_gt_then_eq`, `lt_succ`, `lt_succ_then_lt`, `lt_succ_then_lt_wp`, `lt_self_σ_self`, `exists_greater_nat`, `nexists_greater_forall`, `lt_succ_iff_lt_or_eq`, `nblt_iff_nLt`, `nbgt_iff_nGt`, `neq_01_then_gt_1`, `lt_0_succ`, `lt_1_succ_succ`, `nlt_then_ltc_or_eq`, `lt_or_eq_then_nltc`, `lt_or_eq_iff_nltc`, `succ_lt_succ_iff_forall`, `lt_then_lt_succ_forall`, `lt_succ_then_lt_forall`, `lt_then_lt_succs`, `succ_lt_succ_then`, `lt_n_sm_then_lt_n_m_or_eq`, `lt_n_sm_then_lt_n_m_or_eq_wp`, `lt_sn_m_then_lt_n_m`, `lt_0_1`, `lt_1_b_then_b_neq_1`, `lt_sn_m_then_lt_n_m_wp`, `lt_1_b_then_b_neq_0`, `lt_b_1_then_b_eq_0`, `neq_0_then_lt_0`, `lt_0_then_neq_0`, `lt_then_lt_σ_σ_wp`, `lt_σ_σ_then_lt_wp`, `not_lt_and_not_eq_implies_gt`, `lt_asymm_wp`

---

## 5. Order.lean — `namespace Peano.Order`

*Dependencias: `PeanoNat`, `Axioms`, `StrictOrder`*

### 5.1. Definiciones

**[D5.1]** `Le`

- **Lean4:** `def Le (n m : ℕ₀) : Prop := Lt n m ∨ n = m`
- **Matemática:** n ≤ m ⟺ n < m ∨ n = m
- **Computable:** No (Prop); par decidible: instancia `decidableLe`
- **Notación:** `n ≤ m` (instancia `LE ℕ₀`)
- **Dependencias:** `Lt`

**[D5.2]** `Ge`

- **Lean4:** `def Ge (n m : ℕ₀) : Prop := Lt m n ∨ n = m`
- **Matemática:** n ≥ m ⟺ m < n ∨ n = m

**[D5.3]** `le'` (definición alternativa recursiva)

- **Lean4:**

  ```
  def le' (n m : ℕ₀) : Prop :=
    match n, m with
    | 𝟘,   _    => True
    | σ _, 𝟘   => False
    | σ n', σ m' => le' n' m'
  ```

- **Matemática:** Definición recursiva equivalente de ≤

**[D5.4]** `ble`, `bge` (booleanos)

- **Lean4:** `def ble (n m : ℕ₀) : Bool` / `def bge (n m : ℕ₀) : Bool`
- **Computable:** Sí

**[D5.5]** Instancias

- **Lean4:**

  ```
  instance : LE ℕ₀ := ⟨Le⟩
  instance decidableLe (n m : ℕ₀) : Decidable (Le n m)
  instance decidableGe (n m : ℕ₀) : Decidable (Ge n m)
  ```

### 5.2. Teoremas principales (orden total no estricto)

**[T5.1]** `le_refl`

- **Lean4:** `theorem le_refl (n : ℕ₀) : Le n n`
- **Matemática:** ∀n ∈ ℕ₀, n ≤ n

**[T5.2]** `le_antisymm`

- **Lean4:** `theorem le_antisymm (n m : ℕ₀) : Le n m → Le m n → n = m`
- **Matemática:** n ≤ m ∧ m ≤ n ⇒ n = m

**[T5.3]** `le_trans`

- **Lean4:** `theorem le_trans (a b c : ℕ₀) : Le a b → Le b c → Le a c`
- **Matemática:** a ≤ b ∧ b ≤ c ⇒ a ≤ c

**[T5.4]** `le_total`

- **Lean4:** `theorem le_total (n m : ℕ₀) : Le n m ∨ Le m n`
- **Matemática:** ∀n, m ∈ ℕ₀, n ≤ m ∨ m ≤ n

**[T5.5]** `zero_le`

- **Lean4:** `theorem zero_le (n : ℕ₀) : Le 𝟘 n`
- **Matemática:** ∀n ∈ ℕ₀, 0 ≤ n

**[T5.6]** `lt_imp_le`

- **Lean4:** `theorem lt_imp_le {n m : ℕ₀} : Lt n m → Le n m`
- **Matemática:** n < m ⇒ n ≤ m

**[T5.7]** `le_iff_lt_succ` / `lt_succ_iff_le`

- **Lean4:** `theorem le_iff_lt_succ (n m : ℕ₀) : Le n m ↔ Lt n (σ m)`
- **Matemática:** n ≤ m ⟺ n < σ(m)

**[T5.8]** `succ_le_succ_iff`

- **Lean4:** `theorem succ_le_succ_iff {n m : ℕ₀} : Le (σ n) (σ m) ↔ Le n m`
- **Matemática:** σ(n) ≤ σ(m) ⟺ n ≤ m

**[T5.9]** `le_zero_eq`

- **Lean4:** `theorem le_zero_eq (n : ℕ₀) (h : Le n 𝟘) : n = 𝟘`
- **Matemática:** n ≤ 0 ⇒ n = 0

**[T5.10]** `not_succ_le_zero`

- **Lean4:** `theorem not_succ_le_zero (n : ℕ₀) : ¬ Le (σ n) 𝟘`
- **Matemática:** ∀n ∈ ℕ₀, ¬(σ(n) ≤ 0)

**[T5.11]** `le_not_lt`

- **Lean4:** `theorem le_not_lt {n m : ℕ₀} (h : Le n m) : ¬ Lt m n`
- **Matemática:** n ≤ m ⇒ ¬(m < n)

**[T5.12]** `Le_iff_le'`

- **Lean4:** `theorem Le_iff_le' (n m : ℕ₀) : Le n m ↔ le' n m`
- **Matemática:** Equivalencia de definiciones de ≤

**[T5.13]** `ble_iff_Le` / `bge_iff_Ge`

- **Lean4:** `theorem ble_iff_Le (n m : ℕ₀) : ble n m = true ↔ Le n m` / `theorem bge_iff_Ge (n m : ℕ₀) : bge n m = true ↔ Ge n m`

**[T5.14]** `isomorph_Ψ_le` / `isomorph_Λ_le`

- **Lean4:** `theorem isomorph_Ψ_le (a b : ℕ₀) : Le a b ↔ Ψ a ≤ Ψ b` / `theorem isomorph_Λ_le (a b : Nat) : a ≤ b ↔ Le (Λ a) (Λ b)`

**[T5.15]** `well_ordering_principle`

- **Lean4:** `theorem well_ordering_principle {P : ℕ₀ → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, Lt m n → ¬P m`
- **Matemática:** Todo conjunto no vacío de ℕ₀ tiene un elemento minimal para <

**[T5.17]** `lt_or_ge`

- **Lean4:** `theorem lt_or_ge (a b : ℕ₀) : Lt a b ∨ Le b a`
- **Matemática:** ∀a, b ∈ ℕ₀, a < b ∨ b ≤ a

**[T5.18]** `le_or_lt`

- **Lean4:** `theorem le_or_lt (a b : ℕ₀) : Le a b ∨ Lt b a`
- **Matemática:** ∀a, b ∈ ℕ₀, a ≤ b ∨ b < a

**[T5.16]** Teoremas adicionales exportados

`lt_imp_le_wp`, `le_of_eq`, `le_of_eq_wp`, `le_self_of_eq_self`, `le_0_of_eq_0`, `le_then_le_succ`, `le_succ_self`, `le_succ`, `le_1_succ`, `le_zero_eq_zero`, `le_succ_zero_zero`, `le_1_0_then_false`, `le_succ_iff_le_or_eq`, `le_succ_then_le_or_eq`, `le_or_eq_then_le_succ`, `lt_of_le_neq`, `lt_of_le_neq_wp`, `le_zero_eq_wp`, `succ_le_succ_then`, `succ_le_succ_then_wp`, `succ_le_succ_if`, `succ_le_succ_if_wp`, `succ_le_succ_iff_wp`, `succ_le_succ'_then_wp`, `lt_of_le_of_ne`, `lt_iff_le_not_le`, `lt_succ_iff_lt_or_eq_alt`, `le_succ_iff_le_or_eq_alt`, `le_of_succ_le_succ`, `nle_then_gt`, `nle_then_gt_wp`, `gt_then_nle`, `gt_then_nle_wp`, `le_1_m_then_m_neq_0`, `le_1_m_then_m_neq_0_wp`, `m_neq_0_proved_lt_1_m`, `le_m_1_then_m_eq_0or1_wp`, `le_n_m_then_m_neq_0`, `le_n_m_n_neq_0_then_m_neq_0`, `m_neq_0_proved_lt_1_m_wp`, `le_0_succ_then_lt_0_succ`, `le_0_succ_then_lt_0_succ_wp`, `lt_0_succ_then_le_0_succ`, `lt_0_succ_then_le_0_succ_wp`, `le_0_succ_iff_lt_0_succ`, `le_then_lt_succ`, `le_then_lt_succ_wp`, `le_succ_then_le_or_eq_wp`, `le_or_eq_then_le_succ_wp`, `le_succ_k_n_then_le_k_n`, `lt_k_succ_n_then_le_k_n`, `lt_k_succ_n_then_le_k_n_wp`, `le_succ_k_n_then_lt_k_n`, `le_succ_k_n_then_lt_k_n_wp`, `le_succ_then_le`, `le_succ_then_le_wp`, `le_k_n_then_le_k_sn_wp`, `le_n_m_then_le_n_sm`, `le_n_m_then_le_n_sm_wp`, `le_sn_m_then_le_n_m_or_succ`, `le_sn_m_then_le_n_m_or_succ_wp`, `le_then_lt_or_eq`, `nle_σn_n`, `le_σn_n_then_false`, `lt_0n_then_le_1n`, `lt_0n_then_le_1n_wp`, `lt_nm_then_le_nm`, `lt_nm_then_le_nm_wp`, `le_then_ngt`, `le_then_ngt_wp`, `ngt_then_le`, `ngt_then_le_wp`, `le_succ_then_lt`, `le_succ_then_lt_wp`, `lt_then_le_succ_wp`, `lt_then_le_succ`, `ngt_iff_le`, `lt_or_ge`, `le_or_lt`

---

## 6. Lattice.lean — `namespace Peano.Lattice`

*Dependencias: `PeanoNat`, `Axioms`, `StrictOrder`, `Order`*

### 6.1. Definiciones

**[D6.1]** `max`

- **Lean4:**

  ```
  def max (n m : ℕ₀) : ℕ₀ :=
    match n, m with
    | 𝟘,    m    => m
    | n,    𝟘    => n
    | σ n', σ m' =>
        if n' = m' then σ m'
        else if blt n' m' then σ m'
        else σ n'
  ```

- **Matemática:** max: ℕ₀ × ℕ₀ → ℕ₀
- **Computable:** Sí (usa `blt`)

**[D6.2]** `min`

- **Lean4:**

  ```
  def min (n m : ℕ₀) : ℕ₀ :=
    match n, m with
    | 𝟘,    _    => 𝟘
    | _,    𝟘    => 𝟘
    | σ n', σ m' =>
        if n' = m' then σ n'
        else if blt n' m' then σ n'
        else σ m'
  ```

- **Matemática:** min: ℕ₀ × ℕ₀ → ℕ₀
- **Computable:** Sí

**[D6.3]** `min_max` / `max_min`

- **Lean4:**

  ```
  def min_max (n m : ℕ₀) : ℕ₀ × ℕ₀   -- devuelve (min n m, max n m)
  def max_min (n m : ℕ₀) : ℕ₀ × ℕ₀   -- devuelve (max n m, min n m)
  ```

- **Computable:** Sí

### 6.2. Teoremas — Propiedades básicas de retículo

**[T6.1]** Idempotencia

- `theorem max_idem (n : ℕ₀) : max n n = n`
- `theorem min_idem (n : ℕ₀) : min n n = n`

**[T6.2]** Conmutatividad

- `theorem max_comm (n m : ℕ₀) : max n m = max m n`
- `theorem min_comm (n m : ℕ₀) : min n m = min m n`

**[T6.3]** Asociatividad

- `theorem max_assoc (n m k : ℕ₀) : max (max n m) k = max n (max m k)`
- `theorem min_assoc (n m k : ℕ₀) : min (min n m) k = min n (min m k)`

**[T6.4]** Cotas sup/inf

- `theorem le_max_left (n m : ℕ₀) : Le n (max n m)`
- `theorem le_max_right (n m : ℕ₀) : Le m (max n m)`
- `theorem min_le_left (n m : ℕ₀) : Le (min n m) n`
- `theorem min_le_right (n m : ℕ₀) : Le (min n m) m`

**[T6.5]** Universalidad de sup/inf

- `theorem max_le (n m k : ℕ₀) (h₁ : Le n k) (h₂ : Le m k) : Le (max n m) k`
- `theorem le_min (k n m : ℕ₀) (h₁ : Le k n) (h₂ : Le k m) : Le k (min n m)`

**[T6.6]** Distributividad (retículo distributiva)

- `theorem max_distrib_min (n m k : ℕ₀) : max n (min m k) = min (max n m) (max n k)`
- `theorem min_distrib_max (n m k : ℕ₀) : min n (max m k) = max (min n m) (min n k)`

### 6.3. Teoremas — Identidades y extremos

**[T6.7]** Identidades con 𝟘

- `theorem min_abs_0 (n : ℕ₀) : min 𝟘 n = 𝟘`
- `theorem min_0_abs (n : ℕ₀) : min n 𝟘 = 𝟘`
- `theorem max_not_0 (n : ℕ₀) : max 𝟘 n = n`
- `theorem max_0_not (n : ℕ₀) : max n 𝟘 = n`

**[T6.8]** Igualdad y max/min

- `theorem eq_of_max_eq_min (n m : ℕ₀) : (max n m = min n m) → (n = m)`
- `theorem eq_then_eq_max_min (n m : ℕ₀) : (n = m) → (max n m = min n m)`
- `theorem eq_iff_eq_max_min (n m : ℕ₀) : n = m ↔ max n m = min n m`

### 6.4. Teoremas — Selección y orden

**[T6.9]** max/min selecciona un argumento

- `theorem max_is_any (n m : ℕ₀) : max n m = n ∨ max n m = m`
- `theorem min_is_any (n m : ℕ₀) : min n m = n ∨ min n m = m`

**[T6.10]** Relación con ≤ / <

- `theorem lt_then_min (a b : ℕ₀) : Lt a b → min a b = a`
- `theorem min_then_le (a b : ℕ₀) : min a b = a → Le a b`
- `theorem min_eq_of_gt {a b : ℕ₀} (h : Lt b a) : min a b = b`
- `theorem max_eq_of_lt {a b : ℕ₀} (h : Lt a b) : max a b = b`
- `theorem max_eq_of_gt {a b : ℕ₀} (h : Lt b a) : max a b = a`
- `theorem lt_of_not_le {n m : ℕ₀} (h : ¬ Le n m) : Lt m n`

**[T6.11]** Equivalencias Le ↔ max/min

- `theorem le_then_max_eq_right (n m : ℕ₀) (h : Le n m) : max n m = m`
- `theorem le_then_max_eq_left (n m : ℕ₀) (h : Le m n) : max n m = n`
- `theorem le_then_min_eq_left (n m : ℕ₀) (h : Le n m) : min n m = n`
- `theorem le_then_min_eq_right (n m : ℕ₀) (h : Le m n) : min n m = m`
- `theorem max_eq_left {a b : ℕ₀} (h : b ≤ a) : max a b = a`
- `theorem max_eq_right {a b : ℕ₀} (h : a ≤ b) : max a b = b`
- `theorem min_eq_left {a b : ℕ₀} (h : a ≤ b) : min a b = a`
- `theorem min_eq_right {a b : ℕ₀} (h : b ≤ a) : min a b = b`

**[T6.12]** Discriminación por desigualdad

- `theorem max_ne_min_of_ne (n m : ℕ₀) : n ≠ m ↔ ...`
- `theorem if_neq_then_min_xor (n m : ℕ₀) : n ≠ m ↔ ...`
- `theorem lt_max_of_ne (n m : ℕ₀) : n ≠ m ↔ Lt (min n m) (max n m)`

**[T6.13]** Absorción

- `theorem min_of_min_max (n m : ℕ₀) : min n m = min (max n m) (min n m)`
- `theorem max_of_min_max (n m : ℕ₀) : max n m = max (min n m) (max n m)`

**[T6.14]** Propiedades varias

- `theorem not_exists_max : ∀ k, ∃ n, max n k = n ∧ n ≠ k`

**[T6.15]** Galois connections (Le ↔ min/max)

- `theorem le_a_le_b_then_le_min_a_b_left (a b c : ℕ₀) : Le c a → Le c b → Le c (min a b)`
- `theorem le_min_a_b_then_le_a_le_b_left (a b c : ℕ₀) : Le c (min a b) → Le c a ∧ Le c b`
- `theorem le_a_le_b_then_le_min_a_b_right (a b c : ℕ₀) : Le a c → Le b c → Le (min a b) c`
- `theorem le_a_le_b_then_le_max_a_b_right (a b c : ℕ₀) : Le a c → Le b c → Le (max a b) c`
- `theorem le_max_a_b_then_le_a_le_b_right (a b c : ℕ₀) : Le (max a b) c → Le a c ∧ Le b c`
- `theorem le_a_le_b_then_le_max_a_b_left (a b c : ℕ₀) : Le c a → Le c b → Le c (max a b)`

### 6.5. Teoremas — Isomorfismos

- `theorem isomorph_Λ_max (n m : Nat) : max (Λ n) (Λ m) = Λ (Nat.max n m)`
- `theorem isomorph_Λ_min (n m : Nat) : min (Λ n) (Λ m) = Λ (Nat.min n m)`
- `theorem isomorph_Ψ_max (n m : ℕ₀) : Nat.max (Ψ n) (Ψ m) = Ψ (max n m)`
- `theorem isomorph_Ψ_min (n m : ℕ₀) : Nat.min (Ψ n) (Ψ m) = Ψ (min n m)`

### 6.6. Teoremas — Extensiones Mathlib-style (§ 7 del archivo)

**[T6.16]** Absorción (Mathlib naming)

- `theorem max_min_self (a b : ℕ₀) : max a (min a b) = a`  — `sup_inf_self`
- `theorem min_max_self (a b : ℕ₀) : min a (max a b) = a`  — `inf_sup_self`

**[T6.17]** inf ≤ sup

- `theorem min_le_max (a b : ℕ₀) : Le (min a b) (max a b)`

**[T6.18]** Iff characterizations

- `theorem max_eq_left_iff {a b : ℕ₀} : max a b = a ↔ Le b a`
- `theorem max_eq_right_iff {a b : ℕ₀} : max a b = b ↔ Le a b`
- `theorem min_eq_left_iff {a b : ℕ₀} : min a b = a ↔ Le a b`
- `theorem min_eq_right_iff {a b : ℕ₀} : min a b = b ↔ Le b a`

**[T6.19]** max_le / le_min as iff

- `theorem max_le_iff {a b c : ℕ₀} : Le (max a b) c ↔ Le a c ∧ Le b c`
- `theorem le_min_iff {c a b : ℕ₀} : Le c (min a b) ↔ Le c a ∧ Le c b`

**[T6.20]** Monotonía

- `theorem max_le_max {a a' b b' : ℕ₀} (h₁ : Le a a') (h₂ : Le b b') : Le (max a b) (max a' b')`
- `theorem min_le_min {a a' b b' : ℕ₀} (h₁ : Le a a') (h₂ : Le b b') : Le (min a b) (min a' b')`

**[T6.21]** Left/right commutativity

- `theorem max_left_comm (a b c : ℕ₀) : max a (max b c) = max b (max a c)`
- `theorem min_left_comm (a b c : ℕ₀) : min a (min b c) = min b (min a c)`
- `theorem max_right_comm (a b c : ℕ₀) : max (max a b) c = max (max a c) b`
- `theorem min_right_comm (a b c : ℕ₀) : min (min a b) c = min (min a c) b`

**[T6.22]** Successor structural

- `theorem max_succ_succ (a b : ℕ₀) : max (σ a) (σ b) = σ (max a b)`
- `theorem min_succ_succ (a b : ℕ₀) : min (σ a) (σ b) = σ (min a b)`

### 6.7. Export block completo (74 símbolos)

`max`, `min`, `min_max`, `max_min`, `max_idem`, `min_idem`, `min_abs_0`, `min_0_abs`, `max_not_0`, `max_0_not`, `eq_of_max_eq_min`, `eq_then_eq_max_min`, `eq_iff_eq_max_min`, `min_of_min_max`, `max_of_min_max`, `max_is_any`, `min_is_any`, `lt_then_min`, `min_then_le`, `min_eq_of_gt`, `max_eq_of_lt`, `max_ne_min_of_ne`, `if_neq_then_min_xor`, `lt_max_of_ne`, `max_comm`, `min_comm`, `le_then_max_eq_right`, `le_then_max_eq_left`, `le_max_left`, `le_max_right`, `max_le`, `max_assoc`, `le_then_min_eq_left`, `le_then_min_eq_right`, `min_le_left`, `min_le_right`, `le_min`, `min_assoc`, `not_exists_max`, `max_distrib_min`, `min_distrib_max`, `isomorph_Λ_max`, `isomorph_Λ_min`, `isomorph_Ψ_max`, `isomorph_Ψ_min`, `max_eq_left`, `max_eq_right`, `min_eq_left`, `min_eq_right`, `le_a_le_b_then_le_min_a_b_left`, `le_min_a_b_then_le_a_le_b_left`, `le_a_le_b_then_le_min_a_b_right`, `le_a_le_b_then_le_max_a_b_right`, `le_max_a_b_then_le_a_le_b_right`, `le_a_le_b_then_le_max_a_b_left`, `max_min_self`, `min_max_self`, `min_le_max`, `max_eq_left_iff`, `max_eq_right_iff`, `min_eq_left_iff`, `min_eq_right_iff`, `max_le_iff`, `le_min_iff`, `max_le_max`, `min_le_min`, `max_left_comm`, `min_left_comm`, `max_right_comm`, `min_right_comm`, `max_succ_succ`, `min_succ_succ`

---

## 7. WellFounded.lean — `namespace Peano.WellFounded`

*Dependencias: `PeanoNat`, `Axioms`, `StrictOrder`, `Order`, `Lattice`, `Init.Classical`*

### 7.1. Definiciones

**[D7.1]** Instancia `SizeOf ℕ₀`

- **Lean4:** `instance : SizeOf ℕ₀ where sizeOf := Ψ`
- **Descripción:** Conecta la relación `Lt` con la terminación de Lean vía el isomorfismo Ψ: ℕ₀ → Nat
- **Computable:** Sí (Ψ es computable)

### 7.2. Instancias

**[I7.1]** `WellFoundedRelation ℕ₀`

- **Lean4:** `instance : WellFoundedRelation ℕ₀ where rel := Lt; wf := well_founded_lt`
- **Descripción:** Registra `Lt` como relación bien fundada para `ℕ₀`, habilitando `termination_by` y `decreasing_by` con hipótesis `Lt` directas.

### 7.3. Teoremas principales

**[T7.1]** `acc_lt_wf`

- **Lean4:** `theorem acc_lt_wf (n : ℕ₀) : Acc Lt n`
- **Matemática:** ∀n ∈ ℕ₀, n es accesible respecto a <

**[T7.2]** `well_founded_lt`

- **Lean4:** `theorem well_founded_lt : WellFounded Lt`
- **Matemática:** < es una relación bien fundada en ℕ₀

**[T7.3]** `strongRecOn` (recursión fuerte)

- **Lean4:** `noncomputable def strongRecOn {C : ℕ₀ → Sort _} (n : ℕ₀) (h : ∀ m : ℕ₀, (∀ k : ℕ₀, Lt k m → C k) → C m) : C n`
- **Matemática:** Para construir C(n), basta suponer C(k) para todo k < n.
- **Computable:** No (`noncomputable`, depende de `WellFounded.recursion`)

**[T7.4]** `strongInductionOn` (inducción fuerte)

- **Lean4:** `theorem strongInductionOn {P : ℕ₀ → Prop} (n : ℕ₀) (h : ∀ m : ℕ₀, (∀ k : ℕ₀, Lt k m → P k) → P m) : P n`
- **Matemática:** Para probar P(n), basta suponer P(k) para todo k < n.

---

## 8. Add.lean — `namespace Peano.Add`

*Dependencias: `PeanoNat`, `Axioms`, `StrictOrder`, `Order`, `Lattice`, `WellFounded`*

### 8.1. Definiciones

**[D8.1]** `add`

- **Lean4:**

  ```
  def add (n m : ℕ₀) : ℕ₀ :=
    match m with
    | 𝟘    => n
    | σ m' => σ (add n m')
  ```

- **Matemática:** n + 0 = n;  n + σ(m) = σ(n + m)
- **Computable:** Sí
- **Terminado por:** recursión estructural sobre `m`
- **Notación:** `n + m` (instancia `Add ℕ₀`)

**[D8.2]** `add_l` (suma recursiva sobre el argumento izquierdo)

- **Lean4:**

  ```
  def add_l (n m : ℕ₀) : ℕ₀ :=
    match n with
    | 𝟘    => m
    | σ n' => σ (add n' m)
  ```

- **Matemática:** Definición alternativa (recursión sobre primer argumento)
- **Computable:** Sí
- **Notación:** `n +l m`

### 8.2. Teoremas principales

**[T8.1]** `add_zero` / `zero_add`

- **Lean4:** `theorem add_zero (n : ℕ₀) : add n 𝟘 = n` / `theorem zero_add (n : ℕ₀) : add 𝟘 n = n`
- **Matemática:** n + 0 = n;  0 + n = n

**[T8.2]** `add_succ` / `succ_add`

- **Lean4:** `theorem add_succ (n m : ℕ₀) : add n (σ m) = σ (add n m)` / `theorem succ_add (n m : ℕ₀) : add (σ n) m = σ (add n m)`
- **Matemática:** n + σ(m) = σ(n + m);  σ(n) + m = σ(n + m)

**[T8.3]** `add_one` / `one_add`

- **Lean4:** `theorem add_one (n : ℕ₀) : add n 𝟙 = σ n` / `theorem one_add (n : ℕ₀) : add 𝟙 n = σ n`
- **Matemática:** n + 1 = σ(n);  1 + n = σ(n)

**[T8.4]** `add_comm`

- **Lean4:** `theorem add_comm (n m : ℕ₀) : add n m = add m n`
- **Matemática:** ∀n, m ∈ ℕ₀, n + m = m + n

**[T8.5]** `add_assoc`

- **Lean4:** `theorem add_assoc (n m k : ℕ₀) : add n (add m k) = add (add n m) k`
- **Matemática:** ∀n, m, k ∈ ℕ₀, n + (m + k) = (n + m) + k

**[T8.6]** `add_cancel`

- **Lean4:** `theorem add_cancel (n m k : ℕ₀) : add n m = add n k → m = k`
- **Matemática:** n + m = n + k ⇒ m = k

**[T8.7]** `add_eq_zero_iff`

- **Lean4:** `theorem add_eq_zero_iff {n m : ℕ₀} : add n m = 𝟘 ↔ n = 𝟘 ∧ m = 𝟘`
- **Matemática:** n + m = 0 ⟺ n = 0 ∧ m = 0

**[T8.8]** `le_iff_exists_add`

- **Lean4:** `theorem le_iff_exists_add (a b : ℕ₀) : Le a b ↔ ∃ p, b = add a p`
- **Matemática:** a ≤ b ⟺ ∃p ∈ ℕ₀, b = a + p

**[T8.9]** `lt_iff_exists_add_succ`

- **Lean4:** `theorem lt_iff_exists_add_succ (a b : ℕ₀) : Lt a b ↔ ∃ p, b = add a (σ p)`
- **Matemática:** a < b ⟺ ∃p ∈ ℕ₀, b = a + σ(p)

**[T8.10]** `isomorph_Ψ_add` / `isomorph_Λ_add`

- **Lean4:** Preservación de la suma por Ψ y Λ

**[T8.11]** Teoremas adicionales exportados

`add_zero_l`, `zero_add_l`, `add_zero_eq_add_l_zero`, `add_one_l`, `one_add_l`, `add_one_eq_add_l_one`, `add_succ_l`, `succ_add_l`, `add_succ_eq_add_l_succ`, `add_eq_add_l`, `eq_fn_add_add_l`, `add_le`, `add_le_r`, `le_self_add_r`, `le_self_add_r_forall`, `lt_self_add_r`, `lt_self_add_r_forall`, `le_self_add_l`, `le_self_add_l_forall`, `lt_self_add_l`, `lt_self_add_l_forall`, `add_lt`, `cancelation_add`, `add_lt_cancelation`, `add_le_cancelation`, `le_then_le_add_zero`, `le_then_le_add_one`, `le_add_then_le_add_succ`, `le_add_zero_then_le`, `le_add_one_then_le`, `le_add_r_add_r_then_le`, `le_add_l_add_l_then_le`, `le_then_le_add_r_add_r_then_le`, `le_then_le_add_l_add_l_then_le`, `le_iff_le_add_r_add_r_forall`, `le_iff_le_add_l_add_l_forall`, `le_add_then_le`, `le_iff_le_add`, `le_iff_le_add_forall`, `le_add_cancel`, `le_then_exists_zero_add`, `le_self_add`, `add_σn_m_eq_add_n_σm`, `add_σn_m_eq_σadd_n_m`, `add_τn_m_eq_add_n_τm`, `le_self_add_forall`, `lt_add_succ`, `le_then_exists_add`, `le_then_exists_add_wp`, `lt_then_exists_add_succ`, `lt_then_exists_add_succ_wp`, `add_lt_add_left_iff`, `lt_iff_add_cancel`, `lt_iff_add_lt`, `lt_n_add_n_σm`, `lt_add_of_pos_right`, `le_add_compat`, `le_add_compat_wp`, `lt_le_then_lt_add_compat`, `lt_le_then_add_add_compat_wp`, `le_lt_then_lt_add_compat`, `le_lt_then_lt_add_compat_wp`, `lt_lt_then_lt_add_compat`, `lt_lt_then_lt_add_compat_wp`, `le_a_b_then_le_2a_2b`, `le_a_b_then_le_2a_2b_wp`, `lt_a_b_then_lt_2a_2b`, `lt_a_b_then_lt_2a_2b_wp`, `linear_equation_right`, `linear_inequation_left`, `linear_equation_left`, `linear_inequation_right`, `lt_add_pos`, `lt_0_then_le_1`

---

## 9. Sub.lean — `namespace Peano.Sub`

*Dependencias: `…Add` y anteriores*

### 9.1. Definiciones

**[D9.1]** `subₕₖ` (resta con prueba)

- **Lean4:**

  ```
  def subₕₖ (n m : ℕ₀) (h : Le m n) : ℕ₀ :=
    match n, m with
    | k,    𝟘    => k
    | 𝟘,    σ m' => False.elim (succ_neq_zero m' (le_zero_eq (σ m') h))
    | σ n', σ m' => subₕₖ n' m' (succ_le_succ_then h)
  termination_by n
  ```

- **Matemática:** n ∸ m con prueba m ≤ n (resta exacta)
- **Computable:** Sí
- **Terminado por:** `termination_by n`
- **Notación:** `n -( h ) m` (prioridad 65)

**[D9.2]** `sub` (resta truncada / monus)

- **Lean4:**

  ```
  def sub (n m : ℕ₀) : ℕ₀ :=
    if h : Le m n then subₕₖ n m h else 𝟘
  ```

- **Matemática:** n ∸ m = n − m si m ≤ n, else 0
- **Computable:** Sí (usa instancia `decidableLe`)
- **Notación:** `n - m` (infijo, prioridad 65)

### 9.2. Teoremas principales

**[T9.1]** `sub_zero` / `zero_sub`

- **Lean4:** `theorem sub_zero (n : ℕ₀) : sub n 𝟘 = n` / `theorem zero_sub (n : ℕ₀) : sub 𝟘 n = 𝟘`
- **Matemática:** n ∸ 0 = n;  0 ∸ n = 0

**[T9.2]** `sub_k_add_k`

- **Lean4:** `theorem sub_k_add_k (n k : ℕ₀) (h : Le k n) : add (sub n k) k = n`
- **Matemática:** k ≤ n ⇒ (n ∸ k) + k = n

**[T9.3]** `add_k_sub_k`

- **Lean4:** `theorem add_k_sub_k (n k : ℕ₀) : sub (add n k) k = n`
- **Matemática:** (n + k) ∸ k = n

**[T9.4]** `sub_self`

- **Lean4:** `theorem sub_self (n : ℕ₀) : sub n n = 𝟘`
- **Matemática:** n ∸ n = 0

**[T9.5]** `le_sub_iff_add_le_of_le`

- **Lean4:** `theorem le_sub_iff_add_le_of_le (n m k : ℕ₀) (h : Le m n) : Le k (sub n m) ↔ Le (add m k) n`
- **Matemática:** m ≤ n ⇒ (k ≤ n ∸ m ⟺ m + k ≤ n)

**[T9.6]** `sub_pos_iff_lt`

- **Lean4:** `theorem sub_pos_iff_lt (n m : ℕ₀) : Le 𝟙 (sub n m) ↔ Lt m n`
- **Matemática:** 1 ≤ n ∸ m ⟺ m < n

**[T9.7]** `sub_lt_self`

- **Lean4:** `theorem sub_lt_self (a b : ℕ₀) (h_le : Le b a) (h_b_ne : b ≠ 𝟘) : Lt (sub a b) a`
- **Matemática:** b ≤ a ∧ b ≠ 0 ⇒ a ∸ b < a

**[T9.8]** `isomorph_Λ_sub` / `isomorph_Ψ_sub`

- **Lean4:** Preservación de la resta por Λ y Ψ

**[T9.9]** Teoremas adicionales exportados

`subₕₖ_zero`, `zero_subₕₖ`, `subₕₖ_eq_zero`, `sub_eq_zero`, `subₕₖ_one`, `sub_one`, `one_sub`, `subₕₖ_succ`, `sub_succ`, `succ_sub`, `sub_succ_succ_eq`, `subₕₖ_k_add_k`, `subₕₖ_k_add_k_forall`, `sub_k_add_k_forall`, `add_k_subₕₖ_k`, `add_k_sub_k_forall`, `aux_ge_1`, `nle_one_zero`, `aux_neq_0`, `subₕₖ_le_self`, `subₕₖ_lt_self`, `sub_lt_self_wp`, `sub_le_self`, `subₕₖ_eq_iff_eq_add_of_le`, `subₕₖ_le_subₕₖ_right`, `subₕₖ_le_subₕₖ_left`, `add_sub_assoc`, `add_le_add_left`, `sub_eq_of_le`, `sub_sub`, `sub_lt_iff_lt_add_of_le`, `lt_b_a_then_sub_a_b_neq_0`, `sub_pos_of_lt`

---

## 10. Mul.lean — `namespace Peano.Mul`

*Dependencias: `…Sub` y anteriores*

### 10.1. Definiciones

**[D10.1]** `mul`

- **Lean4:**

  ```
  def mul (n m : ℕ₀) : ℕ₀ :=
    match m with
    | 𝟘    => 𝟘
    | σ m' => add (mul n m') n
  ```

- **Matemática:** n·0 = 0;  n·σ(m) = n·m + n
- **Computable:** Sí
- **Terminado por:** recursión estructural sobre `m`
- **Notación:** `n * m` (infijo, prioridad 70)

### 10.2. Teoremas principales

**[T10.1]** `mul_zero` / `zero_mul`

- **Lean4:** `theorem mul_zero (n : ℕ₀) : mul n 𝟘 = 𝟘` / `theorem zero_mul (n : ℕ₀) : mul 𝟘 n = 𝟘`
- **Matemática:** n·0 = 0;  0·n = 0

**[T10.2]** `mul_one` / `one_mul`

- **Lean4:** `theorem mul_one (n : ℕ₀) : mul n 𝟙 = n` / `theorem one_mul (m : ℕ₀) : mul 𝟙 m = m`
- **Matemática:** n·1 = n;  1·m = m

**[T10.3]** `mul_succ` / `succ_mul`

- **Lean4:** `theorem mul_succ (n m : ℕ₀) : mul n (σ m) = add (mul n m) n` / `theorem succ_mul (n m : ℕ₀) : mul (σ n) m = add (mul n m) m`
- **Matemática:** n·σ(m) = n·m + n;  σ(n)·m = n·m + m

**[T10.4]** `mul_comm`

- **Lean4:** `theorem mul_comm (n m : ℕ₀) : mul n m = mul m n`
- **Matemática:** ∀n, m ∈ ℕ₀, n·m = m·n

**[T10.5]** `mul_assoc`

- **Lean4:** `theorem mul_assoc (m n k : ℕ₀) : mul (mul m n) k = mul m (mul n k)`
- **Matemática:** ∀m, n, k ∈ ℕ₀, (m·n)·k = m·(n·k)

**[T10.6]** `mul_add` / `add_mul`

- **Lean4:** `theorem mul_add (m n k : ℕ₀) : mul m (add n k) = add (mul m n) (mul m k)` / `theorem add_mul (m n k : ℕ₀) : mul (add m n) k = add (mul m k) (mul n k)`
- **Matemática:** Distributividad izquierda y derecha

**[T10.7]** `mul_eq_zero`

- **Lean4:** `theorem mul_eq_zero (n m : ℕ₀) : mul n m = 𝟘 ↔ n = 𝟘 ∨ m = 𝟘`
- **Matemática:** n·m = 0 ⟺ n = 0 ∨ m = 0

**[T10.8]** `mul_cancelation_left` / `mul_cancelation_right`

- **Lean4:** `theorem mul_cancelation_left {a b c : ℕ₀} (h : a ≠ 𝟘) : mul a b = mul a c → b = c` / análogo derecho
- **Matemática:** a ≠ 0 ∧ a·b = a·c ⇒ b = c

**[T10.9]** `mul_sub`

- **Lean4:** `theorem mul_sub (c a b : ℕ₀) (h : Lt b a) : mul c (sub a b) = sub (mul c a) (mul c b)`
- **Matemática:** b < a ⇒ c·(a ∸ b) = c·a ∸ c·b

**[T10.10]** `archimedean_property`

- **Lean4:** `theorem archimedean_property {n : ℕ₀} (m : ℕ₀) (h : Lt 𝟘 n) : ∃ j, Lt m (mul j n)`
- **Matemática:** n > 0 ⇒ ∀m ∈ ℕ₀, ∃j ∈ ℕ₀, m < j·n

**[T10.11]** `exists_unique_mul_le_and_lt_succ_mul`

- **Lean4:**

  ```
  theorem exists_unique_mul_le_and_lt_succ_mul
      (n m : ℕ₀) (h : Lt 𝟘 n) :
      ∃¹ k, Le (mul k n) m ∧ Lt m (mul (σ k) n)
  ```

- **Matemática:** n > 0 ⇒ ∃¹k ∈ ℕ₀, k·n ≤ m < σ(k)·n

**[T10.12]** Teoremas adicionales exportados

`mul_two`, `two_mul`, `mul_three`, `three_mul`, `eq_zero_of_mul_eq_zero`, `obvio_1`, `le_n_mul_n_σn`, `mul_le_right`, `mul_le_left`, `mul_le_full_right`, `mul_le_full_left`, `mul_lt_left`, `mul_lt_right`, `mul_lt_full_left`, `mul_lt_full_right`, `mul_le_mono_right`, `lt_σn_mul_σn_σσm`, `mul_n_τm`, `mul_τn_m`, `lt_of_lt_of_le`, `exists_factor_of_mul_le`, `le_le_mul_le_compat`, `mul_pos`, `lt_lt_mul_lt_compat`, `le_lt_mul_lt_compat`

### 10.3. Isomorfismos Nat ↔ ℕ₀ para mul

**[T10.13]** `isomorph_Ψ_mul`

- **Lean4:** `theorem isomorph_Ψ_mul (n m : ℕ₀) : Ψ (mul n m) = Nat.pow (Ψ n) (Ψ m)`
- **Matemática:** Ψ(n·m) = Ψ(n)^ₙ Ψ(m)

**[T10.14]** `isomorph_Λ_mul`

- **Lean4:** `theorem isomorph_Λ_mul (n m : Nat) : Λ (Nat.mul n m) = mul (Λ n) (Λ m)`
- **Matemática:** Λ(n ×ₙ m) = Λ(n)·Λ(m)

---

## 11. Div.lean — `namespace Peano.Div`

*Dependencias: `…Mul` y anteriores*

### 11.1. Definiciones

**[D11.1]** `divMod`

- **Lean4:**

  ```
  def divMod (a b : ℕ₀) : ℕ₀ × ℕ₀ :=
    if b  = 𝟘 then (𝟘, 𝟘)
    else if a = 𝟘 then (𝟘, 𝟘)
    else if b = 𝟙 then (a, 𝟘)
    else if Lt a b then (𝟘, a)
    else if a = b  then (𝟙, 𝟘)
    else let (a', b') := divMod (sub a b) b; (σ a', b')
  termination_by a
  ```

- **Matemática:** ((⌊a/b⌋, a mod b))
- **Computable:** Sí
- **Terminado por:** `termination_by a` vía `sub_lt_self` + `lt_sizeOf`

**[D11.2]** `div`

- **Lean4:** `def div (a b : ℕ₀) : ℕ₀ := (divMod a b).1`
- **Matemática:** ⌊a/b⌋
- **Computable:** Sí
- **Notación:** `a / b`

**[D11.3]** `mod`

- **Lean4:** `def mod (a b : ℕ₀) : ℕ₀ := (divMod a b).2`
- **Matemática:** a mod b
- **Computable:** Sí
- **Notación:** `a % b`

**[D11.4]** `lt_sizeOf`

- **Lean4:** `theorem lt_sizeOf (a b : ℕ₀) : Lt a b → sizeOf a < sizeOf b`

### 11.2. Teoremas principales

**[T11.1]** `divMod_spec`

- **Lean4:** `theorem divMod_spec (a b : ℕ₀) (h : b ≠ 𝟘) : add (mul (div a b) b) (mod a b) = a`
- **Matemática:** b ≠ 0 ⇒ (a/b)·b + (a mod b) = a

**[T11.2]** `mod_lt`

- **Lean4:** `theorem mod_lt (a b : ℕ₀) (h : b ≠ 𝟘) : Lt (mod a b) b`
- **Matemática:** b ≠ 0 ⇒ (a mod b) < b

**[T11.3]** `div_le_self`

- **Lean4:** `theorem div_le_self (a b : ℕ₀) : Le (div a b) a`
- **Matemática:** ⌊a/b⌋ ≤ a

**[T11.4]** `div_lt_self`

- **Lean4:** `theorem div_lt_self ...`
- **Matemática:** Condiciones bajo las cuales ⌊a/b⌋ < a

**[T11.5]** Teoremas adicionales exportados

`gt_imp_neq_zero_one`, `div_of_lt`, `mod_of_lt`, `div_of_lt_fst_interval`, `div_eq_two`, `le___mul__div_a_b__b____a`, `div_of_lt_nth_interval`, `mod_of_lt_fst_interval`, `mod_of_lt_snd_interval`, `mod_of_lt_nth_interval`

### 11.3. Isomorfismos Nat ↔ ℕ₀ para div y mod

**[T11.6]** `isomorph_Ψ_div`

- **Lean4:** `theorem isomorph_Ψ_div (n m : ℕ₀) : Ψ (div n m) = Nat.div (Ψ n) (Ψ m)`
- **Matemática:** Ψ(⌊n/m⌋) = ⌊Ψ(n)/Ψ(m)⌋ₙ

**[T11.7]** `isomorph_Ψ_mod`

- **Lean4:** `theorem isomorph_Ψ_mod (n m : ℕ₀) (hm : m ≠ 𝟘) : Ψ (mod n m) = Nat.mod (Ψ n) (Ψ m)`
- **Matemática:** m ≠ 0 ⇒ Ψ(n mod m) = Ψ(n) modₙ Ψ(m)
- **Nota:** Requiere `m ≠ 𝟘` (Peano: `mod n 𝟘 = 𝟘`; Lean core: `Nat.mod n 0 = n`)

**[T11.8]** `isomorph_Λ_div`

- **Lean4:** `theorem isomorph_Λ_div (n m : Nat) : Λ (Nat.div n m) = div (Λ n) (Λ m)`
- **Matemática:** Λ(⌊n/m⌋ₙ) = ⌊Λ(n)/Λ(m)⌋

**[T11.9]** `isomorph_Λ_mod`

- **Lean4:** `theorem isomorph_Λ_mod (n m : Nat) (hm : m ≠ 0) : Λ (Nat.mod n m) = mod (Λ n) (Λ m)`
- **Matemática:** m ≠ 0 ⇒ Λ(n modₙ m) = Λ(n) mod Λ(m)

---

## 12. Arith.lean — `namespace Peano.Arith`

*Dependencias: todos los módulos anteriores, `Init.Classical`*

### 12.1. Definiciones para `ℕ₀`

**[D12.1]** `Divides`

- **Lean4:** `def Divides (a b : ℕ₀) : Prop := ∃ k : ℕ₀, b = mul a k`
- **Matemática:** a ∣ b  ⟺  ∃k ∈ ℕ₀, b = a·k
- **Computable:** No (Prop)
- **Notación:** `a ∣ b` (infijo, prioridad 50); `a ∤ b` ≡ ¬(a ∣ b) (prioridad 50)

**[D12.2]** `MultipleOf`, `DivisorOf`

- **Lean4:**

  ```
  def MultipleOf (n m : ℕ₀) : Prop := Divides n m
  def DivisorOf  (d n : ℕ₀) : Prop := Divides d n
  ```

- **Matemática:** Sinónimos orientados

**[D12.3]** `Divisors`

- **Lean4:** `def Divisors (n : ℕ₀) : ℕ₀ → Prop := fun d => d ∣ n`
- **Matemática:** Divisors(n) = {d ∈ ℕ₀ | d ∣ n}

**[D12.4]** `IsGCD`

- **Lean4:** `def IsGCD (a b d : ℕ₀) : Prop := d ∣ a ∧ d ∣ b ∧ ∀ c, (c ∣ a ∧ c ∣ b) → c ∣ d`
- **Matemática:** IsGCD(a, b, d)  ⟺  d∣a ∧ d∣b ∧ (∀c, c∣a ∧ c∣b ⇒ c∣d)

**[D12.5]** `IsLCM`

- **Lean4:** `def IsLCM (a b m : ℕ₀) : Prop := a ∣ m ∧ b ∣ m ∧ ∀ c, (a ∣ c ∧ b ∣ c) → m ∣ c`
- **Matemática:** IsLCM(a, b, m)  ⟺  a∣m ∧ b∣m ∧ (∀c, a∣c ∧ b∣c ⇒ m∣c)

**[D12.6]** `Coprime`

- **Lean4:** `def Coprime (a b : ℕ₀) : Prop := IsGCD a b 𝟙`
- **Matemática:** gcd(a, b) = 1

**[D12.7]** `Prime`

- **Lean4:** `def Prime (p : ℕ₀) : Prop := p ≠ 𝟘 ∧ p ≠ 𝟙 ∧ ∀ a b, p ∣ (mul a b) → p ∣ a ∨ p ∣ b`
- **Matemática:** p ≠ 0 ∧ p ≠ 1 ∧ (∀a,b, p∣ab ⇒ p∣a ∨ p∣b)

**[D12.8]** `gcd`

- **Lean4:**

  ```
  def gcd (a b : ℕ₀) : ℕ₀ :=
    if b = 𝟘 then a else gcd b (a % b)
  termination_by b
  ```

- **Matemática:** gcd(a, 0) = a;  gcd(a, b) = gcd(b, a mod b)
- **Computable:** Sí
- **Terminado por:** `termination_by b` vía `mod_lt` + `lt_sizeOf`

**[D12.9]** `lcm`

- **Lean4:** `def lcm (a b : ℕ₀) : ℕ₀ := div (mul a b) (gcd a b)`
- **Matemática:** lcm(a, b) = (a·b) / gcd(a, b)
- **Computable:** Sí

**[D12.10]** `Multiples` (inductivo)

- **Lean4:**

  ```
  inductive Multiples (n : ℕ₀) : ℕ₀ → Prop
    | zero    : Multiples n 𝟘
    | add_step {k : ℕ₀} : Multiples n k → Multiples n (add k n)
  ```

- **Matemática:** Multiples(n) = {0, n, 2n, 3n, …}

**[D12.11]** Estructuras de listas de divisores

- **Lean4:**

  ```
  inductive DList (α : Type) : Type
  def range_from_one : ℕ₀ → DList ℕ₀
  def dividesb (d n : ℕ₀) : Bool
  def factorsOf (n : ℕ₁) : DList ℕ₀
  structure DivisorsList (n : ℕ₀) : Type
  ```

- **Computable:** Sí

### 12.2. Definiciones para `ℕ₁`

**[D12.12]** `Divides₁`

- **Lean4:** `def Divides₁ (a b : ℕ₁) : Prop := a.val ∣ b.val`
- **Notación:** `a ∣₁ b` (infijo, prioridad 50)

**[D12.13]** `IsGCD₁`

- **Lean4:** `def IsGCD₁ (a b d : ℕ₁) : Prop := d ∣₁ a ∧ d ∣₁ b ∧ ∀ c : ℕ₁, (c ∣₁ a ∧ c ∣₁ b) → c ∣₁ d`

**[D12.14]** `gcd₁`

- **Lean4:**

  ```
  def gcd₁ (a b : ℕ₁) : ℕ₁ :=
    if hr : (a.val % b.val) = 𝟘 then b
    else gcd₁ b ⟨a.val % b.val, hr⟩
  termination_by b.val
  ```

- **Computable:** Sí

**[D12.15]** `Coprime₁`

- **Lean4:** `def Coprime₁ (a b : ℕ₁) : Prop := gcd₁ a b = ⟨𝟙, by decide⟩`

### 12.3. Teoremas — Divisibilidad básica

**[T12.1]** `divides_refl`

- **Lean4:** `theorem divides_refl (a : ℕ₀) : a ∣ a`

**[T12.2]** `one_divides`

- **Lean4:** `theorem one_divides (a : ℕ₀) : 𝟙 ∣ a`

**[T12.3]** `divides_zero`

- **Lean4:** `theorem divides_zero (a : ℕ₀) : a ∣ 𝟘`

**[T12.4]** `zero_divides_iff`

- **Lean4:** `theorem zero_divides_iff (b : ℕ₀) : (𝟘 ∣ b) ↔ b = 𝟘`

**[T12.5]** `divides_trans`

- **Lean4:** `theorem divides_trans {a b c : ℕ₀} : a ∣ b → b ∣ c → a ∣ c`

**[T12.6]** `divides_mul_right` / `divides_mul_left`

- **Lean4:** `theorem divides_mul_right {a b c : ℕ₀} : a ∣ b → a ∣ (mul b c)` / análogo izquierdo

**[T12.7]** `divides_add`

- **Lean4:** `theorem divides_add {a b c : ℕ₀} : a ∣ b → a ∣ c → a ∣ (add b c)`

**[T12.8]** `divides_le`

- **Lean4:** `theorem divides_le {a b : ℕ₀} : a ∣ b → b ≠ 𝟘 → Le a b`
- **Matemática:** a ∣ b ∧ b ≠ 0 ⇒ a ≤ b

**[T12.9]** `antisymm_divides`

- **Lean4:** `theorem antisymm_divides {a b : ℕ₀} : (a ∣ b) → (b ∣ a) → a = b`

**[T12.10]** `divides_sub`

- **Lean4:** `theorem divides_sub {a b c : ℕ₀} (h : Lt b a) (ha : c ∣ a) (hb : c ∣ b) : c ∣ (sub a b)`

**[T12.11]** `divides_mod`

- **Lean4:** `theorem divides_mod {a b c : ℕ₀} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (a % b)`

**[T12.12]** `multiples_iff_divides`

- **Lean4:** `theorem multiples_iff_divides (n m : ℕ₀) : Multiples n m ↔ n ∣ m`

### 12.4. Teoremas — MCD y Bézout

**[T12.13]** `gcd_greatest`

- **Lean4:** `theorem gcd_greatest (a b c : ℕ₀) : (c ∣ a ∧ c ∣ b) → c ∣ gcd a b`

**[T12.14]** `gcd_divides_linear_combo`

- **Lean4:** `theorem gcd_divides_linear_combo (a b n m : ℕ₀) : gcd a b ∣ (add (mul a n) (mul b m))`

**[T12.15]** `gcd_divides_max` / `gcd_divides_min`

- **Lean4:** `theorem gcd_divides_max (a b : ℕ₀) : gcd a b ∣ max a b` / `theorem gcd_divides_min (a b : ℕ₀) : gcd a b ∣ min a b`

**[T12.16]** `bezout_natform`

- **Lean4:**

  ```
  theorem bezout_natform (a b : ℕ₀) :
      ∃ n m, (gcd a b = sub (mul n a) (mul m b)) ∨
             (gcd a b = sub (mul n b) (mul m a))
  ```

- **Matemática:** ∃n,m ∈ ℕ₀, gcd(a,b) = n·a ∸ m·b  ∨  gcd(a,b) = n·b ∸ m·a

### 12.5. Teoremas — DivisorsList

**[T12.17]** `divisorslist_one_mem`

- **Lean4:** `theorem divisorslist_one_mem {n : ℕ₀} (d : DivisorsList n) : 𝟙 ∈ d.vals`

**[T12.18]** `divisorslist_self_mem`

- **Lean4:** `theorem divisorslist_self_mem {n : ℕ₀} (d : DivisorsList n) : n ∈ d.vals`

### 12.6. Teoremas — ℕ₁

**[T12.19]** `divides₁_refl` / `divides₁_trans` / `divides₁_antisymm`

- **Lean4:** Reflexividad, transitividad y antisimetría de `∣₁`

**[T12.20]** `mod_eq_zero_iff_divides`

- **Lean4:** `theorem mod_eq_zero_iff_divides {a b : ℕ₁} : (a.val % b.val) = 𝟘 ↔ (b ∣₁ a)`

**[T12.21]** `gcd₁_val_eq`

- **Lean4:** `theorem gcd₁_val_eq (a b : ℕ₁) : (gcd₁ a b).val = gcd a.val b.val`

**[T12.22]** `gcd₁_comm`

- **Lean4:** `theorem gcd₁_comm (a b : ℕ₁) : gcd₁ a b = gcd₁ b a`

**[T12.23]** `gcd₁_divides_left` / `gcd₁_divides_right` / `gcd₁_divides_both`

- **Lean4:** `theorem gcd₁_divides_left (a b : ℕ₁) : gcd₁ a b ∣₁ a` / análogos

### 12.7. Extensiones GCD/LCM/Coprime estilo Mathlib (§ 8)

**[T12.24]** `gcd_comm`

- **Lean4:** `theorem gcd_comm (a b : ℕ₀) : gcd a b = gcd b a`

**[T12.25]** `gcd_dvd_left` / `gcd_dvd_right`

- **Lean4:** `theorem gcd_dvd_left (a b : ℕ₀) : gcd a b ∣ a`
- **Lean4:** `theorem gcd_dvd_right (a b : ℕ₀) : gcd a b ∣ b`

**[T12.26]** `dvd_gcd`

- **Lean4:** `theorem dvd_gcd {c a b : ℕ₀} (ha : c ∣ a) (hb : c ∣ b) : c ∣ gcd a b`

**[T12.27]** `gcd_zero_right` / `gcd_zero_left`

- **Lean4:** `theorem gcd_zero_right (a : ℕ₀) : gcd a 𝟘 = a`
- **Lean4:** `theorem gcd_zero_left (a : ℕ₀) : gcd 𝟘 a = a`

**[T12.28]** `gcd_one_right` / `gcd_one_left`

- **Lean4:** `theorem gcd_one_right (a : ℕ₀) : gcd a 𝟙 = 𝟙`
- **Lean4:** `theorem gcd_one_left (a : ℕ₀) : gcd 𝟙 a = 𝟙`

**[T12.29]** `gcd_self`

- **Lean4:** `theorem gcd_self (a : ℕ₀) : gcd a a = a`

**[T12.30]** `gcd_eq_zero_iff`

- **Lean4:** `theorem gcd_eq_zero_iff (a b : ℕ₀) : gcd a b = 𝟘 ↔ a = 𝟘 ∧ b = 𝟘`

**[T12.31]** `gcd_ne_zero_left` / `gcd_ne_zero_right`

- **Lean4:** `theorem gcd_ne_zero_left {a b : ℕ₀} (ha : a ≠ 𝟘) : gcd a b ≠ 𝟘`
- **Lean4:** `theorem gcd_ne_zero_right {a b : ℕ₀} (hb : b ≠ 𝟘) : gcd a b ≠ 𝟘`

**[T12.32]** `dvd_gcd_iff`

- **Lean4:** `theorem dvd_gcd_iff {c a b : ℕ₀} : c ∣ gcd a b ↔ c ∣ a ∧ c ∣ b`

**[T12.33]** `gcd_assoc`

- **Lean4:** `theorem gcd_assoc (a b c : ℕ₀) : gcd (gcd a b) c = gcd a (gcd b c)`

**[T12.34]** `IsGCD_gcd`

- **Lean4:** `theorem IsGCD_gcd (a b : ℕ₀) : IsGCD a b (gcd a b)`

**[T12.35]** `div_mul_cancel`

- **Lean4:** `theorem div_mul_cancel {a b : ℕ₀} (hb : b ≠ 𝟘) (h : b ∣ a) : mul (a / b) b = a`

**[T12.36]** `gcd_mul_lcm`

- **Lean4:** `theorem gcd_mul_lcm (a b : ℕ₀) : mul (gcd a b) (lcm a b) = mul a b`

**[T12.37]** `lcm_comm`

- **Lean4:** `theorem lcm_comm (a b : ℕ₀) : lcm a b = lcm b a`

**[T12.38]** `lcm_zero_left` / `lcm_zero_right`

- **Lean4:** `theorem lcm_zero_left (a : ℕ₀) : lcm 𝟘 a = 𝟘`
- **Lean4:** `theorem lcm_zero_right (a : ℕ₀) : lcm a 𝟘 = 𝟘`

**[T12.39]** `dvd_lcm_left` / `dvd_lcm_right`

- **Lean4:** `theorem dvd_lcm_left (a b : ℕ₀) : a ∣ lcm a b`
- **Lean4:** `theorem dvd_lcm_right (a b : ℕ₀) : b ∣ lcm a b`

**[T12.40]** `lcm_self`

- **Lean4:** `theorem lcm_self (a : ℕ₀) : lcm a a = a`

**[T12.41]** `coprime_comm`

- **Lean4:** `theorem coprime_comm {a b : ℕ₀} : Coprime a b ↔ Coprime b a`

**[T12.42]** `coprime_one_right` / `coprime_one_left`

- **Lean4:** `theorem coprime_one_right (a : ℕ₀) : Coprime a 𝟙`
- **Lean4:** `theorem coprime_one_left (a : ℕ₀) : Coprime 𝟙 a`

### 12.8. Isomorfismos Nat ↔ ℕ₀ para gcd y lcm

**[T12.43]** `isomorph_Ψ_gcd`

- **Lean4:** `theorem isomorph_Ψ_gcd (a b : ℕ₀) : Ψ (gcd a b) = Nat.gcd (Ψ a) (Ψ b)`
- **Matemática:** Ψ(gcd(a,b)) = gcdₙ(Ψ(a), Ψ(b))

**[T12.44]** `isomorph_Λ_gcd`

- **Lean4:** `theorem isomorph_Λ_gcd (n m : Nat) : Λ (Nat.gcd n m) = gcd (Λ n) (Λ m)`
- **Matemática:** Λ(gcdₙ(n,m)) = gcd(Λ(n), Λ(m))

**[T12.45]** `isomorph_Ψ_lcm`

- **Lean4:** `theorem isomorph_Ψ_lcm (a b : ℕ₀) : Ψ (lcm a b) = Nat.lcm (Ψ a) (Ψ b)`
- **Matemática:** Ψ(lcm(a,b)) = lcmₙ(Ψ(a), Ψ(b))

**[T12.46]** `isomorph_Λ_lcm`

- **Lean4:** `theorem isomorph_Λ_lcm (n m : Nat) : Λ (Nat.lcm n m) = lcm (Λ n) (Λ m)`
- **Matemática:** Λ(lcmₙ(n,m)) = lcm(Λ(n), Λ(m))

### 12.9. IsEven / IsOdd

**[D12.12]** `IsEven`

- **Lean4:** `def IsEven (n : ℕ₀) : Prop := n % 𝟚 = 𝟘`
- **Matemática:** IsEven(n) ⟺ n mod 2 = 0
- **Computable:** No (Prop)
- **Decidable:** Sí (`decidableIsEven`)

**[D12.13]** `IsOdd`

- **Lean4:** `def IsOdd (n : ℕ₀) : Prop := n % 𝟚 = 𝟙`
- **Matemática:** IsOdd(n) ⟺ n mod 2 = 1
- **Computable:** No (Prop)
- **Decidable:** Sí (`decidableIsOdd`)

**[I12.1]** `decidableIsEven`

- **Lean4:** `instance decidableIsEven (n : ℕ₀) : Decidable (IsEven n)`
- **Descripción:** Decidabilidad de paridad vía `DecidableEq`

**[I12.2]** `decidableIsOdd`

- **Lean4:** `instance decidableIsOdd (n : ℕ₀) : Decidable (IsOdd n)`
- **Descripción:** Decidabilidad de imparidad vía `DecidableEq`

**[T12.47]** `even_zero`

- **Lean4:** `theorem even_zero : IsEven 𝟘`
- **Matemática:** 0 es par

**[T12.48]** `odd_one`

- **Lean4:** `theorem odd_one : IsOdd 𝟙`
- **Matemática:** 1 es impar

**[T12.49]** `even_or_odd`

- **Lean4:** `theorem even_or_odd (n : ℕ₀) : IsEven n ∨ IsOdd n`
- **Matemática:** ∀n ∈ ℕ₀, n es par ∨ n es impar

**[T12.50]** `not_even_and_odd`

- **Lean4:** `theorem not_even_and_odd {n : ℕ₀} : ¬(IsEven n ∧ IsOdd n)`
- **Matemática:** Ningún n es par e impar a la vez

**[T12.51]** `not_even_iff_odd`

- **Lean4:** `theorem not_even_iff_odd {n : ℕ₀} : ¬IsEven n ↔ IsOdd n`
- **Matemática:** ¬par(n) ⟺ impar(n)

**[T12.52]** `not_odd_iff_even`

- **Lean4:** `theorem not_odd_iff_even {n : ℕ₀} : ¬IsOdd n ↔ IsEven n`
- **Matemática:** ¬impar(n) ⟺ par(n)

---

## 13. Primes.lean — `namespace Peano.Primes`

*Dependencias: todos los módulos anteriores + `Arith`*

> Teorema Fundamental de la Aritmética (TFA) — existencia y unicidad de la factorización en primos.

### 13.1. Definiciones

**[D13.1]** `Irreducible`

- **Lean4:** `def Irreducible (p : ℕ₀) : Prop := p ≠ 𝟘 ∧ p ≠ 𝟙 ∧ ∀ a b, p = mul a b → a = 𝟙 ∨ b = 𝟙`
- **Matemática:** p irreducible ⟺ p ≠ 0 ∧ p ≠ 1 ∧ (p = ab ⇒ a = 1 ∨ b = 1)

**[D13.2]** `HasExactlyTwoDivisors`

- **Lean4:** `def HasExactlyTwoDivisors (p : ℕ₀) : Prop := ...`
- **Matemática:** p tiene exactamente dos divisores: 1 y p

**[D13.3]** `ℙ` (tipo de primos)

- **Lean4:** `def ℙ := {n : ℕ₂ // Prime n.val.val}`
- **Matemática:** ℙ = {p ∈ ℕ₂ | Prime(p)}

**[D13.4]** `PrimeList`

- **Lean4:** `def PrimeList (ps : DList ℕ₀) : Prop`
- **Matemática:** Todos los elementos de la lista son primos

**[D13.5]** `product_list`

- **Lean4:** `def product_list : DList ℕ₀ → ℕ₀`
- **Matemática:** Producto de una lista de naturales

### 13.2. Propiedades básicas de `Prime`

**[T13.1]** `prime_ne_zero` / `prime_ne_one`

- **Lean4:** `theorem prime_ne_zero {p : ℕ₀} (hp : Prime p) : p ≠ 𝟘` / `theorem prime_ne_one {p : ℕ₀} (hp : Prime p) : p ≠ 𝟙`

**[T13.2]** `one_lt_prime` / `prime_ge_two`

- **Lean4:** `theorem one_lt_prime {p : ℕ₀} (hp : Prime p) : Lt 𝟙 p` / `theorem prime_ge_two {p : ℕ₀} (hp : Prime p) : Le 𝟚 p`

**[T13.3]** `not_prime_one` / `not_prime_zero`

- **Lean4:** `theorem not_prime_one : ¬ Prime 𝟙` / `theorem not_prime_zero : ¬ Prime 𝟘`

**[T13.4]** `mul_eq_one`

- **Lean4:** `theorem mul_eq_one {a b : ℕ₀} : mul a b = 𝟙 → a = 𝟙 ∧ b = 𝟙`
- **Matemática:** a·b = 1 ⇒ a = 1 ∧ b = 1

**[T13.5]** `prime_divisors`

- **Lean4:** `theorem prime_divisors {p : ℕ₀} (hp : Prime p) {d : ℕ₀} (hd : d ∣ p) : d = 𝟙 ∨ d = p`

### 13.3. Equivalencias de primalidad

**[T13.6]** `prime_imp_irreducible`

- **Lean4:** `theorem prime_imp_irreducible {p : ℕ₀} (hp : Prime p) : Irreducible p`

**[T13.7]** `irreducible_imp_prime`

- **Lean4:** `theorem irreducible_imp_prime {p : ℕ₀} (hp : Irreducible p) : Prime p`

**[T13.8]** `prime_iff_irreducible`

- **Lean4:** `theorem prime_iff_irreducible {p : ℕ₀} : Prime p ↔ Irreducible p`

**[T13.9]** `prime_iff_has_exactly_two_divisors`

- **Lean4:** `theorem prime_iff_has_exactly_two_divisors {p : ℕ₀} : Prime p ↔ HasExactlyTwoDivisors p`

### 13.4. Coprimalidad y Lema de Gauss

**[T13.10]** `coprime_symm`

- **Lean4:** `theorem coprime_symm {a b : ℕ₀} : Coprime a b → Coprime b a`

**[T13.11]** `gcd_eq_one_iff_coprime`

- **Lean4:** `theorem gcd_eq_one_iff_coprime (a b : ℕ₀) : gcd a b = 𝟙 ↔ Coprime a b`

**[T13.12]** `prime_not_dvd_imp_coprime`

- **Lean4:** `theorem prime_not_dvd_imp_coprime {p a : ℕ₀} (hp : Prime p) (h : ¬ p ∣ a) : Coprime p a`

**[T13.13]** `prime_coprime_or_dvd`

- **Lean4:** `theorem prime_coprime_or_dvd {p a : ℕ₀} (hp : Prime p) : Coprime p a ∨ p ∣ a`

**[T13.14]** `coprime_dvd_of_dvd_mul` (Lema de Gauss)

- **Lean4:** `theorem coprime_dvd_of_dvd_mul {a b c : ℕ₀} (h : Coprime a b) (h2 : a ∣ mul b c) : a ∣ c`
- **Matemática:** gcd(a,b)=1 ∧ a∣bc ⇒ a∣c

### 13.5. Listas y productos

**[T13.15]** `product_nil` / `product_cons` / `product_append`

- **Lean4:** Reglas de simplificación para `product_list`

**[T13.16]** `product_list_pos`

- **Lean4:** `theorem product_list_pos ...`
- **Matemática:** El producto de una PrimeList es positivo

**[T13.17]** `prime_dvd_product_list`

- **Lean4:** `theorem prime_dvd_product_list {p : ℕ₀} {ps : DList ℕ₀} (hp : Prime p) (hpl : PrimeList ps) (hd : p ∣ product_list ps) : ∃ q, q ∈ ps ∧ p = q`

**[T13.18]** `mem_dvd_product`

- **Lean4:** `theorem mem_dvd_product {a : ℕ₀} {l : DList ℕ₀} (h : a ∈ l) : a ∣ product_list l`

### 13.6. Teorema Fundamental de la Aritmética

**[T13.19]** `exists_prime_divisor`

- **Lean4:** `theorem exists_prime_divisor {n : ℕ₀} (h : Lt 𝟙 n) : ∃ p, Prime p ∧ p ∣ n`
- **Matemática:** n > 1 ⇒ ∃p primo, p ∣ n

**[T13.20]** `exists_prime_factorization` (TFA — existencia)

- **Lean4:** `theorem exists_prime_factorization (n : ℕ₀) (h : Lt 𝟙 n) : ∃ ps : DList ℕ₀, PrimeList ps ∧ product_list ps = n`
- **Matemática:** n > 1 ⇒ ∃ lista de primos cuyo producto es n

**[T13.21]** `unique_prime_factorization` (TFA — unicidad)

- **Lean4:** `theorem unique_prime_factorization ...`
- **Matemática:** La factorización en primos es única salvo permutación

### 13.7. Decidabilidad de `Prime`

**[D13.6]** `isPrimeb`

- **Lean4:** `def isPrimeb (n : ℕ₀) : Bool := ble 𝟚 n && decide (smallestDivisor n = n)`
- **Matemática:** Test booleano de primalidad
- **Computable:** Sí
- **Decidable:** `isPrimeb n = true ↔ Prime n`

**[T13.22]** `prime_imp_smallestDivisor_eq_self`

- **Lean4:** `theorem prime_imp_smallestDivisor_eq_self {p : ℕ₀} (hp : Prime p) : smallestDivisor p = p`
- **Matemática:** p primo ⇒ smallestDivisor(p) = p

**[T13.23]** `isPrimeb_iff`

- **Lean4:** `theorem isPrimeb_iff {n : ℕ₀} : isPrimeb n = true ↔ Prime n`
- **Matemática:** isPrimeb(n) = true ⟺ n es primo

**[I13.1]** `decidablePrime`

- **Lean4:** `instance decidablePrime (n : ℕ₀) : Decidable (Prime n)`
- **Descripción:** Decidabilidad de la primalidad vía `isPrimeb`

---

## 14. Combinatorics/Pow.lean — `namespace Peano.Pow`

*Dependencias: `…Mul`, `Div`*

### 14.1. Definiciones

**[D14.1]** `pow`

- **Lean4:**

  ```
  def pow (n m : ℕ₀) : ℕ₀ :=
    match m with
    | 𝟘 => 𝟙
    | σ m' => mul (pow n m') n
  ```

- **Matemática:** n⁰ = 1;  n^{σ m} = n^m · n
- **Computable:** Sí
- **Terminado por:** recursión estructural sobre `m`
- **Notación:** `n ^ m` (infijo, prioridad 80)

### 14.2. Teoremas principales

**[T14.1]** `pow_zero`

- **Lean4:** `theorem pow_zero (n : ℕ₀) : n ^ 𝟘 = 𝟙`
- **Matemática:** n⁰ = 1

**[T14.2]** `zero_pow`

- **Lean4:** `theorem zero_pow {m : ℕ₀} (h : m ≠ 𝟘) : 𝟘 ^ m = 𝟘`
- **Matemática:** m ≠ 0 ⇒ 0^m = 0

**[T14.3]** `one_pow` / `pow_one`

- **Lean4:** `theorem one_pow (m : ℕ₀) : 𝟙 ^ m = 𝟙` / `theorem pow_one (n : ℕ₀) : n ^ 𝟙 = n`
- **Matemática:** 1^m = 1;  n¹ = n

**[T14.4]** `pow_succ`

- **Lean4:** `theorem pow_succ (n m : ℕ₀) : n ^ (σ m) = mul (n ^ m) n`
- **Matemática:** n^{σ(m)} = n^m · n

**[T14.5]** `pow_add_eq_mul_pow`

- **Lean4:** `theorem pow_add_eq_mul_pow (n m k : ℕ₀) : n ^ (add m k) = mul (n ^ m) (n ^ k)`
- **Matemática:** n^{m+k} = n^m · n^k

**[T14.6]** `pow_pow_eq_pow_mul`

- **Lean4:** `theorem pow_pow_eq_pow_mul (n m k : ℕ₀) : pow (pow n m) k = pow n (mul m k)`
- **Matemática:** (n^m)^k = n^{m·k}

**[T14.7]** `mul_pow_n_m_pow_k_m_eq_pow_nk_m`

- **Lean4:** `theorem mul_pow_n_m_pow_k_m_eq_pow_nk_m (n k m : ℕ₀) : mul (pow n m) (pow k m) = pow (mul n k) m`
- **Matemática:** n^m · k^m = (n·k)^m

**[T14.8]** `pow_eq_zero_iff`

- **Lean4:** `theorem pow_eq_zero_iff {n m : ℕ₀} : n ^ m = 𝟘 ↔ n = 𝟘 ∧ m ≠ 𝟘`
- **Matemática:** n^m = 0 ⟺ n = 0 ∧ m ≠ 0

**[T14.9]** `pow_eq_one_iff`

- **Lean4:** `theorem pow_eq_one_iff {n : ℕ₀} (h : n ≠ 𝟘) {m : ℕ₀} : n ^ m = 𝟙 ↔ n = 𝟙 ∨ m = 𝟘`
- **Matemática:** n ≠ 0 ⇒ (n^m = 1 ⟺ n = 1 ∨ m = 0)

**[T14.10]** `pow_two`

- **Lean4:** `theorem pow_two (n : ℕ₀) : n ^ 𝟚 = mul n n`
- **Matemática:** n² = n·n

**[T14.11]** `pow_ne_zero`

- **Lean4:** `theorem pow_ne_zero {n : ℕ₀} (h : n ≠ 𝟘) (m : ℕ₀) : n ^ m ≠ 𝟘`

**[T14.12]** `pow_gt` / `pow_ge_one`

- **Lean4:** `theorem pow_gt {n m : ℕ₀} (h_n : Gt n 𝟘) (h_m : Gt m 𝟘) : Gt (n ^ m) 𝟘` / `theorem pow_ge_one {n m : ℕ₀} (h : Gt n 𝟘) : Ge (n ^ m) 𝟙`

**[T14.13]** `pow_lt_mono_exp` / `pow_le_pow_right`

- **Lean4:** `theorem pow_lt_mono_exp {n : ℕ₀} (h : Lt 𝟙 n) {m k : ℕ₀} (h₂ : Lt m k) : Lt (n ^ m) (n ^ k)` / `theorem pow_le_pow_right {n : ℕ₀} (h : Lt 𝟙 n) {m k : ℕ₀} (h₂ : Le m k) : Le (n ^ m) (n ^ k)`
- **Matemática:** Monotonía del exponente (base > 1)

**[T14.14]** `pow_lt_mono_base` / `pow_le_pow_left`

- **Lean4:** `theorem pow_lt_mono_base {m n : ℕ₀} (h : Lt m n) {k : ℕ₀} (h₂ : k ≠ 𝟘) : Lt (m ^ k) (n ^ k)` / `theorem pow_le_pow_left {m n : ℕ₀} (h : Le m n) {k : ℕ₀} (h₂ : k ≠ 𝟘) : Le (m ^ k) (n ^ k)`
- **Matemática:** Monotonía de la base (exponente > 0)

**[T14.15]** `pow_lt_succ_base` / `pow_lt_succ_base_strong` / `pow_lt_succ_exp`

- **Lean4:** Teoremas de crecimiento estricto de potencias

**[T14.16]** `one_lt_pow` / `pow_mul_comm`

- **Lean4:** `theorem one_lt_pow {n : ℕ₀} (h₁ : Lt 𝟙 n) {m : ℕ₀} (h₂ : m ≠ 𝟘) : Lt 𝟙 (n ^ m)` / `theorem pow_mul_comm (n m k : ℕ₀) : mul (n ^ m) (n ^ k) = mul (n ^ k) (n ^ m)`

### 14.3. Isomorfismos Nat ↔ ℕ₀ para pow

**[T14.17]** `isomorph_Ψ_pow`

- **Lean4:** `theorem isomorph_Ψ_pow (n m : ℕ₀) : Ψ (pow n m) = Nat.pow (Ψ n) (Ψ m)`
- **Matemática:** Ψ(n^m) = Ψ(n)^ₙ Ψ(m)

**[T14.18]** `isomorph_Λ_pow`

- **Lean4:** `theorem isomorph_Λ_pow (n m : Nat) : Λ (Nat.pow n m) = pow (Λ n) (Λ m)`
- **Matemática:** Λ(n^ₙ m) = Λ(n)^Λ(m)

---

## 15. Combinatorics/Factorial.lean — `namespace Peano.Factorial`

*Dependencias: `…Add`, `Mul`*

### 15.1. Definiciones

**[D15.1]** `factorial`

- **Lean4:**

  ```
  def factorial : ℕ₀ → ℕ₀
    | 𝟘 => 𝟙
    | σ n => mul (factorial n) (σ n)
  ```

- **Matemática:** 0! = 1;  (σ n)! = n! · σ(n)
- **Computable:** Sí
- **Terminado por:** recursión estructural

### 15.2. Teoremas principales

**[T15.1]** `factorial_zero` / `factorial_one` / `factorial_two`

- **Lean4:** `theorem factorial_zero : factorial 𝟘 = 𝟙` / `theorem factorial_one : factorial 𝟙 = 𝟙` / `theorem factorial_two : factorial 𝟚 = 𝟚`

**[T15.2]** `factorial_succ`

- **Lean4:** `theorem factorial_succ (n : ℕ₀) : factorial (σ n) = mul (factorial n) (σ n)`
- **Matemática:** (σ n)! = n! · σ(n)

**[T15.3]** `factorial_pos`

- **Lean4:** `theorem factorial_pos (n : ℕ₀) : Gt (factorial n) 𝟘`
- **Matemática:** n! > 0

**[T15.4]** `factorial_ne_zero`

- **Lean4:** `theorem factorial_ne_zero (n : ℕ₀) : factorial n ≠ 𝟘`

**[T15.5]** `factorial_ge_one`

- **Lean4:** `theorem factorial_ge_one (n : ℕ₀) : Ge (factorial n) 𝟙`
- **Matemática:** n! ≥ 1

**[T15.6]** `factorial_le_succ` / `factorial_le_mono`

- **Lean4:** `theorem factorial_le_succ (n : ℕ₀) : Le (factorial n) (factorial (σ n))` / `theorem factorial_le_mono {m n : ℕ₀} (h : Le m n) : Le (factorial m) (factorial n)`
- **Matemática:** Monotonía del factorial

---

## 16. Combinatorics/Binom.lean — `namespace Peano.Binom`

*Dependencias: `…Mul`, `Sub`, `Factorial`*

### 16.1. Definiciones

**[D16.1]** `binom`

- **Lean4:**

  ```
  def binom : ℕ₀ → ℕ₀ → ℕ₀
    | 𝟘,   𝟘    => 𝟙
    | 𝟘,   σ _  => 𝟘
    | σ n, 𝟘    => 𝟙
    | σ n, σ k  => add (binom n k) (binom n (σ k))
  ```

- **Matemática:** C(0,0)=1; C(0,σk)=0; C(σn,0)=1; C(σn,σk)=C(n,k)+C(n,σk)
- **Computable:** Sí
- **Terminado por:** recursión estructural
- **Notación:** `C(n, k)` → `binom n k`

### 16.2. Teoremas principales

**[T16.1]** `binom_zero_zero` / `binom_zero_succ` / `binom_succ_zero`

- **Lean4:** Casos base

**[T16.2]** `binom_pascal`

- **Lean4:** `theorem binom_pascal (n k : ℕ₀) : C(σ n, σ k) = add (binom n k) (binom n (σ k))`
- **Matemática:** C(n+1, k+1) = C(n, k) + C(n, k+1)  (Triángulo de Pascal)

**[T16.3]** `binom_n_zero` / `binom_n_one`

- **Lean4:** `theorem binom_n_zero (n : ℕ₀) : C(n, 𝟘) = 𝟙` / `theorem binom_n_one (n : ℕ₀) : C(n, 𝟙) = n`
- **Matemática:** C(n,0) = 1;  C(n,1) = n

**[T16.4]** `binom_eq_zero_of_gt`

- **Lean4:** `theorem binom_eq_zero_of_gt {n k : ℕ₀} (h : Lt n k) : C(n, k) = 𝟘`
- **Matemática:** n < k ⇒ C(n,k) = 0

**[T16.5]** `binom_self`

- **Lean4:** `theorem binom_self (n : ℕ₀) : C(n, n) = 𝟙`
- **Matemática:** C(n,n) = 1

**[T16.6]** `binom_pos`

- **Lean4:** `theorem binom_pos {n k : ℕ₀} (h : Le k n) : Gt (binom n k) 𝟘`
- **Matemática:** k ≤ n ⇒ C(n,k) > 0

**[T16.7]** `binom_one` / `binom_succ_n_by_n`

- **Lean4:** `theorem binom_one (n : ℕ₀) : C(σ n, 𝟙) = σ n` / `theorem binom_succ_n_by_n (n : ℕ₀) : C(σ n, n) = σ n`

**[T16.8]** `binom_mul_factorials`

- **Lean4:** `theorem binom_mul_factorials {n k : ℕ₀} (h : Le k n) : mul (mul (binom n k) (factorial k)) (factorial (sub n k)) = factorial n`
- **Matemática:** k ≤ n ⇒ C(n,k) · k! · (n−k)! = n!

---

## 17. Combinatorics/NewtonBinom.lean — `namespace Peano.NewtonBinom`

*Dependencias: `…Pow`, `Factorial`, `Binom`*

### 17.1. Definiciones

**[D17.1]** `finSum`

- **Lean4:**

  ```
  def finSum (f : ℕ₀ → ℕ₀) : ℕ₀ → ℕ₀
    | 𝟘 => f 𝟘
    | σ n => add (finSum f n) (f (σ n))
  ```

- **Matemática:** finSum(f, n) = Σ_{k=0}^{n} f(k)
- **Computable:** Sí
- **Terminado por:** recursión estructural
- **Notación:** `∑ k ≤ n, f` — macro

**[D17.2]** `binomTerm`

- **Lean4:** `def binomTerm (a b n k : ℕ₀) : ℕ₀ := mul (mul (binom n k) (pow a k)) (pow b (sub n k))`
- **Matemática:** binomTerm(a, b, n, k) = C(n,k) · a^k · b^{n−k}
- **Computable:** Sí

### 17.2. Teoremas principales

**[T17.1]** `finSum_zero` / `finSum_succ`

- **Lean4:** `theorem finSum_zero (f : ℕ₀ → ℕ₀) : finSum f 𝟘 = f 𝟘` / `theorem finSum_succ (f : ℕ₀ → ℕ₀) (n : ℕ₀) : finSum f (σ n) = add (finSum f n) (f (σ n))`

**[T17.2]** `finSum_zero_fn`

- **Lean4:** `theorem finSum_zero_fn (n : ℕ₀) : finSum (fun _ => 𝟘) n = 𝟘`
- **Matemática:** Σ_{k=0}^{n} 0 = 0

**[T17.3]** `finSum_add_fn`

- **Lean4:** `theorem finSum_add_fn (f g : ℕ₀ → ℕ₀) (n : ℕ₀) : finSum (fun k => add (f k) (g k)) n = add (finSum f n) (finSum g n)`
- **Matemática:** Σ(f+g) = Σf + Σg

**[T17.4]** `finSum_mul_const` / `finSum_mul_const_right`

- **Lean4:** Distribución de constantes sobre sumas finitas

**[T17.5]** `finSum_le_of_le`

- **Lean4:** `theorem finSum_le_of_le (f g : ℕ₀ → ℕ₀) (h : ∀ k, Le (f k) (g k)) (n : ℕ₀) : Le (finSum f n) (finSum g n)`
- **Matemática:** (∀k, f(k) ≤ g(k)) ⇒ Σf ≤ Σg

**[T17.6]** `finSum_pos`

- **Lean4:** `theorem finSum_pos (f : ℕ₀ → ℕ₀) (h : ∀ k, Lt 𝟘 (f k)) (n : ℕ₀) : Lt 𝟘 (finSum f n)`

**[T17.7]** `finSum_const`

- **Lean4:** `theorem finSum_const (c n : ℕ₀) : finSum (fun _ => c) n = mul (σ n) c`
- **Matemática:** Σ_{k=0}^{n} c = (n+1)·c

**[T17.8]** `sum_binom_eq_pow_two`

- **Lean4:** `theorem sum_binom_eq_pow_two (n : ℕ₀) : finSum (fun k => binom n k) n = pow 𝟚 n`
- **Matemática:** Σ_{k=0}^{n} C(n,k) = 2^n

**[T17.9]** `binomTerm_zero` / `binomTerm_self`

- **Lean4:** `theorem binomTerm_zero (a b n : ℕ₀) : binomTerm a b n 𝟘 = pow b n` / `theorem binomTerm_self (a b n : ℕ₀) : binomTerm a b n n = pow a n`
- **Matemática:** Término k=0 es b^n;  término k=n es a^n

**[T17.10]** `newton_binom` (Binomio de Newton)

- **Lean4:** `theorem newton_binom (a b n : ℕ₀) : pow (add a b) n = finSum (binomTerm a b n) n`
- **Matemática:** (a + b)^n = Σ_{k=0}^{n} C(n,k) · a^k · b^{n−k}

**[T17.11]** `pow_add_split`

- **Lean4:** `theorem pow_add_split (n m k : ℕ₀) : pow n (add m k) = mul (pow n m) (pow n k)`
- **Matemática:** n^{m+k} = n^m · n^k

**[T17.12]** `exists_nm_growth`

- **Lean4:** `theorem exists_nm_growth : ∃ n m, ∀ k, Le 𝟙 k → Lt (pow (add n k) m) (pow n (add m k))`
- **Matemática:** ∃n,m, ∀k≥1, (n+k)^m < n^{m+k}

**[T17.13]** Teoremas adicionales exportados

`finSum_succ_left`, `finSum_reverse`

---

## 18. Isomorph.lean — Módulo de reexportación

*Dependencias: `Arith` y todos los anteriores*

Módulo sin definiciones ni demostraciones nuevas. Reexporta todos los teoremas de isomorfismo Nat ↔ ℕ₀ (vía Λ y Ψ) dispersos en los módulos de la cadena principal.

**Reexporta de `Peano.Axioms`:** `Λ_inj`, `Λ_surj`, `Λ_bij`, `Ψ_inj`, `Ψ_surj`, `Ψ_bij`, `comp_Λ_eq_Ψ`, `comp_Ψ_eq_Λ`, `ΨΛ`, `ΛΨ`, `Ψ_σ_eq_σ_Λ`, `Λ_σ_eq_σ_Ψ`, `Ψ_τ_eq_τ_Λ`, `Λ_τ_eq_τ_Ψ`, `isomorph_0_Λ`, `isomorph_0_Ψ`, `isomorph_σ_Λ`, `isomorph_σ_Ψ`, `isomorph_τ_Λ`, `isomorph_τ_Ψ`, `isomorph_ρ_Ψ`, `isomorph_Λ_ρ`

**Reexporta de `Peano.StrictOrder`:** `isomorph_Λ_lt`, `isomorph_Ψ_lt`

**Reexporta de `Peano.Order`:** `isomorph_Ψ_le`, `isomorph_Λ_le`

**Reexporta de `Peano.Lattice`:** `isomorph_Λ_max`, `isomorph_Λ_min`, `isomorph_Ψ_max`, `isomorph_Ψ_min`

**Reexporta de `Peano.Add`:** `isomorph_Ψ_add`, `isomorph_Λ_add`

**Reexporta de `Peano.Sub`:** `isomorph_Λ_sub`, `isomorph_Ψ_sub`

**Reexporta de `Peano.Mul`:** `isomorph_Ψ_mul`, `isomorph_Λ_mul`

**Reexporta de `Peano.Div`:** `isomorph_Ψ_div`, `isomorph_Ψ_mod`, `isomorph_Λ_div`, `isomorph_Λ_mod`

**Reexporta de `Peano.Pow`:** `isomorph_Ψ_pow`, `isomorph_Λ_pow`

**Reexporta de `Peano.Arith`:** `isomorph_Ψ_gcd`, `isomorph_Λ_gcd`, `isomorph_Ψ_lcm`, `isomorph_Λ_lcm`

---

## 19. Decidable.lean — Módulo de reexportación

*Dependencias: `Order` y anteriores*

Módulo sin definiciones ni demostraciones nuevas. Reúne todas las instancias `Decidable`, funciones booleanas de comparación y sus equivalencias iff.

**Reexporta de `Peano.StrictOrder`:** `blt`, `bgt`, `blt_iff_Lt`, `blt_then_Lt_wp`, `bgt_iff_Gt`, `nblt_iff_nLt`, `nbgt_iff_nGt`, `decidableLt`, `decidableGt`

**Reexporta de `Peano.Order`:** `ble`, `bge`, `ble_iff_Le`, `bge_iff_Ge`, `decidableLe`, `decidableGe`, `bexLe`, `decidableBExLe_of_bool`

### 19.1. Instancias propias

**[I19.1]** `Ord ℕ₀`

- **Lean4:** `instance : Ord ℕ₀ where compare a b := if Lt a b then .lt else if Lt b a then .gt else .eq`
- **Descripción:** Comparación ternaria basada en `Lt`

**[I19.2]** `DecidableRel (@LT.lt ℕ₀ _)`

- **Lean4:** `instance : DecidableRel (@LT.lt ℕ₀ _) := fun a b => Peano.StrictOrder.decidableLt a b`
- **Descripción:** Decidabilidad de `<` vía typeclass `LT`

**[I19.3]** `DecidableRel (@LE.le ℕ₀ _)`

- **Lean4:** `instance : DecidableRel (@LE.le ℕ₀ _) := fun a b => Peano.Order.decidableLe a b`
- **Descripción:** Decidabilidad de `≤` vía typeclass `LE`

---

## 20. Log.lean — `namespace Peano.Log`

*Dependencias: `Div`, `Pow` y anteriores*

Logaritmo entero por debajo con resto: `logMod b n = (k, r)` donde $n = b^k + r$ y $n < b^{k+1}$.
El resto `r = 0` sii `n` es potencia exacta de `b`.

### 20.1. Definiciones [D]

**[D20.1]** `logMod (b n : ℕ₀) : ℕ₀ × ℕ₀`
Devuelve `(⌊log_b(n)⌋, n − b^⌊log_b(n)⌋)`. Recurre sobre `n / b`.
Casos borde: `logMod b 0 = (0,0)`, `logMod b n = (0,0)` si `b ≤ 1`.
*Termina por `div_lt_self` + `isomorph_Ψ_lt`.*

**[D20.2]** `log (b n : ℕ₀) : ℕ₀ := (logMod b n).1`
Piso del logaritmo en base `b` de `n`.

**[D20.3]** `logRem (b n : ℕ₀) : ℕ₀ := (logMod b n).2`
Resto: `n − b^(log b n)`.

### 20.2. Teoremas [T]

**[T20.1]** `log_zero (b : ℕ₀) : log b 𝟘 = 𝟘`

**[T20.2]** `logRem_zero (b : ℕ₀) : logRem b 𝟘 = 𝟘`

**[T20.3]** `log_of_lt {b n : ℕ₀} (h_b : Lt 𝟙 b) (h_n : n ≠ 𝟘) (h_lt : Lt n b) : log b n = 𝟘`
Si $1 < b$ y $0 < n < b$, entonces $\lfloor\log_b n\rfloor = 0$.

**[T20.4]** `logRem_of_lt {b n : ℕ₀} (h_b : Lt 𝟙 b) (h_n : n ≠ 𝟘) (h_lt : Lt n b) : logRem b n = sub n 𝟙`
Si $0 < n < b$, el resto es $n - 1$ (ya que $b^0 = 1$).

**[T20.5]** `log_one {b : ℕ₀} (h_b : Lt 𝟙 b) : log b 𝟙 = 𝟘`

**[T20.6]** `logRem_one {b : ℕ₀} (h_b : Lt 𝟙 b) : logRem b 𝟙 = 𝟘`

**[T20.7]** `logMod_spec {b n : ℕ₀} (h_b : Lt 𝟙 b) (h_n : n ≠ 𝟘) : n = add (pow b (logMod b n).1) (logMod b n).2`
Especificación principal: $n = b^k + r$ con $k = \lfloor\log_b n\rfloor$.

**[T20.8]** `log_upper_bound {b n : ℕ₀} (h_b : Lt 𝟙 b) (h_n : n ≠ 𝟘) : Lt n (pow b (σ (logMod b n).1))`
Cota superior: $n < b^{k+1}$.

---

## 21. Sqrt.lean — `namespace Peano.Sqrt`

*Dependencias: `Mul`, `Sub`, `Pow` y anteriores*

Raíz cuadrada entera por debajo con resto: `sqrtMod n = (k, r)` donde $n = k^2 + r$ y $r < 2k + 1$ (equivalentemente $n < (k+1)^2$).
El resto `r = 0` sii `n` es cuadrado perfecto.

### 21.1. Definiciones [D]

**[D21.1]** `sqrtMod (n : ℕ₀) : ℕ₀ × ℕ₀`
Devuelve `(⌊√n⌋, n − ⌊√n⌋²)`. Recurre sobre `sub n 𝟙`.
Usa la identidad: si `sqrtMod(n−1) = (k, r)` y `σ r = 2k + 1`, devuelve `(σ k, 0)`; si no, `(k, σ r)`.
*Termina por `sub_lt_self` + `isomorph_Ψ_lt`.*

**[D21.2]** `sqrt (n : ℕ₀) : ℕ₀ := (sqrtMod n).1`
Piso de la raíz cuadrada de `n`.

**[D21.3]** `sqrtRem (n : ℕ₀) : ℕ₀ := (sqrtMod n).2`
Resto: $n - \lfloor\sqrt{n}\rfloor^2$.

### 21.2. Teoremas [T]

**[T21.1]** `sqrt_zero : sqrt 𝟘 = 𝟘`

**[T21.2]** `sqrtRem_zero : sqrtRem 𝟘 = 𝟘`

**[T21.3]** `sqrt_one : sqrt 𝟙 = 𝟙`

**[T21.4]** `sqrtRem_one : sqrtRem 𝟙 = 𝟘`

**[T21.5]** `sqrtMod_spec (n : ℕ₀) : n = add (pow (sqrtMod n).1 𝟚) (sqrtMod n).2`
Especificación principal: $n = k^2 + r$ con $k = \lfloor\sqrt{n}\rfloor$.

**[T21.6]** `sqrtRem_lt (n : ℕ₀) : Lt (sqrtMod n).2 (add (add (sqrtMod n).1 (sqrtMod n).1) 𝟙)`
Cota del resto: $r < 2k + 1$.

**[T21.7]** `sqrt_upper_bound (n : ℕ₀) : Lt n (pow (σ (sqrtMod n).1) 𝟚)`
Cota superior: $n < (k+1)^2$. Se deriva de [T21.5] + [T21.6] + la identidad $(k+1)^2 = k^2 + (2k+1)$.

---

## 22. NumberTheory/Totient.lean — `namespace Peano.Totient`

*Dependencias: `Arith` (gcd), `Lists` (lengthₚ, range_from_one), `Primes` (Prime, prime_coprime_or_dvd), `Sub` (sub_one)*

Función de Euler φ(n): cuenta los enteros en {1, …, n} coprimos con n.
Incluye lemas auxiliares sobre `lengthₚ`, `List.filter` y `range_from_one`.

### 22.1. Lemas auxiliares [T]

**[T22.1]** `lengthₚ_append {α} (l₁ l₂ : List α) : lengthₚ (l₁ ++ l₂) = add (lengthₚ l₁) (lengthₚ l₂)`

**[T22.2]** `lengthₚ_singleton {α} (x : α) : lengthₚ [x] = 𝟙`

**[T22.3]** `lengthₚ_range_from_one (n : ℕ₀) : lengthₚ (range_from_one n) = n`

**[T22.4]** `lengthₚ_filter_le {α} (p : α → Bool) (l : List α) : Le (lengthₚ (List.filter p l)) (lengthₚ l)`

**[T22.5]** `filter_append_singleton {α} (p : α → Bool) (l : List α) (x : α) : List.filter p (l ++ [x]) = if p x then List.filter p l ++ [x] else List.filter p l`

**[T22.6]** `filter_all_true {α} (p : α → Bool) (l : List α) (h : ∀ x ∈ l, p x = true) : List.filter p l = l`

**[T22.7]** `mem_range_from_one_pos {k n} (h : k ∈ range_from_one n) : k ≠ 𝟘`

**[T22.8]** `mem_range_from_one_le {k n} (h : k ∈ range_from_one n) : Le k n`

### 22.2. Definiciones [D]

**[D22.1]** `totient (n : ℕ₀) : ℕ₀`
$\varphi(n) := |\{k \in \{1, \ldots, n\} : \gcd(k, n) = 1\}|$.
Implementado como `lengthₚ ((range_from_one n).filter (fun d => decide (gcd d n = 𝟙)))`.

### 22.3. Valores básicos [T]

**[T22.9]** `totient_zero : totient 𝟘 = 𝟘`

**[T22.10]** `totient_one : totient 𝟙 = 𝟙`

**[T22.11]** `totient_two : totient 𝟚 = 𝟙`

### 22.4. Cotas [T]

**[T22.12]** `totient_le (n : ℕ₀) : Le (totient n) n`
$\varphi(n) \leq n$.

**[T22.13]** `totient_pos {n} (h : n ≠ 𝟘) : Le 𝟙 (totient n)`
$\varphi(n) \geq 1$ para $n \geq 1$, ya que $\gcd(1, n) = 1$.

### 22.5. Totient de un primo [T]

**[T22.14]** `totient_prime {p} (hp : Arith.Prime p) : totient p = sub p 𝟙`
$\varphi(p) = p - 1$ para primo $p$: todos los $k \in \{1, ..., p-1\}$ son coprimos con $p$.

### 22.6. Infraestructura [I]

**[I22.1]** `instDecidableEqTotient (n m : ℕ₀) : Decidable (totient n = m)`

---

## 23. NumberTheory/ChineseRemainder.lean — `namespace Peano.CRT`

**Archivo**: `Peano/PeanoNat/NumberTheory/ChineseRemainder.lean`
**Dependencias**: ModEq, Arith (Coprime, bezout_natform), Primes (gcd_eq_one_iff_coprime)

### 23.1. Teorema chino del resto [T]

**[T23.1]** `chinese_remainder {m n : ℕ₀} (hcop : Coprime m n) (a b : ℕ₀) : ∃ x : ℕ₀, ModEq m x a ∧ ModEq n x b`

- **Tipo**: `Coprime m n → ∀ (a b : ℕ₀), ∃ x, ModEq m x a ∧ ModEq n x b`
- **Descripción**: Teorema chino del resto (existencia). Si `m` y `n` son coprimos, para cualesquiera `a` y `b` existe `x` con `x ≡ a [MOD m]` y `x ≡ b [MOD n]`.
- **Estrategia**: Usa la identidad de Bézout (`bezout_natform`) para construir un inverso modular, luego construye explícitamente el testigo `x = add a (mul (mul c s) m)` donde `c = sub (add b n) (mod a n)`.

---

## 24. ListsAndSets/FSetFunction.lean — `namespace Peano.FSetFunction`

**Archivo**: `Peano/PeanoNat/ListsAndSets/FSetFunction.lean`
**Dependencias**: `ListsAndSets/List`, `ListsAndSets/FSet`, `ListsAndSets/FSetFSet`, `Mul`
**Dependido por**: `Combinatorics/Perm`, `Combinatorics/Group`
**Estado**: ✅ sin `sorry` en este módulo

Módulo polimórfico sobre tipos `α`, `β` con `[DecidableEq]` y `[LT]` que desarrolla:

1. funciones entre conjuntos finitos (`MapOn`),
2. imagen/preimagen/fibras,
3. cardinalidad por inyección/sobreyeción/biyeción,
4. principio del palomar,
5. endomorfismos y permutaciones,
6. tablas de funciones (`FunTable`, `FunPerm`).

### 24.1. Definiciones base [D]

**[D24.1]** `MapOn` (polimórfica)

- **Lean4:**

  ```
  structure MapOn {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
      (A : FSet α) (B : FSet β) where
    toFun : α → β
    map_carrier : ∀ a, a ∈ A.elems → toFun a ∈ B.elems
  ```

- **Matemática:** aplicación total $f : A \to B$ entre conjuntos finitos con prueba de cierre.

**[D24.2]** `InjectiveOn`, `SurjectiveOn`, `MapOn.Injective`, `MapOn.Surjective`, `MapOn.Bijective`

**[D24.3]** `MapOn.comp`, `MapOn.id`

**[D24.4]** `MapOn.Im`, `MapOn.PreIm`, `MapOn.fiber`, `MapOn.restrict`

**[D24.5]** `BinOpOn`

- **Lean4:** `structure BinOpOn (A : FSet α) where toFun : α → α → α; map_carrier : ...`

**[D24.6]** `Perm` (permutación como `MapOn A A` biyectiva)

**[D24.7]** `FunTable`, `FunPerm`

### 24.2. Teoremas estructurales [T]

**[T24.1]** Composición e identidad

- `MapOn.comp_injective`, `MapOn.comp_surjective`, `MapOn.comp_bijective`, `MapOn.comp_assoc`
- `MapOn.id_injective`, `MapOn.id_surjective`, `MapOn.id_bijective`, `MapOn.comp_id`, `MapOn.id_comp`
- `MapOn.injective_of_comp_injective`, `MapOn.surjective_of_comp_surjective`

**[T24.2]** Inversas

- `MapOn.rightInverse`, `MapOn.rightInverse_prop`, `MapOn.rightInverse_injective`
- `MapOn.leftInverse`, `MapOn.leftInverse_prop`, `MapOn.leftInverse_surjective`
- `MapOn.injective_of_has_leftInverse`, `MapOn.injective_iff_has_leftInverse`
- `MapOn.surjective_of_has_rightInverse`, `MapOn.surjective_iff_has_rightInverse`
- `MapOn.inverse`, `MapOn.inverse_left_prop`, `MapOn.inverse_right_prop`
- `MapOn.inverse_injective`, `MapOn.inverse_surjective`, `MapOn.inverse_bijective`
- `MapOn.inverse_inverse`, `MapOn.comp_inverse_left`, `MapOn.comp_inverse_right`

### 24.3. Cardinalidad y palomar [T]

**[T24.3]** Imagen/cardinalidad

- `card_image_of_injective`, `injective_of_card_image`
- `card_image_of_surjective`, `surjective_of_card_image`
- `card_le_of_injective`, `card_le_of_surjective`

**[T24.4]** Igualdad de cardinalidad

- `card_eq_of_injections`, `card_eq_of_surjections`
- `MapOn.Bijective.card_eq`
- `MapOn.injective_iff_surjective_of_card_eq`
- `MapOn.injective_iff_bijective_of_card_eq`
- `MapOn.surjective_iff_bijective_of_card_eq`

**[T24.5]** Principio del palomar

- `not_injective_of_card_lt`
- `collision_of_card_lt`

**[T24.6]** Nuevo (2026-04-17): conteo por fibras uniformes

- **Lean4:**

  ```
  theorem card_eq_mul_of_uniform_fibers {α β : Type}
    [DecidableEq α] [LT α] [DecidableEq β] [LT β] [StrictOrder.IrreflLT β]
    {A : FSet α} {B : FSet β}
    (f : MapOn A B)
    (k : ℕ₀) (h_uniform : ∀ b, b ∈ B.elems → (f.fiber b).card = k) :
    A.card = mul k B.card
  ```

- **Matemática:** si todas las fibras de $f : A \to B$ tienen cardinal $k$, entonces
  $|A| = k\,|B|$.
- **Dependencias internas clave:** `MapOn.fiber`, `sorted_nodup`, `lengthₚ`, `mul_succ`, `add_succ`, `succ_add`.

### 24.4. Preimagen/fibras/restricción [T]

**[T24.7]** `MapOn.mem_PreIm_iff`, `MapOn.PreIm_full`, `MapOn.card_PreIm_le`

**[T24.8]** `MapOn.mem_fiber_iff`, `MapOn.card_fiber_le_one_of_injective`

**[T24.9]** `MapOn.restrict_injective`, `MapOn.mem_Im_restrict`

### 24.5. Endomorfismos y permutaciones [T]

**[T24.10]** Endomorfismos (`f : A → A`)

- `MapOn.endo_injective_iff_surjective`
- `MapOn.endo_injective_iff_bijective`
- `MapOn.endo_surjective_iff_bijective`
- `MapOn.endo_bijective_of_injective`
- `MapOn.endo_bijective_of_surjective`
- `MapOn.endo_leftInverse_eq_inverse`
- `MapOn.endo_leftInverse_right_prop`
- `MapOn.endo_rightInverse_eq_inverse`
- `MapOn.endo_rightInverse_left_prop`

**[T24.11]** `Perm`

- `Perm.injective`, `Perm.surjective`, `Perm.id`, `Perm.comp`
- `Perm.comp_id_fn`, `Perm.id_comp_fn`
- `Perm.inv`, `Perm.inv_left`, `Perm.inv_right`, `Perm.inv_inv`
- `Perm.comp_inv_left`, `Perm.comp_inv_right`, `Perm.comp_assoc`

### 24.6. FunTable/FunPerm [D/T]

**[D24.8]** `FunTable` (tabla de imágenes)

- Campos: `table`, `len_eq`, `mem_all`.
- Operaciones exportadas: `FunTable.apply`, `FunTable.applyElem`, `FunTable.applyElem_mem`, `FunTable.id`, `FunTable.comp`.

**[D24.9]** `FunPerm` (tabla con `List.Perm table A.elems`)

- Operaciones exportadas: `FunPerm.id`, `FunPerm.applyElem_injective`.

### 24.7. Inventario de export (proyección completa)

Bloque `export Peano.FSetFunction (...)` actualizado y proyectado al completo, incluyendo:

1. `card_eq_mul_of_uniform_fibers` (nuevo encabezando el bloque),
2. toda la API `MapOn` (§1–§3f),
3. preimagen/fibras/restricción,
4. `BinOpOn`, `FunTable`, `FunPerm`,
5. auxiliares reexportados: `sorted_nodup`, `nodup_map_of_inj_on`, `perm_of_nodup_subset_same_length`, `perm_map_of_injective_on_nodup`.

### 24.8. Archivo auxiliar reciente

**Archivo**: `temp_check2.lean`

- Contenido actual: `import Peano.PeanoNat.ListsAndSets.List` + `#check @List.length_erase_of_mem`.
- Estado: archivo de sondeo/verificación interactiva (sin definiciones, sin teoremas, no exporta símbolos).
- Impacto en REFERENCE: no añade API nueva del proyecto.

## 24A. ListsAndSets/FSet.lean — actualización reciente (2026-04-16)

**Archivo**: `Peano/PeanoNat/ListsAndSets/FSet.lean`
**Namespace**: `Peano.FSet` (con lema privado en `Peano`)

### 24A.1. Cambios proyectados [D/T]

**[D24A.1]** Alias exportados

- `ℕ₀FSet := FSet ℕ₀` (añadido)
- `ℕ₁FSet := FSet ℕ₁` (añadido)
- `ℕ₂FSet := FSet ℕ₂` (ya existente)

**[T24A.1]** Extensionalidad semántica para `FSet ℕ₀`

- **Lean4:**

  ```
  theorem FSet.eq_of_mem_iff {s₁ s₂ : FSet ℕ₀}
    (h : ∀ z : ℕ₀, z ∈ s₁.elems ↔ z ∈ s₂.elems) : s₁ = s₂
  ```

- **Matemática:** si dos conjuntos finitos de `ℕ₀` tienen la misma pertenencia elemento a elemento,
  entonces son iguales.
- **Dependencias:** `FSet.ext` + lema privado de unicidad de listas ordenadas estrictas.

**[T24A.2]** Lema privado de canonicidad (no exportado)

- `sorted_nodup_unique_list` en `namespace Peano`:
  igualdad de listas `List.Pairwise (· < ·)` por equivalencia de pertenencia.

### 24A.2. Export block de FSet

El bloque `export Peano.FSet (...)` ya incluye `FSet.eq_of_mem_iff`, `ℕ₀FSet`, `ℕ₁FSet` y
permanece consistente con la API pública actual del módulo.

---

## 25. Combinatorics/Group.lean — `namespace Peano.Group`

**Archivo**: `Peano/PeanoNat/Combinatorics/Group.lean`
**Dependencias**: `FSet`, `FSetFunction`
**Dependido por**: `Orbit`, `Action`
**Tamaño**: ~480 líneas
**Sorry activos**: 2 (en `cyclicSubgroup` y `cyclicSubgroup'`, bloqueados en B2.3 `order`)

### 25.1. § 4 — `FinGroup`: estructura de grupo finito [D]

**[D25.1]** `FinGroup` (estructura)

```lean
structure FinGroup where
  carrier : ℕ₀FSet
  op      : BinOpOn carrier
  id      : ℕ₀
  inv     : MapOn carrier carrier
  id_in   : id ∈ carrier.elems
  op_assoc : ∀ a b c, a ∈ carrier → b ∈ carrier → c ∈ carrier → op (op a b) c = op a (op b c)
  op_id    : ∀ a, a ∈ carrier → op a id = a ∧ op id a = a
  op_inv   : ∀ a, a ∈ carrier → op a (inv a) = id ∧ op (inv a) a = id
```

- **Matemática:** Grupo finito con soporte `ℕ₀FSet`, operación `op`, neutro `id`, inversa `inv`.
- **Computable:** Sí (todos los campos son funciones computables o `ℕ₀FSet`).

### 25.2. § 4b — Lemas auxiliares [T]

**[T25.1]** `id_unique (G : FinGroup) (e' : ℕ₀) (h_e'_in) (h_is_id) : e' = G.id`

- El neutro es único.

**[T25.2]** `inv_mem (G : FinGroup) {a : ℕ₀} (ha) : G.inv a ∈ G.carrier.elems`

**[T25.3]** `op_mem (G : FinGroup) {a b : ℕ₀} (ha) (hb) : G.op a b ∈ G.carrier.elems`

**[T25.4]** `op_cancel_left (G : FinGroup) {a x y : ℕ₀} (ha) (hx) (hy) (h : G.op a x = G.op a y) : x = y`

**[T25.5]** `op_cancel_right (G : FinGroup) {a x y : ℕ₀} (ha) (hx) (hy) (h : G.op x a = G.op y a) : x = y`

**[T25.6]** `inv_inv_eq (G : FinGroup) {a : ℕ₀} (ha) : G.inv (G.inv a) = a`

**[T25.7]** `inv_id_eq (G : FinGroup) : G.inv G.id = G.id`

**[T25.8]** `inv_op_eq (G : FinGroup) {a b : ℕ₀} (ha) (hb) : G.inv (G.op a b) = G.op (G.inv b) (G.inv a)`

- Anti-homomorfismo del inverso.

**[T25.9]** `inv_unique (G : FinGroup) {a b : ℕ₀} (ha) (hb) (h : G.op a b = G.id ∧ G.op b a = G.id) : b = G.inv a`

### 25.3. § 4c — `gpow`: potencia iterada [D/T]

**[D25.2]** `gpow (G : FinGroup) (g : ℕ₀) : ℕ₀ → ℕ₀`

```lean
def gpow (G : FinGroup) (g : ℕ₀) : ℕ₀ → ℕ₀
  | .zero   => G.id
  | .succ n => G.op (gpow G g n) g
```

- **Matemática:** g^n = id si n=0; g^(n+1) = g^n · g
- **Computable:** Sí

**[T25.10]** `@[simp] gpow_zero (G : FinGroup) (g : ℕ₀) : gpow G g 𝟘 = G.id`

**[T25.11]** `@[simp] gpow_succ (G : FinGroup) (g : ℕ₀) (n : ℕ₀) : gpow G g (σ n) = G.op (gpow G g n) g`

**[T25.12]** `gpow_one (G : FinGroup) (g : ℕ₀) (hg) : gpow G g 𝟙 = g`

**[T25.13]** `gpow_mem (G : FinGroup) {g : ℕ₀} (hg) : ∀ n : ℕ₀, gpow G g n ∈ G.carrier.elems`

- Por inducción: g^0 = id ∈ G; g^(n+1) = g^n · g ∈ G.

**[T25.14]** `gpow_add (G : FinGroup) {g : ℕ₀} (hg) (m n : ℕ₀) : gpow G g (add m n) = G.op (gpow G g m) (gpow G g n)`

- g^(m+n) = g^m · g^n.

**[T25.15]** `gpow_comm_single (G : FinGroup) {g : ℕ₀} (hg) (n : ℕ₀) : G.op g (gpow G g n) = G.op (gpow G g n) g`

- g · g^n = g^n · g (la potencia conmuta con la base). Demostrado via `gpow_add` + `add_comm`.

**[T25.16]** `gpow_inv (G : FinGroup) {g : ℕ₀} (hg) : ∀ n : ℕ₀, gpow G (G.inv g) n = G.inv (gpow G g n)`

- (g⁻¹)^n = (g^n)⁻¹. Demostrado por inducción usando `gpow_comm_single` + `inv_op_eq`.

### 25.4. § 5 — `Subgroup`: subgrupo [D/T]

**[D25.3]** `Subgroup (G : FinGroup)` (estructura)

```lean
structure Subgroup (G : FinGroup) where
  carrier    : ℕ₀FSet
  nonempty   : ∃ a, a ∈ carrier.elems
  subset     : ∀ a, a ∈ carrier.elems → a ∈ G.carrier.elems
  op_closed  : ∀ a b, a ∈ carrier.elems → b ∈ carrier.elems → G.op a b ∈ carrier.elems
  id_in      : G.id ∈ carrier.elems
  inv_closed : ∀ a, a ∈ carrier.elems → G.inv a ∈ carrier.elems
```

**[T25.17]** `Subgroup.op_inv_closed (G : FinGroup) (H : Subgroup G) (a b : ℕ₀) (ha) (hb) : G.op a (G.inv b) ∈ H.carrier.elems`

- Criterio de un paso (consecuencia directa de las clausuras).

**[D25.4]** `subgroup_of_op_inv_closed (G : FinGroup) (S : ℕ₀FSet) (h_sub) (h_ne) (h_cl) : Subgroup G`

- Recíproco: si S ⊆ G, S ≠ ∅, y a·b⁻¹ ∈ S para todo a,b ∈ S, entonces S es subgrupo.

### 25.5. § 5b — Subgrupos especiales [D]

**[D25.5]** `trivialSubgroup (G : FinGroup) : Subgroup G`

- El subgrupo `{G.id}`. Carrier = `ℕ₀FSet.singleton G.id`.

**[D25.6]** `improperSubgroup (G : FinGroup) : Subgroup G`

- El subgrupo `G`. Carrier = `G.carrier`.

**[D25.7]** `Subgroup.IsTrivial {G : FinGroup} (H : Subgroup G) : Prop := H.carrier.card = 𝟙`

**[D25.8]** `Subgroup.IsProper {G : FinGroup} (H : Subgroup G) : Prop := H.carrier.card ≠ G.carrier.card`

### 25.6. § 5c — Subgrupo cíclico [D] ⚠ 2 sorry

**[D25.9]** `cyclicSubgroup (G : FinGroup) (g : ℕ₀) (hg) : Subgroup G` ⚠ sorry

- Vía `subgroup_of_op_inv_closed` con `cyclicCarrier G g`.
- Sorry en el cierre a·b⁻¹: necesita `gpow_mod_order` (B2.3 pendiente).

**[D25.10]** `cyclicSubgroup' (G : FinGroup) (g : ℕ₀) (hg) : Subgroup G` ⚠ sorry

- Construcción directa (Subgroup con todos los campos).
- `op_closed`: sorry en índice `add m n` fuera del rango (necesita `order G g`).
- `inv_closed`: sorry en reducción de `gpow G (G.inv g) n` a `gpow G g k` (necesita `order G g`).
- **Dependencia**: ambos sorry se resolverán cuando esté `order G g hg` (B2.3).

**Nota de implementación (subgrupo cíclico)**: `cyclicCarrier G g` está definido como
`ℕ₀FSet.filter (fun x => Fin₀Set(σ|G|).elems.any (fun i => decide (gpow G g i = x))) G.carrier`.
Esto es correcto pero el testigo de índice `add m n` puede exceder `σ|G|`. La solución
es usar `mod (add m n) (order G g hg)` como testigo una vez que `order` esté disponible.

### 25.7. § 5d — Normalidad [D/T]

**[D25.11]** `Subgroup.IsNormal {G : FinGroup} (N : Subgroup G) : Prop`

- `∀ g n, g ∈ G.carrier → n ∈ N.carrier → G.op (G.op g n) (G.inv g) ∈ N.carrier`

**[T25.18]** `trivialSubgroup_normal (G : FinGroup) : (trivialSubgroup G).IsNormal`

**[T25.19]** `improperSubgroup_normal (G : FinGroup) : (improperSubgroup G).IsNormal`

### 25.8. § 5e — Intersección de subgrupos [D/T]

**[D25.12]** `Subgroup.inter {G : FinGroup} (H₁ H₂ : Subgroup G) : Subgroup G`

- Carrier = `ℕ₀FSet.filter (fun x => decide (x ∈ H₁.carrier) && decide (x ∈ H₂.carrier)) G.carrier`
- Todos los campos demostrados sin sorry. Patrón: `rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]`.

**[T25.20]** `Subgroup.inter_subset_left {G : FinGroup} (H₁ H₂ : Subgroup G) {a : ℕ₀} (ha) : a ∈ H₁.carrier.elems`

**[T25.21]** `Subgroup.inter_subset_right {G : FinGroup} (H₁ H₂ : Subgroup G) {a : ℕ₀} (ha) : a ∈ H₂.carrier.elems`

**[T25.22]** `Subgroup.inter_normal_of_normal {G : FinGroup} {H₁ H₂ : Subgroup G} (hn₁ : H₁.IsNormal) (hn₂ : H₂.IsNormal) : (H₁.inter H₂).IsNormal`

### 25.9. § 6 — `GroupHom`: homomorfismo [D]

**[D25.13]** `GroupHom (G H : FinGroup)` (estructura)

```lean
structure GroupHom (G H : FinGroup) where
  map     : MapOn G.carrier H.carrier
  map_op  : ∀ a b, a ∈ G.carrier → b ∈ G.carrier → map (G.op a b) = H.op (map a) (map b)
  map_id  : map G.id = H.id
  map_inv : ∀ a, a ∈ G.carrier → map (G.inv a) = H.inv (map a)
```

- **Matemática:** Homomorfismo de grupos finitos que preserva op, id, inv.
- **Computable:** Sí.
- **Estado:** Estructura definida. Im, ker, comp y resultados de teoría de homomorfismos son trabajo futuro (B4).

---

## 44. Combinatorics/GroupTheory/Sylow/Sylow.lean — `namespace Peano.GroupTheory`

*Dependencias: `Action`, `Cosets`, `Totient`, `Group`, `Arith`, `Primes`*

**Estado:** 🔄 En progreso (3 sorrys). *Última actualización: 2026-04-23.*

### 44.1. Definiciones base [D]

**[D44.1]** `dvd_card (p : ℕ₀) (H : ℕ₀FSet) : Prop`

**[D44.2]** `pow_dvd_card (p k : ℕ₀) (H : ℕ₀FSet) : Prop`

**[D44.3]** `isPSubgroup (G : FinGroup) (H : Subgroup G) (p : ℕ₀) : Prop`

**[D44.4]** `isSylowExponent (G : FinGroup) (p n : ℕ₀) : Prop`

**[D44.5]** `isSylowSubgroup (G : FinGroup) (H : Subgroup G) (p : ℕ₀) : Prop`

**[D44.6]** `Vector (α : Type) (n : ℕ₀) : Type` — subtipo `{ l : List α // lengthₚ l = n }`. *Computable.* Instancias exportadas: `vectorDecEq : DecidableEq (Vector ℕ₀ n)`, `vectorLT : LT (Vector ℕ₀ n)`, `vectorDecLT : DecidableRel (@LT.lt (Vector ℕ₀ n) _)`.

### 44.2. Teorema de Cauchy (McKay) [T]

**Lemas de subgrupo cíclico (privados, sin sorry):**

- `card_pos_of_mem_aux`, `order_dvd_of_pow_eq_id`, `order_eq_prime_of_pow`, `gpow_lt_p_mem_cyclic`, `cyclicSubgroup_card_eq_prime`.

**Infraestructura de Listas/Tuplas para McKay (privada, sin sorry):**

- `listProd (G : FinGroup) : List ℕ₀ → ℕ₀`, `listProd_nil`, `listProd_cons`, `listProd_mem`, `listProd_append`, `listProd_singleton`.
- `rotateList {α} : List α → List α` — rotación cíclica de un paso.
- `lengthₚ_rotateList`, `rotateList_fixed_all_eq`.
- `rotateVector {α} {n} (v : Vector α n) : Vector α n` — versión tipada de `rotateList`.
- `listProdVector (G : FinGroup) {n} (v : Vector ℕ₀ n) : ℕ₀`.
- `allVectorsList (elems : List ℕ₀) : (n : ℕ₀) → List (Vector ℕ₀ n)` — generador combinatorio de `n`-tuplas.
- `listProd_rotate_eq_id`.
- `gpow_id_eq_id`.

**Operación de desplazamiento de McKay (privada, sin sorry):**

- `mckayShiftList (G : FinGroup) : List ℕ₀ → List ℕ₀` — desplaza y añade inverso del producto.
- `mckayShift (G : FinGroup) {n} (v : Vector ℕ₀ n) : Vector ℕ₀ n` — versión tipada.
- `lengthₚ_mckayShiftList`, `mckayShiftList_mem` (preservación de G), `append_singleton_inj`, `mckayShiftList_inj` (inyectividad).

**Infraestructura de rotación iterada (privada, sin sorry):**

- `nthRotate {α} : ℕ₀ → List α → List α` — `k`-ésima iteración de `rotateList`.
- `nthRotate_succ_comm : nthRotate k (rotateList l) = rotateList (nthRotate k l)`.
- `nthRotate_add : nthRotate (k₁ + k₂) l = nthRotate k₁ (nthRotate k₂ l)`.
- `nthRotate_length_self : nthRotate (lengthₚ l) l = l` — periodicidad natural.
- `nthRotate_mul_period`, `nthRotate_append_general`, `nthRotate_fixed_all`.
- `gcd_eq_one_of_pos_lt_prime (k p : ℕ₀) (hk_pos hk_lt : _) (hp : Prime p) : gcd k p = 𝟙`.
- `nthRotate_one_fixed_of_gcd_one` — si `gcd k p = 1` y `nthRotate k l = l` entonces `rotateList l = l`.
- `vector_eq_of_rotateVector_eq_fixed` — si `v` es fijo y `rotateVector w = v` entonces `w = v`.
- `gpow_comm_left`, `listProd_all_eq_gpow`.

**Argumento de McKay sobre Vector ℕ₀ p (privado, sin sorry):**

- `mckay_orbit_remove (p) (hp) (S) (v ∈ S) (hv : rotateVector v ≠ v) (hnodup) (hrot) : ∃ S', S'.Nodup ∧ (∀ w ∈ S', rotateVector w ∈ S') ∧ |S| = |S'| + p ∧ fix(S) = fix(S')` — extrae la órbita de `v` bajo `rotateVector` (de tamaño exactamente `p`) y devuelve el complemento `S'`. Sub-lemas internos: `orb_inj`, `orbit_no_fixed`, `rl_inj`, `orbit_preimage`, `orbit_closed_rv`, `nodup_sub_len`, `filter_part`. **Cerrado en sesión 2026-04-22.**
- `mckay_orbit_count (p) (hp) (T) (hT_nodup) (hT_rot) : ∃ k, |T| = |fix(T)| + p·k` — el cardinal de `T` es el de sus puntos fijos más un múltiplo de `p`. Usa `mckay_orbit_remove` por inducción bien fundada. **Sin sorry.**

**Lemas auxiliares para mckay_p_dvd_powEqId (privados, sin sorry, sesión 2026-04-23):**

- `listProd_append_inv_eq_id (G) {l} (hl) : listProd G (l ++ [G.inv (listProd G l)]) = G.id` — el producto de una lista seguida de su inverso es el neutro.
- `list_split_last {α} : ∀ l ≠ [], ∃ ini last, l = ini ++ [last]` — toda lista no vacía se puede separar en prefijo e último elemento.
- `list_σn_split_last {α} (l) (n) (hl : lengthₚ l = σ n) : ∃ ini last, l = ini ++ [last] ∧ lengthₚ ini = n` — separación con longitud del prefijo.
- `replicate_cons_append {α} (a) : ∀ n, List.replicate n a ++ [a] = a :: List.replicate n a` — commutativity of singleton append for replicate.
- `rotateList_replicate_pos {α} (a) : ∀ n ≠ 0, rotateList (List.replicate n a) = List.replicate n a` — las listas constantes son puntos fijos de `rotateList`.
- `all_eq_then_replicate {α} (a) : ∀ l, (∀ x ∈ l, x = a) → l = List.replicate l.length a` — si todos los elementos son iguales, la lista es `replicate`.
- `pow_dvd_of_dvd {p a : ℕ₀} (h : p ∣ a) {n} (hn : n ≠ 𝟘) : p ∣ pow a n` — la divisibilidad se eleva a potencias (abierto con `open Peano.Arith`).

**[T44.1]** `mckay_p_dvd_powEqId (G : FinGroup) (p : ℕ₀) (hp : Prime p) (hdvd : ∃ t, p·t = |G|) : p ∣ |{g ∈ G | g^p = e}|`

- **Sin sorry.** Estrategia: sea `T = {v ∈ G^p | ∏ v = e}`. Se demuestra `|T| = |G|^(p-1)` por biyección (`fwd : Vector ℕ₀ (p-1) → Vector ℕ₀ p`, `u ↦ u ++ [inv(∏u)]`). `p ∣ |T|` por `pow_dvd_of_dvd`. Se aplica `mckay_orbit_count` para obtener `|T| = |fix(T)| + p·k`. Se demuestra `|fix(T)| = |F|` por biyección (`g ↦ replicate p g`). Conclusión por `divides_sub`. **Cerrado en sesión 2026-04-23.**

**[T44.2]** `cauchy_minimal (G : FinGroup) (p : ℕ₀) (hp : Prime p) (hdvd : ∃ t, p·t = |G|) : ∃ K : Subgroup G, K.carrier.card = p`

- **Sin sorry.** Completamente cerrado: usa `mckay_p_dvd_powEqId` (ahora demostrado) para obtener `g ∈ F` con `g ≠ e`, luego `cyclicSubgroup_card_eq_prime`. **Cerrado en sesión 2026-04-23.**

### 44.3. Teoremas de Sylow [T]

**[T44.3]** `sylow_lift_from_cauchy (hC : ...) (G : FinGroup) (p m : ℕ₀) ... : ∃ H : Subgroup G, H.carrier.card = p ^ (σ m)`

- Demostrado por inducción fuerte sobre `|G|`, generalizada sobre todos los FinGroups.
- Caso 1: `|G| = p^(m+1)` → subgrupo impropio.
- Caso 2: ∃ subgrupo propio M con `p^(m+1) | |M|` → HI sobre `subgroupToFinGroup G M`.
- Caso 3: ningún subgrupo propio es divisible por `p^(m+1)` → `sylow_center_step` (axioma temporal).
- Usa helpers privados: `subgroupToFinGroup`, `subgroupOfSubgroup`, `sylow_center_step`.

**[T44.4]** `sylow_first (G : FinGroup) (p n : ℕ₀) (hp : Prime p) (hdvd : pow_dvd_card p n G.carrier) : ∃ H : Subgroup G, H.carrier.card = p ^ n`

- Demostrado por inducción: caso base `n=0` (subgrupo trivial), paso inductivo usa `sylow_lift_from_cauchy`.

**[T44.5]** `sylow_second (G : FinGroup) (p : ℕ₀) (H K : Subgroup G) ...` ⚠️ sorry

**[T44.6]** `sylow_third (G : FinGroup) (p : ℕ₀) (hp : Prime p) (sylows : ...) ... : (n_p ≡ 1 mod p) ∧ (n_p ∣ |G|)` ⚠️ sorry

> **Secciones pendientes** (módulos sin sección en este documento):
> §26 `List.lean`, §27 `ListList.lean`, §28 `FSet.lean`, §29 `FSetFSet.lean`,
> §30 `NumberSets.lean`, §31 `ModEq.lean`, §32 `NumberTheory/Fermat.lean`,
> §33 `Combinatorics/Summation.lean`, §34 `Combinatorics/Product.lean`,
> §35 `Combinatorics/Fibonacci.lean`, §36 `Combinatorics/Counting.lean`,
> §37 `Digits.lean`, §38 `Pairing.lean`,
> §39 `Combinatorics/Perm.lean`, §40 `Combinatorics/Sign.lean`,
> §41 `Combinatorics/Orbit.lean`, §42 `GroupTheory/Action.lean`,
> §43 `GroupTheory/Sylow/Cosets.lean`.

<!-- AUTO-UPDATE-2026-04-17-START -->
## Actualizacion de estado - 2026-04-17

- Estado del build: compila en el estado actual de la rama makingdecidable.
- Lagrange: cerrado en Sylow/Cosets con conteo por fibras y clases de cosets.
- GroupAction: sorries cerrados en orbit_stabilizer y orbits_partition.
- Sylow I: caso base n=0 cerrado; estructura separada en paso de Cauchy y paso de elevacion.
- Nota temporal: cauchy_minimal se apoya en un axioma explicito cauchy_minimal_axiom para continuar el desarrollo.
- Pendientes activos en Sylow: sylow_second, sylow_third. (sylow_lift_from_cauchy cerrado con axioma).
- Objetivo proximo: reemplazar cauchy_minimal_axiom por demostracion interna y completar Sylow I.

<!-- AUTO-UPDATE-2026-04-17-END -->

<!-- AUTO-UPDATE-2026-04-20-START -->
## Actualizacion de estado - 2026-04-20

- Estado del build: 52 jobs, 0 errores, 4 sorry warnings (todos en Sylow.lean).
- Vector, allVectorsList, mckayShiftList, mckayShift completamente definidos y con instancias DecidableEq/LT/DecidableRel.
- mckayShiftList_mem (preservacion) y mckayShiftList_inj (inyectividad) demostrados sin sorry.
- cauchy_minimal formalizado condicionalmente: unico sorry es mckay_p_dvd_powEqId.
- Sorries vigentes: mckay_p_dvd_powEqId (~498), sylow_lift_from_cauchy (~577), sylow_second (~610), sylow_third (~627).
- D44.6 anadido en REFERENCE.md: Vector con sus tres instancias publicas.

<!-- AUTO-UPDATE-2026-04-20-END -->

<!-- AUTO-UPDATE-2026-04-22-START -->
## Actualizacion de estado - 2026-04-22

- Estado del build: 52 jobs, 0 errores, 4 sorry warnings (sin cambio).
- mckay_orbit_remove demostrado completamente sin sorry (sesion 2026-04-22).
- mckay_orbit_count ya compilaba; confirmado sin sorry.
- Seccion 44.2 de REFERENCE.md ampliada: rotateVector, nthRotate y familia, gcd_eq_one_of_pos_lt_prime, nthRotate_one_fixed_of_gcd_one, vector_eq_of_rotateVector_eq_fixed, mckay_orbit_remove, mckay_orbit_count.
- Sorries vigentes: mckay_p_dvd_powEqId (~1190), sylow_lift_from_cauchy (~1273), sylow_second (~1307), sylow_third (~1324).
- Proximo objetivo: mckay_p_dvd_powEqId (conectar mckay_orbit_count con el conteo sobre G^p).

<!-- AUTO-UPDATE-2026-04-22-END -->

<!-- AUTO-UPDATE-2026-04-23-START -->
## Actualizacion de estado - 2026-04-23

- Estado del build: 52 jobs, 0 errores, 2 sorry warnings (sylow_second, sylow_third en Sylow.lean).
- mckay_p_dvd_powEqId demostrado completamente sin sorry (sesion 2026-04-23, manana).
- cauchy_minimal ahora completamente cerrado.
- sylow_lift_from_cauchy demostrado por induccion fuerte sobre |G|, con axioma temporal sylow_center_step para el caso duro (sin subgrupos propios divisibles por p^(m+1)), que requiere ecuacion de clases + Cauchy + grupo cociente o argumento de Wielandt.
- Nuevos helpers privados en Sylow.lean: subgroupToFinGroup (convierte Subgroup G en FinGroup), subgroupOfSubgroup (convierte Subgroup (subgroupToFinGroup G M) en Subgroup G), sylow_center_step (axioma para el caso duro de la induccion de Sylow).
- Sorries vigentes: sylow_second (~1791), sylow_third (~1808).
- Axiomas no-sorry vigentes: sylow_center_step (en Sylow.lean).
- Proximo objetivo: sylow_second (conjugacion de p-subgrupos de Sylow).

<!-- AUTO-UPDATE-2026-04-23-END -->
