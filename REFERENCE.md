# Referencia Técnica — Proyecto Peano

**Última actualización:** 2026-03-04 12:00
**Autor**: Julián Calderón Almendros

> Documentación técnica de referencia para IA y desarrolladores Lean 4. **No** es documentación de usuario final.
> Contiene únicamente lo que está demostrado o construido en los archivos `.lean` (requisito 8).
> **Proyectar** un `.lean` en este archivo = actualizar las secciones correspondientes con todo lo exportable (no privado).

---

## 0. Estructura del Proyecto (requisitos 1–3)

### 0.1. Módulos `.lean`

| Módulo (ruta) | Namespace | Docs | Depende de | Dependido por |
|---|---|---|---|---|
| `Peano.lean` | — | Sí | todos los módulos de `PeanoNatLib/` | — |
| `PeanoNatLib/PeanoNatLib.lean` | `Peano` | Sí | `Init.Classical` | todos |
| `PeanoNatLib/PeanoNatAxioms.lean` | `Peano.Axioms` | Sí | `PeanoNatLib` | `StrictOrder`, `Order`, `MaxMin`, `WellFounded`, `Add`, `Sub`, `Mul`, `Div`, `Arith` |
| `PeanoNatLib/PeanoNatStrictOrder.lean` | `Peano.StrictOrder` | Sí | `PeanoNatLib`, `PeanoNatAxioms` | `Order`, `MaxMin`, `WellFounded`, `Add`, `Sub`, `Mul`, `Div`, `Arith` |
| `PeanoNatLib/PeanoNatOrder.lean` | `Peano.Order` | Sí | `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder` | `MaxMin`, `WellFounded`, `Add`, `Sub`, `Mul`, `Div`, `Arith` |
| `PeanoNatLib/PeanoNatMaxMin.lean` | `Peano.MaxMin` | Sí | `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder` | `WellFounded`, `Add`, `Sub`, `Mul`, `Div`, `Arith` |
| `PeanoNatLib/PeanoNatWellFounded.lean` | `Peano.WellFounded` | Sí | `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `Init.Classical` | `Add`, `Sub`, `Mul`, `Div`, `Arith` |
| `PeanoNatLib/PeanoNatAdd.lean` | `Peano.Add` | Sí | `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `PeanoNatWellFounded` | `Sub`, `Mul`, `Div`, `Arith` |
| `PeanoNatLib/PeanoNatSub.lean` | `Peano.Sub` | Sí | `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `PeanoNatWellFounded`, `PeanoNatAdd` | `Mul`, `Div`, `Arith` |
| `PeanoNatLib/PeanoNatMul.lean` | `Peano.Mul` | Sí | `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `PeanoNatWellFounded`, `PeanoNatAdd`, `PeanoNatSub` | `Div`, `Arith` |
| `PeanoNatLib/PeanoNatDiv.lean` | `Peano.Div` | Sí | `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `PeanoNatWellFounded`, `PeanoNatAdd`, `PeanoNatSub`, `PeanoNatMul` | `Arith` |
| `PeanoNatLib/PeanoArith.lean` | `Peano.Arith` | Sí | todos los anteriores, `Init.Classical` | — |

### 0.2. Espacios de nombres y relaciones (requisito 3)

| Namespace | Módulo | Sub-namespace de |
|---|---|---|
| `Peano` | `PeanoNatLib.lean` | — (raíz del proyecto) |
| `Peano.Axioms` | `PeanoNatAxioms.lean` | `Peano` |
| `Peano.StrictOrder` | `PeanoNatStrictOrder.lean` | `Peano` |
| `Peano.Order` | `PeanoNatOrder.lean` | `Peano` |
| `Peano.MaxMin` | `PeanoNatMaxMin.lean` | `Peano` |
| `Peano.WellFounded` | `PeanoNatWellFounded.lean` | `Peano` |
| `Peano.Add` | `PeanoNatAdd.lean` | `Peano` |
| `Peano.Sub` | `PeanoNatSub.lean` | `Peano` |
| `Peano.Mul` | `PeanoNatMul.lean` | `Peano` |
| `Peano.Div` | `PeanoNatDiv.lean` | `Peano` |
| `Peano.Arith` | `PeanoArith.lean` | `Peano` |

### 0.3. Notaciones registradas (requisito 4.4)

| Símbolo | Tipo | Prioridad | Namespace | Módulo |
|---|---|---|---|---|
| `σ n` | prefijo | `max` | `Peano` | `PeanoNatLib.lean` |
| `𝟘` | constante | — | `Peano` | `PeanoNatLib.lean` |
| `𝟙` | constante | — | `Peano` | `PeanoNatLib.lean` |
| `𝟚` | constante | — | `Peano` | `PeanoNatLib.lean` |
| `𝟛` | constante | — | `Peano` | `PeanoNatLib.lean` |
| `∃¹ x, p x` | macro cuantificador (4 variantes) | — | `Peano` | `PeanoNatLib.lean` |
| `n + m` | infijo, instancia `Add ℕ₀` | ~65 | `Peano.Add` | `PeanoNatAdd.lean` |
| `a + b` (alias) | `notation a "+" b => Peano.Add.add a b` | — | `Peano.Add` | `PeanoNatAdd.lean` |
| `a +l b` | `notation a "+l" b => Peano.Add.add_l a b` | — | `Peano.Add` | `PeanoNatAdd.lean` |
| `n - m` | infijo | 65 | `Peano.Sub` | `PeanoNatSub.lean` |
| `n -( h ) m` | notación con prueba | 65 | `Peano.Sub` | `PeanoNatSub.lean` |
| `n * m` | infijo | 70 | `Peano.Mul` | `PeanoNatMul.lean` |
| `a / b` | notación | — | `Peano.Div` | `PeanoNatDiv.lean` |
| `a % b` | notación | — | `Peano.Div` | `PeanoNatDiv.lean` |
| `n < m` | instancia `LT ℕ₀` | — | `Peano.StrictOrder` | `PeanoNatStrictOrder.lean` |
| `n ≤ m` | instancia `LE ℕ₀` | — | `Peano.Order` | `PeanoNatOrder.lean` |
| `a ∣ b` | infijo | 50 | `Peano.Arith` | `PeanoArith.lean` |
| `a ∤ b` | notación negación | 50 | `Peano.Arith` | `PeanoArith.lean` |
| `a ∣₁ b` | infijo | 50 | `Peano.Arith` | `PeanoArith.lean` |

---

## 1. PeanoNatLib.lean — `namespace Peano`

*Dependencias: `Init.Classical`*

### 1.1. Definiciones

**[D1.1]** `ExistsUnique`
- **Lean4:** `def ExistsUnique {α : Type} (p : α → Prop) : Prop := ∃ x, (p x ∧ ∀ y, p y → y = x)`
- **Matemática:** ∃¹x ∈ α, p(x)  ⟺  ∃x, (p(x) ∧ ∀y, p(y) ⇒ y = x)
- **Computable:** No (Prop)
- **Notación:** `∃¹ x, p x` | `∃¹ (x), p x` | `∃¹ (x : T), p x` | `∃¹ x : T, p x` — macro, 4 variantes

**[D1.2]** `ℕ₀`
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

**[D1.3]** `ℕ₁`
- **Lean4:** `def ℕ₁ : Type := {n : ℕ₀ // n ≠ ℕ₀.zero}`
- **Matemática:** ℕ₁ = {n ∈ ℕ₀ | n ≠ 0}
- **Computable:** Sí

**[D1.4]** `ℕ₂`
- **Lean4:** `def ℕ₂ : Type := {n : ℕ₁ // n.val ≠ ℕ₀.succ ℕ₀.zero}`
- **Matemática:** ℕ₂ = {n ∈ ℕ₁ | n ≠ 1}
- **Computable:** Sí

**[D1.5]** Constantes numéricas
- **Lean4:**
  ```
  def cero  : ℕ₀ := ℕ₀.zero    -- notación: 𝟘
  def one   : ℕ₀ := σ 𝟘         -- notación: 𝟙
  def two   : ℕ₀ := σ one       -- notación: 𝟚
  def three : ℕ₀ := σ two       -- notación: 𝟛
  ```
- **Matemática:** 0, 1 = σ(0), 2 = σ(1), 3 = σ(2)
- **Computable:** Sí

**[D1.6]** `Λ` y `Ψ` (isomorfismo con `Nat`)
- **Lean4:**
  ```
  def Λ (n : Nat) : ℕ₀   -- recursión sobre Nat; Nat.zero ↦ 𝟘, Nat.succ k ↦ σ(Λ k)
  def Ψ (n : ℕ₀)  : Nat   -- recursión sobre ℕ₀
  ```
- **Matemática:** Λ: ℕ → ℕ₀, Ψ: ℕ₀ → ℕ; isomorfismo de semiestructuras
- **Computable:** Sí (ambos)

**[D1.7]** `choose` (elección clásica)
- **Lean4:** `noncomputable def choose {α : Type} {p : α → Prop} (h : ∃ x, p x) : α`
- **Matemática:** Operador ε: dado ∃x, p(x), elige un testigo
- **Computable:** No (noncomputable; usa `Classical.indefiniteDescription`)
- **Dependencias:** `Init.Classical`

**[D1.8]** `ExistsUnique.exists`
- **Lean4:** `def ExistsUnique.exists {α : Type} {p : α → Prop} (h : ExistsUnique p) : ∃ x, p x`
- **Computable:** Sí

**[D1.9]** `choose_unique`
- **Lean4:** `noncomputable def choose_unique {α : Type} {p : α → Prop} (h : ExistsUnique p) : α`
- **Matemática:** Elección del único testigo de ∃¹x, p(x)
- **Computable:** No
- **Dependencias:** `choose`, `ExistsUnique.exists`

**[D1.10]** Funciones auxiliares de igualdad funcional
- **Lean4:**
  ```
  def idℕ₀   (n : ℕ₀) : ℕ₀
  def idNat  (n : Nat) : Nat
  def EqFnGen {α β} (f g : α → β)       : Prop  -- ∀ x, f x = g x
  def Comp    {α β} (f : α→β) (g : β→α) : Prop  -- ∀ x, g(f x) = x
  def EqFn    {α}   (f g : ℕ₀ → α)      : Prop
  def EqFn2   {α}   (f g : ℕ₀×ℕ₀ → α) : Prop
  def EqFnNat {α}   (f g : Nat → α)     : Prop
  ```
- **Computable:** Sí (identidades y definiciones proposicionales)

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

## 2. PeanoNatAxioms.lean — `namespace Peano.Axioms`

*Dependencias: `PeanoNatLib`*

Los axiomas de Peano se demuestran como teoremas a partir de la estructura inductiva de `ℕ₀`.

### 2.1. Definiciones auxiliares

**[D2.1]** `is_zero`, `is_succ`, `return_branch`
- **Lean4:**
  ```
  def is_zero      : ℕ₀ → Prop   -- True iff n = 𝟘
  def is_succ      : ℕ₀ → Prop   -- True iff ∃k, n = σ k
  def return_branch : ℕ₀ → Prop   -- is_zero | is_succ según constructor
  ```
- **Computable:** No (Prop)

**[D2.2]** `succ_inj` (alias)
- **Lean4:** `def succ_inj (n m : ℕ₀) := AXIOM_succ_inj n m`
- **Computable:** No (Prop → Prop)

### 2.2. Axiomas (demostrados como teoremas), ordenados de declaración

**[A1]** `AXIOM_zero_is_an_PeanoNat`
- **Lean4:** `theorem AXIOM_zero_is_an_PeanoNat : is_zero 𝟘`
- **Matemática:** is_zero(0)
- **Dependencias:** `is_zero`

**[A2]** `AXIOM_succ_is_an_PeanoNat`
- **Lean4:** `theorem AXIOM_succ_is_an_PeanoNat (n : ℕ₀) : is_succ (σ n)`
- **Matemática:** ∀n ∈ ℕ₀, is_succ(σ n)
- **Dependencias:** `is_succ`

**[A3]** `AXIOM_cero_neq_succ`
- **Lean4:** `theorem AXIOM_cero_neq_succ : ∀ (k : ℕ₀), 𝟘 ≠ σ k`
- **Matemática:** ∀k ∈ ℕ₀, 0 ≠ σ(k)

**[A4]** `AXIOM_zero_notin_ima_succ`
- **Lean4:** `theorem AXIOM_zero_notin_ima_succ : ∀ (n : ℕ₀), 𝟘 ≠ σ n`
- **Matemática:** 0 ∉ Im(σ)

**[A5]** `AXIOM_succ_is_funct_forall_n_in_PeanoNat`
- **Lean4:** `theorem AXIOM_succ_is_funct_forall_n_in_PeanoNat : ∀ (n : ℕ₀), ∃ (k : ℕ₀), k = σ n`
- **Matemática:** ∀n ∈ ℕ₀, ∃k ∈ ℕ₀, k = σ(n)

**[A6]** `AXIOM_uniqueness_on_image`
- **Lean4:** `theorem AXIOM_uniqueness_on_image (n m : ℕ₀) : n = m → σ n = σ m`
- **Matemática:** n = m ⇒ σ(n) = σ(m)  (univocidad de σ)

**[A7]** `AXIOM_succ_inj`
- **Lean4:** `theorem AXIOM_succ_inj (n m : ℕ₀) : σ n = σ m → n = m`
- **Matemática:** σ(n) = σ(m) ⇒ n = m  (inyectividad de σ)

**[A8]** `AXIOM_induction_on_PeanoNat`
- **Lean4:**
  ```
  theorem AXIOM_induction_on_PeanoNat
      (P : ℕ₀ → Prop) (h_0 : P 𝟘)
      (h_succ : ∀ n, P n → P (σ n)) : ∀ n, P n
  ```
- **Matemática:** P(0) ∧ (∀n, P(n) ⇒ P(σ n)) ⇒ ∀n ∈ ℕ₀, P(n)

### 2.3. Teoremas auxiliares exportados

**[T2.1]** `noConfusion`
- **Lean4:** `theorem noConfusion (n : ℕ₀) : (is_zero n → ¬ is_succ n) ∧ (is_succ n → ¬ is_zero n)`
- **Matemática:** is_zero(n) e is_succ(n) son mutuamente excluyentes

**[T2.2]** `cero_neq_succ`
- **Lean4:** `theorem cero_neq_succ : ∀ (n : ℕ₀), 𝟘 ≠ σ n`
- **Matemática:** ∀n ∈ ℕ₀, 0 ≠ σ(n)

**[T2.3]** `succ_neq_zero`
- **Lean4:** `theorem succ_neq_zero (n : ℕ₀) : σ n ≠ 𝟘`
- **Matemática:** ∀n ∈ ℕ₀, σ(n) ≠ 0

**[T2.4]** `succ_inj_wp`
- **Lean4:** `theorem succ_inj_wp {n m : ℕ₀} (h_neq : ¬ n = m) : σ n ≠ σ m`
- **Matemática:** n ≠ m ⇒ σ(n) ≠ σ(m)

**[T2.5]** `succ_inj_neg`
- **Lean4:** `theorem succ_inj_neg : ∀ n m : ℕ₀, σ n ≠ σ m → n ≠ m`
- **Matemática:** σ(n) ≠ σ(m) ⇒ n ≠ m

**[T2.6]** `succ_inj_pos_wp`
- **Lean4:** `theorem succ_inj_pos_wp {n m : ℕ₀} (h_succeq : σ n = σ m) : n = m`
- **Matemática:** σ(n) = σ(m) ⇒ n = m

---

## 3. PeanoNatStrictOrder.lean — `namespace Peano.StrictOrder`

*Dependencias: `PeanoNatLib`, `PeanoNatAxioms`*

### 3.1. Definiciones

**[D3.1]** `Lt`
- **Lean4:**
  ```
  def Lt (n m : ℕ₀) : Prop :=
    match n, m with
    | _,      ℕ₀.zero => False
    | ℕ₀.zero, σ _   => True
    | σ n',    σ m'  => Lt n' m'
  ```
- **Matemática:** Lt(n, 0) = ⊥;  Lt(0, σm) = ⊤;  Lt(σn, σm) = Lt(n, m)
- **Computable:** No (Prop); par booleano: `BLt`
- **Terminado por:** recursión estructural sobre ambos argumentos
- **Notación:** `n < m` (instancia `LT ℕ₀`)

**[D3.2]** `BLt` (par booleano de `Lt`)
- **Lean4:**
  ```
  def BLt (n m : ℕ₀) : Bool :=
    match n, m with
    | _,       ℕ₀.zero => false
    | ℕ₀.zero, σ _    => true
    | σ n',    σ m'   => BLt n' m'
  ```
- **Computable:** Sí

**[D3.3]** `Gt`
- **Lean4:**
  ```
  def Gt (n m : ℕ₀) : Prop :=
    match n, m with
    | ℕ₀.zero, _      => False
    | σ _,  ℕ₀.zero   => True
    | σ n',  σ m'     => Gt n' m'
  ```
- **Matemática:** Gt(n, m) ⟺ Lt(m, n)
- **Computable:** No; par booleano: `BGt`

**[D3.4]** `BGt` (par booleano de `Gt`)
- **Lean4:** `def BGt (n m : ℕ₀) : Bool` — recursión análoga a `BLt`
- **Computable:** Sí

**[D3.5]** Instancias de decisión y clase de orden
- **Lean4:**
  ```
  instance : LT ℕ₀ := ⟨Lt⟩
  instance decidableLt (n m : ℕ₀) : Decidable (Lt n m)
  instance decidableGt (n m : ℕ₀) : Decidable (Gt n m)
  ```

### 3.2. Teoremas principales (orden estricto total)

**[T3.1]** `lt_irrefl`
- **Lean4:** `theorem lt_irrefl (n : ℕ₀) : ¬(Lt n n)`
- **Matemática:** ∀n ∈ ℕ₀, ¬(n < n)

**[T3.2]** `lt_asymm`
- **Lean4:** `theorem lt_asymm (n m : ℕ₀) : Lt n m → ¬(Lt m n)`
- **Matemática:** n < m ⇒ ¬(m < n)

**[T3.3]** `lt_trans`
- **Lean4:** `theorem lt_trans (n m k : ℕ₀) : Lt n m → Lt m k → Lt n k`
- **Matemática:** n < m ∧ m < k ⇒ n < k

**[T3.4]** `trichotomy`
- **Lean4:** `theorem trichotomy (n m : ℕ₀) : (Lt n m) ∨ (n = m) ∨ (Lt m n)`
- **Matemática:** ∀n, m ∈ ℕ₀, n < m ∨ n = m ∨ m < n

**[T3.5]** `lt_iff_lt_σ_σ`
- **Lean4:** `theorem lt_iff_lt_σ_σ (n m : ℕ₀) : Lt n m ↔ Lt (σ n) (σ m)`
- **Matemática:** n < m ⟺ σ(n) < σ(m)

**[T3.6]** `lt_0_n`
- **Lean4:** `theorem lt_0_n (n : ℕ₀) (h : n ≠ 𝟘) : Lt 𝟘 n`
- **Matemática:** n ≠ 0 ⇒ 0 < n

**[T3.7]** `lt_zero`
- **Lean4:** `theorem lt_zero (n : ℕ₀) : ¬ Lt n 𝟘`
- **Matemática:** ∀n ∈ ℕ₀, ¬(n < 0)

**[T3.8]** `lt_then_lt_succ`
- **Lean4:** `theorem lt_then_lt_succ (n m : ℕ₀) : Lt n m → Lt n (σ m)`
- **Matemática:** n < m ⇒ n < σ(m)

**[T3.9]** `not_lt_and_not_eq_implies_gt`
- **Lean4:** `theorem not_lt_and_not_eq_implies_gt (a b : ℕ₀) : ¬ Lt a b → ¬ (a = b) → Lt b a`
- **Matemática:** ¬(a < b) ∧ a ≠ b ⇒ b < a

---

## 4. PeanoNatOrder.lean — `namespace Peano.Order`

*Dependencias: `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`*

### 4.1. Definiciones

**[D4.1]** `Le`
- **Lean4:** `def Le (n m : ℕ₀) : Prop := Lt n m ∨ n = m`
- **Matemática:** n ≤ m ⟺ n < m ∨ n = m
- **Computable:** No (Prop); par decidible: instancia `decidableLe`
- **Notación:** `n ≤ m` (instancia `LE ℕ₀`)
- **Dependencias:** `Lt`

**[D4.2]** `Ge`
- **Lean4:** `def Ge (n m : ℕ₀) : Prop := Lt m n ∨ n = m`
- **Matemática:** n ≥ m ⟺ m < n ∨ n = m

**[D4.3]** `Le'` (definición alternativa recursiva)
- **Lean4:**
  ```
  def Le' (n m : ℕ₀) : Prop :=
    match n, m with
    | 𝟘,   _    => True
    | σ _, 𝟘   => False
    | σ n', σ m' => Le' n' m'
  ```
- **Matemática:** Definición recursiva equivalente de ≤

**[D4.4]** Instancias
- **Lean4:**
  ```
  instance : LE ℕ₀ := ⟨Le⟩
  instance decidableLe (n m : ℕ₀) : Decidable (Le n m)
  instance decidableGe (n m : ℕ₀) : Decidable (Ge n m)
  ```

### 4.2. Teoremas principales (orden total no estricto)

**[T4.1]** `le_refl`
- **Lean4:** `theorem le_refl (n : ℕ₀) : Le n n`
- **Matemática:** ∀n ∈ ℕ₀, n ≤ n

**[T4.2]** `le_antisymm`
- **Lean4:** `theorem le_antisymm (n m : ℕ₀) : Le n m → Le m n → n = m`
- **Matemática:** n ≤ m ∧ m ≤ n ⇒ n = m

**[T4.3]** `le_trans`
- **Lean4:** `theorem le_trans (n m k : ℕ₀) : Le n m → Le m k → Le n k`
- **Matemática:** n ≤ m ∧ m ≤ k ⇒ n ≤ k

**[T4.4]** `le_total`
- **Lean4:** `theorem le_total (n m : ℕ₀) : Le n m ∨ Le m n`
- **Matemática:** ∀n, m ∈ ℕ₀, n ≤ m ∨ m ≤ n

**[T4.5]** `zero_le`
- **Lean4:** `theorem zero_le (n : ℕ₀) : Le 𝟘 n`
- **Matemática:** ∀n ∈ ℕ₀, 0 ≤ n

**[T4.6]** `le_self_add_r`
- **Lean4:** `theorem le_self_add_r (n m : ℕ₀) : Le n (add n m)`
- **Matemática:** ∀n, m ∈ ℕ₀, n ≤ n + m
- **Dependencias:** `add`

**[T4.7]** `lt_of_lt_of_le`
- **Lean4:** `theorem lt_of_lt_of_le {a b c : ℕ₀} (h₁ : Lt a b) (h₂ : Le b c) : Lt a c`
- **Matemática:** a < b ∧ b ≤ c ⇒ a < c

**[T4.8]** `lt_imp_le`
- **Lean4:** `theorem lt_imp_le {n m : ℕ₀} : Lt n m → Le n m`
- **Matemática:** n < m ⇒ n ≤ m

**[T4.9]** `le_iff_lt_or_eq`
- **Lean4:** `theorem le_iff_lt_or_eq (n m : ℕ₀) : Le n m ↔ Lt n m ∨ n = m`
- **Matemática:** n ≤ m ⟺ n < m ∨ n = m

**[T4.10]** `succ_le_succ_then`
- **Lean4:** `theorem succ_le_succ_then {n m : ℕ₀} : Le (σ n) (σ m) → Le n m`
- **Matemática:** σ(n) ≤ σ(m) ⇒ n ≤ m

**[T4.11]** `lt_succ_iff_le`
- **Lean4:** `theorem lt_succ_iff_le (n m : ℕ₀) : Lt n (σ m) ↔ Le n m`
- **Matemática:** n < σ(m) ⟺ n ≤ m

**[T4.12]** `le_zero_eq`
- **Lean4:** `theorem le_zero_eq (n : ℕ₀) (h : Le n 𝟘) : n = 𝟘`
- **Matemática:** n ≤ 0 ⇒ n = 0

**[T4.13]** `not_succ_le_zero`
- **Lean4:** `theorem not_succ_le_zero (n : ℕ₀) : ¬ Le (σ n) 𝟘`
- **Matemática:** ∀n ∈ ℕ₀, ¬(σ(n) ≤ 0)

**[T4.14]** `le_not_lt` (antisimetría estricto/no-estricto)
- **Lean4:** `theorem le_not_lt {n m : ℕ₀} (h : Le n m) : ¬ Lt m n`
- **Matemática:** n ≤ m ⇒ ¬(m < n)

**[T4.15]** `well_ordering_principle` (en este módulo, sobre `Le`)
- **Lean4:** `theorem well_ordering_principle {P : ℕ₀ → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, Lt m n → ¬P m`
- **Matemática:** Todo conjunto no vacío de ℕ₀ tiene un elemento minimal para <
- **Dependencias:** `well_founded_lt` (PeanoNatWellFounded)

---

## 5. PeanoNatMaxMin.lean — `namespace Peano.MaxMin`

*Dependencias: `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`*

### 5.1. Definiciones

**[D5.1]** `max`
- **Lean4:**
  ```
  def max (n m : ℕ₀) : ℕ₀ :=
    match n, m with
    | 𝟘,    m    => m
    | n,    𝟘    => n
    | σ n', σ m' =>
        if n' = m' then σ m'
        else if BLt n' m' then σ m'
        else σ n'
  ```
- **Matemática:** max: ℕ₀ × ℕ₀ → ℕ₀
- **Computable:** Sí (usa `BLt`)
- **Par booleano:** Sí (usa `BLt` internamente)

**[D5.2]** `min`
- **Lean4:**
  ```
  def min (n m : ℕ₀) : ℕ₀ :=
    match n, m with
    | 𝟘,    _    => 𝟘
    | _,    𝟘    => 𝟘
    | σ n', σ m' =>
        if n' = m' then σ n'
        else if BLt n' m' then σ n'
        else σ m'
  ```
- **Matemática:** min: ℕ₀ × ℕ₀ → ℕ₀
- **Computable:** Sí

**[D5.3]** `min_max` / `max_min`
- **Lean4:**
  ```
  def min_max (n m : ℕ₀) : ℕ₀ × ℕ₀   -- devuelve (min n m, max n m)
  def max_min (n m : ℕ₀) : ℕ₀ × ℕ₀   -- devuelve (max n m, min n m)
  ```
- **Computable:** Sí

### 5.2. Teoremas principales (retícula distributiva)

**[T5.1]** `max_idem` / `min_idem`
- **Lean4:** `theorem max_idem (n : ℕ₀) : max n n = n` / `theorem min_idem (n : ℕ₀) : min n n = n`
- **Matemática:** max(n,n) = n;  min(n,n) = n

**[T5.2]** `max_comm` / `min_comm`
- **Lean4:** `theorem max_comm (n m : ℕ₀) : max n m = max m n` / `theorem min_comm (n m : ℕ₀) : min n m = min m n`
- **Matemática:** max(n,m) = max(m,n);  min(n,m) = min(m,n)

**[T5.3]** `max_assoc` / `min_assoc`
- **Lean4:** `theorem max_assoc (n m k : ℕ₀) : max (max n m) k = max n (max m k)`
  `theorem min_assoc (n m k : ℕ₀) : min (min n m) k = min n (min m k)`
- **Matemática:** Asociatividad de max y min

**[T5.4]** `le_max_left` / `le_max_right`
- **Lean4:** `theorem le_max_left (n m : ℕ₀) : Le n (max n m)` / `theorem le_max_right (n m : ℕ₀) : Le m (max n m)`
- **Matemática:** n ≤ max(n,m);  m ≤ max(n,m)

**[T5.5]** `min_le_left` / `min_le_right`
- **Lean4:** `theorem min_le_left (n m : ℕ₀) : Le (min n m) n` / `theorem min_le_right (n m : ℕ₀) : Le (min n m) m`
- **Matemática:** min(n,m) ≤ n;  min(n,m) ≤ m

**[T5.6]** `max_distrib_min`
- **Lean4:** `theorem max_distrib_min (n m k : ℕ₀) : max n (min m k) = min (max n m) (max n k)`
- **Matemática:** max(n, min(m,k)) = min(max(n,m), max(n,k))

**[T5.7]** `min_distrib_max`
- **Lean4:** `theorem min_distrib_max (n m k : ℕ₀) : min n (max m k) = max (min n m) (min n k)`
- **Matemática:** min(n, max(m,k)) = max(min(n,m), min(n,k))

**[T5.8]** `eq_max_min_then_eq`
- **Lean4:** `theorem eq_max_min_then_eq (n m : ℕ₀) : (max n m = min n m) → (n = m)`
- **Matemática:** max(n,m) = min(n,m) ⇒ n = m

---

## 6. PeanoNatWellFounded.lean — `namespace Peano.WellFounded`

*Dependencias: `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `Init.Classical`*

### 6.1. Definiciones

**[D6.1]** Instancia `SizeOf ℕ₀`
- **Lean4:** `instance : SizeOf ℕ₀ where sizeOf := Ψ`
- **Descripción:** Conecta la relación `Lt` con la terminación de Lean vía el isomorfismo Ψ: ℕ₀ → Nat
- **Computable:** Sí (Ψ es computable)

### 6.2. Teoremas principales

**[T6.1]** `acc_lt_wf`
- **Lean4:** `theorem acc_lt_wf (n : ℕ₀) : Acc Lt n`
- **Matemática:** ∀n ∈ ℕ₀, n es accesible respecto a <
- **Dependencias:** `Lt`, `lt_succ_iff_le`, `le_iff_lt_or_eq`

**[T6.2]** `well_founded_lt`
- **Lean4:** `theorem well_founded_lt : WellFounded Lt`
- **Matemática:** < es una relación bien fundada en ℕ₀ (no existen cadenas descendentes infinitas)
- **Dependencias:** `acc_lt_wf`

**[T6.3]** `well_ordering_principle`
- **Lean4:**
  ```
  theorem well_ordering_principle (P : ℕ₀ → Prop) (h_nonempty : ∃ k, P k) :
      ∃¹ (n : ℕ₀), (P n) ∧ ∀ (m : ℕ₀), (P m) → (Le n m)
  ```
- **Matemática:** (∃k, P(k)) ⇒ ∃¹n, (P(n) ∧ ∀m, P(m) ⇒ n ≤ m)
- **Dependencias:** `well_founded_lt`, `ExistsUnique`, `Le`

**[T6.4]** `isomorph_Ψ_lt`
- **Lean4:** `theorem isomorph_Ψ_lt (a b : ℕ₀) : Lt a b ↔ Ψ a < Ψ b`
- **Matemática:** a < b en ℕ₀ ⟺ Ψ(a) < Ψ(b) en ℕ
- **Dependencias:** `Ψ`, `Lt`

---

## 7. PeanoNatAdd.lean — `namespace Peano.Add`

*Dependencias: `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `PeanoNatWellFounded`*

### 7.1. Definiciones

**[D7.1]** `add`
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
- **Notación:** `n + m` (instancia `Add ℕ₀`, prioridad hereda de la typeclass); alias `notation a "+" b`

**[D7.2]** `add_l` (suma recursiva sobre el argumento izquierdo)
- **Lean4:**
  ```
  def add_l (n m : ℕ₀) : ℕ₀ :=
    match n with
    | 𝟘    => m
    | σ n' => σ (add n' m)
  ```
- **Matemática:** Definición alternativa de la suma (recursión sobre el primer argumento)
- **Computable:** Sí
- **Terminado por:** recursión estructural sobre `n`
- **Notación:** `n +l m`

### 7.2. Teoremas principales

**[T7.1]** `add_zero`
- **Lean4:** `theorem add_zero (n : ℕ₀) : add n 𝟘 = n`
- **Matemática:** n + 0 = n

**[T7.2]** `zero_add`
- **Lean4:** `theorem zero_add (n : ℕ₀) : add 𝟘 n = n`
- **Matemática:** 0 + n = n

**[T7.3]** `add_succ`
- **Lean4:** `theorem add_succ (n m : ℕ₀) : add n (σ m) = σ (add n m)`
- **Matemática:** n + σ(m) = σ(n + m)

**[T7.4]** `add_one`
- **Lean4:** `theorem add_one (n : ℕ₀) : add n 𝟙 = σ n`
- **Matemática:** n + 1 = σ(n)

**[T7.5]** `add_comm`
- **Lean4:** `theorem add_comm (n m : ℕ₀) : add n m = add m n`
- **Matemática:** ∀n, m ∈ ℕ₀, n + m = m + n

**[T7.6]** `add_assoc`
- **Lean4:** `theorem add_assoc (n m k : ℕ₀) : add n (add m k) = add (add n m) k`
- **Matemática:** ∀n, m, k ∈ ℕ₀, n + (m + k) = (n + m) + k

**[T7.7]** `add_cancelation`
- **Lean4:** `theorem add_cancelation (n m k : ℕ₀) : add n m = add n k → m = k`
- **Matemática:** n + m = n + k ⇒ m = k

**[T7.8]** `le_iff_exists_add`
- **Lean4:** `theorem le_iff_exists_add (a b : ℕ₀) : Le a b ↔ ∃ p, b = add a p`
- **Matemática:** a ≤ b ⟺ ∃p ∈ ℕ₀, b = a + p
- **Dependencias:** `Le`, `add`

---

## 8. PeanoNatSub.lean — `namespace Peano.Sub`

*Dependencias: `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `PeanoNatWellFounded`, `PeanoNatAdd`*

### 8.1. Definiciones

**[D8.1]** `subₕₖ` (resta con prueba)
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
- **Terminado por:** `termination_by n` + `Nat.lt_succ_self`
- **Notación:** `n -( h ) m` (prioridad 65)
- **Dependencias:** `Le`, `succ_le_succ_then`, `le_zero_eq`

**[D8.2]** `sub` (resta truncada / monus)
- **Lean4:**
  ```
  def sub (n m : ℕ₀) : ℕ₀ :=
    if h : Le m n then subₕₖ n m h else 𝟘
  ```
- **Matemática:** n ∸ m = n − m si m ≤ n, else 0
- **Computable:** Sí (usa instancia `decidableLe`)
- **Par booleano:** Sí, via `decidableLe`
- **Notación:** `n - m` (infijo, prioridad 65)
- **Dependencias:** `subₕₖ`, `Le`, `decidableLe`

### 8.2. Teoremas principales

**[T8.1]** `sub_zero`
- **Lean4:** `theorem sub_zero (n : ℕ₀) : sub n 𝟘 = n`
- **Matemática:** n ∸ 0 = n

**[T8.2]** `zero_sub`
- **Lean4:** `theorem zero_sub (n : ℕ₀) : sub 𝟘 n = 𝟘`
- **Matemática:** 0 ∸ n = 0

**[T8.3]** `sub_k_add_k`
- **Lean4:** `theorem sub_k_add_k (n k : ℕ₀) (h : Le k n) : add (sub n k) k = n`
- **Matemática:** k ≤ n ⇒ (n ∸ k) + k = n

**[T8.4]** `add_k_sub_k`
- **Lean4:** `theorem add_k_sub_k (n k : ℕ₀) : sub (add n k) k = n`
- **Matemática:** (n + k) ∸ k = n

**[T8.5]** `le_sub_iff_add_le_of_le`
- **Lean4:** `theorem le_sub_iff_add_le_of_le (n m k : ℕ₀) (h : Le m n) : Le k (sub n m) ↔ Le (add m k) n`
- **Matemática:** m ≤ n ⇒ (k ≤ n ∸ m ⟺ m + k ≤ n)

**[T8.6]** `sub_pos_iff_lt`
- **Lean4:** `theorem sub_pos_iff_lt (n m : ℕ₀) : Le 𝟙 (sub n m) ↔ Lt m n`
- **Matemática:** 1 ≤ n ∸ m ⟺ m < n

**[T8.7]** `sub_lt_self`
- **Lean4:** `theorem sub_lt_self (a b : ℕ₀) (h_le : Le b a) (h_b_ne : b ≠ 𝟘) : Lt (sub a b) a`
- **Matemática:** b ≤ a ∧ b ≠ 0 ⇒ a ∸ b < a
- **Dependencias:** `sub`, `Lt`, `Le`

---

## 9. PeanoNatMul.lean — `namespace Peano.Mul`

*Dependencias: `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `PeanoNatWellFounded`, `PeanoNatAdd`, `PeanoNatSub`*

### 9.1. Definiciones

**[D9.1]** `mul`
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
- **Dependencias:** `add`

### 9.2. Teoremas principales

**[T9.1]** `mul_zero` / `zero_mul`
- **Lean4:** `theorem mul_zero (n : ℕ₀) : mul n 𝟘 = 𝟘` / `theorem zero_mul (n : ℕ₀) : mul 𝟘 n = 𝟘`
- **Matemática:** n·0 = 0;  0·n = 0

**[T9.2]** `mul_one` / `one_mul`
- **Lean4:** `theorem mul_one (n : ℕ₀) : mul n 𝟙 = n` / `theorem one_mul (m : ℕ₀) : mul 𝟙 m = m`
- **Matemática:** n·1 = n;  1·m = m

**[T9.3]** `mul_succ` / `succ_mul`
- **Lean4:** `theorem mul_succ (n m : ℕ₀) : mul n (σ m) = add (mul n m) n`
  `theorem succ_mul (n m : ℕ₀) : mul (σ n) m = add (mul n m) m`
- **Matemática:** n·σ(m) = n·m + n;  σ(n)·m = n·m + m

**[T9.4]** `mul_comm`
- **Lean4:** `theorem mul_comm (n m : ℕ₀) : mul n m = mul m n`
- **Matemática:** ∀n, m ∈ ℕ₀, n·m = m·n

**[T9.5]** `mul_assoc`
- **Lean4:** `theorem mul_assoc (m n k : ℕ₀) : mul (mul m n) k = mul m (mul n k)`
- **Matemática:** ∀m, n, k ∈ ℕ₀, (m·n)·k = m·(n·k)

**[T9.6]** `mul_ldistr`
- **Lean4:** `theorem mul_ldistr (m n k : ℕ₀) : mul m (add n k) = add (mul m n) (mul m k)`
- **Matemática:** m·(n + k) = m·n + m·k

**[T9.7]** `mul_eq_zero`
- **Lean4:** `theorem mul_eq_zero (n m : ℕ₀) : mul n m = 𝟘 ↔ n = 𝟘 ∨ m = 𝟘`
- **Matemática:** n·m = 0 ⟺ n = 0 ∨ m = 0

**[T9.8]** `mul_sub`
- **Lean4:** `theorem mul_sub (c a b : ℕ₀) (h_lt : Lt b a) : mul c (sub a b) = sub (mul c a) (mul c b)`
- **Matemática:** b < a ⇒ c·(a ∸ b) = c·a ∸ c·b
- **Dependencias:** `sub`, `mul`, `Lt`

**[T9.9]** `archimedean_property`
- **Lean4:** `theorem archimedean_property {n : ℕ₀} (m : ℕ₀) (h_n_pos : Lt 𝟘 n) : ∃ j, Lt m (mul j n)`
- **Matemática:** n > 0 ⇒ ∀m ∈ ℕ₀, ∃j ∈ ℕ₀, m < j·n

**[T9.10]** `exists_unique_mul_le_and_lt_succ_mul`
- **Lean4:**
  ```
  theorem exists_unique_mul_le_and_lt_succ_mul
      (n m : ℕ₀) (h_n_pos : Lt 𝟘 n) :
      ∃¹ k, Le (mul k n) m ∧ Lt m (mul (σ k) n)
  ```
- **Matemática:** n > 0 ⇒ ∃¹k ∈ ℕ₀, k·n ≤ m < σ(k)·n
- **Dependencias:** `ExistsUnique`, `mul`, `Le`, `Lt`

---

## 10. PeanoNatDiv.lean — `namespace Peano.Div`

*Dependencias: `PeanoNatLib`, `PeanoNatAxioms`, `PeanoNatStrictOrder`, `PeanoNatOrder`, `PeanoNatMaxMin`, `PeanoNatWellFounded`, `PeanoNatAdd`, `PeanoNatSub`, `PeanoNatMul`*

### 10.1. Definiciones

**[D10.1]** `divMod`
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
- **Terminado por:** `termination_by a`;  `decreasing_by` usa `lt_sizeOf` + `sub_lt_self`
- **Dependencias:** `sub`, `Lt`, `Le`, `SizeOf ℕ₀` (via `isomorph_Ψ_lt`)

**[D10.2]** `div`
- **Lean4:** `def div (a b : ℕ₀) : ℕ₀ := (divMod a b).1`
- **Matemática:** ⌊a/b⌋
- **Computable:** Sí
- **Notación:** `a / b`

**[D10.3]** `mod`
- **Lean4:** `def mod (a b : ℕ₀) : ℕ₀ := (divMod a b).2`
- **Matemática:** a mod b
- **Computable:** Sí
- **Notación:** `a % b`

**[D10.4]** `lt_sizeOf` (lema de conexión, exportado)
- **Lean4:** `theorem lt_sizeOf (a b : ℕ₀) : Lt a b → sizeOf a < sizeOf b`
- **Dependencias:** `isomorph_Ψ_lt`, `SizeOf ℕ₀`

### 10.2. Teoremas principales

**[T10.1]** `divMod_eq`
- **Lean4:** `theorem divMod_eq (a b : ℕ₀) : b ≠ 𝟘 → a = add (mul (div a b) b) (mod a b)`
- **Matemática:** b ≠ 0 ⇒ a = (a/b)·b + (a mod b)
- **Dependencias:** `divMod`, `add`, `mul`, `well_founded_lt`

**[T10.2]** `mod_lt_divisor`
- **Lean4:** `theorem mod_lt_divisor (a b : ℕ₀) : b ≠ 𝟘 → Lt (mod a b) b`
- **Matemática:** b ≠ 0 ⇒ (a mod b) < b
- **Dependencias:** `mod`, `Lt`

---

## 11. PeanoArith.lean — `namespace Peano.Arith`

*Dependencias: todos los módulos anteriores, `Init.Classical`*

### 11.1. Definiciones para `ℕ₀`

**[D11.1]** `Divides`
- **Lean4:** `def Divides (a b : ℕ₀) : Prop := ∃ k : ℕ₀, b = mul a k`
- **Matemática:** a ∣ b  ⟺  ∃k ∈ ℕ₀, b = a·k
- **Computable:** No (Prop)
- **Notación:** `a ∣ b` (infijo, prioridad 50); `a ∤ b` ≡ ¬(a ∣ b) (prioridad 50)

**[D11.2]** `MultipleOf`, `DivisorOf`
- **Lean4:**
  ```
  def MultipleOf (n m : ℕ₀) : Prop := Divides n m
  def DivisorOf  (d n : ℕ₀) : Prop := Divides d n
  ```
- **Matemática:** Sinónimos orientados de n ∣ m

**[D11.3]** `Divisors`
- **Lean4:** `def Divisors (n : ℕ₀) : ℕ₀ → Prop := fun d => d ∣ n`
- **Matemática:** Divisors(n) = {d ∈ ℕ₀ | d ∣ n}

**[D11.4]** `IsGCD`
- **Lean4:** `def IsGCD (a b d : ℕ₀) : Prop := d ∣ a ∧ d ∣ b ∧ ∀ c, (c ∣ a ∧ c ∣ b) → c ∣ d`
- **Matemática:** IsGCD(a, b, d)  ⟺  d∣a ∧ d∣b ∧ (∀c, c∣a ∧ c∣b ⇒ c∣d)

**[D11.5]** `IsLCM`
- **Lean4:** `def IsLCM (a b m : ℕ₀) : Prop := a ∣ m ∧ b ∣ m ∧ ∀ c, (a ∣ c ∧ b ∣ c) → m ∣ c`
- **Matemática:** IsLCM(a, b, m)  ⟺  a∣m ∧ b∣m ∧ (∀c, a∣c ∧ b∣c ⇒ m∣c)

**[D11.6]** `Coprime`
- **Lean4:** `def Coprime (a b : ℕ₀) : Prop := IsGCD a b 𝟙`
- **Matemática:** gcd(a, b) = 1

**[D11.7]** `Prime`
- **Lean4:** `def Prime (p : ℕ₀) : Prop := p ≠ 𝟘 ∧ p ≠ 𝟙 ∧ ∀ a b, p ∣ (mul a b) → p ∣ a ∨ p ∣ b`
- **Matemática:** p ≠ 0 ∧ p ≠ 1 ∧ (∀a,b, p∣ab ⇒ p∣a ∨ p∣b)  (Lema de Euclides como definición)

**[D11.8]** `gcd`
- **Lean4:**
  ```
  def gcd (a b : ℕ₀) : ℕ₀ :=
    if b = 𝟘 then a else gcd b (a % b)
  termination_by b
  ```
- **Matemática:** gcd(a, 0) = a;  gcd(a, b) = gcd(b, a mod b)
- **Computable:** Sí
- **Terminado por:** `termination_by b` vía `mod_lt_divisor` + `lt_sizeOf`
- **Dependencias:** `mod`, `well_founded_lt`

**[D11.9]** `lcm`
- **Lean4:** `def lcm (a b : ℕ₀) : ℕ₀ := div (mul a b) (gcd a b)`
- **Matemática:** lcm(a, b) = (a·b) / gcd(a, b)
- **Computable:** Sí
- **Dependencias:** `mul`, `div`, `gcd`

**[D11.10]** `Multiples` (inductivo)
- **Lean4:**
  ```
  inductive Multiples (n : ℕ₀) : ℕ₀ → Prop
    | zero    : Multiples n 𝟘
    | add_step {k : ℕ₀} : Multiples n k → Multiples n (add k n)
  ```
- **Matemática:** Multiples(n) = {0, n, 2n, 3n, …}

**[D11.11]** Estructuras auxiliares de listas de divisores
- **Lean4:**
  ```
  inductive DList (α : Type) : Type          -- lista inductiva propia
  def range_from_one : ℕ₀ → DList ℕ₀        -- rango [1 .. n]
  def dividesb (d n : ℕ₀) : Bool            -- (n % d = 𝟘)
  def Factors_of (n : ℕ₁) : DList ℕ₀        -- factores de n
  structure DivisorsList (n : ℕ₀) : Type    -- lista certificada de divisores
  ```
- **Computable:** Sí (`DList`, `dividesb`, `Factors_of`, `range_from_one`)

### 11.2. Definiciones para `ℕ₁`

**[D11.12]** `Divides₁`
- **Lean4:** `def Divides₁ (a b : ℕ₁) : Prop := a.val ∣ b.val`
- **Matemática:** a ∣₁ b  ⟺  a_ℕ ∣ b_ℕ
- **Computable:** No (Prop)
- **Notación:** `a ∣₁ b` (infijo, prioridad 50)

**[D11.13]** `IsGCD₁`
- **Lean4:** `def IsGCD₁ (a b d : ℕ₁) : Prop := d ∣₁ a ∧ d ∣₁ b ∧ ∀ c : ℕ₁, (c ∣₁ a ∧ c ∣₁ b) → c ∣₁ d`
- **Matemática:** MCD en ℕ₁

**[D11.14]** `gcd₁`
- **Lean4:**
  ```
  def gcd₁ (a b : ℕ₁) : ℕ₁ :=
    if hr : (a.val % b.val) = 𝟘 then b
    else gcd₁ b ⟨a.val % b.val, hr⟩
  termination_by b.val
  ```
- **Matemática:** Algoritmo de Euclides en ℕ₁
- **Computable:** Sí
- **Terminado por:** `termination_by b.val` vía `mod_lt_divisor` + `lt_sizeOf`
- **Dependencias:** `mod`, `well_founded_lt`, `ℕ₁`

**[D11.15]** `Coprime₁`
- **Lean4:** `def Coprime₁ (a b : ℕ₁) : Prop := gcd₁ a b = ⟨𝟙, by decide⟩`
- **Matemática:** gcd₁(a, b) = 1 en ℕ₁

### 11.3. Teoremas para `ℕ₀` — Divisibilidad básica

**[T11.1]** `divides_refl`
- **Lean4:** `theorem divides_refl (a : ℕ₀) : a ∣ a`
- **Matemática:** ∀a ∈ ℕ₀, a ∣ a

**[T11.2]** `one_divides`
- **Lean4:** `theorem one_divides (a : ℕ₀) : 𝟙 ∣ a`
- **Matemática:** ∀a ∈ ℕ₀, 1 ∣ a

**[T11.3]** `divides_zero`
- **Lean4:** `theorem divides_zero (a : ℕ₀) : a ∣ 𝟘`
- **Matemática:** ∀a ∈ ℕ₀, a ∣ 0

**[T11.4]** `zero_divides_iff`
- **Lean4:** `theorem zero_divides_iff (b : ℕ₀) : (𝟘 ∣ b) ↔ b = 𝟘`
- **Matemática:** 0 ∣ b ⟺ b = 0

**[T11.5]** `divides_trans`
- **Lean4:** `theorem divides_trans {a b c : ℕ₀} : a ∣ b → b ∣ c → a ∣ c`
- **Matemática:** a ∣ b ∧ b ∣ c ⇒ a ∣ c

**[T11.6]** `divides_mul_right`
- **Lean4:** `theorem divides_mul_right {a b c : ℕ₀} : a ∣ b → a ∣ (mul b c)`
- **Matemática:** a ∣ b ⇒ a ∣ b·c

**[T11.7]** `divides_mul_left`
- **Lean4:** `theorem divides_mul_left {a b c : ℕ₀} : a ∣ b → a ∣ (mul c b)`
- **Matemática:** a ∣ b ⇒ a ∣ c·b

**[T11.8]** `divides_add`
- **Lean4:** `theorem divides_add {a b c : ℕ₀} : a ∣ b → a ∣ c → a ∣ (add b c)`
- **Matemática:** a ∣ b ∧ a ∣ c ⇒ a ∣ (b + c)

**[T11.9]** `divides_le`
- **Lean4:** `theorem divides_le {a b : ℕ₀} : a ∣ b → b ≠ 𝟘 → Le a b`
- **Matemática:** a ∣ b ∧ b ≠ 0 ⇒ a ≤ b

**[T11.10]** `antisymm_divides`
- **Lean4:** `theorem antisymm_divides {a b : ℕ₀} : (a ∣ b) → (b ∣ a) → a = b`
- **Matemática:** a ∣ b ∧ b ∣ a ⇒ a = b

**[T11.11]** `divides_sub`
- **Lean4:** `theorem divides_sub {a b c : ℕ₀} (h_lt_a_b : Lt b a) (ha : c ∣ a) (hb : c ∣ b) : c ∣ (sub a b)`
- **Matemática:** b < a ∧ c ∣ a ∧ c ∣ b ⇒ c ∣ (a ∸ b)

**[T11.12]** `divides_mod`
- **Lean4:** `theorem divides_mod {a b c : ℕ₀} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (a % b)`
- **Matemática:** c ∣ a ∧ c ∣ b ⇒ c ∣ (a mod b)

**[T11.13]** `multiples_iff_divides`
- **Lean4:** `theorem multiples_iff_divides (n m : ℕ₀) : Multiples n m ↔ n ∣ m`
- **Matemática:** m ∈ Multiples(n) ⟺ n ∣ m

### 11.4. Teoremas para `ℕ₀` — MCD y Bézout

**[T11.14]** `gcd_greatest`
- **Lean4:** `theorem gcd_greatest (a b c : ℕ₀) : (c ∣ a ∧ c ∣ b) → c ∣ gcd a b`
- **Matemática:** c ∣ a ∧ c ∣ b ⇒ c ∣ gcd(a, b)
- **Dependencias:** `gcd`, `well_founded_lt`, `divides_mod`

**[T11.15]** `gcd_divides_linear_combo`
- **Lean4:** `theorem gcd_divides_linear_combo (a b n m : ℕ₀) : gcd a b ∣ (add (mul a n) (mul b m))`
- **Matemática:** gcd(a,b) ∣ (a·n + b·m) para todo n, m ∈ ℕ₀

**[T11.16]** `gcd_divides_max`
- **Lean4:** `theorem gcd_divides_max (a b : ℕ₀) : gcd a b ∣ max a b`
- **Matemática:** gcd(a,b) ∣ max(a,b)

**[T11.17]** `gcd_divides_min`
- **Lean4:** `theorem gcd_divides_min (a b : ℕ₀) : gcd a b ∣ min a b`
- **Matemática:** gcd(a,b) ∣ min(a,b)

**[T11.18]** `bezout_natform`
- **Lean4:**
  ```
  theorem bezout_natform (a b : ℕ₀) :
      ∃ n m, (gcd a b = sub (mul n a) (mul m b)) ∨
             (gcd a b = sub (mul n b) (mul m a))
  ```
- **Matemática:** ∃n,m ∈ ℕ₀, gcd(a,b) = n·a ∸ m·b  ∨  gcd(a,b) = n·b ∸ m·a
- **Dependencias:** `gcd`, `mul`, `sub`, `add_k_sub_k`
- **Nota:** La forma OR es intrínseca a la recursión de Euclides con coeficientes en ℕ₀ (sin enteros negativos). La alternancia se propaga como tipo `Or` a cada nivel de la inducción bien fundada.

### 11.5. Teoremas para `ℕ₀` — DivisorsList

**[T11.19]** `divisorslist_one_mem`
- **Lean4:** `theorem divisorslist_one_mem {n : ℕ₀} (d : DivisorsList n) : 𝟙 ∈ d.vals`
- **Matemática:** 1 ∈ divisores(n)

**[T11.20]** `divisorslist_self_mem`
- **Lean4:** `theorem divisorslist_self_mem {n : ℕ₀} (d : DivisorsList n) : n ∈ d.vals`
- **Matemática:** n ∈ divisores(n)

### 11.6. Teoremas para `ℕ₁`

**[T11.21]** `divides₁_refl`
- **Lean4:** `theorem divides₁_refl (a : ℕ₁) : a ∣₁ a`
- **Matemática:** ∀a ∈ ℕ₁, a ∣₁ a

**[T11.22]** `divides₁_trans`
- **Lean4:** `theorem divides₁_trans {a b c : ℕ₁} (hab : a ∣₁ b) (hbc : b ∣₁ c) : a ∣₁ c`
- **Matemática:** a ∣₁ b ∧ b ∣₁ c ⇒ a ∣₁ c

**[T11.23]** `divides₁_antisymm`
- **Lean4:** `theorem divides₁_antisymm {a b : ℕ₁} (hab : a ∣₁ b) (hba : b ∣₁ a) : a = b`
- **Matemática:** a ∣₁ b ∧ b ∣₁ a ⇒ a = b

**[T11.24]** `mod_eq_zero_iff_divides`
- **Lean4:** `theorem mod_eq_zero_iff_divides {a b : ℕ₁} : (a.val % b.val) = 𝟘 ↔ (b ∣₁ a)`
- **Matemática:** a mod b = 0 ⟺ b ∣₁ a

**[T11.25]** `gcd₁_val_eq`
- **Lean4:** `theorem gcd₁_val_eq (a b : ℕ₁) : (gcd₁ a b).val = gcd a.val b.val`
- **Matemática:** (gcd₁(a,b))_ℕ = gcd(a_ℕ, b_ℕ)

**[T11.26]** `gcd₁_comm`
- **Lean4:** `theorem gcd₁_comm (a b : ℕ₁) : gcd₁ a b = gcd₁ b a`
- **Matemática:** gcd₁(a, b) = gcd₁(b, a)

**[T11.27]** `gcd₁_divides_left`
- **Lean4:** `theorem gcd₁_divides_left (a b : ℕ₁) : gcd₁ a b ∣₁ a`
- **Matemática:** gcd₁(a, b) ∣₁ a

**[T11.28]** `gcd₁_divides_right`
- **Lean4:** `theorem gcd₁_divides_right (a b : ℕ₁) : gcd₁ a b ∣₁ b`
- **Matemática:** gcd₁(a, b) ∣₁ b

**[T11.29]** `gcd₁_divides_both`
- **Lean4:** `theorem gcd₁_divides_both (a b : ℕ₁) : gcd₁ a b ∣₁ a ∧ gcd₁ a b ∣₁ b`
- **Matemática:** gcd₁(a,b) ∣₁ a  ∧  gcd₁(a,b) ∣₁ b

---

## 12. Peano.lean — Módulo Raíz

*Archivo de entrada. No introduce definiciones ni teoremas propios.*
*Importa y re-exporta todos los módulos de `PeanoNatLib/`*

```lean4
import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatWellFounded
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatDiv
import PeanoNatLib.PeanoArith
```

