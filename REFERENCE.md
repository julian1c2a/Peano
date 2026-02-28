# Guía de Referencia Técnica para el Proyecto Peano

**Última actualización:** 2026-02-28 12:00
**Autor**: Julián Calderón Almendros

---

## 1. Módulos, Namespaces y Dependencias

Esta sección documenta los archivos `.lean` del proyecto, sus `namespaces` y las dependencias entre ellos.

| Archivo                   | Dependencias                                                                                                                                                                                                                                                                    | Descripción                                                                 |
| ------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------- |
| `Peano.lean`              | `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatAdd`, `PeanoNatLib.PeanoNatMul`, `PeanoNatLib.PeanoNatSub`, `PeanoNatLib.PeanoNatDiv`, `PeanoNatLib.PeanoNatArith`, `PeanoNatLib.PeanoNatOrder`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatMaxMin`, `PeanoNatLib.PeanoNatWellFounded` | Archivo principal que importa y re-exporta la biblioteca.                |
| `PeanoNatLib.lean`        | `Init.Classical`                                                                                                                                                                                                                                                | Define los tipos `ℕ₀`, `ℕ₁`, `ℕ₂`, la proposición `ExistsUnique` y utilidades. |
| `PeanoNatAxioms.lean`     | `PeanoNatLib.PeanoNatLib`                                                                                                                                                                                                                                                               | Formaliza los axiomas de Peano como teoremas.                               |
| `PeanoNatAdd.lean`        | `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatOrder`, `PeanoNatLib.PeanoNatMaxMin`, `PeanoNatLib.PeanoNatWellFounded` | Define la suma y demuestra sus propiedades (conmutatividad, asociatividad, etc.). |
| `PeanoNatMul.lean`        | `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatOrder`, `PeanoNatLib.PeanoNatMaxMin`, `PeanoNatLib.PeanoNatWellFounded`, `PeanoNatLib.PeanoNatAdd`, `PeanoNatLib.PeanoNatSub` | Define la multiplicación y demuestra sus propiedades (conmutatividad, asociatividad, distributividad, etc.). |
| `PeanoNatSub.lean`        | `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatAdd`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatOrder`, `PeanoNatLib.PeanoNatMaxMin`, `PeanoNatLib.PeanoNatWellFounded` | Define la resta truncada (monus) y demuestra sus propiedades.            |
| `PeanoNatDiv.lean`        | `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatOrder`, `PeanoNatLib.PeanoNatMaxMin`, `PeanoNatLib.PeanoNatWellFounded`, `PeanoNatLib.PeanoNatAdd`, `PeanoNatLib.PeanoNatSub`, `PeanoNatLib.PeanoNatMul` | Define la división euclidiana (`div`, `mod`) y prueba el teorema de la división. |
| `PeanoNatArith.lean`      | `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatOrder`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatAdd`, `PeanoNatLib.PeanoNatMul`, `PeanoNatLib.PeanoNatSub`, `PeanoNatLib.PeanoNatDiv`, `PeanoNatLib.PeanoNatMaxMin` | Introduce conceptos de teoría de números como divisibilidad, GCD, LCM y primalidad. |
| `PeanoNatOrder.lean`      | `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatStrictOrder` | Define la relación de orden no estricto `Le` (≤), prueba que es un orden total y demuestra el principio de buen orden. |
| `PeanoNatStrictOrder.lean`| `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms` | Define la relación de orden estricto `Lt` (<) y demuestra que es un orden total estricto. |
| `PeanoNatMaxMin.lean`     | `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatOrder` | Define las funciones `max` y `min` y demuestra que forman una retícula distributiva. |
| `PeanoNatWellFounded.lean`| `PeanoNatLib.PeanoNatLib`, `PeanoNatLib.PeanoNatAxioms`, `PeanoNatLib.PeanoNatStrictOrder`, `PeanoNatLib.PeanoNatOrder`, `PeanoNatLib.PeanoNatMaxMin`, `Init.Classical` | Demuestra que la relación de orden estricto `Lt` es bien fundada, base para la inducción bien fundada. |

---

## 2. Axiomas, Definiciones y Teoremas

Esta sección documenta los axiomas, definiciones y teoremas principales del proyecto.

### 2.1. PeanoNatLib.lean

Este módulo define los tipos y proposiciones fundamentales.

#### Definiciones

*   **`ℕ₀`**: Tipo inductivo para los números naturales de Peano.
    *   **`ℕ₀.zero : ℕ₀`**: El número cero. Notación: `𝟘`.
    *   **`ℕ₀.succ : ℕ₀ → ℕ₀`**: La función sucesor. Notación: `σ n`.

*   **`ExistsUnique {α : Type} (p : α → Prop) : Prop`**: Proposición que afirma que existe un único elemento que satisface el predicado `p`.
    *   **Notación**: `∃¹ x, p x`

*   **`choose {α : Type} {p : α → Prop} (h : ∃ x, p x) : α`**: Función no computable (clásica) que elige un elemento que satisface `p`, dada la prueba de que tal elemento existe.

*   **`choose_unique {α : Type} {p : α → Prop} (h : ExistsUnique p) : α`**: Versión de `choose` para `ExistsUnique`.

#### Teoremas

*   **`choose_spec {α : Type} {p : α → Prop} (h : ∃ x, p x) : p (choose h)`**: El elemento elegido por `choose` satisface el predicado `p`.

*   **`choose_uniq {α : Type} {p : α → Prop} (h : ExistsUnique p) {y : α} (hy : p y) : y = choose_unique h`**: Cualquier elemento `y` que satisface el predicado `p` es igual al elemento elegido por `choose_unique`.

### 2.2. PeanoNatAxioms.lean

Este módulo establece los axiomas de Peano como teoremas demostrados a partir de las propiedades del tipo inductivo `ℕ₀`.

#### Axiomas (Demostrados como Teoremas)

*   **`AXIOM_cero_neq_succ`**: `∀ (k : ℕ₀), 𝟘 ≠ σ k`
    *   **Matemáticamente**: El cero no es el sucesor de ningún número natural.

*   **`AXIOM_succ_is_funct_forall_n_in_PeanoNat`**: `∀ (n : ℕ₀), ∃ (k : ℕ₀), k = σ n`
    *   **Matemáticamente**: La función sucesor está definida para todo número natural.

*   **`AXIOM_uniqueness_on_image`**: `n = m → σ n = σ m`
    *   **Matemáticamente**: La función sucesor es unívoca (si dos números son iguales, sus sucesores también lo son).

*   **`AXIOM_succ_inj`**: `σ n = σ m → n = m`
    *   **Matemáticamente**: La función sucesor es inyectiva.

*   **`AXIOM_induction_on_PeanoNat`**: `(P 𝟘 ∧ (∀ n, P n → P (σ n))) → ∀ n, P n`
    *   **Matemáticamente**: El principio de inducción matemática.

### 2.3. PeanoNatAdd.lean

Este módulo define la operación de suma y sus propiedades.

#### Definiciones

*   **`add (n m : ℕ₀) : ℕ₀`**: La función de suma, definida por recursión sobre el segundo argumento.
    *   `add n 𝟘 := n`
    *   `add n (σ m) := σ (add n m)`
    *   **Notación**: `n + m`

#### Teoremas Principales

*   **`add_comm (n m : ℕ₀) : n + m = m + n`**: La suma es conmutativa.

*   **`add_assoc (n m k : ℕ₀) : n + (m + k) = (n + m) + k`**: La suma es asociativa.

*   **`add_cancelation (n m k : ℕ₀) : n + m = n + k → m = k`**: Ley de cancelación para la suma.

*   **`le_iff_exists_add (a b : ℕ₀) : a ≤ b ↔ ∃ p, b = a + p`**: La relación de orden `≤` se define en términos de la suma. Un número `a` es menor o igual que `b` si y solo si existe un número `p` tal que `b = a + p`.

### 2.4. PeanoNatMul.lean

Este módulo define la operación de multiplicación y sus propiedades.

#### Definiciones

*   **`mul (n m : ℕ₀) : ℕ₀`**: La función de multiplicación, definida por recursión sobre el segundo argumento usando la suma.
    *   `mul n 𝟘 := 𝟘`
    *   `mul n (σ m) := add (mul n m) n`
    *   **Notación**: `n * m`

#### Teoremas Principales

*   **`mul_comm (n m : ℕ₀) : n * m = m * n`**: La multiplicación es conmutativa.

*   **`mul_assoc (n m k : ℕ₀) : (m * n) * k = m * (n * k)`**: La multiplicación es asociativa.

*   **`mul_ldistr (m n k : ℕ₀) : m * (n + k) = (m * n) + (m * k)`**: La multiplicación distribuye sobre la suma.

*   **`mul_eq_zero (n m : ℕ₀) : n * m = 0 ↔ n = 0 ∨ m = 0`**: Un producto es cero si y solo si al menos uno de los factores es cero.

*   **`archimedean_property {n : ℕ₀} (m : ℕ₀) (h_n_pos : Lt 𝟘 n)`**: `∃ j, m < j * n`. Propiedad Arquimediana. Para cualquier par de números `m` y `n` (con `n > 0`), existe un múltiplo de `n` que es mayor que `m`.

*   **`exists_unique_mul_le_and_lt_succ_mul (n m : ℕ₀) (h_n_pos : Lt 𝟘 n)`**: `∃¹ k, k * n ≤ m < (σ k) * n`. Este teorema es la base de la división euclidiana.

### 2.5. PeanoNatSub.lean

Este módulo define la operación de resta truncada (monus).

#### Definiciones

*   **`sub (n m : ℕ₀) : ℕ₀`**: La función de resta truncada. Si `m ≤ n`, se comporta como la resta normal. Si `m > n`, el resultado es `𝟘`.
    *   **Notación**: `n - m`

#### Teoremas Principales

*   **`sub_k_add_k (n k : ℕ₀) (h : k ≤ n) : (n - k) + k = n`**: La suma cancela la resta (cuando la resta está bien definida).

*   **`add_k_sub_k (n k : ℕ₀) : (n + k) - k = n`**: La resta cancela la suma.

*   **`le_sub_iff_add_le_of_le (n m k : ℕ₀) (h : m ≤ n) : k ≤ n - m ↔ m + k ≤ n`**: Relación fundamental entre la resta, la suma y el orden.

*   **`sub_pos_iff_lt (n m : ℕ₀) : 1 ≤ n - m ↔ m < n`**: El resultado de la resta es positivo si y solo si el minuendo es estrictamente mayor que el sustraendo.

### 2.6. PeanoNatOrder.lean

Este módulo define la relación de orden no estricto `Le` (≤) y demuestra las propiedades que la convierten en un orden total, incluyendo el principio de buen orden.

#### Definiciones

*   **`Le (n m : ℕ₀) : Prop`**: La relación "menor o igual que", definida como `Lt n m ∨ n = m`.
    *   **Notación**: `n ≤ m`

#### Teoremas Principales (Propiedades de Orden Total)

*   **`le_refl (n : ℕ₀) : n ≤ n`**: La relación `≤` es reflexiva.

*   **`le_antisymm (n m : ℕ₀) : n ≤ m → m ≤ n → n = m`**: La relación `≤` es antisimétrica.

*   **`le_trans (n m k : ℕ₀) : n ≤ m → m ≤ k → n ≤ k`**: La relación `≤` es transitiva.

*   **`le_total (n m : ℕ₀) : n ≤ m ∨ m ≤ n`**: La relación `≤` es total. Cualquier par de números puede ser comparado.

#### Teorema Principal (Buen Orden)

*   **`well_ordering_principle {P : ℕ₀ → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬P m`**: Principio de buen orden. Todo conjunto no vacío de números naturales (definido por una propiedad `P`) tiene un elemento mínimo.

### 2.7. PeanoNatStrictOrder.lean

Este módulo define la relación de orden estricto `Lt` (<) y demuestra sus propiedades fundamentales.

#### Definiciones

*   **`Lt (n m : ℕ₀) : Prop`**: La relación "menor que", definida por recursión.
    *   `Lt n 𝟘` es `False`.
    *   `Lt 𝟘 (σ m)` es `True`.
    *   `Lt (σ n) (σ m)` es `Lt n m`.
    *   **Notación**: `n < m`

#### Teoremas Principales (Propiedades de Orden Total Estricto)

*   **`lt_irrefl (n : ℕ₀) : ¬(n < n)`**: La relación `<` es irreflexiva. Ningún número es menor que sí mismo.

*   **`lt_asymm (n m : ℕ₀) : n < m → ¬(m < n)`**: La relación `<` es asimétrica.

*   **`lt_trans (n m k : ℕ₀) : n < m → m < k → n < k`**: La relación `<` es transitiva.

*   **`trichotomy (n m : ℕ₀) : (n < m) ∨ (n = m) ∨ (m < n)`**: Para cualquier par de números, se cumple exactamente una de las tres condiciones: o el primero es menor, o son iguales, o el segundo es menor.

### 2.8. PeanoNatMaxMin.lean

Este módulo define las funciones `max` y `min` y establece las propiedades de la retícula (lattice) que forman.

#### Definiciones

*   **`max (n m : ℕ₀) : ℕ₀`**: Devuelve el mayor de dos números.
*   **`min (n m : ℕ₀) : ℕ₀`**: Devuelve el menor de dos números.

#### Teoremas Principales (Propiedades de Retícula)

*   **`max_comm` / `min_comm`**: `max n m = max m n` y `min n m = min m n` (Conmutatividad).

*   **`max_assoc` / `min_assoc`**: `max (max n m) k = max n (max m k)` y análogo para `min` (Asociatividad).

*   **`le_max_left` / `le_max_right`**: `n ≤ max n m` y `m ≤ max n m`.

*   **`min_le_left` / `min_le_right`**: `min n m ≤ n` y `min n m ≤ m`.

*   **`max_distrib_min`**: `max n (min m k) = min (max n m) (max n k)` (Distributividad de `max` sobre `min`).

*   **`min_distrib_max`**: `min n (max m k) = max (min n m) (min n k)` (Distributividad de `min` sobre `max`).

### 2.9. PeanoNatWellFounded.lean

Este módulo demuestra que el orden de los números naturales es bien fundado, una propiedad crucial para la inducción.

#### Teoremas Principales

*   **`well_founded_lt : WellFounded Lt`**: Afirma que la relación de orden estricto `Lt` (<) es bien fundada. Esto significa que no existen secuencias infinitas descendentes de números naturales (ej. `... < n₂ < n₁ < n₀`). Esta propiedad garantiza que la inducción fuerte (o inducción bien fundada) es un método de prueba válido sobre los números naturales.

### 2.10. PeanoNatDiv.lean

Este módulo define la división euclidiana (cociente y resto).

#### Definiciones

*   **`div (a b : ℕ₀) : ℕ₀`**: El cociente de la división de `a` por `b`.
    *   **Notación**: `a / b`
*   **`mod (a b : ℕ₀) : ℕ₀`**: El resto de la división de `a` por `b`.
    *   **Notación**: `a % b`

#### Teoremas Principales (División Euclidiana)

*   **`divMod_eq (a b : ℕ₀) : b ≠ 0 → a = (a / b) * b + (a % b)`**: Teorema de la división. Todo número `a` puede expresarse como `cociente * divisor + resto`.

*   **`mod_lt_divisor (a b : ℕ₀) : b ≠ 0 → a % b < b`**: El resto es siempre estrictamente menor que el divisor (si el divisor no es cero).

### 2.11. PeanoNatArith.lean

Este módulo introduce conceptos de la teoría de números elemental.

#### Definiciones

*   **`Divides (a b : ℕ₀) : Prop`**: Proposición que afirma que `a` divide a `b`.
    *   `∃ k, b = a * k`
    *   **Notación**: `a ∣ b`

*   **`gcd (a b : ℕ₀) : ℕ₀`**: El máximo común divisor, implementado con el algoritmo de Euclides (`gcd b (a % b)`).

*   **`lcm (a b : ℕ₀) : ℕ₀`**: El mínimo común múltiplo, definido como `(a * b) / gcd a b`.

*   **`Prime (p : ℕ₀) : Prop`**: Un número `p` es primo si no es 0 ni 1, y si `p ∣ a * b`, entonces `p ∣ a` o `p ∣ b` (Lema de Euclides).

*   **`Coprime (a b : ℕ₀) : Prop`**: Dos números son coprimos si su `gcd` es 1.

*Teoremas importantes como la identidad de Bézout (`bezout_natform`) y la conmutatividad del `gcd` (`gcd_comm`) están enunciados pero pendientes de demostración (`sorry`).*

