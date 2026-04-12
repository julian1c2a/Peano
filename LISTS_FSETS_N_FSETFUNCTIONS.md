# Plan de Implementación: `Lists`, `FSet` y `FSetFunction`

**Última actualización:** 2026-04-12
**Autor**: Julián Calderón Almendros & Gemini Code Assist

> Este documento detalla el plan de refactorización y extensión para la infraestructura de conjuntos finitos (`FSet`) y funciones sobre ellos, basándose en las ideas del fichero `Peano/PeanoNat/FSetFunction.lean` y la estructura existente del proyecto.

---

## Resumen de la Estrategia

El objetivo es evolucionar la librería actual hacia un sistema más genérico y potente para manejar colecciones y funciones. Esto implica varias fases de refactorización y desarrollo:

1. **Generalización**: Abstraer `FSet` para que no esté limitado a `ℕ₀` y dotar a `Tuple` (el producto cartesiano n-veces de `ℕ₀`) de una relación de orden.
2. **Centralización de Funciones**: Mover y generalizar `MapOn` desde `Group.lean` a un nuevo fichero `FSetFunction.lean`.
3. **Jerarquía de Colecciones**: Construir tipos para manejar colecciones complejas como `TupleFSet` (conjuntos de tuplas), `FSetList` (listas de conjuntos) y `FSetSet` (conjuntos de conjuntos), como se describe en `FSetFunction.lean`.
4. **Funciones de Alto Nivel**: Implementar `FSetTuple` (tuplas de conjuntos) y `FSetFunction` (funciones entre tuplas de conjuntos), completando la visión de `FSetFunction.lean`.

---

## Fase 1: Prerrequisitos — Generalización de `FSet` y Orden en `Tuple`

**Objetivo**: Sentar las bases para poder definir conjuntos de objetos más complejos que `ℕ₀`, como las tuplas.

### Acciones

1. **Refactorizar `Peano/PeanoNat/FSet.lean` para un `FSet` genérico:**
    * La `structure ℕ₀FSet` actual será reemplazada por una estructura genérica que pueda contener cualquier tipo con las propiedades necesarias (orden y decidibilidad).

      ```lean
      structure FSet (α : Type) [DecidableEq α] [LT α] [DecidableRel (LT.lt α)] where
        elems : List α
        sorted : Sorted (· < ·) elems
      ```

    * Los tipos existentes se convertirán en alias para mantener la compatibilidad:

      ```lean
      abbrev ℕ₀FSet := FSet ℕ₀
      abbrev ℕ₁FSet := FSet ℕ₁
      abbrev ℕ₂FSet := FSet ℕ₂
      -- Para FactFSet, primero necesitaremos una instancia de LT para (ℕ₂ × ℕ₁)
      abbrev FactFSet := FSet (ℕ₂ × ℕ₁)
      ```

    * Las funciones como `insert`, `ofList`, `filter`, etc., deberán generalizarse para `FSet α`.

2.  **Centralizar la lógica de `Tuple` en `Peano/PeanoNat/Tuple.lean`:**
    *   Se ha creado el fichero `Peano/PeanoNat/Tuple.lean`.
    *   **Movimiento**: Se ha trasladado la definición de `Tuple` y sus operaciones básicas (`emptyTuple`, `consTuple`, `headTuple`, `tailTuple`, `mkTuple`) desde `Peano/PeanoNat.lean` a este nuevo fichero.
    *   **Orden Lexicográfico**: Se ha implementado el orden lexicográfico (`lexLt`, `lexLe`) y las instancias `LT`, `LE`, y `DecidableRel` correspondientes dentro de `Tuple.lean`, como se pedía en el plan.
    *   Esto permite que `Tuple n` pueda ser usado como elemento en un `FSet` genérico.

---

## Fase 2: Refactorización de Funciones sobre Conjuntos

**Objetivo**: Centralizar la lógica de funciones entre conjuntos en `FSetFunction.lean` y adoptar una definición más robusta y general.

### Acciones

1. **Limpiar `Peano/PeanoNat/Group.lean`** (o donde resida `MapOn` actualmente):
    * Eliminar por completo la `structure MapOn` y todas las definiciones y teoremas relacionados (`InjectiveOn`, `SurjectiveOn`, `MapOn.Bijective`, `MapOn.comp_injective`, etc.). El grupo simétrico `Sym` dependerá de la nueva definición.

2. **Construir `Peano/PeanoNat/FSetFunction.lean`**:
    * **Generalizar `MapOn`**: Implementar la nueva `MapOn` genérica que funcione entre `FSet α` y `FSet β`, como se sugiere en los puntos 2 y 3 de `FSetFunction.lean`.

      ```lean
      -- En Peano/PeanoNat/FSetFunction.lean
      structure MapOn {α β : Type} [DecidableEq α] [LT α] [DecidableRel (LT.lt α)]
                                 [DecidableEq β] [LT β] [DecidableRel (LT.lt β)]
                                 (A : FSet α) (B : FSet β) where
        toFun : α → β
        map_carrier : ∀ a, a ∈ A → toFun a ∈ B
      ```

      *Nota: Esta definición (`toFun : α → β`) es más flexible y estándar en Lean que usar subtipos (`{x // x ∈ A} → {y // y ∈ B}`), facilitando la composición y la aplicación de la función.*

    * **Definir la Imagen (`Im`)**: Implementar la función que calcula el conjunto imagen, como se pide en el punto 1 de `FSetFunction.lean`.

      ```lean
      def Im {α β} {A : FSet α} {B : FSet β} (f : MapOn A B) : FSet β :=
        FSet.ofList (A.elems.map f.toFun)
      ```

    * **Re-implementar Teoremas**: Adaptar las demostraciones de `comp_injective`, `comp_surjective`, `injective_iff_surjective_of_card_eq`, etc., para que funcionen con la nueva `MapOn` genérica. Esto implicará usar `Im` y propiedades de cardinalidad sobre `FSet` genéricos.

---

## Fase 3: Jerarquía de Colecciones de Conjuntos

**Objetivo**: Implementar los tipos necesarios para manejar colecciones de conjuntos, como se describe en los puntos 6, 7, 8 y 9 de `FSetFunction.lean`.

### Acciones

1. **Modificar `Peano/PeanoNat/FSet.lean`**:
    * Añadir el alias para conjuntos de tuplas (punto 6). Esto será trivial una vez completada la Fase 1.

      ```lean
      abbrev TupleFSet (n : ℕ₀) := FSet (Tuple n)
      ```

    * Añadir el alias para listas de conjuntos (punto 7).

      ```lean
      abbrev FSetList := List (FSet ℕ₀)
      ```

2. **Crear `Peano/PeanoNat/FSetOrder.lean` (o añadir a `FSet.lean`)**:
    * **Orden para `FSet`**: Primero, definir un orden total entre conjuntos `FSet α`. El orden lexicográfico sobre sus listas de elementos es una opción natural.

      ```lean
      def FSet.lt {α} [LT α] (A B : FSet α) : Prop :=
        List.lex (· < ·) A.elems B.elems
      ```

    * **Orden para `FSetList`**: Definir la relación de orden para listas de conjuntos, como se pide en el punto 8. La idea es comparar primero por cardinal (longitud de la lista) y luego lexicográficamente.

      ```lean
      def lexListFSetLt (l₁ l₂ : FSetList) : Prop :=
        if l₁.length < l₂.length then True
        else if l₁.length > l₂.length then False
        else List.lex FSet.lt l₁ l₂ -- Comparación lexicográfica elemento a elemento
      ```

    * **Definir `FSetSet`**: Crear la estructura para "conjuntos de conjuntos" (punto 9), usando el orden anterior para su invariante de ordenación.

      ```lean
      structure FSetSet where
        elems : FSetList
        sorted : Sorted lexListFSetLt elems
      ```

---

## Fase 4: Tuplas de Conjuntos y Funciones entre Ellas

**Objetivo**: Construir los tipos de más alto nivel para trabajar con familias finitas de conjuntos, como se pide en los puntos 10 y 11.

### Acciones

1. **Modificar `Peano/PeanoNat/FSet.lean`**:
    * Añadir el tipo inductivo para tuplas de conjuntos finitos (punto 10).

      ```lean
      inductive FSetTuple : ℕ₀ → Type where
        | nil : FSetTuple 𝟘
        | cons {n : ℕ₀} : FSet ℕ₀ × FSetTuple n → FSetTuple (σ n)
      ```

2. **Modificar `Peano/PeanoNat/FSetFunction.lean`**:
    * Definir la estructura para funciones entre tuplas de conjuntos (punto 11).

      ```lean
      structure FSetFunction (n m : ℕ₀) where
        toFun : FSetTuple n → FSetTuple m
      ```

      *Nota: La sugerencia original `map_carrier : ∀ t, t ∈ FSetTuple n → ...` no es aplicable aquí, ya que `FSetTuple n` es un tipo, no un conjunto. La definición simple `toFun` es la correcta y más general.*

---

Este plan proporciona una hoja de ruta clara y modular. Sugiero empezar por la **Fase 1**, ya que la generalización de `FSet` y la definición del orden en `Tuple` son los cimientos para todo lo demás.

¡Mucho éxito con la implementación!
