# Refactorización de Listas y Conjuntos en Peano

Este documento detalla la estrategia de refactorización arquitectónica para los módulos de listas y conjuntos (`List.lean`, `FSet.lean`, etc.) en el proyecto Peano. El objetivo es transicionar de implementaciones acopladas a los números naturales (`ℕ₀`) hacia un diseño completamente abstracto, culminando en un tipo dinámico estructurado recursivo capaz de representar jerarquías infinitas (escalares, listas, listas de listas, etc.).

## Fase 1: Consolidación y Limpieza (ListList.lean → List.lean)

**Problema actual:**
El archivo `ListList.lean` no introduce nuevos tipos, sino que añade instancias de clases de tipo (como `LE`, `LT`, `DecidableRel`, `Repr`) a los tipos ya definidos en `List.lean` (como `List α`, `Nats`, y `PeanoVal`). Esto fragmenta la definición de los tipos de sus comportamientos fundamentales.

**Acciones:**
1. Mover todas las secciones de `ListList.lean` (§ 11 a § 15) al final del archivo `List.lean`.
2. Eliminar el archivo `ListList.lean`.
3. Actualizar todas las importaciones en el proyecto (por ejemplo, en `FSetFSet.lean`) que apunten a `ListList.lean` para que apunten únicamente a `Peano.PeanoNat.ListsAndSets.List`.

**Beneficio:** Cohesión máxima. Un único archivo define los tipos base de listas y su comportamiento estándar.

## Fase 2: Fundamentos Matemáticos (Orden Lineal Estricto)

**Problema actual:**
La lógica algorítmica de inserción ordenada (`sortedInsert` en `FSet.lean`) está fuertemente acoplada al tipo `ℕ₀` porque depende de teoremas específicos de tricotomía y transitividad de los naturales.

**La cuestión de la Asimetría:**
Un orden estricto requiere irreflexividad, transitividad y asimetría. Sin embargo, matemáticamente, **la asimetría se deduce de la irreflexividad y la transitividad**:
Si tuviéramos $a < b$ y $b < a$, por transitividad tendríamos $a < a$, lo cual contradice la irreflexividad. 
Aun así, en la formalización en Lean 4, es muy útil (y estándar) proveer la asimetría ya sea como un campo de la clase o como un teorema/instancia derivada inmediata, para facilitar las demostraciones y la integración con las typeclasses estándar de Lean (`Std.Asymm`).

**Acciones:**
1. Definir una typeclass en `Order.lean` o `StrictOrder.lean` que empaquete las propiedades de un orden lineal estricto decidible:
   ```lean4
   class StrictLinearOrder (α : Type) extends LT α where
     decLt : DecidableRel (· < ·)
     irrefl : ∀ a : α, ¬ (a < a)
     trans  : ∀ {a b c : α}, a < b → b < c → a < c
     trichotomy : ∀ a b : α, a < b ∨ a = b ∨ b < a
     -- La asimetría puede ser un lema derivado o incluido explícitamente:
     -- asymm : ∀ {a b : α}, a < b → ¬ (b < a)
   ```
2. Demostrar el lema genérico de asimetría basado en `irrefl` y `trans` (si no se incluye como axioma).
3. Instanciar `StrictLinearOrder` para `ℕ₀`, `ℕ₁`, `ℕ₂` y `Tuple n`, utilizando los teoremas ya existentes en el proyecto.

## Fase 3: Generalización de Algoritmos (FSet.lean)

**Problema actual:**
Debido a la falta de abstracción, operaciones como `insert`, `ofList`, y `filter` sobre conjuntos finitos están limitadas a `FSet ℕ₀`.

**Acciones:**
1. Trasladar el algoritmo `sortedInsert` y su demostración de correctitud desde `FSet.lean` hacia `List.lean`.
2. Generalizar la firma de `sortedInsert` para que opere sobre cualquier tipo `List α` donde `[StrictLinearOrder α]`.
3. Actualizar `FSet.lean` para que las funciones `insert`, `ofList`, etc., sean genéricas para cualquier `FSet α` que cumpla con el orden lineal estricto.

**Beneficio:** Cualquier conjunto (de primos, de tuplas, de Nats) obtiene automáticamente toda el álgebra de conjuntos finitos sin duplicar código.

## Fase 4: El Universo Recursivo (La Torre Infinita)

**Problema actual:**
El tipo suma `PeanoVal` define manualmente cada nivel de anidamiento (`ofNat`, `ofNatList`, `ofTuple`, `ofTupleList`), lo que genera una explosión combinatoria al implementar `DecidableEq` y `LT` (actualmente con 36 casos). Si quisiéramos listas de listas, necesitaríamos añadir más constructores y los casos crecerían exponencialmente.

**El Diseño Propuesto (Árboles Universales):**
Abstraer los niveles base de escalares y usar un único constructor recursivo para las colecciones.

```lean4
-- Esquema de jerarquía de subtipos
inductive Level where
  | base : Level  -- α   (ej. ℕ₀)
  | sub1 : Level  -- α₁  (ej. ℕ₁)
  | sub2 : Level  -- α₂  (ej. ℕ₂)

def Level.toType {α α₁ α₂ : Type} : Level → Type
  | .base => α
  | .sub1 => α₁
  | .sub2 => α₂

-- El valor universal recursivo
inductive UnivVal {α α₁ α₂ : Type} : Type where
  | ofScalar (lvl : Level) (x : Level.toType lvl) : UnivVal
  | ofTuple  (n : ℕ₀)      (t : Tuple n)          : UnivVal
  | ofList   (xs : List UnivVal)                  : UnivVal
```

**Ventajas de la Fase 4:**
1. **Recursión gratuita:** `ofList` permite construir `List α`, `List (List α)`, y estructuras heterogéneas profundas sin añadir constructores al tipo.
2. **Reducción de casos:** La comprobación de igualdad y ordenamiento se hace por inducción estructural recursiva, colapsando los 36 casos a apenas un puñado de patrones básicos.
3. **Escalabilidad:** El framework de conjuntos `FSet UnivVal` podrá albergar cualquier estructura matemática arbitraria.
