# Implementación de Inducción y Recursión Transfinita

El objetivo de esta fase es dotar a las estructuras `Ordinal` en `CountableOrd` y `UnivOrd` de principios formales y ergonómicos para razonar por inducción y definir funciones por recursión.

Tras revisar la base de código actual, se ha constatado que en ambos módulos (`CountableOrd/WellOrder.lean` y `UnivOrd/WellOrder.lean`) ya se ha demostrado que la relación estricta `<` (heredada de `PreOrd.Mem`) es bien fundada (`WellFounded (· < ·)`). Este es un cimiento excelente.

A continuación se propone un plan estratégico para implementar la inducción y recursión.

## User Review Required

> [!IMPORTANT]
> **Enfoque de Recursión**: La recursión en Lean 4 para cocientes como `Ordinal` puede ser complicada. Hay dos enfoques principales:
> 1. **Well-Founded Recursion (`WellFounded.fix`)**: Se define directamente sobre `Ordinal` usando el hecho de que `<` es bien fundado. Es muy potente pero puede ser difícil de evaluar computacionalmente.
> 2. **Lifting desde `PreOrd`**: Se define la recursión estructuralmente sobre `PreOrd` (usando `PreOrd.rec`) y luego se demuestra que respeta la equivalencia (`Equiv`) para usar `Quotient.lift`. 
> 
> *Ambos enfoques se abordarán en el plan, pero me gustaría saber si tienes preferencia por priorizar uno sobre el otro para el uso práctico en el proyecto Aczel.*

## Open Questions

> [!WARNING]
> ¿Tenemos ya alguna definición de **Ordinal Límite** explícita en `scratch/` o deberíamos definirla desde cero? Una definición típica sería `IsLimit α := α ≠ 0 ∧ ∀ β < α, succ β < α`.

## Proposed Changes

La implementación será simétrica para ambos ecosistemas, variando únicamente en los universos polimórficos requeridos por `UnivOrd`.

### 1. Inducción Bien Fundada (Strong Induction)
Dado que ya tenemos `well_founded_lt`, el primer paso es exponer el principio general de inducción transfinita.

#### [NEW] `OrdinalsInductionRecursion/CountableOrd/Induction.lean`
#### [NEW] `OrdinalsInductionRecursion/UnivOrd/Induction.lean`
- **`Ordinal.inductionOn`**: Exponer un teorema alias directo de `WellFounded.induction well_founded_lt`.
  `theorem inductionOn {C : Ordinal → Prop} (o : Ordinal) (h : ∀ α, (∀ β < α, C β) → C α) : C o`

### 2. Clasificación: Cero, Sucesor y Límite
Para hacer inducciones clásicas de teoría de conjuntos, necesitamos clasificar los ordinales.

#### [MODIFY] `OrdinalsInductionRecursion/CountableOrd/Ordinals.lean`
#### [MODIFY] `OrdinalsInductionRecursion/UnivOrd/Ordinals.lean`
- **Definir `succ`** sobre el cociente `Ordinal` (actualmente solo existe `zero` y `omega`, pero la operación sucesor `succ` se debe promover a `Ordinal`).
- **Definir `IsLimit`**: `def IsLimit (x : Ordinal) : Prop := x ≠ 0 ∧ ∀ y < x, succ y < x` (o equivalente).
- **Teorema de Tricotomía Estructural**: `theorem zero_succ_limit (x : Ordinal) : x = 0 ∨ (∃ y, x = succ y) ∨ IsLimit x`

### 3. Inducción y Recursión por Casos Límite
Una vez definida la tricotomía, construiremos un principio de inducción "clásico".

#### [MODIFY] `OrdinalsInductionRecursion/CountableOrd/Induction.lean`
#### [MODIFY] `OrdinalsInductionRecursion/UnivOrd/Induction.lean`
- **`limitInductionOn`**: Un teorema que requiere 3 demostraciones:
  - Caso base: `C 0`
  - Paso inductivo: `∀ α, C α → C (succ α)`
  - Caso límite: `∀ λ, IsLimit λ → (∀ β < λ, C β) → C λ`
- **`limitRec`**: Función basada en `WellFounded.fix` para producir datos separando por casos según la tricotomía.

### 4. Recursión sobre `PreOrd` y Lifting (Alternativa Estructural)
Para funciones como la suma, multiplicación o exponenciación recursiva, a veces es más fácil definirlas en los `PreOrd` y hacer *lifting*.

#### [MODIFY] `OrdinalsInductionRecursion/CountableOrd/Arith.lean`
#### [MODIFY] `OrdinalsInductionRecursion/UnivOrd/Arith.lean`
- Establecer patrones o macros de cómo definir operaciones sobre `PreOrd` por inducción estructural (`PreOrd.recOn`) y demostrar que respetan `Equiv` usando lemas auxiliares.

## Verification Plan

### Automated Tests
- Compilar los nuevos módulos y asegurarse de que los teoremas `inductionOn` y `limitInductionOn` pasan el kernel de Lean sin axiomas inconsistentes (usar `#print axioms`).

### Manual Verification
- Utilizaremos el directorio `scratch/` para definir una pequeña función recurrente sobre `Ordinal` (por ejemplo, definir la adición ordinal usando el principio de recursión transfinita creado) y demostraremos que se evalúa o razona correctamente.
