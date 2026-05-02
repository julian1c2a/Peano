# Planificación: Rama Fundacional — Álgebra Inicial de Peano

**Rama:** `peano-foundations`  
**Fecha:** 2026-05-02  
**Autor:** Julián Calderón Almendros

---

## 1. El problema fundacional identificado

### Situación actual

El proyecto construye `ℕ₀` como un tipo inductivo de Lean 4:

```lean
inductive ℕ₀ : Type where
  | zero : ℕ₀
  | succ : ℕ₀ → ℕ₀
```

Los axiomas de Peano (inyectividad de `succ`, `zero ≠ succ n`, principio de inducción) se demuestran como **teoremas** sobre esta definición inductiva. El fundamento real del sistema es **CIC** (Cálculo de Construcciones Inductivas), la teoría de tipos de Lean 4 — no la aritmética de Peano.

### La inversión fundacional

En el diseño original, la dirección de dependencia es:

```
CIC  →  inductive ℕ₀  →  axiomas PA (como teoremas)
```

El objetivo fundacional del proyecto es que los axiomas de Peano sean el **punto de partida**, y que todo lo demás — incluyendo la existencia del tipo inductivo `ℕ₀` — sea *consecuencia* de esos axiomas.

---

## 2. Análisis teórico

### ¿Por qué no se puede escapar de CIC en Lean 4?

Lean 4 tiene CIC como meta-teoría. Cualquier declaración, incluyendo `axiom ℕ₀ : Type 0`, vive dentro de CIC. No es posible eliminar CIC del sustrato.

**Opción radical descartada (como sustitución):** Declarar `axiom ℕ₀ : Type 0` junto con los axiomas de PA como `axiom` y *usar ese tipo* para toda la aritmética. Esto destruiría el cómputo (`#eval`, `decide`, reducción definitoria), porque los tipos declarados con `axiom` no tienen reglas de cómputo. La computabilidad es un objetivo central del proyecto.

**Opción no descartada (como paridad):** Declarar un sistema PA puramente axiomático *en paralelo* al tipo inductivo, y demostrar formalmente que ambos son el mismo objeto matemático (vía el isomorfismo único de inicialidad). Esta es la ampliación que desarrolla la sección §2.5 de abajo.

### La respuesta correcta: álgebra inicial

La solución constructivista es demostrar que `ℕ₀` es el **objeto inicial** en la categoría de álgebras de Peano. Esta propiedad:

1. **Caracteriza `ℕ₀` de forma única** (salvo isomorfismo único): cualquier tipo que satisfaga los axiomas de Peano es isomorfo a `ℕ₀` mediante un único isomorfismo.

2. **Es la "construcción desde los axiomas"**: en lugar de postular `ℕ₀` y demostrar que satisface PA, se define qué es un "sistema de Peano" y se demuestra que `ℕ₀` es el único (inicial).

3. **Mantiene el cómputo**: `ℕ₀` sigue siendo el tipo inductivo original, con pattern matching y reducción.

La dirección de dependencia queda así:

```
CIC
 └→  inductive ℕ₀  (realización canónica y computable)
 └→  PeanoSystem   (axiomas de Peano como estructura)
      └→  ℕ₀_initial  (ℕ₀ es el álgebra inicial)
           └→  toda la aritmética, combinatoria, teoría de grupos...
```

### Consecuencia filosófica

La pregunta "¿construyo el tipo inductivo desde los axiomas de PA?" tiene respuesta precisa en este marco:

> El tipo inductivo `ℕ₀` **es** la construcción. Los axiomas de PA más el principio de recursión primitiva caracterizan únicamente (salvo iso.) a `ℕ₀`. La inicialidad en la categoría de álgebras de Peano es exactamente esa unicidad.

---

## 2.5 El sistema axiomático puro y la paridad formal

Existe una segunda dirección que **complementa** — no sustituye — el enfoque anterior. En lugar de demostrar que el tipo inductivo es el álgebra inicial, se puede *declarar* un sistema de Peano puramente axiomático usando los mecanismos `axiom` de Lean 4:

```lean
-- Sistema PA puro: sin implementación, sólo lógica
axiom ℕ₀_pa   : Type 0
axiom zero_pa  : ℕ₀_pa
axiom succ_pa  : ℕ₀_pa → ℕ₀_pa
axiom succ_inj_pa     : ∀ m n : ℕ₀_pa, succ_pa m = succ_pa n → m = n
axiom zero_ne_succ_pa : ∀ n : ℕ₀_pa, zero_pa ≠ succ_pa n
axiom ind_pa          : ∀ P : ℕ₀_pa → Prop,
                          P zero_pa → (∀ n, P n → P (succ_pa n)) → ∀ n, P n
```

Este sistema:

- **No tiene reglas de cómputo**: `#eval` no funciona sobre `ℕ₀_pa`.
- **Es puramente lógico/proposicional**: captura los axiomas de Peano en sentido estricto.
- **Es consistente**: no añade inconsistencia porque los seis `axiom` son satisfacibles (testigo: el propio `ℕ₀` inductivo).

### La paridad: `PurePA : PeanoSystem`

Los seis axiomas forman exactamente una instancia de `PeanoSystem`:

```lean
def PurePA : PeanoSystem where
  N        := ℕ₀_pa
  zero     := zero_pa
  succ     := succ_pa
  inj      := succ_inj_pa
  discr    := zero_ne_succ_pa
  ind      := ind_pa
  prim_rec := by
    -- prim_rec se deriva de ind_pa por el mismo argumento de ℕ₀_prim_rec
    -- (la inducción basta para construir la función recursiva canónica)
    ...
```

Por `peano_unique` (ya demostrado en `Initiality.lean`), existe un **único isomorfismo**:

```lean
theorem pa_parity :
    ∃! f : PeanoMorphism ℕ₀_PeanoSystem PurePA, isPeanoIso ℕ₀_PeanoSystem PurePA f
```

Esto es la **paridad formal**:

> Los axiomas de Peano declarados con `axiom` de Lean y el tipo inductivo `ℕ₀` son *el mismo objeto matemático*, distinguibles únicamente en su implementación computacional.

### Tabla comparativa

| Dimensión | `ℕ₀` (inductivo) | `ℕ₀_pa` (axiomático) |
|---|---|---|
| Cómputo | ✅ `#eval`, `decide`, pattern matching | ❌ sólo proposicional |
| Reducción definitoria | ✅ `match` reduce | ❌ opaco |
| Derivación de teoremas PA | ✅ todos | ✅ todos (vía iso.) |
| Fundamento en CIC | Tipo inductivo nativo | `axiom` + consistencia externa |
| Transporte de resultados | — | ✅ via morfismo `ℕ₀_PeanoSystem → PurePA` |

### ¿Por qué esto importa?

1. **Independencia de la implementación**: ningún teorema sobre `ℕ₀` depende de que sea inductivo — sólo depende de los axiomas de Peano. El isomorfismo hace esto *verificable*.

2. **Fundamentos explícitos**: establece cuáles son exactamente los axiomas necesarios (los seis), sin dependencia oculta de CIC más allá de lo que cualquier sistema de Peano requeriría en cualquier meta-teoría.

3. **Transporte bidireccional**: cualquier teorema demostrado sobre `ℕ₀_PeanoSystem` se transporta a `PurePA` mediante el morfismo de la paridad, y viceversa. En particular, la aritmética completa del proyecto (suma, multiplicación, primos, Sylow…) es válida en cualquier sistema de Peano, no sólo en `ℕ₀`.

4. **Justificación del tipo inductivo**: la paridad no elimina al tipo inductivo — lo *justifica*: es la única realización computable de los axiomas de Peano.

### Nota sobre `prim_rec` en `PurePA`

El campo `prim_rec` de `PeanoSystem` requiere demostrar el principio de recursión primitiva desde `ind_pa`. Esto es posible porque la recursión primitiva *se deriva* de la inducción proposicional más el axioma de elección (`Classical.choice` de Lean), siguiendo el mismo argumento usado en `Initiality.lean → ℕ₀_prim_rec`. Como `PurePA` vive dentro del universo de Lean 4, tiene acceso a `Classical.choice`.

Alternativamente, se puede añadir un séptimo `axiom` de recursión y demostrar que sigue siendo consistente (con testigo `ℕ₀`). La opción preferida es derivar `prim_rec` de `ind_pa` para minimizar axiomas.

---

## 3. La cuestión de los pares y las listas

Una vez justificada la construcción de `ℕ₀`, se puede demostrar que `ℕ₀` es *computacionalmente completo* en el sentido de que:

- **Pares ordenados**: `ℕ₀ × ℕ₀ ≅ ℕ₀` mediante la función de apareamiento de Cantor.
- **Listas finitas**: las listas finitas de elementos de `ℕ₀` se codifican en `ℕ₀` mediante la función β de Gödel (que usa el Teorema Chino del Resto).

Esto muestra que no es necesario introducir tipos adicionales (pares, listas) como primitivos: todos son "construibles" desde `ℕ₀`.

---

## 4. Estructura de archivos de la nueva rama

```
Peano/PeanoNat/Foundation/
├── PeanoSystem.lean       -- Estructuras: PeanoSystem, PeanoMorphism, isPeanoIso
├── Initiality.lean        -- ℕ₀ es la álgebra inicial; corolarios de unicidad y rec
├── PureAxioms.lean        -- Sistema PA axiomático puro + teorema de paridad
├── CantorPairing.lean     -- Biyección ℕ₀ × ℕ₀ ≅ ℕ₀
└── GodelBeta.lean         -- Codificación de listas en ℕ₀ via β de Gödel
Peano/PeanoNat/Foundation.lean  -- Módulo paraguas
```

---

## 5. Detalle por archivo

### 5.1 `PeanoSystem.lean`

Define la categoría de álgebras de Peano.

```lean
namespace Peano.Foundation

-- Los axiomas de Peano como estructura (bundled algebra)
structure PeanoSystem where
  N    : Type 0
  zero : N
  succ : N → N
  inj   : ∀ m n : N, succ m = succ n → m = n
  discr : ∀ n : N, zero ≠ succ n
  ind   : ∀ P : N → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n

-- Morfismo entre álgebras de Peano
structure PeanoMorphism (A B : PeanoSystem) where
  map       : A.N → B.N
  pres_zero : map A.zero = B.zero
  pres_succ : ∀ n, map (A.succ n) = B.succ (map n)

-- Isomorfismo de álgebras de Peano
def isPeanoIso (A B : PeanoSystem) (f : PeanoMorphism A B) : Prop :=
  ∃ g : PeanoMorphism B A,
    (∀ x, g.map (f.map x) = x) ∧ (∀ y, f.map (g.map y) = y)
```

**Nota sobre `rec`:** No se incluye el principio de recursión (`rec`) como campo de `PeanoSystem`. Se demostrará como *corolario* de la inicialidad. Esto es más limpio: un sistema de Peano se define sólo con `ind` (inducción sobre `Prop`), y la recursión se *deriva*.

---

### 5.2 `Initiality.lean`

Contiene la prueba central de la rama.

**Instancia `ℕ₀_PeanoSystem`** — reutiliza de `Axioms.lean`:

- `succ_injective` (línea 146)
- `cero_neq_succ` (línea 91)
- `induction_principle` (línea 198)

```lean
def ℕ₀_PeanoSystem : PeanoSystem where
  N    := ℕ₀
  zero := 𝟘
  succ := σ
  inj   := fun n m h => Peano.Axioms.succ_injective n m h
  discr := Peano.Axioms.cero_neq_succ
  ind   := Peano.Axioms.induction_principle
```

**Morfismo canónico** — definido por recursión estructural:

```lean
def ℕ₀_to (A : PeanoSystem) : ℕ₀ → A.N
  | 𝟘   => A.zero
  | σ n => A.succ (ℕ₀_to A n)
```

**Teorema central:**

```lean
theorem ℕ₀_initial (A : PeanoSystem) :
    ∃! h : ℕ₀ → A.N,
      h 𝟘 = A.zero ∧ ∀ n, h (σ n) = A.succ (h n)
```

- *Existencia:* `ℕ₀_to A` satisface ambas ecuaciones por definición.
- *Unicidad:* si `h'` también satisface las ecuaciones, entonces `h' = ℕ₀_to A` por inducción usando `A.ind`.

**Corolario — unicidad salvo iso. único:**

```lean
theorem peano_unique (A B : PeanoSystem) :
    ∃! f : PeanoMorphism A B, isPeanoIso A B f
```

**Corolario — principio de recursión:**

```lean
theorem ℕ₀_rec_principle (A : Type 0) (a : A) (f : A → A) :
    ∃! h : ℕ₀ → A, h 𝟘 = a ∧ ∀ n, h (σ n) = f (h n)
```

Esto formaliza que la recursión primitiva es *deducible* de la inicialidad, no un axioma adicional.

---

### 5.3 `CantorPairing.lean`

Demuestra `ℕ₀ × ℕ₀ ≅ ℕ₀`.

**Prerequisitos existentes:** `Add.lean`, `Mul.lean`, `Div.lean` (con `mod`, `%`, división entera).

**Números triangulares** (nueva definición):

```lean
-- T(n) = n * (n+1) / 2
def triag (n : ℕ₀) : ℕ₀ := (n * (σ n)) / (𝟙 + 𝟙)
```

Lema previo: `two_dvd_mul_succ : ∀ n, (𝟙 + 𝟙) ∣ n * (σ n)`
(Demostración: por inducción; uno de n, σ n es par.)

**Función de apareamiento de Cantor:**

```lean
def pair (m n : ℕ₀) : ℕ₀ := triag (m + n) + m
```

**Anti-diagonal** (inversa parcial):

```lean
-- El único w tal que T(w) ≤ z < T(w+1)
def antidiag (z : ℕ₀) : ℕ₀   -- por recursión bien fundada (WellFounded.lean)
def fst (z : ℕ₀) : ℕ₀ := z - triag (antidiag z)
def snd (z : ℕ₀) : ℕ₀ := antidiag z - fst z
```

**Teoremas de corrección:**

```lean
theorem pair_fst (m n : ℕ₀) : fst (pair m n) = m
theorem pair_snd (m n : ℕ₀) : snd (pair m n) = n
theorem pair_surj (z : ℕ₀)  : pair (fst z) (snd z) = z
-- Corolario: pair es biyección ℕ₀ × ℕ₀ → ℕ₀
```

---

### 5.4 `GodelBeta.lean`

Codifica listas finitas de `ℕ₀` como elementos de `ℕ₀`. Demuestra que la introducción de `List ℕ₀` como tipo primitivo es innecesaria desde el punto de vista fundacional.

**Prerequisitos existentes:**

- `chinese_remainder` en `NumberTheory/ChineseRemainder.lean`
- `mod` / `%` en `Div.lean` + `NumberTheory/ModEq.lean`
- Factorial en `Combinatorics/Factorial.lean`
- `Coprime`, `coprime_comm` en `Arith.lean`

**Lema de coprimalidad** (nuevo):

```lean
-- Si (j - i) ∣ b y i ≠ j, entonces (1 + i·b) y (1 + j·b) son coprimos
lemma one_add_mul_coprime (i j b : ℕ₀)
    (hdvd : (j - i) ∣ b) (hij : i ≠ j) :
    Coprime (𝟙 + i * b) (𝟙 + j * b)
```

*Demostración:* si primo `p | gcd`, entonces `p | (j-i)·b`; como `p | 1+i·b`, resulta `p ∤ b`; luego `p | (j-i)` y por tanto `p | b` (pues `(j-i) | b`): contradicción.

**CRT para n módulos** (extensión de `chinese_remainder`):

```lean
-- Para b = n! y módulos 1+(j+1)·b pairwise coprimos:
theorem crt_sequence (n b : ℕ₀) (a : ℕ₀ → ℕ₀) :
    ∃ x : ℕ₀, ∀ j, j ≤ n → x % (𝟙 + (σ j) * b) = a j
```

*Demostración:* inducción en `n`, aplicando `chinese_remainder` en cada paso.

**Función β de Gödel:**

```lean
def beta (c b i : ℕ₀) : ℕ₀ := c % (𝟙 + (σ i) * b)
```

**Codificación y decodificación:**

```lean
-- Codifica la lista l en un par (c, b) representado como natural via pair
def encodeList (l : List ℕ₀) : ℕ₀
-- Decodifica extrayendo n elementos desde z = pair c b
def decodeList (z : ℕ₀) (n : ℕ₀) : List ℕ₀

theorem encode_decode (l : List ℕ₀) :
    decodeList (encodeList l) l.length = l
```

---

### 5.5 `Foundation.lean` (paraguas)

```lean
import Peano.PeanoNat.Foundation.PeanoSystem
import Peano.PeanoNat.Foundation.Initiality
import Peano.PeanoNat.Foundation.CantorPairing
import Peano.PeanoNat.Foundation.GodelBeta
```

Se añade `import Peano.PeanoNat.Foundation` a `Peano.lean` (raíz).

---

## 6. Orden de implementación

| Paso | Archivo | Dificultad | Dependencias |
|------|---------|-----------|--------------|
| 1 | `PeanoSystem.lean` | Baja | `PeanoNat` |
| 2 | `Initiality.lean` | Media | `PeanoSystem`, `Axioms` |
| 2b | `PureAxioms.lean` | Baja | `PeanoSystem`, `Initiality` |
| 3 | `CantorPairing.lean` | Media | `Add`, `Mul`, `Div`, `WellFounded` |
| 4 | `GodelBeta.lean` | Alta | `ChineseRemainder`, `Factorial`, `Arith`, `CantorPairing` |
| 5 | `Foundation.lean` | Trivial | todos los anteriores |

---

## 7. Verificación

```bash
lake build
# Esperado: 0 errors, 0 sorry

-- Álgebra inicial
#check Peano.Foundation.ℕ₀_PeanoSystem
#check Peano.Foundation.ℕ₀_initial
#check Peano.Foundation.peano_unique
#check Peano.Foundation.ℕ₀_rec_principle

-- Paridad axiomática
#check Peano.Foundation.PurePA
#check Peano.Foundation.pa_parity
-- (Los axiom privados ℕ₀_pa etc. NO son accesibles desde fuera del archivo)

-- Cantor
#check Peano.Foundation.pair_fst
#check Peano.Foundation.pair_snd
#check Peano.Foundation.pair_surj

-- Gödel
#check Peano.Foundation.encode_decode
```

**Test de confinamiento**: verificar que `ℕ₀_pa` no es accesible fuera de `PureAxioms.lean`:

```lean
-- En cualquier otro archivo, esto debe fallar:
-- #check ℕ₀_pa   -- Error: unknown identifier
```

---

## 8. Relación con el proyecto más amplio

Este módulo es la respuesta a la pregunta: *¿desde los axiomas de Peano se puede construir el tipo inductivo natural?*

La respuesta formal es: **el tipo inductivo `ℕ₀` ES el álgebra inicial de Peano dentro de CIC**, y la inicialidad prueba que es la única realización posible (salvo iso.). Ningún otro sistema de Peano puede ser "diferente" de `ℕ₀`.

En el contexto del proyecto más amplio (con `AczelSetTheory`, `ZfcSetTheory`):

- Los naturales obtenidos aquí son **los naturales de Peano** en sentido estricto, no los de ZFC.
- La función de apareamiento de Cantor y la codificación de Gödel son el puente entre la aritmética pura y la teoría de conjuntos finitos.
- La función β de Gödel es también la base de la aritmética de la computabilidad (funciones recursivas primitivas).

### Sobre el sistema axiomático puro

El módulo `PureAxioms.lean` establece una distinción fundacional que el resto del proyecto presupone pero no formaliza:

> La aritmética de Peano (como teoría lógica de primer orden, o aquí como sistema de `axiom` de Lean) y la aritmética computable de `ℕ₀` (como tipo inductivo) son **coextensivas en contenido lógico** pero **distintas en contenido computacional**.

Esto tiene relevancia directa para la conexión con ZFC: cuando en `ZfcSetTheory` se define `ω` (los naturales de von Neumann) y se demuestra que satisface los axiomas de Peano, el isomorfismo `ω ≅ ℕ₀` es exactamente una instancia de `peano_unique`. El `PurePA` de esta rama es el intermediario lógico: `ω ≅ PurePA ≅ ℕ₀`.
