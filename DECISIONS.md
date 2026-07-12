# Decisiones de Diseño — Peano

**Última actualización:** 2026-07-12
**Autor**: Julián Calderón Almendros

Registro de decisiones arquitectónicas (ADR) de este proyecto. Cada entrada documenta
*qué* se decidió y *por qué*, para referencia futura.

> Este fichero adopta el esqueleto unificado de `lean4-project-template`
> (ADR-001–009, traducidos) y **preserva íntegras**, renumeradas a partir de
> ADR-010, las decisiones reales específicas de Peano que ya existían aquí (FSet
> como lista ordenada, ℕ₀ inductivo, FinGroup polimórfico, el lema puente
> `mapOn_bijective_cast`, etc.) — son, junto con las de ROBINSON_PlusPlus, las de
> mejor calidad entre los proyectos hermanos.

---

## ⚠️ MANDATORIES (reglas vinculantes de este proyecto)

**Sin MANDATORIES declaradas** — este proyecto no prohíbe `Classical.*` (se usa con
normalidad, p. ej. `Classical.byContradiction` como sustituto de `by_contra`, no
disponible sin Mathlib). AczelSetTheory (proyecto sucesor que consume `peanolib`)
**sí** tiene esa directiva — ver su propio `DECISIONS.md` §MANDATORIES — pero no
aplica retroactivamente a Peano.

---

## ADR-001: Sin dependencia de Mathlib

**Fecha**: 2025-01-01
**Estado**: Aceptado

**Decisión**: este proyecto no depende de Mathlib.

**Justificación**: objetivo educativo — formalizar la aritmética de Peano desde cero
usando solo el núcleo de Lean 4. Construir toda la infraestructura (inducción,
recursión, aritmética) desde el tipo inductivo `ℕ₀` es el propósito íntegro del
proyecto.

**Consecuencias**: toda la infraestructura necesaria (`ExistsUnique`, principios de
recursión, div/mod, etc.) se construye desde cero.

---

## ADR-002: `autoImplicit = false`

**Fecha**: 2025-01-01
**Estado**: Aceptado

**Decisión**: `moreServerArgs := #["-DautoImplicit=false"]` en `lakefile.lean`.

**Justificación**: las anotaciones de tipo explícitas evitan problemas accidentales
de polimorfismo de universos y hacen el código más legible y mantenible.

**Consecuencias**: todas las variables deben declararse o anotarse explícitamente.

---

## ADR-003: Sistema de bloqueo de archivos

**Fecha**: 2026-04-08
**Estado**: Aceptado

**Decisión**: usar `git-lock.bash` + `locked_files.txt`/`frozen_files.txt` + hook
`pre-commit` para prevenir ediciones accidentales de módulos terminados. Sustituye
al antiguo sistema de congelado basado en `.bat` (no portable).

**Justificación**: las pruebas de Lean 4 son frágiles. Los scripts bash son
multiplataforma (Windows Git Bash + Linux/macOS), a diferencia del `.bat` anterior.

**Consecuencias**: el flujo de trabajo exige bloquear/desbloquear ficheros (ver
`AI-GUIDE.md` §20-21). **Nota de auditoría (2026-07-12)**: `frozen_files.txt` listaba
17 ficheros con rutas obsoletas (estilo plano previo a la reorganización en
subdirectorios, p. ej. `Peano/PeanoNatAxioms.lean`, hoy `Peano/PeanoNat/Axioms.lean`)
— el sistema de freeze estaba desincronizado con la estructura real. **Corregido
(2026-07-12)**: `frozen_files.txt` reescrito con las 17 rutas actualizadas. También
se corrige un bug real en `git-lock.bash` (`unlock`/`thaw` no vaciaban la lista al
quitar el último fichero, por el exit code 1 de `grep -Fv` cortocircuitando el `&&`
previo al `mv`). El `chmod a-w` de este script tampoco protege nada en NTFS/Windows —
verificado (`IsReadOnly = False` en un fichero listado como bloqueado); el lock es un
contrato social + hook `pre-commit`, no una protección real del sistema de ficheros.

---

## ADR-004: Convenciones de nombres Mathlib

**Fecha**: 2026-04-08
**Estado**: Aceptado

**Decisión**: todos los identificadores siguen las convenciones de nombres de
Mathlib4, documentadas en `NAMING-CONVENTIONS.md`.

**Justificación**: consistencia con el ecosistema Lean 4 más amplio.

**Consecuencias**: ver `NAMING-CONVENTIONS.md` para el diccionario completo. **Nota de
auditoría (2026-07-12, resuelta en ADR-015)**: `Peano/PeanoNat/Add.lean` declara `add_l`, una
definición **alternativa** de la suma que recursa sobre el argumento izquierdo `n` (en
vez de sobre `m`, como `add`), usada solo como andamiaje para demostrar
`add_zero_eq_add_l_zero` y equivalencias similares. El sufijo `_l` aquí **no** es el
`_left` de la Regla 11 (variante lateral de una relación) — denota "definición
alternativa con recursión sobre argumento izquierdo". Resuelto en **ADR-015**: `add_l`
permanece pública.

---

## ADR-005: Namespaces alineados con directorios

**Fecha**: 2025-01-01
**Estado**: Aceptado (con excepción histórica documentada — ver ADR-010)

**Decisión**: cada subdirectorio corresponde a un sub-namespace.

**Justificación**: mapeo 1:1 claro entre sistema de ficheros y jerarquía de
namespaces.

**Consecuencias**: `new-module.bash`/`gen-root.bash` escanean recursivamente. Ver
ADR-010 sobre la excepción histórica de este proyecto (directorio `Peano/` vs.
namespace `Peano` con mismatch heredado).

---

## ADR-006: Subdirectorios temáticos para la organización de módulos

**Fecha**: 2026-04
**Estado**: Aceptado

**Decisión**: agrupar módulos en subdirectorios temáticos: `Combinatorics/`,
`ListsAndSets/`, `NumberTheory/`, `Combinatorics/GroupTheory/`,
`Combinatorics/GroupTheory/Sylow/`, `Prelim/`.

**Justificación**: con 49+ módulos, la organización plana se volvió inmanejable.

**Consecuencias**: los imports usan rutas completas (`Peano.PeanoNat.Combinatorics.Pow`).

---

## ADR-007: Árbol de documentación `doc/REFERENCE-{tema}.md`

**Fecha**: 2026-05-10
**Estado**: Aceptado e **implementado** (el más avanzado de los proyectos hermanos en
este punto)

**Decisión**: `REFERENCE.md` es el índice raíz; `doc/REFERENCE-{tema}.md` son los
nodos temáticos (12 secciones por símbolo: tipo, firma, módulo, importancia). El
directorio `doc/` se creó el 2026-05-10 con `REFERENCE-GroupTheory.md` como primer
nodo.

**Justificación**: `REFERENCE.md` como monolito crecía inmanejable (>1000 líneas) —
exactamente el síntoma que `AI-GUIDE.md` §0.5 advierte evitar.

**Consecuencias**: todo `.lean` nuevo se proyecta en su nodo temático
correspondiente; si no existe, se crea. `REFERENCE.md` se actualiza con la fila de
módulo y el conteo de jobs.

---

## ADR-008: Sistema de anotaciones en REFERENCE.md

**Fecha**: 2026-04
**Estado**: Aceptado

**Decisión**: las entradas de REFERENCE.md incluyen anotaciones `@axiom_system` y
`@importance`.

**Justificación**: ayuda a los asistentes de IA a priorizar qué módulos/teoremas
cargar como contexto.

**Consecuencias**: las anotaciones deben mantenerse al actualizar módulos.

---

## ADR-009: `NAMING-CONVENTIONS.md` como fichero separado

**Fecha**: 2026-04-08
**Estado**: Aceptado

**Decisión**: las convenciones de nombres viven en un `NAMING-CONVENTIONS.md`
dedicado, con un resumen en `AI-GUIDE.md`.

**Justificación**: el diccionario completo con 12 reglas es demasiado extenso para
`AI-GUIDE.md` solo.

**Consecuencias**: si divergen, `NAMING-CONVENTIONS.md` es autoritativo.

---

## ADR-010: Directorio `Peano/` vs. namespace `Peano` — mismatch heredado

**Fecha**: 2025-01-01
**Estado**: Aceptado (deuda arquitectónica reconocida, no se corrige retroactivamente)

**Decisión**: los módulos fuente viven en `Peano/`, el `lean_lib` se llama `Peano`, el
fichero raíz es `Peano.lean`. Los imports y namespaces usan el prefijo `Peano.`.

**Justificación**: arquitectura histórica desde el inicio del proyecto — el nombre de
directorio `Peano` refleja el contenido de la librería, mientras que `Peano` es
también el namespace de cara al público.

**Consecuencias**: los scripts (`gen-root.bash`, `new-module.bash`) detectan el
directorio de módulos a partir de `Glob.submodules` en `lakefile.lean`. Requiere estar
al tanto del desajuste namespace/import-prefix al escribir scripts de scaffolding
nuevos.

---

## ADR-011: Tipo inductivo `ℕ₀` como fundamento — axiomas de Peano demostrados, no postulados

**Fecha**: 2025-01-01
**Estado**: Aceptado

**Decisión**: los 8 axiomas de Peano se derivan como teoremas a partir del tipo
inductivo `ℕ₀`, no se postulan como `axiom`.

**Justificación**: máximo rigor — los axiomas se demuestran, no se asumen. Da un
fundamento constructivo donde toda propiedad es trazable a la definición del tipo
inductivo.

**Consecuencias**: el módulo `PeanoNat/Axioms.lean` contiene teoremas, no axiomas.

---

## ADR-012: `FSet` como estructura de lista ordenada (no `Quotient`)

**Fecha**: 2026-04 (revisado 2026-04-27)
**Estado**: Aceptado

**Decisión**: `FSet α` se define como una `structure` con una lista ordenada y un
invariante `Sorted`:

```lean
structure FSet (α : Type) [LT α] [StrictLinearOrder α] where
  elems  : List α
  sorted : Sorted (· < ·) elems
  nodup  : elems.Nodup
```

No como `Quotient (Perm.setoid α)`.

**Justificación**: el enfoque de lista ordenada mantiene todas las operaciones
computables (sin `noncomputable`), da representantes canónicos para la igualdad
(`FSet.eq_of_mem_iff`), y es directamente compatible con `DecidableEq (List α)`.
Requiere `LT α` con `StrictLinearOrder α` en el tipo de elemento — ya disponible para
todos los tipos usados en el proyecto (`ℕ₀`, `Tuple`, `List`, `FSet` mismo). El
enfoque `Quotient` haría `DecidableEq FSet` no computable.

**Consecuencias**: `FSet α` requiere `[StrictLinearOrder α]` en el tipo de elemento.
`sortedInsert` es la primitiva de inserción central. Dos `FSet` son iguales sii tienen
los mismos elementos (extensionalidad vía `FSet.eq_of_mem_iff`).

---

## ADR-013: Sin typeclasses algebraicas propias

**Fecha**: 2026-05
**Estado**: Aceptado

**Decisión**: no definir typeclasses propias como `CommMonoid ℕ₀` u
`OrderedCommSemiring ℕ₀`. En su lugar, probar las propiedades como lemas sueltos.

**Justificación**: sin Mathlib, las typeclasses propias duplicarían pobremente la
jerarquía de Mathlib. Los lemas sueltos bastan para las necesidades actuales y evitan
una abstracción prematura.

**Consecuencias**: no hay `instance : CommMonoid ℕ₀` etc. Propiedades como
conmutatividad/asociatividad existen como teoremas nombrados.

---

## ADR-014: `FinGroup` polimórfico sobre un tipo arbitrario con `StrictLinearOrder`

**Fecha**: 2026-04-27
**Estado**: Aceptado

**Decisión**: `FinGroup` se parametriza sobre un tipo de elemento arbitrario `α`:

```lean
structure FinGroup (α : Type) [DecidableEq α] [LT α] [StrictLinearOrder α] where
  carrier  : FSet α
  op       : BinOpOn carrier
  id       : α
  inv      : MapOn carrier carrier
  id_in    : id ∈ carrier.elems
  op_assoc : ...
  op_id    : ...
  op_inv   : ...

abbrev ℕ₀FinGroup := FinGroup ℕ₀
```

Antes, `FinGroup` estaba fijado a `ℕ₀` (carrier era `ℕ₀FSet`, id era `ℕ₀`).

**Justificación**: el enfoque fijado a ℕ₀ bloqueaba desarrollos clave: (1)
`FinGroup (Subgroup G)` para la acción de conjugación que necesita Sylow III, (2)
grupos cociente para uso futuro. Hacer `FinGroup` polimórfico sobre `α` con
`StrictLinearOrder α` desbloquea ambos. El alias `abbrev ℕ₀FinGroup := FinGroup ℕ₀`
preserva la compatibilidad con todo el código existente de Sylow/Cosets/Action.

**Consecuencias**:

- `Action.lean`, `Cosets.lean`, `Sylow.lean` usan `(G : FinGroup ℕ₀)` (anotación de
  tipo explícita) — cambio mecánico, pruebas no afectadas.
- `Group.lean` cuantifica ahora sobre `{α} [DecidableEq α] [LT α] [StrictLinearOrder α]`.
- `FSet (Tuple ℕ₀ n)` funciona automáticamente vía `instStrictLinearOrderTuple`.
- Build: 51 jobs (`ListList.lean` y `FSetFSet.lean` eliminados, fusionados en
  `List.lean` y `FSet.lean`).

---

## ADR-015: Lema puente `mapOn_bijective_cast` — transporte de biyectividad por igualdad de codominio

**Fecha**: 2026-05-10
**Estado**: Aceptado

**Decisión**: cuando `▸` (transporte por igualdad) sobre un `MapOn` falla en el sitio
de uso porque ambos lados de la igualdad son términos concretos de tipo
`FSet (FSet ℕ₀)` (construidos vía `sortFSetList`), extraer un lema privado general
con variables libres `{B C : FSet β}` donde `subst heq` sí funciona:

```lean
private theorem mapOn_bijective_cast
    {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
    {A : FSet α} {B C : FSet β} (f : MapOn A B) (h : f.Bijective) (heq : B = C) :
    (heq ▸ f).Bijective := by
  subst heq; exact h
```

**Justificación**: Lean 4 no puede descargar `sortFSetList (...) = sortFSetList (...)`
automáticamente para `cases`/`subst`/`rcases rfl` en un sitio de uso concreto — la
eliminación dependiente necesita que la variable sea libre (metavariable) en el
contexto local. Al extraer a un lema donde `B : FSet β` es genuinamente libre,
`subst heq` sustituye `C := B` sin problemas.

**Consecuencias**: patrón reutilizable cada vez que se necesita transportar
`f.Bijective : (heq ▸ f).Bijective` cuando `heq` conecta tipos concretos. La solución
directa (`cases heq`, `subst heq`, `rcases rfl`, `▸` en modo término) siempre fallará
en ese caso; hace falta el lema puente.

---

## Plantilla para nuevas decisiones

## ADR-NNN: [Título]

**Fecha**: YYYY-MM-DD
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]

---

## ADR-015: `add_l` permanece pública en `Peano.Add`

**Fecha**: 2026-07-12
**Estado**: Aceptado

**Contexto**: `Add.lean` expone `add_l` (suma con recursión sobre el argumento
izquierdo) y sus lemas asociados (`add_zero_l`, `zero_add_l`, `add_one_l`,
`one_add_l`, `add_succ_l`, `succ_add_l`, `add_one_eq_add_l_one`,
`add_zero_eq_add_l_zero`). Dado que `add_l` no seguía ningún sufijo axiomático
documentado, se planteó hacerla `private` en ADR-004.

**Decisión**: `add_l` y sus lemas asociados **permanecen públicos** en el namespace
`Peano.Add` y en el export de `Peano.lean`.

**Justificación**:
1. Consumidores externos (p. ej. `AczelSetTheory`) pueden necesitar la definición
   alternativa para pruebas que se benefician de recursar sobre el argumento izquierdo.
2. Hacer `private` una definición ya exportada en el barrel raíz requiere desbloquear
   `Add.lean` (módulo congelado) y forzar una recompilación completa sin beneficio real.
3. El sufijo `_l` queda ahora documentado en `NAMING-CONVENTIONS.md` §9 con su
   semántica exacta, eliminando la ambigüedad original.

**Consecuencias**: el sufijo `_l` denota oficialmente "definición alternativa con
recursión sobre argumento izquierdo" en este proyecto. No generaliza a otras
operaciones salvo que se documente explícitamente en §9 de `NAMING-CONVENTIONS.md`.
