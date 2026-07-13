# Decisiones de Diseño — Peano

**Última actualización:** 2026-07-13
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

**MANDATORY-1 (desde 2026-07-13, ver ADR-017): prohibido `Classical.*` en código
nuevo.** Este proyecto se re-desarrolla como completamente intuicionista y
constructivista. Ningún `def`/`theorem` nuevo puede depender de `Classical.choice`
(verificable con `#assert_constructive`, ver `Peano/ConstructiveCheck.lean`). El
código existente que aún depende de él (`Prelim/Classical.lean`,
`Foundation/GodelBeta.lean`, `Combinatorics/GroupTheory/{Action,Sylow/CosetAction,
Sylow/Sylow}.lean`) es deuda a eliminar según el plan de `PLANNING.md`, no un
precedente a imitar. Esto **revierte** la nota histórica de esta sección (previamente
"este proyecto no prohíbe Classical.*") — ver ADR-017 para la justificación completa.

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
auditoría (2026-07-12, resuelta en ADR-016)**: `Peano/PeanoNat/Add.lean` declara `add_l`, una
definición **alternativa** de la suma que recursa sobre el argumento izquierdo `n` (en
vez de sobre `m`, como `add`), usada solo como andamiaje para demostrar
`add_zero_eq_add_l_zero` y equivalencias similares. El sufijo `_l` aquí **no** es el
`_left` de la Regla 11 (variante lateral de una relación) — denota "definición
alternativa con recursión sobre argumento izquierdo". Resuelto en **ADR-016**: `add_l`
permanece pública.

---

## ADR-005: Namespace plano por fichero — los directorios organizan, no anidan namespaces

**Fecha**: 2025-01-01 (corregido 2026-07-12 tras auditoría — la versión anterior de
este ADR describía mirroring completo de directorio, que **nunca** fue la práctica
real del proyecto)
**Estado**: Aceptado

**Decisión**: cada fichero `.lean` recibe un namespace propio de un solo nivel bajo
`Peano`: `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean` →
`namespace Peano.Sylow`, **no** `Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Sylow`.
Los subdirectorios (`Combinatorics/`, `GroupTheory/`, `Sylow/`, `Foundation/`, …) son
puramente organizativos. Un fichero puede declarar sub-namespaces internos más finos
para sub-conceptos (p. ej. dentro de `FSet.lean`), documentado localmente.

**Corrección de auditoría (2026-07-12)**: se encontró que 11 ficheros de
`Combinatorics/GroupTheory/` (incluyendo `Sylow/`) y 5 ficheros de `Foundation/`
**compartían literalmente el mismo namespace interno** (`namespace GroupTheory` /
`namespace Foundation`) en vez de tener cada uno el suyo — violación real de "un
namespace por fichero", no del mirroring de directorio (que nunca fue la regla
seguida). Corregido: cada fichero recibió su propio namespace
(`Action`, `NormalSubgroup`, `QuotientGroup`, `FirstIsomorphism`, `SecondIsomorphism`,
`ThirdIsomorphism`, `CorrespondenceTheorem`, `Zassenhaus`, `Cosets`, `CosetAction`,
`Sylow` / `PeanoSystem`, `Initiality`, `PureAxioms`, `CantorPairing`, `GodelBeta`),
añadiendo los `open Peano.<Dependencia>` necesarios para preservar las referencias
cruzadas sin cualificar entre estos ficheros. De paso se descubrió y corrigió un bug
de wiring preexistente y no relacionado: `Foundation/Foundation.lean` (el barrel)
nunca importaba `PureAxioms.lean`, dejando su `export` en `Peano.lean` como código
muerto nunca verificado por un build limpio.

**Justificación**: es la convención que el código ya seguía de facto en el resto del
proyecto (verificado por auditoría exhaustiva: 57/57 ficheros de producción fuera de
`GroupTheory/`/`Foundation/` ya usaban `Peano.<Concepto>` plano). Un mapeo 1:1
directorio↔namespace se vuelve verboso y frágil pasados 3-4 niveles de anidamiento
temático.

**Consecuencias**: `new-module.bash` crea el fichero en el subdirectorio indicado
pero declara el namespace con el nombre del fichero, no la ruta completa.
`gen-root.bash` sigue escaneando subdirectorios recursivamente para los `import`
(independiente del namespace). Ver ADR-010 sobre el mismatch, distinto y no
relacionado, entre el directorio raíz `Peano/` y el namespace/lean_lib `Peano`.

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

## ADR-016: `add_l` permanece pública en `Peano.Add`

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

---

## ADR-017: Re-desarrollo como proyecto completamente intuicionista/constructivista — prohibición de `Classical.*`

**Fecha**: 2026-07-13
**Estado**: Aceptado

**Contexto**: Peano nació sin la restricción de evitar lógica clásica (ver
MANDATORIES arriba, versión previa a esta entrada). Una auditoría de 2026-07-13
(`AUDIT-2026-07-13.md`) verificó por grep exhaustivo de `Classical\.` en los 73
módulos de producción que el uso real de `Classical.*` es mucho más acotado de lo que
la documentación histórica (`ConstructiveCheck.lean`) sugería: `FSet.lean` y
`FSetFunction.lean` usan `Decidable.byContradiction` (constructivo, no depende de
`Classical.choice`), no `Classical.byContradiction` como se documentaba; y
`CantorPairing.antidiag/fst/snd` son `def` computables, no `noncomputable` vía
`choose_unique` como decía el CHANGELOG histórico. El alcance real de `Classical.*` se
reduce a 3 focos:

1. `Prelim/Classical.lean` — expone `choose`/`choose_unique` vía
   `Classical.indefiniteDescription` (el único punto de entrada de `Classical.choice`
   al proyecto).
2. `Foundation/GodelBeta.lean` — `Classical.choose`/`choose_spec` en la reconstrucción
   de la función β de Gödel (4 usos).
3. `Combinatorics/GroupTheory/{Action.lean, Sylow/CosetAction.lean, Sylow/Sylow.lean}`
   — `Classical.em`/`Classical.byContradiction` en case-splits de teoría de grupos (10
   usos en total), en contextos donde el predicado en cuestión es sobre un `FSet`
   finito y probablemente `Decidable`.

**Decisión**: Peano se re-desarrolla como proyecto completamente intuicionista y
constructivista. `Classical.*` queda prohibido para código nuevo (MANDATORY-1 arriba).
El código existente que lo usa se elimina progresivamente reemplazando cada
`Classical.em`/`Classical.byContradiction` por un `Decidable`/`by_cases` explícito
cuando el predicado lo permite, y sustituyendo `Prelim.choose`/`GodelBeta`'s
`Classical.choose` por construcciones con búsqueda acotada/recursión bien fundada
(siguiendo el precedente ya sentado por `CantorPairing.antidiag`, que ya es
constructivo). Ver `PLANNING.md` §"Plan de desarrollo — eliminación de Classical" para
las fases concretas.

**Justificación**: máximo rigor lógico — un desarrollo intuicionista es constructivo
por diseño (todo teorema de existencia viene acompañado de un algoritmo real para
construir el testigo), lo cual es coherente con el espíritu fundacional del proyecto
(ADR-001: construir todo desde cero sin atajos) y con el hecho verificado de que el
95% del código ya era constructivo sin proponérselo explícitamente. `AczelSetTheory`
(sucesor que consume `peanolib`) ya exige esto en su propio `DECISIONS.md`
§MANDATORIES — alinear Peano con esa exigencia desde ahora evita una migración de
compatibilidad más costosa después del handoff.

**Consecuencias**:

- El plan de feature-freeze + handoff a `AczelSetTheory` (antes NEXT-STEPS.md T.3,
  PLANNING.md P.3) queda **pospuesto** hasta cerrar la eliminación de `Classical.*`
  — ver `CURRENT-STATUS-PROJECT.md` §"Próximos objetivos".
- `Peano/ConstructiveCheck.lean` (el mecanismo `#assert_constructive` que ya existía)
  pasa a ser la puerta de verificación de este ADR — se amplía su cobertura a todo
  símbolo público, no solo a la aritmética base.
- Los módulos "core aritmético" ya congelados (`frozen_files.txt`) no se ven afectados
  — ya son constructivos y no requieren tocarse.
- Los ficheros con `Classical.*` activo deben desbloquearse uno a uno siguiendo el
  protocolo de `AI-GUIDE.md` §20 para su refactorización; ninguno está congelado
  (`frozen_files.txt`), así que no aplica el protocolo de extensión `*Ext.lean`.

---

## Plantilla para nuevas decisiones

## ADR-NNN: [Título]

**Fecha**: YYYY-MM-DD
**Estado**: [Propuesto | Aceptado | Obsoleto | Sustituido por ADR-XXX]

**Contexto**: [¿Por qué hace falta esta decisión?]

**Decisión**: [¿Qué se decidió?]

**Justificación**: [¿Por qué esta opción frente a las alternativas?]

**Consecuencias**: [¿Cuáles son las contrapartidas?]
