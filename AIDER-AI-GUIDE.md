# Guía de Requisitos para REFERENCE.md y Documentación del Proyecto

**Última actualización:** 2026-02-12 18:45  
**Autor**: Julián Calderón Almendros

Este documento establece los requisitos y estándares para la documentación técnica del proyecto Peano.

---

## Requisitos para REFERENCE.md

### (1.) Los diferentes módulos .lean

### (2.) Las dependencias entre los módulos

### (3.) Espacios de nombres y relaciones entre ellos

### (4.) Axiomas introducidos y sus referencias a dónde se encuentran, módulo, namespace, orden en el que se declaran/definen

### (5.) En cuanto a los axiomas y las definciones, las queremos:

#### (5.1.) En nomenclatura matemática (no lean code), para una fácil comprensión humana, y para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean

#### (5.2.) Firma lean4 para que cuando se llamen en demostraciones o construcciones más elaboradas, se haga correctamente

#### (5.3.) Debe quedar en algún sitio las dependencias para construir la definición o el axioma

### (6.) Teoremas principales **sin demostración de ningún tipo**, con su referencia a dónde se encuentran, módulo, namespace, orden en el que se declaran/demuestran:

#### (6.1.) En nomenclatura matemática (no lean code), para una fácil comprensión humana, y para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean

#### (6.2.) Firma lean4 para que cuando se llamen en demostraciones o construcciones más elaboradas, se haga correctamente

#### (6.3.) Debe quedar en algún sitio las dependencias para construir la demostración del teorema

### (7.) Nada que no esté demostrado o construido debe estar en este archivo, ni siquiera como comentario o como "teorema pendiente". Solo lo que ya esté demostrado o construido en los archivos .lean

### (8.) Cada vez que cargas un archivo .lean, actualizas (si es necesario) el REFERENCE.md con lo que se ha demostrado o construido en ese archivo, siguiendo los puntos anteriores. Si hace falta anotar una fecha y la fecha de la última modificación del archivo .lean, estará bien, para trazar bien lo que de hecho tenemos

### (9.) El archivo REFERENCE.md debe ser lo único que necesites para escribir la documentación, o para hacer un nuevo archivo/módulo .lean de forma que no haya que cargar la totalidad de los tokens que tiene actualmente el proyecto

---

## Requisitos de Timestamps

### (10.) Formato de Fecha y Hora

Todos los archivos de documentación técnica deben incluir timestamps completos con el siguiente formato:

**Formato requerido**: `YYYY-MM-DD HH:MM` (ISO 8601 abreviado)

**Ejemplos válidos**:

- `2026-02-12 14:30`
- `2026-02-12 09:15`
- `2026-01-05 23:45`

**Dónde aplicar**:

- **REFERENCE.md**: Timestamp principal en el encabezado del documento
- **CURRENT-STATUS-PROJECT.md**: Fecha de última actualización
- **CHANGELOG.md**: Fechas de cada entrada
- **DEPENDENCIES.md**: Fecha de última actualización
- **TEMPORAL.md**: Timestamp de compilación y actualización
- **Cualquier archivo de resumen técnico**: Incluir timestamp de última modificación

**Propósito**: Permite rastrear cuánto está desactualizado un archivo respecto a REFERENCE.md y viceversa, incluso dentro de la misma sesión de trabajo.

**Ejemplo de uso**:

```markdown
**Last updated**: 2026-02-12 14:30
```

---

## Requisitos de Autoría y Licencia

### (11.) Información de Autoría

En todos los archivos de documentación principal (README.md, REFERENCE.md, CURRENT-STATUS-PROJECT.md), debe quedar claro:

**Autor**: Julián Calderón Almendros

### (12.) Créditos y Reconocimientos

Los siguientes créditos deben estar claramente visibles en README.md:

**Recursos Educativos**:

- "Razonando con Lean" - José A. Alonso (YouTube)
- Adrián GQ (@conjuntos_y_logica) - YouTube

**Referencias Bibliográficas**:

- "Axiomatic Set Theory" - Patrick Suppes (1960/1972)
- "Axiomatic Set Theory" - Paul Bernays (1958)

**Herramientas de IA**:

- Claude Code AI (Anthropic)
- Gemini AI (Google)

### (13.) Licencia

**Licencia del proyecto**: MIT License

Debe estar claramente indicada en:

- Archivo LICENSE (texto completo con copyright de Julián Calderón Almendros)
- README.md (sección de licencia con enlace)
- CURRENT-STATUS-PROJECT.md (en el footer)
- Badge en README.md: `[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)`

### (14.) Cabeceras de Archivos .lean

**Todos los archivos .lean DEBEN incluir una cabecera con información de copyright y licencia.**

**Formato requerido**:

```lean
/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
```

**Dónde aplicar**: En TODOS los archivos `.lean` del proyecto, antes de cualquier `import`.

**Colocación exacta**:

1. Abrir el archivo .lean
2. Primera línea: `/-`
3. Segunda línea: `Copyright (c) 2025. All rights reserved.`
4. Tercera línea: `Author: Julián Calderón Almendros`
5. Cuarta línea: `License: MIT`
6. Quinta línea: `-/`
7. Sexta línea: Línea en blanco
8. Séptima línea en adelante: `import ...` y código

**Excepciones**: Ninguna - todos los archivos .lean, incluyendo el módulo principal `Peano.lean`.

**Propósito**:

- Clarificar propiedad del código
- Comunicar licencia MIT explícitamente en el código fuente
- Cumplir con estándares de código abierto
- Facilitar rastreo legal y atribución

**Verificación**:

```bash
grep -n "Copyright (c) 2025" Peano/*.lean | wc -l
# Debe devolver ?? (número total de archivos .lean)
```

---

## Cumplimiento de Requisitos

Verificar que REFERENCE.md, archivos .lean y otros archivos de documentación cumplan con todos los puntos (1-14) antes de considerar la documentación completa y actualizada.
