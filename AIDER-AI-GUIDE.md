# Guía de Requisitos para REFERENCE.md y Documentación del Proyecto

**Última actualización:** 2026-02-12 18:45  
**Autor**: Julián Calderón Almendros

Este documento establece los requisitos y estándares para la documentación técnica del proyecto Peano.

---

## Documentación que debe contener REFERENCE.md

### (0.) **Esta documentación es de tipo técnico, no de usuario final**, incluso como referencia de la IA, para no tener que cargar el proyecto completo. Debe ser clara, precisa y completa, pero no necesariamente amigable para usuarios sin conocimientos técnicos

### (1.) **Los diferentes módulos .lean** : tanto en el módulo raíz como en los módulos secundarios, con su ubicación, namespace, dependencias y estado de documentación (si está documentado o no, o si está pendiente de documentación)

### (2.) **Las dependencias entre los módulos**: cada módulo tiene que tener claramente documentado a qué otros módulos depende, y qué módulos dependen de él, para entender la estructura del proyecto y las relaciones entre los diferentes componentes. Esto es especialmente importante para la IA, para que pueda entender cómo se relacionan los diferentes módulos y cómo navegar por el proyecto sin necesidad de cargarlo completamente

### (3.) **Espacios de nombres y relaciones entre ellos**: al no ser necesariamente iguales los espacioes de nombre que los módulos, es importante documentar claramente qué espacios de nombre existen, a qué módulos pertenecen, y cómo se relacionan entre sí. Esto ayudará a la IA a entender la organización del proyecto y a navegar por él de manera más eficiente

### (4.) **Definiciones introducidas**: por cada módulo y espacio de nombres debe quedar claras las definiciones que se introducen, con su ubicación, dependencias, y formato tanto en nomenclatura matemática como en firma lean4, para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean, y para que la IA pueda entender claramente qué definiciones existen, cómo se relacionan entre sí, y cómo se pueden usar en demostraciones o construcciones más elaboradas

#### (4.1.) **Como reflejar en la documentación las definiciones**: Debe que dar, además de la firma lean4, la nomenclatura matemática (sin explicaciones, los destinatarios de esta documentación son matemáticos y técnicos en lean4) de cada definición siguiendo lo más fielmente posible la estructura del código. Debe aparecer el módulo y el espacio de nombres al que pertenece, y las dependencias necesarias para construir la definición

#### (4.2.) **Característica de computabilidad**: Debe indicarse si la definición es computable o no, si tiene par booleano

#### (4.3.) **Característica de buena fundación**: Debe indicarse si en la definición se contiene una demostración terminación de la computación (*terminated by*)

#### (4.4.) **Notación**: Debe quedar registrada la notación introducida por cada deficnión, si es infija o prefija, o más compleja, qué símbolos se usan y qué prioridades hay entre las notaciones, para que se puedan usar correctamente en la documentación y en los comentarios de los archivos .lean, y para que la IA pueda entender claramente cómo se pueden usar en demostraciones o construcciones más elaboradas

### (5.) **Axiomas introducidos y sus referencias**: cada axioma debe tener claramente documentado dónde se encuentra, en qué módulo, en qué namespace, y el orden en el que se declaran/definen, su relación con las definiciones

### (6.) En cuanto a los axiomas y las definciones, las queremos

#### (6.1.) En **nomenclatura matemática (no lean code)**, para una fácil comprensión humana, y para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean. No necesitamos explicaciones, el lenguiaje matemático se bastará por sí mismo

#### (6.2.) **Firma lean4** para que cuando se llamen en demostraciones o construcciones más elaboradas, se haga correctamente

#### (6.3.) Deben quedar registradas las **dependencias** para construir el axioma

### (7.) Teoremas principales **sin demostración de ningún tipo**, con su referencia a dónde se encuentran, módulo, namespace, orden en el que se declaran/demuestran

#### (7.1.) En **nomenclatura matemática (no lean code)**, para una fácil comprensión humana, y para que se puedan usar como referencia en la documentación y en los comentarios de los archivos .lean. No se necesitan explicaciones, el lenguaje matemático se bastará por sí mismo

#### (7.2.) **Firma lean4** para que cuando se llamen en demostraciones o construcciones más elaboradas, se haga correctamente

#### (7.3.) Deben quedar registradas las **dependencias** para construir la demostración del teorema

### (8.) Nada que no esté demostrado o construido debe estar en este archivo, ni siquiera como comentario o como "teorema pendiente". Solo lo que ya esté demostrado o construido en los archivos .lean

### (9.) Cada vez que cargas un archivo .lean, actualizas (si es necesario) el REFERENCE.md con lo que se ha demostrado o construido en ese archivo, siguiendo los puntos anteriores. Si hace falta anotar una fecha y la fecha de la última modificación del archivo .lean, estará bien, para trazar bien lo que de hecho tenemos

### (10.) El archivo REFERENCE.md debe ser lo único que necesites para escribir la documentación, o para hacer un nuevo archivo/módulo .lean de forma que no haya que cargar la totalidad de los tokens que tiene actualmente el proyecto. Esto es especialmente importante para la IA, para que pueda entender claramente qué definiciones, axiomas, teoremas, módulos y espacios de nombre existen, cómo se relacionan entre sí, y cómo se pueden usar en demostraciones o construcciones más elaboradas sin necesidad de cargar el proyecto completo

### (11.) Cunado leas este archivo introduce en cada archivo .lean una cabecera de instrucciones de su relación con REFERENCE.md, para que al entrar y leer, si es que es necesario, un archivo .lean, se recuerde la necesidad de **proyectar** ese archivo de código en REFERENCE.md

### (12.) Defino **proyectar** un archivo .lean en REFERENCE.md como el poceso de actualizar REFERENCE.md con toda la información relevante demostrada o construida en ese archivo .lean, siguiendo los puntos anteriores

### (13.) Por información relevante me refiero a todoas las definciones, notaciones, axiomas, teoremas no privados, y cualquier otro contenido que se haya demostrado o construido en ese archivo .lean, y que sea necesario para entender el proyecto, para usarlo como referencia, o para construir demostraciones o construcciones más elaboradas

### (14.) Todo lo exportable en un módulo .lean debe estar proyectado en REFERENCE.md, y debe aparecer en el export de ese módulo .lean

---

## Requisitos de Timestamps

### (15.) Formato de Fecha y Hora

Todos los archivos de documentación técnica deben incluir timestamps completos con el siguiente formato:

**Formato requerido**: `YYYY-MM-DD HH:MM` (ISO 8601 abreviado)

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

### (16.) Información de Autoría

En todos los archivos de documentación principal (README.md, REFERENCE.md, CURRENT-STATUS-PROJECT.md), debe quedar claro:

**Autor**: Julián Calderón Almendros

### (17.) Créditos y Reconocimientos

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

### (18.) Licencia

**Licencia del proyecto**: MIT License

Debe estar claramente indicada en:

- Archivo LICENSE (texto completo con copyright de Julián Calderón Almendros)
- README.md (sección de licencia con enlace)
- CURRENT-STATUS-PROJECT.md (en el footer)
- Badge en README.md: `[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)`

### (19.) Cabeceras de Archivos .lean

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
# Debe devolver N (N es el número total de archivos .lean)
```

---

## Cumplimiento de Requisitos

Verificar que REFERENCE.md, archivos .lean y otros archivos de documentación cumplan con todos los puntos (1-19) antes de considerar la documentación completa y actualizada.
