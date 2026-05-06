# FUNDAMENTACIÓN DE LAS MATEMÁTICAS EN UN ENTORNO DE PEANO Y FOL= CON INDUCCIÓN GENERAL

## PARTE I: EL MARCO TEÓRICO Y EL PROBLEMA FUNDACIONAL

### 1. El Problema de los Objetos Matemáticos

El problema se plantea de la siguiente manera: cuando tratamos de definir objetos matemáticos complejos como listas, tuplas o funciones, nos encontramos con la dificultad de que no tenemos una definición clara de qué sean estos objetos en el mundo de la lógica pura, por muy inmediatos que nos parezcan a la intuición y al cálculo computacional.

**Listas**: Sea $L : \text{List } \mathbb{N}$ una lista finita de naturales, escrita como $[n_1, n_2, \ldots, n_k]$. Inicialmente no es un objeto lógico definido: no sabemos qué es, si existe, ni cómo probar su existencia.

**Tuplas**: Sea $p : \text{2-Tuple } \mathbb{N}$ una 2-tupla $\langle n_1, n_2 \rangle$. Inicialmente carece de estatus ontológico en el sistema.

**Funciones**: Conocemos funciones concretas postuladas axiomáticamente ($\sigma$, $+$, $*$), pero no tenemos una definición general de función discreta ni cómo probar su existencia.

### 2. De lo que SÍ disponemos (El Entorno Completo)

A diferencia de aproximaciones más restringidas, aquí disponemos de $\text{FOL}^= + \text{Peano}$ **con el Principio de Inducción Generalizado**. Esto significa que cuantificamos y permitimos la inducción sobre todas las fórmulas bien formadas de nuestro lenguaje de primer orden. Gracias a este principio fundamental, las propiedades algebraicas del semianillo $(\mathbb{N}, +, *)$, las propiedades del orden total (irreflexividad, tricotomía), y la existencia y unicidad de funciones u operaciones auxiliares como la raíz cuadrada o la paridad, ya no necesitan ser adoptadas como axiomas independientes. Todas ellas se derivan formalmente como teoremas a partir de sus definiciones recursivas base.

---

## PARTE II: EL SISTEMA FORMAL

### 2.1 El Alfabeto Formal ($\mathcal{\Lambda}$)

$$\mathcal{B} = \{ \exists, \forall, \land, \lor, \neg, \implies, \iff, (, ), = \}$$
$$\mathcal{C} = \left\{ 0, \sigma, \tau, +, *, <, \le, \sqrt{\phantom{n}} \right\}$$
$$\mathcal{D} = \{ a, b, c, d, e, f, g, h \} \qquad \mathcal{E} = \{ x, y, z, w \}$$
$$\mathcal{F} = \{ i, j, k, l, m, n, r, s, t, p, q \} \qquad \mathcal{G} = \{ u, v \}$$
$$\mathcal{H} = \{ \prime \} \qquad \mathcal{I} = \{ 1, 2, 3, \exists^1 \} \qquad \mathcal{J} = \{ div2, mod2 \}$$
$$\mathcal{K} = \{ \langle, \rangle, [, ], \{, \}, ., :, ; \}$$
$$\mathcal{\Lambda} = \mathcal{B} \cup \mathcal{C} \cup \mathcal{D} \cup \mathcal{E} \cup \mathcal{F} \cup \mathcal{G} \cup \mathcal{H} \cup \mathcal{I} \cup \mathcal{J} \cup \mathcal{K}$$
$$\mathcal{\Gamma} = \{ \phi, \psi, \zeta, \delta, \varepsilon, \eta, \theta \} \quad \text{(Variables de fórmulas)}$$

### 2.2 Axiomas Fundamentales

#### Axiomas de Peano Puros y Principio de Inducción

Ax 1. $\exists 0$

Ax 2. $\forall n,\quad \sigma(n) \neq 0$

Ax 3. $\forall n,\ \forall m,\quad \sigma(n) = \sigma(m) \implies n = m$

**Ax-Ind (Esquema de Inducción General).** Para cualquier fórmula $\varphi(x)$ del lenguaje $\mathcal{\Lambda}$:
$$\varphi(0) \land \forall n,\ \bigl(\varphi(n) \implies \varphi(\sigma(n))\bigr) \implies \forall n,\ \varphi(n)$$

> **Nota sobre Inducción Fuerte:** A partir de Ax-Ind, se deriva como metateorema el principio de inducción fuerte, tomando como fórmula auxiliar $\psi(n) := \forall m \le n,\ \varphi(m)$.

#### Definiciones Recursivas de la Suma y el Producto

En un sistema con inducción general, la suma y el producto se introducen axiomáticamente por sus ecuaciones fundamentales; el resto de sus propiedades son teoremas.

Ax 4. $\forall n,\quad n + 0 = n$

Ax 5. $\forall n,\ \forall m,\quad n + \sigma(m) = \sigma(n + m)$

Ax 6. $\forall n,\quad n * 0 = 0$

Ax 7. $\forall n,\ \forall m,\quad n * \sigma(m) = (n * m) + n$

#### Definición del Orden Estricto

Ax 8. $\forall n,\ \forall m,\quad n < m \iff \exists k,\ n + \sigma(k) = m$

#### Definiciones de la División Entera por 2

Ax 9. $\forall n,\quad mod2(n) = 0 \iff mod2(\sigma(n)) = 1$

Ax 10. $\forall n,\quad \bigl(div2(n) * 2\bigr) + mod2(n) = n$

> *Todos los demás axiomas del sistema restringido o finito original (álgebra, orden total, raíz cuadrada) ahora son **teoremas demostrables** mediante el esquema de inducción.*

### 2.3 Definiciones Base

Def 1. $\forall a,\ \forall b,\quad a \le b \;\iff\; a < b \lor a = b$

Def 2. $1 := \sigma(0)$

Def 3. $2 := \sigma(1)$

Def 4. $3 := \sigma(2)$

Def 5. $4 := \sigma(3)$

Def 6. $\tau(0) := 0$ *(predecesor totalizado, base)*

Def 7. $\forall n,\quad \tau(\sigma(n)) := n$ *(predecesor totalizado, paso)*

Def 8. $n^2 := n * n$

### 2.4 La Estrategia Constructiva: Función de Cantor

Def 9. $c(x,y) \;:=\; div2\!\bigl((x+y)*(x+y+1) + 2*y\bigr)$
Def 10. $r(x,y) \;:=\; mod2\!\bigl((x+y)*(x+y+1) + 2*y\bigr)$
Def 11. $\text{Cantor}(x,y,c) \;:\Leftrightarrow\; 2*c = (x+y)*(x+y+1) + 2*y$
Def 12. $[c].1 \;:=\; \text{proj}_1(c)$
Def 13. $[c].2 \;:=\; \text{proj}_2(c)$

---

## PARTE III: DESARROLLO DEDUCTIVO FORMAL

---

### BLOQUE I — ARITMÉTICA BÁSICA Y ÁLGEBRA

Con el esquema de inducción general (Ax-Ind), todas las propiedades algebraicas que antes se asumían axiomáticamente (o por inducción restringida) se demuestran formalmente de forma directa:

**Teoremas Derivados por Inducción (Antiguos Axiomas):**
- **Teo (Conmutatividad de la suma):** $\forall n, m,\ n + m = m + n$
- **Teo (Asociatividad de la suma):** $\forall n, m, k,\ (n + m) + k = n + (m + k)$
- **Teo (Conmutatividad del producto):** $\forall n, m,\ n * m = m * n$
- **Teo (Asociatividad del producto):** $\forall n, m, k,\ (n * m) * k = n * (m * k)$
- **Teo (Distributividad):** $\forall n, m, k,\ n * (m + k) = (n * m) + (n * k)$

**Propiedades del Orden (Demostradas por Inducción Fuerte o Simple):**
- **Teo (Irreflexividad):** $\forall n,\ \neg(n < n)$
- **Teo (Tricotomía):** $\forall a, b,\ a < b \lor a = b \lor b < a$
- **Teo (Decidibilidad de la igualdad):** $\forall n, m,\ n = m \lor n \neq m$
- **Teo (Monotonía):** $\forall n, k,\ n < n + \sigma(k)$

---

### BLOQUE II — RAÍZ CUADRADA

En lugar de postular la existencia y cotas de la raíz cuadrada axiomáticamente, se demuestra su existencia por inducción fuerte sobre los naturales.

**Teo (Existencia y cotas de la raíz cuadrada):** $\forall n,\ \exists r,\ r^2 \le n \land n < (\sigma(r))^2$
*Prueba (esquema):* Por inducción fuerte sobre $n$. Para el caso base $n=0$, $r=0$ satisface las cotas. Asumiendo que existe un tal $r_n$ para $n$, verificamos constructivamente si $(r_n + 1)^2 \le n+1$. En caso afirmativo, $r_{n+1} = r_n + 1$; en caso contrario, $r_{n+1} = r_n$. La unicidad de dicho $r$ se demuestra también.

Definimos entonces $\sqrt{n}$ como ese único $r$.

---

### BLOQUE III — div2 Y mod2

**Teo (Rango de mod2):** $\forall n,\ mod2(n) = 0 \lor mod2(n) = 1$
*Prueba:* Demostración directa por inducción simple sobre $n$ utilizando Ax 9. (Este resultado reemplaza al antiguo axioma explícito del rango de mod2).

---

### BLOQUE IV — FUNCIÓN DE CANTOR

El desarrollo constructivo del par sigue siendo idéntico. El **Lema de Paridad P1** ($\forall w,\ \exists k,\ w*(w+1) = 2*k$) se apoya ahora sobre los teoremas algebraicos formales y el teorema del rango de mod2 recién demostrados. Las propiedades clave de la biyección de Cantor:
- **Teo C2 (Totalidad)**
- **Teo C4 (Inyectividad)**
- **Teo C6 (Sobreyectividad)**
- **Teo C7 (Unicidad Proyectiva)**

Se derivan tal como en el planteamiento original, ahora ancladas sobre un sistema aritmético plenamente derivado en Peano + Inducción.

---

### BLOQUE V — TUPLAS Y PROYECCIONES

**Def 14.** $\langle x, y \rangle := c \;\iff\; \text{Cantor}(x,y,c)$
**Def 15.** $[c].1 := x \text{ donde } \text{Cantor}(x,y,c)$
**Def 16.** $[c].2 := y \text{ donde } \text{Cantor}(x,y,c)$

Los teoremas proyectivos C8, C9, C10, y C11 operan de igual manera, fundamentando las tuplas estrictamente sobre $\mathbb{N}$.

---

### BLOQUE VI — LISTAS

Las operaciones y axiomas estructurales de las listas (Nil, Cons, In, $\oplus$) mantienen su estructura definicional. Sin embargo, la ventaja de disponer del principio de inducción general es que propiedades fundamentales de las listas que requerían validación meta-teórica pueden ahora ser demostradas dentro del propio lenguaje formal, mapeando la longitud o la profundidad estructural a los naturales:

**Teo L7** $\quad (L \oplus M) \oplus N = L \oplus (M \oplus N)$
*Prueba:* Formalmente demostrable traduciendo la inducción estructural sobre $L$ a una inducción ordinaria sobre la codificación natural de $L$.

**Teo L8** $\quad In(x,\, L \oplus M) \iff In(x,L) \lor In(x,M)$
*Prueba:* Formalmente demostrable por inducción.

---

### BLOQUE VII — FUNCIONES DISCRETAS

El tratamiento de las funciones discretas es idéntico, utilizando $IsFunction(F)$ y la correspondencia lógica $Map(F, x, y)$ con subconjuntos del producto cartesiano.

---

### BLOQUE VIII — PRIMOS Y GÖDELIZACIÓN

**Teorema Fundamental de la Aritmética (TFA)**
En un sistema restringido sin inducción, la existencia y unicidad de la factorización prima debía tomarse como un axioma macroscópico ($Ax-P$). Gracias a la disponibilidad de la inducción fuerte a través de Ax-Ind, el TFA se reduce a un teorema demostrable del sistema:

**Teo (Factorización Única):** $\forall n \ge 1,\ \exists^1 f,\ IsFactorization(f,n)$
*Prueba (esquema):* La existencia se establece por inducción fuerte: si $n$ es primo, su factorización es él mismo. Si es compuesto, $n = a*b$ con $a,b < n$. Por hipótesis inductiva fuerte, $a$ y $b$ poseen factorización en listas; su concatenación da la factorización de $n$. La unicidad se demuestra apoyándose en el Lema de Euclides, también demostrable por inducción.

---

## APÉNDICE: RESUMEN DE LA BASE AXIOMÁTICA MINIMALISTA

Al incorporar el Principio de Inducción General (Ax-Ind), la extensa lista de 22 axiomas independientes de las aproximaciones más limitadas colapsa a los verdaderos fundamentos de la Aritmética de Peano, logrando una máxima pureza fundacional sin sacrificar expresividad:

| Axiomas Fundamentales | Descripción |
| --- | --- |
| Ax 1, 2, 3 | Axiomas de Peano Puros ($0$, $\sigma$, e inyectividad de $\sigma$) |
| **Ax-Ind** | **Esquema de Inducción Generalizado sobre fórmulas de $\mathcal{\Lambda}$** |
| Ax 4, 5 | Ecuaciones recursivas de la Suma |
| Ax 6, 7 | Ecuaciones recursivas del Producto |
| Ax 8 | Definición del Orden Estricto ($<$) |
| Ax 9, 10 | Ecuaciones base para la división y paridad ($div2$, $mod2$) |

*Todos los demás enunciados matemáticos descritos (álgebra, orden, raíz, propiedades de listas y tuplas, factorización de primos) pierden su estatus de axioma y se erigen firmemente como **teoremas** en el sistema.*