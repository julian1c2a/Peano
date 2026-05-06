FUNDAMENTACIÓN DE LAS MATEMÁTICAS EN UN ENTORNO DE PEANO Y FOL=

PARTE I: EL MARCO TEÓRICO Y EL PROBLEMA FUNDACIONAL

1. El Problema de los Objetos Matemáticos

El problema se plantea de la siguiente manera: cuando tratamos de definir objetos matemáticos complejos como listas, tuplas o funciones, nos encontramos con la dificultad de que no tenemos una definición clara de qué sean estos objetos en el mundo de la lógica pura, por muy inmediatos que nos parezcan a la intuición y al cálculo computacional.

Listas: Sea $L : \text{List } \mathbb{N}$ una lista (finita) de números naturales, comúnmente escrita como $[n_1, n_2, ..., n_k]$. Inicialmente no es un objeto lógico definido, no sabemos qué es una lista, ni siquiera si existe. No sabemos cómo definirla, ni cómo probar su existencia.

Tuplas: Sea $p : \text{2-Tuple } \mathbb{N}$ una 2-tupla, expresada como $\langle n_1, n_2 \rangle$. Inicialmente carece de estatus ontológico en nuestro sistema.

Funciones: Sea $f : \text{List } \mathbb{N} \to \text{List } \mathbb{N} : n \mapsto m$. Conocemos funciones concretas postuladas axiomáticamente (sucesor $\sigma$, suma $+$, producto $*$), pero más allá de estas, no tenemos una definición general de qué es una función discreta ni cómo probar su existencia.

En el sistema base en el que operamos, no tenemos ni la más remota idea de qué son estos objetos.

2. De lo que SÍ disponemos (El Entorno Restringido)

Disponemos solo de la teoría de los axiomas de Peano añadidos a la Lógica de Predicados de Primer Orden con igualdad ($\text{FOL}^=$). Operamos de forma muy restringida:

Vivimos en $\text{FOL}^+ \text{Peano}$.

No disponemos del Principio de Inducción Generalizado extendido a cualquier propiedad (lo que evitará cuantificación sobre predicados de segundo orden).

Solo tenemos las reglas constructivas de derivación en $\text{FOL}^=$ (sin ley del tercero excluido $P \lor \neg P$, ni doble negación estricta $\neg(\neg P) \implies P$).

2.1 El Alfabeto Formal ($\mathcal{\Lambda}$)

$$\mathcal{B} = \{ \exists, \forall, \land, \lor, \neg, \implies, \iff, (, ), = \}$$

$$\mathcal{C} = \left\{ 0, \sigma, \tau, +, *, <, \sqrt{} \right\}$$

$$\mathcal{D} = \{ a', b, c, d, e, f, g, h \}$$

$$\mathcal{E} = \{ x, y, z, w \}$$

$$\mathcal{F} = \{ i, j, k, l, m, n, r, s, t, p, q \}$$

$$\mathcal{G} = \{ u, v \}$$

$$\mathcal{H} = \{ ' \}$$

$$\mathcal{I} = \{ 1, 2, 3, \exists^1 \}$$

$$\mathcal{J} = \{ div2, mod2 \}$$

$$\mathcal{K} = \{ \langle, \rangle, [, ], \{, \}, ., :, ;, , \}$$

$$\mathcal{\Lambda} = \mathcal{B} \cup \mathcal{C} \cup \mathcal{D} \cup \mathcal{E} \cup \mathcal{F} \cup \mathcal{G} \cup \mathcal{H} \cup \mathcal{I} \cup \mathcal{J} \cup \mathcal{K}$$

$$\mathcal{\Gamma} = \{ \phi, \psi, \zeta, \delta, \epsilon, \eta, \theta \} \quad \text{(Variables de fórmulas)}$$

(Las letras minúsculas o con apóstrofes actuarán como variables término, instanciadas sobre el universo de los números naturales).

2.2 Axiomas Fundamentales

Ax 1. $\exists 0$

Ax 2. $\forall n, \exists \sigma(n)$

Ax 3. $\forall n, \sigma(n) \neq 0$

Ax 4. $\forall n, \forall m, \sigma(n) = \sigma(m) \implies n = m$

Ax 5. $\forall n, \neg(n = 0) \implies \exists m, \sigma(m) = n$

Ax 6. $\forall n, n + 0 = n$

Ax 7. $\forall n, \forall m, n + \sigma(m) = \sigma(n + m)$

Ax 8. $\forall n, n * 0 = 0$

Ax 9. $\forall n, \forall m, n * \sigma(m) = (n * m) + n$

Ax 10. $\forall n, \forall m, n < m \iff \exists k, n + \sigma(k) = m$

Ax 11. $\forall n, \exists \sqrt{n}, (\sqrt{n} * \sqrt{n}) \le n$

Ax 12. $\forall n, n < ((\sqrt{n} + 1) * (\sqrt{n} + 1))$

(Nota: Entendemos de forma estándar $a \le b \iff a < b \lor a = b$)

2.3 Definiciones Base

Def 1. $1 := \sigma(0)$

Def 2. $2 := \sigma(1)$

Def 3. $3 := \sigma(2)$

Def 4. $4 := \sigma(3)$

Def 5. $Div2(n, q) := (2 * q = n \lor 2 * q + 1 = n)$

Def 6. $Mod2(n, r) := \exists q, (Div2(n, q) \land (2 * q + r = n))$

Def 7. $\tau(0) := 0$

Def 8. $\forall n, \exists \tau(n), \tau(\sigma(n)) = n$

Def 9. $n^2 := n * n \quad \text{(Azúcar sintáctico para cuadrados perfectos)}$

3. La Estrategia Constructiva: Función de Cantor

Para introducir las 2-Tuplas lógicamente, postulamos la función de emparejamiento de Cantor y su residuo:

Def 10. $$c(x,y) := div2((x+y) * (x+y+1) + 2 * y)$$

Def 11. $$r(x,y) := mod2((x+y) * (x+y+1) + 2 * y)$$

El predicado relacional base sobre tres naturales se define como:

Def 12. $$\text{Cantor}(x,y,c) := (2 * c = (x+y) * (x+y+1) + 2 * y)$$

Meta Deductiva: Demostrar formalmente que $\text{Cantor}(x,y,c)$ es total, sobreyectiva e inyectiva (biyectiva) permitiéndonos definir rigurosamente $\text{2-Tuple}(x,y) := c$ y sus proyecciones:

$$[c].1 := \text{proyCantor}_1(c) \quad \text{y} \quad [c].2 := \text{proyCantor}_2(c)$$

Evaluando algebraicamente: $2x = -(2y+1) \pm \sqrt{4y^2 + 4y + 1 - 4y^2 - 12y + 8c}$.

PARTE II: DESARROLLO DEDUCTIVO FORMAL (FASES 1-20)

FASE 1: Aritmética de Constantes (Evaluación Mecánica)

Aplicando instanciación universal ($\forall E$) y las reglas de igualdad sobre las definiciones base:

Teorema 1: $2 = \sigma(\sigma(0))$

Teorema 2: $1 + 1 = 2$ (Vía Ax 7 y Ax 6)

Teorema 3: $3 = \sigma(\sigma(\sigma(0)))$

Teorema 4: $1 + 2 = 3$

Teorema 5: $2 + 1 = 3$

FASE 2: Desigualdades y el Cero

Teorema 22: $0 \neq 1$ (Demostrado invocando $\forall n, \sigma(n) \neq 0$)

Teorema 32: $0 + 0 = 0$ (Instanciando el Ax 6)

FASE 3 y 4: Límite del Sistema y Adopción Algebraica

Al intentar probar $\forall n, 0+n=n$, el motor formal constata que en FOL= sin inducción es imposible. Para operar polinomios, asumimos temporalmente los axiomas de la estructura de semianillo:

Ax 17 (Conmutatividad +): $\forall n, \forall m, n + m = m + n$

Ax 18 (Asociatividad +): $\forall n, \forall m, \forall k, (n + m) + k = n + (m + k)$

Ax 19 (Conmutatividad *): $\forall n, \forall m, n * m = m * n$

Ax 20 (Asociatividad *): $\forall n, \forall m, \forall k, (n * m) * k = n * (m * k)$

Ax 21 (Distributividad): $\forall n, \forall m, \forall k, n * (m + k) = (n * m) + (n * k)$

FASE 5: Teoremas Algebraicos Generales

Teorema 33: $\forall n, 0 + n = n$ (Por Ax 6 y Ax 17)

Teorema 38/37: $\forall n, n * 1 = n \land 1 * n = n$

Teorema 40: $\forall n, 2 * n = n + n$

Teorema 52: $\forall n, \sigma(n) = n + 1 = 1 + n$

FASE 6: Lema Polinómico

Lema C1: $\forall x, \forall y, (x+y) * (x+y+1) = (x+y)^2 + x + y$ (Demostrado por distributividad).

FASE 7: Relaciones de Orden ($<$) y Raíz Cuadrada ($\sqrt{}$)

Antes de abordar la función de Cantor, establecemos el comportamiento de la raíz cuadrada a partir de sus dos únicos axiomas de acotación (Ax 11 y 12), demostrando que son suficientes para derivar las raíces triviales.

Teorema 60: $\forall n, n < \sigma(n)$

Teorema R1: $\sqrt{0} = 0$
Demostración:

Por Axioma 11, $(\sqrt{0})^2 \le 0$.

Como en $\mathbb{N}$ no hay elementos menores a 0, se deduce estrictamente que $\sqrt{0} * \sqrt{0} = 0$.

El único natural que multiplicado por sí mismo da 0 es el 0 (por Ax 8).

$\therefore \sqrt{0} = 0$. $\blacksquare$

Teorema R2: $\sqrt{1} = 1$
Demostración:

Por Axioma 11, $(\sqrt{1})^2 \le 1$. Esto restringe $\sqrt{1}$ a los valores 0 o 1.

Supongamos por reducción al absurdo que $\sqrt{1} = 0$.

Por Axioma 12, $1 < (\sqrt{1} + 1)^2$.

Sustituyendo nuestra suposición: $1 < (0 + 1)^2 \implies 1 < 1^2 \implies 1 < 1$.

Esto viola la irreflexividad del orden estricto (una contradicción lógica).

$\therefore \sqrt{1} \neq 0$. Por eliminación de casos, $\sqrt{1} = 1$. $\blacksquare$

FASE 8: Lema de Paridad (Producto de Consecutivos)

Lema P1: $\forall w, \exists k, w * (w + 1) = 2 * k$ (Demostrado por casos par/impar mediante mod2).

FASE 9: Totalidad de la Función de Cantor

Teorema C2: $\forall x, \forall y, \exists c, \text{Cantor}(x,y,c)$
(Demostrado porque el Lema P1 garantiza que la división polinómica por 2 siempre es exacta y devuelve un número natural cerrado).

FASE 10: Inyectividad Parcial (Unicidad del Número)

Lema C3: $\forall a, \forall b, 2*a = 2*b \implies a = b$ (Por monotonía del orden).

Teorema C4: $\forall x, \forall y, \forall c, \forall c', (\text{Cantor}(x,y,c) \land \text{Cantor}(x,y,c')) \implies c = c'$.

FASE 11: Sobreyectividad (Existencia de Proyecciones)

Lema C5: $\forall c, \exists w, w*(w+1) \le 2c < (w+1)*(w+2)$ (Garantizado por los límites de $\sqrt{n}$ de los Ax 11 y 12 sobre el discriminante $D = 8c+1$).

Teorema C6: $\forall c, \exists x, \exists y, \text{Cantor}(x,y,c)$.

FASE 12: Biyectividad Completa

Teorema C7 (Unicidad Proyectiva): $\forall c, \forall x, \forall x', \forall y, \forall y', (\text{Cantor}(x,y,c) \land \text{Cantor}(x',y',c)) \implies (x=x' \land y=y')$.

FASE 13: Definición Sintáctica (Azúcar Funcional)

Garantizada la biyección, validamos tu sintaxis original como objetos formales bien definidos:

Def 11: $\langle x, y \rangle := c \iff \text{Cantor}(x,y,c)$

Def 12 & 13: $[c].1 := x$ y $[c].2 := y$

Teoremas C8 y C9: Demostramos que $[\langle x, y \rangle].1 = x$ y que $\langle [c].1, [c].2 \rangle = c$.

FASE 14: Listas Finitas (LISP en Peano)

Para evitar la colisión $\langle 0,0 \rangle = 0$, introducimos el desplazamiento del sucesor:

Def 14: $Nil := 0$

Def 15: $Cons(h, t) := \langle h, \sigma(t) \rangle$

Teorema L1: $\forall h, \forall t, Cons(h, t) \neq Nil$

(Sintaxis: $[x, y]$ se evalúa recursivamente como $Cons(x, Cons(y, Nil))$).

FASE 15 y 16: Álgebra de Listas (Concatenación $\oplus$)

Introducimos Axiomas temporales (22 a 25) para definir casos base ($Nil \oplus L = L$) y recursivos del monoide de listas, demostrando que $[x] \oplus [y] = [x, y]$.

FASE 17: Funciones Discretas (Mapas Finitos)

Un número natural se comporta lógicamente como una función evaluable si, decodificado como lista de tuplas, no posee claves repetidas.

Ax 26 y 27: Establecen el comportamiento del predicado de pertenencia $In(x, L)$.

Def 18 (IsFunction): $\forall p_1, p_2 \in F, ([p_1].1 = [p_2].1) \implies p_1 = p_2$.

Teorema F2: Si $F$ es función, su evaluación $F(x)$ es lógicamente única.

FASE 18: El Isomorfismo de la Correspondencia

Cualquier lista $R$ actúa como una relación lógica $\text{Map}(R, x, y) \iff In(\langle x, y \rangle, R)$.

Teorema F3: Demostramos que una lista cumple estructuralmente nuestra prueba (IsFunction) si y solo si la relación lógica es univalente en la meta-teoría (Functional(Map)).

FASE 19: Factorización (Primos como Dominios)

Se establecen las bases alternativas de secuenciación usando el Teorema Fundamental de la Aritmética (una función $p \mapsto e$ validada con IsFactorization).

FASE 20: Aritmetización de la Sintaxis (Gödelización con Cantor)

Utilizamos las Listas de Cantor (Cons) para codificar cadenas del alfabeto $\mathcal{\Lambda}$.

Asignamos $\mathcal{G}(\forall) = 2, \mathcal{G}(=) = 10, \mathcal{G}(x) = 100$, etc.

Una Fórmula Lógica se convierte en un solo natural: $\ulcorner S \urcorner = Cons(\mathcal{G}(s_1), \dots Nil)$.

Aparecen los meta-predicados: $IsFormula(f)$ y $Dem(d, f)$, culminando la capacidad de autorreferencia del sistema Peano-FOL=.