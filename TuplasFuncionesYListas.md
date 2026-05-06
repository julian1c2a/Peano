## PROBLEMA DE FUNDAMENTACIÓN DE LAS MATEMÁTICAS EN UN ENTORNO DE PEANO Y FOL=

El problema se plantea de la sigueinte manera, cuando tratamos de definir objetos matemáticos como listas, tuplas o funciones, nos encontramos con la dificultad de que no tenemos una definición clara de qué sea estos objetos en el mundo de la lógica, por muy inmediatos que nos parezcan a la intuición y al cálculo.

Sea $L : \text{List } \mathbb{N}$ una lista (finita) de números naturales. La solemos escribir como $[n_1, n_2, ..., n_k]$ dónde cada $n_i$ es un número natural. Pero inicialmente no es un objeto lógico definido, no sabemos qué es una lista, ni siquiera si existe. No sabemos cómo definirla, ni cómo probar su existencia.

Sea $p : \text{2-Tuple } \mathbb{N}$ una 2-tupla de números naturales. Una forma habitual de expresarla es $⟨n_1, n_2⟩$ dónde cada $n_i$ es un número natural. Pero inicialmente no es un objeto lógico definido, no sabemos qué es una tupla, ni siquiera si existe. No sabemos cómo definirla, ni cómo probar su existencia.

Sea $f : \text{List } \mathbb{N} → \text{List } \mathbb{N} : n ↦ m$ una función que asigna a cada natural de una lista de números naturales un natural de otra lista de números naturales. Conocemos en nuestro sistema de FOL= + Peano[restringido a + y *], concretamente para la suma y el producto, la existencia de funciones como la función siguiente $σ : \mathbb{N} → \mathbb{N}$, postulada en los axiomas de Peano, que asigna a cada número natural su sucesor. También tenemos $+$ y $*$, que dados una par de números naturales nos dan exactamente un número natural resultado cada una de ellas. Pero más allá de estas funciones concretas, no tenemos una definición clara de qué es una función en general, ni siquiera si existen funciones más allá de las que ya conocemos. No sabemos cómo definirlas, ni cómo probar su existencia.

En el sistema en que vivimos no sabemos como definir ni hacer nada directamente con listas, tuplas o funciones. No tenemos ni la más menor idea de qué es una lista, una tupla o una función. No sabemos siquiera si existen. No tenemos ni la más menor idea de cómo definirlas, ni de cómo probar su existencia.

### DE LO QUE **SÍ** DISPONEMOS

Disponemos solo de la teoría de los axiomas de Peano añadidos a la lógica de predicados de primer orden FOL con igualdad, FOL=. Pero de una forma muy restringida, solo disponemos de la existencia general de la suma y la multiplicación, y de la función sucesor. También dispondremos de la relación de $<$ entre números naturales. No disponemos de ningún otro objeto matemático definido, ni siquiera de la existencia de otros objetos matemáticos más allá de los números naturales y las funciones suma, producto y sucesor.

Como vivimos en Peano dentro de FOL=, no tendremos disponible, para comenzar, el principio de inducción generalizado, extendido a cualquier propiedad, que nos metería de lleno en lógica de segundo orden (cuantificación sobre predicados). Por lo tanto, no podremos definir ni probar nada sobre listas o tuplas, ni siquiera su existencia, sin antes definirlas y probar su existencia. Pero es que tampoco tenemos una facilidad de definición por recursión clara desde el principio.

Vivimos en FOL=+Peano. ¿Hasta dónde hemos desarrollado los naturales? Solo las existencia general de la suma y la multipliciación: podemos calcular mediante sumas, productos y la función sucesor, pero no tenemos más. A lo sumo tenemos la relación de orden estricto.

Alfabeto del que disponemos:

$$\mathcal{B} = \left\{{∃}, {∀}, {∧}, {∨}, {¬}, {⟹}, {⟺}, {'('}, {')'}, {=}\right\}$$
$$\mathcal{C} = \left\{{0}, {σ} , {τ}, {+}, {*}, {<}, {^}, {√}\right\}$$
$$\mathcal{D} = \left\{ {a'}, {b}, {c}, {d}, {e}, {f}, {g}, {h}\right\}$$
$$\mathcal{E} = \left\{ {x}, {y}, {z}, {w}\right\}$$
$$\mathcal{F} = \left\{ {i}, {j}, {k}, {l}, {m}, {n}, {r}, {s}, {t}, {p}, {q}\right\}$$
$$\mathcal{G} = \left\{ {u}, {v}\right\}$$
$$\mathcal{H} = \left\{ {'} \right\}$$
$$\mathcal{I} = \left\{ {1}, {2}, {3}, {{∃}^1} \right\}$$
$$\mathcal{J} = \left\{div2, mod2\right\}$$
$$\mathcal{K} = \left\{'⟨', '⟩', '[', ']', '{', '}', '.', ':', ';', ','\right\}$$
$$\mathcal{\Lambda} = \mathcal{B} ∪ \mathcal{C} ∪ \mathcal{D} ∪ \mathcal{E} ∪ \mathcal{F} ∪ \mathcal{G} ∪ \mathcal{H}  ∪ \mathcal{I} ∪ \mathcal{J} ∪ \mathcal{K}$$
y usaremos las letras siguientes como a sustituir por términos o fórmulas:
$$\mathcal{\Gamma} = \left\{ ϕ, ψ, ζ, δ, ε, η, θ \right\}$$

Las letras latinas minúsculas dentro de nuestro alfabeto $\mathcal{\Lambda}$ o esas mismas letras seguidas de un número de apóstrofes, como $x$, $y$, $z$, $x'$, $y''$, etc., serán usadas para definir variables término, es decir, objetos matemáticos concretos que pueden variar en un cierto rango de valores de nuestro universo. Nuestro universo define únicamente números naturales, por lo que estas variables término se referirán a números naturales concretos, aunque no sepamos cuáles son exactamente. Por ejemplo, $x$ podría ser el número natural 5, o el número natural 100, o el número natural 0, etc., pero no sabemos cuál es exactamente. Solo sabemos que $x$ es un número natural concreto.

Todo símbolo/letra será usado solo cuando se encuentre definido o en el caso de los símbolos lógicos, cuando se usen para construir fórmulas. Por ejemplo, el símbolo $+$ solo se usará para construir fórmulas que hablen de la suma de números naturales, como $x + y = z$, pero no se usará para definir ningún objeto matemático concreto. De esta forma, no tendremos ningún número natural concreto definido como $+$, ni ningún número natural concreto definido como $σ$, etc.

Las letras usadas como variables término se usarán libremente, y serán cuantificadas por los cuantificadores $∀$ y $∃$. Se permitirán en esas instancias de fórmulas con cuantificadores las pertenecidentes a $\mathcal{E}\cup\mathcal{F}\cup\mathcal{G}$ y esas mismas letras seguidas de un número cualquiera de apóstrofes de $\mathcal{H}$.

De esta forma $∀ x$ se leerá como "para todo número natural $x$" y $∃ x$ se leerá como "existe un número natural $x$". Por ejemplo, $∀ x, x + 0 = x$ se leerá como "para todo número natural $x$, $x + 0$ es igual a $x$". Y $∃ x, x < 5$ se leerá como "existe un número natural $x$ tal que $x$ es menor que 5".

Las palabras que empiecen por letra latina en mayúsculas serán usadas para definir predicados de primer orden.

Las reglas de derivación que se usarán serán las reglas de derivación de la lógica de predicados de primer orden con igualdad, FOL=, solo las reglas que sean constructivas, es decir, que no impliquen el uso de la ley del tercero excluido ni de la doble negación. Por ejemplo, se podrán usar las reglas de introducción y eliminación de los cuantificadores $∀$ y $∃$, pero no se podrá usar la regla de introducción de la negación ni la regla de eliminación de la negación (tenemos disponible $P ⟹ ¬ (¬ P)$ pero no $¬ (¬ P) ⟹ P$, y tampoco tenemos disponible $P ∨ ¬ P$).

Axioma 1: $∃ 0$

Axioma 2: $∀ n, ∃ σ(n)$

Axioma 3: $∀ n, σ(n) ≠ 0$

Axioma 4: $∀ n, ∀ m, σ(n) = σ(m) ⟹ n = m$

Axioma 5: $∀ n, ¬ n = 0 ⟹ ∃ m, σ(m) = n$

Axioma 6: $∀ n, n + 0 = n$

Axioma 7: $∀ n, ∀ m, n + σ(m) = σ(n + m)$

Axioma 8: $∀ n, n * 0 = 0$

Axioma 9: $∀ n, ∀ m, n * σ(m) = (n * m) + n$

Axioma 10: $∀ n, ∀ m, n < m ⟺ ∃ k, n + σ(k) = m$

Axioma 11: $∀ n, n^0 = 1$

Axioma 12: $∀ n, ∀ m, n^{σ(m)} = n^m * n$

Axioma 13: $√ 0 = 0$

Axioma 14: $√ 1 = 1$

Axioma 15: $∀ n, ∃ √n, (√n)^2 ≤ n$

Axioma 16: $∀ n, ∀ m, n < (√n + 1)^2$

Definición 1: $1 := \sigma(0)$

Definición 2: $2 := \sigma(1)$

Definición 3: $3 := \sigma(2)$

Definición 4: $4 := \sigma(3)$

Definición 5: $∀ n, ∃ div2(n), 2 * div2(n) = n ∨ 2 * div2(n) + 1 = n$

Definición 6: $∀ n, ∃ mod2(n), 2 * div2(n) + mod2(n) = n$

Definición 7: $τ(0) := 0$

Definición 8: $∀ n, ∃ τ(n), τ(σ(n)) = n$

Definición 9: $∀ n, Even(n) ⟺ mod2(n) = 0$

Definición 10: $∀ n, Odd(n) ⟺ mod2(n) = 1$

Vamos a empezar por definir las 2-Tuplas de números naturales. Vamos a usa la función de emparejamiento de Cantor. Se trata de una función biyectiva $c : \mathbb{N} → \mathbb{N} → \mathbb{N}$ que asigna a cada par de números naturales un natural único. La función de emparejamiento de Cantor (y su residuo) se define como sigue:

$$c(x,y) := div2({(x+y) * (x+y+1)} + 2 * y)$$
$$r(x,y) := mod2({(x+y) * (x+y+1)} + 2 * y)$$

### ¿Qué deberíamos demostrar con lo definido hasta aquí?

1. $2 = σ(σ(0))$
2. $2 = 1 + 1$
3. $3 = σ(σ(σ(0)))$
4. $3 = 1 + 2$
5. $3 = 2 + 1$
6. $3 = (1 + 1) + 1$
7. $3 = 1 + (1 + 1)$
8. $4 = σ(σ(σ(σ(0))))$
9. $4 = 1 + 3$
10. $4 = 3 + 1$
11. $4 = 2 + 2$
12. $4 = (1 + 1) + (1 + 1)$
13. $4 = ((1 + 1) + 1) + 1 $
14. $4 = 1 + (1 + (1 + 1))$
15. $4 = 1 + (1 + 2) $
16. $4 = (1 + 1) + 2$
17. $4 = 2 + (1 + 1) $
18. $4 = (2 + 1) + 1 $
19. $4 = 2 + 2$
20. $4 = (1 + 2) + 1$
21. $4 = 1 + (2 + 1)$
22. $0 ≠ 1$
23. $0 ≠ 2$
24. $0 ≠ 3$
25. $0 ≠ 4$
26. $1 ≠ 2$
27. $1 ≠ 3$
28. $1 ≠ 4$
29. $2 ≠ 3$
30. $2 ≠ 4$
31. $3 ≠ 4$
32. $0+0 = 0$
33. $∀ n, 0+n=n$
34. $1+1 = 2$
35. $1+2 = 3$ y $2+1 = 3$
36. $1+3 = 4$ y $3+1 = 4$ y $2+2 = 4$
37. $∀ n, 1*n=n$
38. $∀ n, n*1=n$
39. $∀ n, n*2=n+n$
40. $∀ n, 2*n=n+n$
41. $∀ n, 3*n = (n + n) + n$
42. $∀ n, n*3 = (n + n) + n$
43. $∀ n, 3*n = n + (n + n)$
44. $∀ n, n*3 = n + (n + n)$
45. $∀ n, 3*n = n + 2*n$
46. $∀ n, n*3 = n + 2*n$
47. $∀ n, 3*n = 2*n + n$
48. $∀ n, n*3 = 2*n + n$
49. $∀ n, 0*n=0$
50. $2*3=3+3$ y $3*2=3+3$
51. $3*3=3+3+3$ y $3*4=4+4+4$ y $4*3=3+3+3+3$ y $3*4=4*3$
52. $∀ n, σ(n) = n + 1 = 1 + n$
53. $∀ n, σ(n) = n * 1 + 1$
54. $∀ n, ∀ m, n < m ⟺ σ(n) < σ(m)$
55. $∀ n, ¬ n < n$
56. $∀ n, ∀ m, n < m ⟹ ¬ n = m$
57. $∀ n, ∀ m, n < m ⟹ ¬ m < n$
58. $∀ l, ∀ n, ∀ m, l < n ∧ n < m ⟹ l < m$
59. $∀ n, ∀ m, n < m ∨ n = m ∨ m < n$
60. $∀ n, n < σ(n)$
61. $∀ n, ¬ n = 0 ⟹ τ(n) < n$
62. $∀ n, ∀ m, ¬ n = 0 ⟹ τ(n) = m ⟹ n = σ(m)$
63. $∀ n, n < σ(σ(n))$
64. $∀ n, n < σ(σ(σ(n)))$
65. $∀ n, n < σ(σ(σ(σ(n))))$
66. $∀ n, 0 < σ(n)$
67. $∀ n, 1 < σ(σ(m))$
68. $∀ n, 2 < σ(σ(σ(m)))$
69. $∀ n, 3 < σ(σ(σ(σ(m))))$
70. $∀ n, 4 < σ(σ(σ(σ(σ(m)))))$
71. $∀ n, ∀ m, σ(n) < σ(m) → n < m$
72. $∀ n, 2*div2(n) < n ∨ 2*div2(n) = n$
73. $∀ n, mod2(n) = 0 ∨ mod2(n) = 1$

- La función de emparejamiento de Cantor (para nosotros los números `c` de Cantor) es una serie de operaciones que tenemos bien definidas, y que podemos realizar por tanto. La función `r` será el residuo de Cantor, que nos servirá para recuperar la información de `y` a partir de `c`.

- Debemos demostrar que siempre existe un número natural `c` de Cantor para cada par de números naturales `x` e `y`. Es decir, debemos demostrar que la función de emparejamiento de Cantor es total. Formalmente:

  $$∀ x, ∀ y, ∃ c, 2 * c = {(x+y) * (x+y+1)} + 2 * y$$

- Debemos demostrar que el número de Cantor encontrado es único:

  $$∀ x, ∀ y, ∀ c, ∀ c', (2 * c = {(x+y) * (x+y+1)} + 2 * y) ∧ (2 * c' = {(x+y) * (x+y+1)} + 2 * y) → c = c'$$

- A partir de aquí podemos desarrollar la función de emparejamiento de Cantor como un predicado de primer orden sobre tres números naturales, que se cumple si y solo si el tercer número es el número de Cantor de los dos primeros:

  $$\text{Cantor}(x,y,c) := (2 * c = {(x+y) * (x+y+1)} + 2 * y)$$

- Ahora debemos demostrar que, dado un número de Cantor `c`, siempre existe un par de números naturales `x` e `y` tal que `c` es el número de Cantor de `x` e `y`. Es decir, debemos demostrar que la función de emparejamiento de Cantor es sobreyectiva. Formalmente:

  $$∀ c, ∃ x, ∃ y, 2 * c = {(x+y) * (x+y+1)} + 2 * y$$

- Debemos demostrar que `c` determinad e forma única a `x` e `y`:

  $$∀ c, ∀ x, ∀ x', ∀ y, ∀ y', (2 * c = {(x+y) * (x+y+1)} + 2 * y) ∧ (2 * c = {(x'+y') * (x'+y'+1)} + 2 * y') → (x = x' ∧ y = y')$$

- Lo anterior nos permite definir un predicado de primer orden sobre tres números naturales, que se cumple si y solo si el tercer número es el número de Cantor de los dos primeros:

  $${\text{proyCantor}}_1 (c,x) := ∃^1  y ∈ \mathbb{N}, 2 * c = {(x+y) * (x+y+1)} + 2 * y$$

  $${\text{proyCantor}}_2 (c,y) := ∃^1  x ∈ \mathbb{N}, 2 * c = {(x+y) * (x+y+1)} + 2 * y$$

- Ahora tendríamos que probar que $∀ c ∈ \mathbb{N}, ∃ x x' ∈ \mathbb{N}, {\text{proyCantor}}_1(c,x) ∧ {\text{proyCantor}}_1(c,x') ⟹ x = x'$, y que $∀ c ∈ \mathbb{N}, ∃ y y' ∈ \mathbb{N}, {\text{proyCantor}}_2(c,y) ∧ {\text{proyCantor}}_2(c,y') ⟹ y = y'$. Es decir, que cada número de Cantor determina de forma única a su proyección 1 y a su proyección 2.

- Ahora tenemos que probar que:
  Sean $x, y, x', y' ∈ \mathbb{N}$ y $c, c' ∈ \mathbb{N}$, entonces:

  $$\text{Cantor}(x,y,c) ∧ \text{Cantor}(x',y',c') → (c = c' ↔ (x = x' ∧ y = y'))$$

- A partir de aquí podemos definir la 2-tupla de naturales como el número de Cantor de sus componentes, y tener una sintaxism ás natural para escribir tuplas:

  $$\text{2-Tuple}(x,y) := c \text{ tal que } \text{Cantor}(x,y,c)$$

  $$⟨x,y⟩ := \text{2-Tuple}(x,y)$$

- Vamos a calcular las proyecciones de forma concreta:

  $$[⟨x,y⟩].1: = \text{proyCantor}_1(⟨x,y⟩) := x$$

  $$0 = x*x+x*(2*y+1)+(y*(y+3)+2*c)$$

  En una ecuación de segundo grado clásica, tendremos

  $$2*x = {-{(2*y+1)} ± \sqrt{{(2*y+1)}^2 - 4*(y*(y+3)+2*c)}}$$

  dónde el discrimiante es:

    $$D = {(2*y+1)}^2 - 4*{(y*{(y+3)}+2*c)}$$

    $$D = 4*y^2 + 4*y + 1 - 4*y^2 - 12*y - 8*c$$

- Proyección Directa: De $⟨x, y⟩$ a $c = Cantor(x,y)$.

   La función directa es trivial en términos de cálculo pero fundamental para validar la biyectividad. Se define como:

   $$c = f(x, y) = \frac{(x+y)(x+y+1)}{2} + y$$

   Propiedades de la Proyección Directa:

  - Suma de la Diagonal ($w$):

     Se define como $w = x + y$.

  - Número Triangular ($T_w$):

     El término $\frac{w(w+1)}{2}$ representa la cantidad de puntos en todas las diagonales anteriores a la actual.

  - Desplazamiento ($y$):

     Determina la posición específica dentro de la diagonal $w$.

- Algoritmos Implementados

    Para una implementación práctica, hemos desarrollado dos herramientas:

    Calculador Directo: Toma $(x, y)$ y devuelve $c$ aplicando la fórmula polinómica.

    Calculador Inverso: Toma $c$ y busca la diagonal $w$ mediante el método constructivo de "acumulación" (sumas y productos), garantizando que no se requieran raíces cuadradas para encontrar la solución entera.Ambos métodos se han integrado en el simulador interactivo adjunto para permitir la verificación cruzada de los resultados.

Programa de Simulación Interactiva:

```
    <!DOCTYPE html>
    <html lang="es">
    <head>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>Laboratorio de Cantor</title>
        <script src="https://cdn.tailwindcss.com"></script>
        <style>
            .step-entry { animation: fadeIn 0.3s ease-out; }
            @keyframes fadeIn { from { opacity: 0; transform: translateY(4px); } to { opacity: 1; transform: translateY(0); } }
            .math-font { font-family: 'Times New Roman', Times, serif; }
        </style>
    </head>
    <body class="bg-gray-100 min-h-screen p-4 md:p-8">

        <div class="max-w-5xl mx-auto">
            <header class="text-center mb-10">
                <h1 class="text-4xl font-extrabold text-slate-800 mb-2">Laboratorio de la Función de Cantor</h1>
                <p class="text-slate-600 italic">Exploración interactiva de biyectividad entre $\mathbb{N}^2$ y $\mathbb{N}$</p>
            </header>

            <div class="grid grid-cols-1 lg:grid-cols-2 gap-8">
            
                <!-- SIMULADOR DIRECTO -->
                <div class="bg-white rounded-2xl shadow-xl overflow-hidden border border-slate-200">
                    <div class="bg-indigo-600 p-4">
                        <h2 class="text-white text-xl font-bold flex items-center">
                        <span class="mr-2">➡️</span> Proyección Directa (x, y) → c
                        </h2>
                    </div>
                    <div class="p-6">
                        <div class="grid grid-cols-2 gap-4 mb-6">
                            <div>
                                <label class="block text-sm font-semibold text-slate-700">Valor x</label>
                                <input type="number" id="dirX" value="2" min="0" class="w-full mt-1 px-4 py-2 border rounded-lg focus:ring-2 focus:ring-indigo-500 outline-none">
                            </div>
                            <div>
                                <label class="block text-sm font-semibold text-slate-700">Valor y</label>
                                <input type="number" id="dirY" value="1" min="0" class="w-full mt-1 px-4 py-2 border rounded-lg focus:ring-2 focus:ring-indigo-500 outline-none">
                            </div>
                        </div>
                    </div>
                    <button onclick="runDirect()" class="w-full bg-indigo-600 hover:bg-indigo-700 text-white font-bold py-3 rounded-lg transition-all shadow-md">
                        Calcular Cantor(x, y)
                    </button>

                    <div id="dirResult" class="mt-6 p-4 bg-slate-50 rounded-xl border-2 border-dashed border-slate-200 hidden">
                        <p class="text-center text-slate-500 text-sm mb-1 uppercase font-bold tracking-widest">Resultado c</p>
                        <p id="dirOut" class="text-center text-4xl font-black text-indigo-600"></p>
                    </div>
                </div>
            </div>

            <!-- SIMULADOR INVERSO -->
            <div class="bg-white rounded-2xl shadow-xl overflow-hidden border border-slate-200">
                <div class="bg-emerald-600 p-4">
                    <h2 class="text-white text-xl font-bold flex items-center">
                        <span class="mr-2">⬅️</span> Inversión Constructiva c → (x, y)
                    </h2>
                </div>
                <div class="p-6">
                    <div class="mb-6">
                        <label class="block text-sm font-semibold text-slate-700">Valor de Emparejamiento (c)</label>
                        <input type="number" id="invC" value="7" min="0" class="w-full mt-1 px-4 py-2 border rounded-lg focus:ring-2 focus:ring-emerald-500 outline-none">
                    </div>
                    <button onclick="runInverse()" class="w-full bg-emerald-600 hover:bg-emerald-700 text-white font-bold py-3 rounded-lg transition-all shadow-md">
                        Descomponer c
                    </button>

                    <div id="invResult" class="mt-6 hidden">
                        <div class="grid grid-cols-2 gap-4">
                            <div class="p-3 bg-emerald-50 rounded-lg border border-emerald-100 text-center">
                                <span class="block text-xs font-bold text-emerald-600 uppercase">Componente x</span>
                                <span id="invOutX" class="text-3xl font-black text-emerald-700"></span>
                            </div>
                            <div class="p-3 bg-emerald-50 rounded-lg border border-emerald-100 text-center">
                                <span class="block text-xs font-bold text-emerald-600 uppercase">Componente y</span>
                                <span id="invOutY" class="text-3xl font-black text-emerald-700"></span>
                            </div>
                        </div>
                    </div>
                </div>
            </div>

            <!-- LOG DE TRAZA (OCUPA TODA LA FILA ABAJO) -->
            <div class="lg:col-span-2 bg-slate-900 rounded-2xl shadow-2xl p-6 overflow-hidden">
                <div class="flex justify-between items-center mb-4">
                    <h3 class="text-emerald-400 font-mono font-bold uppercase tracking-tighter">Terminal de Ejecución Constructiva</h3>
                    <button onclick="clearLog()" class="text-slate-500 hover:text-white text-xs uppercase underline">Limpiar Log</button>
                </div>
                <div id="consoleLog" class="font-mono text-sm space-y-1 h-64 overflow-y-auto pr-2 custom-scrollbar text-slate-300">
                    <span class="text-slate-500 italic">// Sistema listo. Esperando operación...</span>
                </div>
            </div>
        </div>
    </div>

    <script>
        const consoleLog = document.getElementById('consoleLog');

        function log(msg, color = 'text-slate-300') {
            const div = document.createElement('div');
            div.className = `step-entry ${color}`;
            div.innerHTML = `> ${msg}`;
            consoleLog.appendChild(div);
            consoleLog.scrollTop = consoleLog.scrollHeight;
        }

        function clearLog() { consoleLog.innerHTML = '<span class="text-slate-500 italic">// Consola reiniciada.</span>'; }

        // MÉTODOS DIRECTOS
        function runDirect() {
            const x = parseInt(document.getElementById('dirX').value);
            const y = parseInt(document.getElementById('dirY').value);
            if (isNaN(x) || isNaN(y)) return;

            log(`Iniciando Cálculo Directo: f(${x}, ${y})`, 'text-indigo-400 font-bold');
            const w = x + y;
            log(`Diagonal calculada: w = x + y = ${w}`);
            const triangular = (w * (w + 1)) / 2;
            log(`Base triangular: T_w = (${w} * ${w+1}) / 2 = ${triangular}`);
            const c = triangular + y;
            log(`Resultado Final: c = ${triangular} + ${y} = ${c}`, 'text-white bg-indigo-900 px-2 rounded');

            const outDiv = document.getElementById('dirResult');
            const outVal = document.getElementById('dirOut');
            outVal.innerText = c;
            outDiv.classList.remove('hidden');
        }

        // MÉTODOS INVERSOS (CONSTRUCTIVOS)
        function runInverse() {
            const c = parseInt(document.getElementById('invC').value);
            if (isNaN(c)) return;

            log(`Iniciando Inversión Constructiva: c = ${c}`, 'text-emerald-400 font-bold');
            const doubleC = 2 * c;
            log(`Buscando diagonal mediante comparación: 2c = ${doubleC}`);

            let w = 0;
            // Solo sumas y productos para hallar w
            while ((w + 1) * (w + 2) <= doubleC) {
                w++;
            }

            log(`Diagonal w hallada (máximo w tal que T_w <= c): ${w}`, 'text-emerald-300');
            
            // Calculamos y usando sumas y productos
            const wTriangular2 = w * (w + 1);
            const twoY = (2 * c) - wTriangular2;
            const y = twoY / 2;
            const x = w - y;

            log(`Resolviendo y: (2*${c} - ${w}*${w+1}) / 2 = ${y}`);
            log(`Resolviendo x: w - y = ${w} - ${y} = ${x}`);
            log(`Pareja recuperada: (${x}, ${y})`, 'text-white bg-emerald-900 px-2 rounded');

            document.getElementById('invOutX').innerText = x;
            document.getElementById('invOutY').innerText = y;
            document.getElementById('invResult').classList.remove('hidden');
        }
        </script>
    </body>
    </html>
```
