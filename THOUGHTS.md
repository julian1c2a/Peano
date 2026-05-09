# Thoughts — Peano

**Last updated:** 2026-05-07
*Author: Julián Calderón Almendros

> This is an informal design journal. Records ideas, open questions, and lessons
> learned. Not normative — purely exploratory. Useful for AI context on "why"
> decisions were made.
>
> **Branch status**: This branch finalizes when Sylow.lean is complete (0 private
> axioms) and documentation is migrated to `/doc/`. Phase G.4 (AczelSetTheory
> handoff) follows after freezing and merging.

---

## Design Philosophy

This project formalizes Peano arithmetic from scratch in Lean 4, deriving all
8 Peano axioms as theorems from the inductive type `ℕ₀`. No external dependencies
(not even Mathlib). The goal is a complete, self-contained arithmetic library
covering: order, arithmetic operations (add, sub, mul, div, mod, pow), primes,
factorial, binomial coefficients, Newton binomial theorem, group theory, and the
three Sylow theorems.

---

## Open Questions

- [ ] Should export blocks in Peano.lean be migrated to individual leaf modules per §30?
- [ ] Is the Peano/ vs Peano namespace mismatch worth resolving?

**Resolved questions:**

- ~~How to approach the remaining sorry in group theory modules~~ → All 3 Sylow theorems
  closed; 3 private axioms remain (`wielandt_p_ndvd_r`, `sylow_third_mod`, `sylow_third_dvd`).
- ~~FSet design: Quotient vs sorted list~~ → Sorted list (ADR-007).
- ~~FinGroup polymorphism approach~~ → Phase 5 COMPLETADA (2026-05-07): pleno polimorfismo
  sobre `{α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]` en toda la infraestructura.
- ~~Phase F Foundation (CantorPairing + GodelBeta)~~ → Phase F completamente terminada
  (2026-05-02): F.1 CantorPairing ✅, F.2 GodelBeta ✅, F.3 paraguas Foundation.lean ✅.

---

## Architectural decisions — AczelSetTheory (2026-05-02)

**¿Puede AczelSetTheory definir `Nat` a partir de `HFSet` solo?**

Sí: una vez que el embedding Peano → Aczel es lógicamente completo, el desarrollo
matemático nuevo ocurre en AczelSetTheory — por ejemplo `def Nat := List Unit` o
directamente sobre `HFSet`. Todo lo computable en Peano es computable en AczelSetTheory;
Peano pasa a modo mantenimiento.

**Consecuencia para este proyecto**: solo quedan los coletazos abiertos (3 axiomas
privados en Sylow.lean) y la migración de documentación a `/doc/`. El desarrollo
matemático principal pasa a AczelSetTheory.

**Documentación**: La migración de `REFERENCE.md` monolítico a `REFERENCE-{Tema}.md`
en árbol bajo `/doc/` es importante para que los asistentes de IA puedan navegar sin
perder contexto. Cada nodo de documentación debe ofrecer enlaces hacia los nodos
adyacentes.

---

## Lessons Learned

### Inductive Type Approach

- Defining `ℕ₀` as an inductive type gives all Peano axioms for free as proven theorems
- The recursion principle is the most powerful tool — all arithmetic flows from it
- Well-foundedness proofs are needed for termination of recursive definitions

### Module Organization

- The linear dependency chain (Axioms → Order → Arithmetic → Advanced) works well
- Each module builds strictly on previous ones — no circular dependencies
- 64 build jobs; `FSetFunction.lean` is the largest module (~1500 lines, ~92 exports)

### Documentation

- REFERENCE.md must be self-sufficient for AI assistants
- The "project" protocol (AI-GUIDE.md §12) prevents documentation drift

### Como probar el lema de Zasenhauss

Digamos que tenemos un grupo (notación multiplicativa) `G` y dos subgrupos `H` y `K` de `G`. Además tenemos un subgrupo normal de `H`, digamos `N`, y otros subgrupo normal de `K`, digamos `M`.

En símbolos:

- `G` es un grupo
- `H ≤ G` y `K ≤ G`
- `N ⊲ H` y `M ⊲ K`

El lema de Zasenhauss dice:

$$
\begin{aligned}
& N \cap K \quad ⊴ \quad H \cap K \\
& H \cap M \quad ⊴ \quad H \cap K \\
& (N \cap K)(H \cap M) \quad ⊴ \quad H \cap K \\
& N (H ∩ M) \quad ⊴ \quad N (H ∩ K) \\
& M (N ∩ K) \quad ⊴ \quad M (H ∩ K) \\
& \frac {N (H ∩ K)} {N (H ∩ M)} \quad ≅ \quad \frac {H ∩ K} {(N \cap K)(H \cap M)}  \quad ≅ \quad \frac {M (H ∩ K)} {M (N ∩ K)}
\end{aligned}
$$

**Verificación del enunciado**: correcto. Es el clásico *lema de la mariposa* de Zassenhaus.
Las cinco normalidades son prerrequisitos del isomorfismo final; las tres el cociente central
son consecuencia del Primer Teorema de Isomorfismo aplicado a un único homomorfismo bien elegido.

---

#### Prueba detallada

Trabajamos en notación multiplicativa. Denotamos con $e$ el neutro de $G$.
Recordamos que $N \unlhd H$ equivale a: $N \leq H$ y $hNh^{-1} = N$ para todo $h \in H$.
Para que un subconjunto $S \subseteq G$ sea subgrupo basta verificar: (i) $e \in S$,
(ii) $a, b \in S \Rightarrow ab \in S$, (iii) $a \in S \Rightarrow a^{-1} \in S$.

---

##### Paso 1 — $N \cap K \unlhd H \cap K$

Necesitamos demostrar dos cosas: que $N \cap K$ es subgrupo de $H \cap K$, y que es normal en él.

**1a. $N \cap K$ es subgrupo de $H \cap K$:**

- *Elemento neutro*: $N \leq H$ implica $e \in N$; $K \leq G$ implica $e \in K$. Luego $e \in N \cap K$.
  Análogamente $e \in H \cap K$, y $N \cap K \subseteq H \cap K$ (pues $N \leq H$ y $K \leq K$), así que $e \in N \cap K \subseteq H \cap K$.

- *Clausura por producto*: Sean $a, b \in N \cap K$.
  Como $a, b \in N$ y $N$ es subgrupo, $ab \in N$.
  Como $a, b \in K$ y $K$ es subgrupo, $ab \in K$.
  Luego $ab \in N \cap K$.

- *Clausura por inverso*: Sea $a \in N \cap K$.
  $a \in N$ y $N$ subgrupo implica $a^{-1} \in N$.
  $a \in K$ y $K$ subgrupo implica $a^{-1} \in K$.
  Luego $a^{-1} \in N \cap K$.

**1b. $N \cap K$ es normal en $H \cap K$:**

Sea $x \in H \cap K$ y $a \in N \cap K$. Queremos $x a x^{-1} \in N \cap K$.

- *Parte $N$*: $x \in H$ (pues $x \in H \cap K$), $a \in N \leq H$ y $N \unlhd H$, por lo que
  $x a x^{-1} \in x N x^{-1} = N$.

- *Parte $K$*: $x \in K$, $a \in K$, $x^{-1} \in K$ (pues $K$ es subgrupo) y $K$ cerrado por
  producto, luego $x a x^{-1} \in K$.

Conclusión: $x a x^{-1} \in N \cap K$. ∎

---

##### Paso 2 — $H \cap M \unlhd H \cap K$

Argumento perfectamente simétrico al Paso 1, intercambiando $(N, H) \leftrightarrow (M, K)$.

**2a. $H \cap M$ es subgrupo de $H \cap K$:**

- $e \in H \cap M$: pues $e \in H$ y $e \in M$ (ambos subgrupos). Y $H \cap M \subseteq H \cap K$ pues $M \leq K$.
- *Producto*: $a, b \in H \cap M \Rightarrow ab \in H$ (subgrupo) y $ab \in M$ (subgrupo), luego $ab \in H \cap M$.
- *Inverso*: $a \in H \cap M \Rightarrow a^{-1} \in H$ y $a^{-1} \in M$, luego $a^{-1} \in H \cap M$.

**2b. $H \cap M$ es normal en $H \cap K$:**

Sea $x \in H \cap K$ y $b \in H \cap M$.

- *Parte $H$*: $x, b, x^{-1} \in H$ y $H$ cerrado por producto, luego $x b x^{-1} \in H$.
- *Parte $M$*: $x \in K$ (pues $x \in H \cap K$), $b \in M \leq K$ y $M \unlhd K$, luego
  $x b x^{-1} \in x M x^{-1} = M$.

Conclusión: $x b x^{-1} \in H \cap M$. ∎

---

##### Paso 3 — $(N \cap K)(H \cap M) \unlhd H \cap K$

Sabemos por los pasos anteriores que $A := N \cap K \unlhd H \cap K$ y $B := H \cap M \unlhd H \cap K$.
Escribimos $L := H \cap K$ para abreviar.

**3a. El producto $AB$ es igual a $BA$:**

Sea $a \in A$ y $b \in B$. Como $b \in L$ y $A \unlhd L$, se tiene $b^{-1} a b \in A$. Luego
$$ab = b \underbrace{(b^{-1}ab)}_{\in A} \in BA.$$
Esto prueba $AB \subseteq BA$. El argumento simétrico (usando $B \unlhd L$) da $BA \subseteq AB$.
Por tanto $AB = BA$.

**3b. $AB$ es subgrupo de $L$:**

- *Elemento neutro*: $e = e \cdot e \in AB$.

- *Producto*: Sean $a_1 b_1, a_2 b_2 \in AB$ (con $a_i \in A$, $b_i \in B$). Entonces
  $$(a_1 b_1)(a_2 b_2) = a_1 (b_1 a_2) b_2.$$
  Por 3a, $b_1 a_2 \in AB$, es decir $b_1 a_2 = a_3 b_1$ con $a_3 := b_1 a_2 b_1^{-1} \in A$
  (pues $b_1 \in L$ y $A \unlhd L$). Luego
  $$(a_1 b_1)(a_2 b_2) = a_1 (a_3 b_1) b_2 = (a_1 a_3)(b_1 b_2) \in AB$$
  ya que $a_1 a_3 \in A$ y $b_1 b_2 \in B$.

- *Inverso*: $(ab)^{-1} = b^{-1} a^{-1}$. Por 3a, $b^{-1} a^{-1} = a' b^{-1}$ con
  $a' := b^{-1} a^{-1} b \in A$ (pues $b^{-1} \in L$ y $A \unlhd L$), y $b^{-1} \in B$.
  Luego $(ab)^{-1} \in AB$.

**3c. $AB \unlhd L$:**

Sea $x \in L$ y $ab \in AB$ (con $a \in A$, $b \in B$). Entonces
$$x(ab)x^{-1} = (xax^{-1})(xbx^{-1}).$$
Por el Paso 1, $xax^{-1} \in A$; por el Paso 2, $xbx^{-1} \in B$. Luego $x(ab)x^{-1} \in AB$. ∎

---

##### Paso 4 — $NS$ es subgrupo de $H$ cuando $N \unlhd H$ y $S \leq H$ (criterio auxiliar)

Este criterio se usa en los Pasos 4 y 5. Lo demostramos con detalle porque es la base de todo.

Sea $N \unlhd H$ y $S \leq H$. Definimos $NS := \{ns : n \in N, s \in S\}$.

**4a. $NS \subseteq H$**: $n \in N \leq H$ y $s \in S \leq H$, luego $ns \in H$ (cerrado).

**4b. $e \in NS$**: $e = e \cdot e$ con $e \in N$ y $e \in S$.

**4c. Producto**: Sean $n_1 s_1, n_2 s_2 \in NS$. Entonces
$$(n_1 s_1)(n_2 s_2) = n_1 (s_1 n_2 s_1^{-1}) (s_1 s_2).$$
Como $s_1 \in S \leq H$ y $N \unlhd H$, tenemos $n_3 := s_1 n_2 s_1^{-1} \in N$.
Y $s_1 s_2 \in S$ (subgrupo). Luego el producto es $n_1 n_3 \cdot (s_1 s_2) \in NS$.

**4d. Inverso**: Sea $ns \in NS$.
$(ns)^{-1} = s^{-1} n^{-1} = (s^{-1} n^{-1} s) s^{-1}.$
Como $s^{-1} \in S \leq H$ y $N \unlhd H$, tenemos $n' := s^{-1} n^{-1} s \in N$.
Y $s^{-1} \in S$. Luego $(ns)^{-1} = n' s^{-1} \in NS$.

**Consecuencias inmediatas**:

- $N(H \cap M) \leq H$ (aplicar con $S = H \cap M \leq H$).
- $N(H \cap K) \leq H$ (aplicar con $S = H \cap K \leq H$).
- $N(H \cap M) \leq N(H \cap K)$: pues $H \cap M \leq H \cap K$ (ya que $M \leq K$), luego
  cada $nm$ con $m \in H \cap M$ también pertenece a $N(H\cap K)$.

---

##### Paso 5 — $N(H \cap M) \unlhd N(H \cap K)$

Queremos: para todo $x \in N(H \cap K)$ e $y \in N(H \cap M)$, $xyx^{-1} \in N(H \cap M)$.

Escribimos $x = n_1 k_1$ con $n_1 \in N$, $k_1 \in H \cap K$, y $y = n_2 m_2$ con $n_2 \in N$, $m_2 \in H \cap M$.

**5a. Calcular $x^{-1}$**:
$x^{-1} = (n_1 k_1)^{-1} = k_1^{-1} n_1^{-1}$.
Observamos que $k_1^{-1} \in H \cap K$ (subgrupo) y podemos reescribir:
$x^{-1} = (k_1^{-1} n_1^{-1} k_1) k_1^{-1}$.
Sea $n_1' := k_1^{-1} n_1^{-1} k_1 \in N$ (pues $k_1 \in H$ y $N \unlhd H$). Así $x^{-1} = n_1' k_1^{-1}$.

**5b. Reordenar $x y x^{-1} = n_1 k_1 \cdot n_2 m_2 \cdot k_1^{-1} n_1^{-1}$**:

*Primer bloque*: $k_1 n_2 m_2 k_1^{-1}$. Lo separamos:
$$k_1 n_2 m_2 k_1^{-1} = (k_1 n_2 k_1^{-1})(k_1 m_2 k_1^{-1}).$$

- Sea $n_3 := k_1 n_2 k_1^{-1}$. Como $k_1 \in H \cap K \leq H$ y $N \unlhd H$: $n_3 \in N$.
- Sea $m_3 := k_1 m_2 k_1^{-1}$. Como $k_1 \in H$ y $m_2 \in H$: $m_3 \in H$. Como $k_1 \in K$ y $m_2 \in M$ y $M \unlhd K$: $m_3 \in M$. Por tanto $m_3 \in H \cap M$.

Entonces $k_1 n_2 m_2 k_1^{-1} = n_3 m_3$.

*Segundo bloque*: $n_1 (n_3 m_3) n_1^{-1}$. Lo reordenamos moviendo $n_1^{-1}$ a la izquierda de $m_3$:
$$n_1 n_3 m_3 n_1^{-1} = n_1 n_3 (m_3 n_1^{-1} m_3^{-1}) m_3.$$
Sea $n_4 := m_3 n_1^{-1} m_3^{-1}$. Como $m_3 \in H \cap M \leq H$ y $n_1^{-1} \in N$ y $N \unlhd H$: $n_4 \in N$.

**5c. Conclusión**:
$$x y x^{-1} = n_1 n_3 n_4 m_3$$
donde $n_1 n_3 n_4 \in N$ (producto de tres elementos de $N$) y $m_3 \in H \cap M$.
Luego $xyx^{-1} \in N(H \cap M)$. ∎

**Por simetría** (intercambiando $(N, H) \leftrightarrow (M, K)$) se obtiene $M(N \cap K) \unlhd M(H \cap K)$.

---

##### Paso 6 — El isomorfismo $\tfrac{H \cap K}{(N \cap K)(H \cap M)} \cong \tfrac{N(H \cap K)}{N(H \cap M)}$

Definimos
$$\varphi : H \cap K \;\longrightarrow\; \frac{N(H \cap K)}{N(H \cap M)}, \qquad \varphi(k) := N(H \cap M) \cdot k.$$

**6a. Bien definida**: $k \in H \cap K \leq N(H \cap K)$ (tomando $n = e$), así que $k$ pertenece al grupo del cociente. El cociente está definido porque $N(H\cap M) \unlhd N(H \cap K)$ (Paso 5).

**6b. Homomorfismo**: Para $k_1, k_2 \in H \cap K$,
$$\varphi(k_1 k_2) = N(H\cap M) \cdot k_1 k_2 = \bigl(N(H\cap M) \cdot k_1\bigr)\bigl(N(H\cap M) \cdot k_2\bigr) = \varphi(k_1)\,\varphi(k_2).$$
(La operación en el cociente es por cosets, válida pues $N(H\cap M)$ es normal.)

**6c. Sobreyectividad**: Sea $N(H\cap M) \cdot nk$ un elemento arbitrario del cociente, con $n \in N$ y $k \in H \cap K$. Como $e \in H \cap M$, tenemos $n = n \cdot e \in N(H \cap M)$. Entonces
$$N(H\cap M) \cdot nk = N(H\cap M) \cdot k = \varphi(k).$$
Luego $\varphi$ es sobreyectiva.

**6d. Cálculo del núcleo**:
$$k \in \ker\varphi \iff N(H\cap M) \cdot k = N(H\cap M) \iff k \in N(H\cap M).$$
Así $\ker\varphi = N(H\cap M) \cap (H \cap K)$. Caracterizamos esta intersección:

*$\supseteq$*: Si $k = ab$ con $a \in N \cap K \leq N$ y $b \in H \cap M$, entonces $k \in N(H\cap M)$.
Además $a \in N \leq H$ y $a \in K$, y $b \in H \cap M \leq H \cap K$, luego $k = ab \in H \cap K$. ✓

*$\subseteq$*: Si $k \in N(H\cap M) \cap (H\cap K)$, escribimos $k = nm$ con $n \in N$, $m \in H\cap M$, $k \in H \cap K$.

- $m \in H \cap M \leq M \leq K$ y $k \in K$, así que $n = km^{-1} \in K$.
- Como también $n \in N$: $n \in N \cap K$.
- Luego $k = \underbrace{n}_{\in N\cap K} \cdot \underbrace{m}_{\in H\cap M} \in (N\cap K)(H\cap M)$. ✓

Concluimos $\ker\varphi = (N \cap K)(H \cap M)$.

**6e. Primer Teorema de Isomorfismo**:
$$(H\cap K)\big/\ker\varphi \cong \mathrm{Im}(\varphi) = N(H\cap K)\big/N(H\cap M),$$
$$\boxed{\frac{H \cap K}{(N \cap K)(H \cap M)} \;\cong\; \frac{N(H \cap K)}{N(H \cap M)}}.$$

---

##### Paso 7 — Simetría: $\tfrac{H \cap K}{(N \cap K)(H \cap M)} \cong \tfrac{M(H \cap K)}{M(N \cap K)}$

Intercambiamos $(N, H) \leftrightarrow (M, K)$ en todo el Paso 6. El rol de $N \unlhd H$ lo juega ahora $M \unlhd K$; el rol de $H \cap K$ pasa a ser $K \cap H = H \cap K$ (simétrico); el rol de $H \cap M$ pasa a ser $K \cap N = N \cap K$.

Definimos
$$\psi : H \cap K \;\longrightarrow\; \frac{M(H \cap K)}{M(N \cap K)}, \qquad \psi(k) := M(N \cap K) \cdot k.$$

**7a. Bien definida**: $k \in H \cap K \leq M(H \cap K)$ (con $m = e$). El cociente está definido porque $M(N\cap K) \unlhd M(H\cap K)$ (versión simétrica del Paso 5).

**7b. Homomorfismo**: idéntico al argumento 6b.

**7c. Sobreyectividad**: Un elemento $M(N\cap K) \cdot mk$ con $m \in M$ satisface $m \in M(N\cap K)$ (tomando $n = e$), luego $M(N\cap K) \cdot mk = M(N\cap K) \cdot k = \psi(k)$.

**7d. Núcleo**: $\ker\psi = M(N\cap K) \cap (H\cap K)$.

*$\supseteq$*: $k = ab$ con $a \in N\cap K$ y $b \in H\cap M \leq M$ implica $k \in M(N\cap K)$ y $k \in H\cap K$.

*$\subseteq$*: $k = mn$ con $m \in M$, $n \in N\cap K$, $k \in H\cap K$.

- $n \in N \leq H$ y $k \in H$, así que $m = kn^{-1} \in H$. Como $m \in M$: $m \in H\cap M$.
- Luego $k = \underbrace{n}_{\in N\cap K} \cdot \underbrace{m}_{\in H\cap M}$... pero el orden es $mn$:
    reescribimos usando 3a: como $m \in H\cap K$ (ya que $m \in H$ y $m \in M \leq K$) y $n \in N\cap K$, tenemos $mn = (mn^{-1}m^{-1})^{-1} \cdot \ldots$ — más directamente, por la igualdad $AB = BA$ del Paso 3a, $mn \in (N\cap K)(H\cap M)$. ✓

Concluimos $\ker\psi = (N\cap K)(H\cap M)$.

**7e. Primer Teorema de Isomorfismo**:
$$\boxed{\frac{H \cap K}{(N \cap K)(H \cap M)} \;\cong\; \frac{M(H \cap K)}{M(N \cap K)}}.$$

---

##### Conclusión

Encadenando los isomorfismos de los Pasos 6e y 7e:

$$\frac{N(H \cap K)}{N(H \cap M)} \;\cong\; \frac{H \cap K}{(N \cap K)(H \cap M)} \;\cong\; \frac{M(H \cap K)}{M(N \cap K)}. \quad \blacksquare$$

---

**Mapa lógico de dependencias**:

```
Paso 1 ─┐
         ├──► Paso 3 ──────────────────────────────► Paso 6d (ker = (N∩K)(H∩M))
Paso 2 ─┘                                                    │
                                                             ▼
Paso 4 (criterio NS ≤ H) ──► Paso 5 ──► cociente bien def. ──► PTI ──► Conclusión
                                                                         ▲
                                       Paso 7 (simetría) ───────────────┘
```

**Nota para la formalización en Lean**: los Pasos 1–3 (normalidades en $H \cap K$) y el
Paso 5 (normalidad $N(H\cap M) \unlhd N(H\cap K)$) son los lemas que requieren
más manipulación de igualdades de elementos. El Primer Teorema de Isomorfismo ya
está disponible como `FirstIsomorphism.lean`. El Paso 4 (criterio $NS \leq H$) es
un lema auxiliar reutilizable que conviene extraer como `prod_normal_sub`.
