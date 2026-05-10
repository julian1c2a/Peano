# Referencia Técnica — Teoría de Grupos Finitos (`Peano.GroupTheory`)

**Última actualización:** 2026-05-10  
**Autor:** Julián Calderón Almendros  
**Retorno:** [REFERENCE.md](../REFERENCE.md)

> Documentación de los símbolos públicos del módulo
> `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`.
> Solo contiene lo completamente probado (requisito 8 del AI-GUIDE).
> El placeholder `zassenhaus_bijection` **no se proyecta** por ser `True := trivial`.

---

## Módulo: `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`

- **Namespace:** `Peano.GroupTheory`
- **Import:** `Peano.PeanoNat.Combinatorics.GroupTheory.SecondIsomorphism`
- **Opens:** `Peano.FSet`, `Peano.FSetFunction`, `Peano.Group`, `Peano.Mul`
- **Tema:** Lema de la Mariposa de Zassenhaus (lemas preparatorios y normalidad)

---

## §1. Subgrupo producto `N · S`

### `prodSubgroup`

- **Tipo:** `def` (computable)
- **Notación matemática:** $N \cdot S = \{n \cdot s \mid n \in N,\; s \in S\}$ como subgrupo de $G$,  
  válido cuando $N, S \leq H \leq G$ y $N \trianglelefteq H$.
- **Firma Lean 4:**

  ```lean
  def prodSubgroup
      (G : FinGroup ℕ₀) (N S H : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
      Subgroup G
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

### `mem_prodSubgroup_iff`

- **Tipo:** `theorem`
- **Notación matemática:** $x \in N \cdot S \iff x \in G \;\land\; \exists n \in N,\; \exists s \in S,\; n \cdot s = x$
- **Firma Lean 4:**

  ```lean
  theorem mem_prodSubgroup_iff
      (G : FinGroup ℕ₀) (N S H : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (x : ℕ₀) :
      x ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems ↔
      x ∈ G.carrier.elems ∧
      ∃ n ∈ N.carrier.elems, ∃ s ∈ S.carrier.elems, G.op n s = x
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`

---

### `N_le_prodSubgroup`

- **Tipo:** `theorem`
- **Notación matemática:** $N \leq N \cdot S$ (inclusión del primer factor).  
  $n \in N \Rightarrow n \in N \cdot S$.
- **Firma Lean 4:**

  ```lean
  theorem N_le_prodSubgroup
      (G : FinGroup ℕ₀) (N S H : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (n : ℕ₀) (hn : n ∈ N.carrier.elems) :
      n ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`

---

### `S_le_prodSubgroup`

- **Tipo:** `theorem`
- **Notación matemática:** $S \leq N \cdot S$ (inclusión del segundo factor).  
  $s \in S \Rightarrow s \in N \cdot S$.
- **Firma Lean 4:**

  ```lean
  theorem S_le_prodSubgroup
      (G : FinGroup ℕ₀) (N S H : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (s : ℕ₀) (hs : s ∈ S.carrier.elems) :
      s ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`

---

## §2. $N \cap K \trianglelefteq H \cap K$

### `inter_N_K_normal_in_inter_H_K`

- **Tipo:** `theorem`
- **Notación matemática:** Si $N \trianglelefteq H$ y $K \leq G$, entonces $N \cap K \trianglelefteq H \cap K$.  
  Formalmente: $\forall g \in H \cap K,\; \forall x \in N \cap K,\quad g x g^{-1} \in N \cap K$.
- **Firma Lean 4:**

  ```lean
  theorem inter_N_K_normal_in_inter_H_K
      (G : FinGroup ℕ₀) (H K N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
      ∀ g x,
        g ∈ (H.inter K).carrier.elems →
        x ∈ (N.inter K).carrier.elems →
        G.op (G.op g x) (G.inv g) ∈ (N.inter K).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## §3. $H \cap M \trianglelefteq H \cap K$

### `inter_H_M_normal_in_inter_H_K`

- **Tipo:** `theorem`
- **Notación matemática:** Si $M \trianglelefteq K$ y $H \leq G$, entonces $H \cap M \trianglelefteq H \cap K$.  
  Formalmente: $\forall g \in H \cap K,\; \forall x \in H \cap M,\quad g x g^{-1} \in H \cap M$.
- **Firma Lean 4:**

  ```lean
  theorem inter_H_M_normal_in_inter_H_K
      (G : FinGroup ℕ₀) (H K M : Subgroup G)
      (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
             G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
      ∀ g x,
        g ∈ (H.inter K).carrier.elems →
        x ∈ (H.inter M).carrier.elems →
        G.op (G.op g x) (G.inv g) ∈ (H.inter M).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## §4. $(N \cap K)(H \cap M) \trianglelefteq H \cap K$

### `prodNKHM`

- **Tipo:** `def` (computable)
- **Notación matemática:** El subgrupo $(N \cap K)(H \cap M) \leq H \cap K$,  
  definido como `prodSubgroup G (N∩K) (H∩M) (H∩K) …`, dado $N \trianglelefteq H$ y $M \trianglelefteq K$.
- **Firma Lean 4:**

  ```lean
  def prodNKHM
      (G : FinGroup ℕ₀) (H K N M : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
             G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
      Subgroup G
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

### `prodNKHM_normal`

- **Tipo:** `theorem`
- **Notación matemática:** $(N \cap K)(H \cap M) \trianglelefteq H \cap K$.  
  $\forall g \in H \cap K,\; \forall x \in (N \cap K)(H \cap M),\quad g x g^{-1} \in (N \cap K)(H \cap M)$.
- **Firma Lean 4:**

  ```lean
  theorem prodNKHM_normal
      (G : FinGroup ℕ₀) (H K N M : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
             G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
      ∀ g x,
        g ∈ (H.inter K).carrier.elems →
        x ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems →
        G.op (G.op g x) (G.inv g) ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## §5. Subgrupos producto $N(H \cap K)$ y $N(H \cap M)$

### `prodN_HK`

- **Tipo:** `def` (computable)
- **Notación matemática:** $N(H \cap K)$ = subgrupo producto de $N$ con $H \cap K$,  
  dado $N \leq H$ y $N \trianglelefteq H$.
- **Firma Lean 4:**

  ```lean
  def prodN_HK
      (G : FinGroup ℕ₀) (H K N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
      Subgroup G
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

### `prodN_HM`

- **Tipo:** `def` (computable)
- **Notación matemática:** $N(H \cap M)$ = subgrupo producto de $N$ con $H \cap M$,  
  dado $N \leq H$, $M \leq H$ y $N \trianglelefteq H$.
- **Firma Lean 4:**

  ```lean
  def prodN_HM
      (G : FinGroup ℕ₀) (H M N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
      Subgroup G
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## §6. $N(H \cap M) \trianglelefteq N(H \cap K)$

### `prodN_HM_le_prodN_HK`

- **Tipo:** `theorem`
- **Notación matemática:** $N(H \cap M) \leq N(H \cap K)$, dado $M \leq K$.  
  $x \in N(H \cap M) \Rightarrow x \in N(H \cap K)$.
- **Firma Lean 4:**

  ```lean
  theorem prodN_HM_le_prodN_HK
      (G : FinGroup ℕ₀) (H K M N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (x : ℕ₀) :
      x ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems →
      x ∈ (prodN_HK G H K N hNH hNN).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`

---

### `prodN_HM_normal_in_prodN_HK`

- **Tipo:** `theorem`
- **Notación matemática:** $N(H \cap M) \trianglelefteq N(H \cap K)$,  
  dado $N \trianglelefteq H$ y $M \trianglelefteq K$.  
  $\forall g \in N(H \cap K),\; \forall y \in N(H \cap M),\quad g y g^{-1} \in N(H \cap M)$.
- **Estrategia de prueba:**
  Escribir $g = n_g k_g$ con $n_g \in N$, $k_g \in H \cap K$; y $y = n_y m_y$ con $n_y \in N$, $m_y \in H \cap M$.  
  Definir $m_y' = k_g m_y k_g^{-1} \in H \cap M$ (por $M \trianglelefteq K$, $k_g \in K$).  
  Definir $\alpha = m_y' n_g^{-1} m_y'^{-1} \in N$ (conjugado de $n_g^{-1}$ por $m_y' \in H$).  
  Entonces $n_{\mathrm{pair}} = n_g \cdot (k_g n_y k_g^{-1}) \cdot \alpha \in N$,  
  y la identidad $n_{\mathrm{pair}} \cdot m_y' = g y g^{-1}$ da la membresía en $N(H \cap M)$.
- **Firma Lean 4:**

  ```lean
  theorem prodN_HM_normal_in_prodN_HK
      (G : FinGroup ℕ₀) (H K M N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
             G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
      ∀ g y,
        g ∈ (prodN_HK G H K N hNH hNN).carrier.elems →
        y ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems →
        G.op (G.op g y) (G.inv g) ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## Resumen de símbolos del módulo

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `prodSubgroup` | `def` | ✅ | alta |
| `mem_prodSubgroup_iff` | `theorem` | — | media |
| `N_le_prodSubgroup` | `theorem` | — | media |
| `S_le_prodSubgroup` | `theorem` | — | media |
| `inter_N_K_normal_in_inter_H_K` | `theorem` | — | alta |
| `inter_H_M_normal_in_inter_H_K` | `theorem` | — | alta |
| `prodNKHM` | `def` | ✅ | alta |
| `prodNKHM_normal` | `theorem` | — | alta |
| `prodN_HK` | `def` | ✅ | alta |
| `prodN_HM` | `def` | ✅ | alta |
| `prodN_HM_le_prodN_HK` | `theorem` | — | media |
| `prodN_HM_normal_in_prodN_HK` | `theorem` | — | alta |

> **No proyectados** (privados): `mem_inter_iff`, `inter_subset_left_aux`, `inter_subset_right_aux`,  
> `NormalIn`, `HK`, `NK`, `HM`, `N_normal_in_prodN_HK`.  
> **No proyectado** (placeholder sin prueba): `zassenhaus_bijection` (`True := trivial`).
