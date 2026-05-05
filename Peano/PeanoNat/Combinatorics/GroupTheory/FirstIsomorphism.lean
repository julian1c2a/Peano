import Peano.PeanoNat.Combinatorics.GroupTheory.QuotientGroup

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

# Primer Teorema de Isomorfía

Dado un homomorfismo de grupos finitos `h : G → J` (con `G J : FinGroup ℕ₀`),
este módulo construye:

- `Subgroup.toFinGroup` — un subgrupo hereda estructura de grupo
- `homKer G J h` — el núcleo `Ker h ◁ G` (subgrupo normal de `G`)
- `homImg G J h` — la imagen `Im h ≤ J` (subgrupo de `J`)
- `homKer_isNormal` — `Ker h` es normal en `G`
- `quotientHomomorphism_surjective` — π : G → G/Ker h es sobreyectivo
- `homImgInclusion` — ι : Im h ↪ J es homomorfismo inyectivo
- `firstIsoMap` — φ : G/Ker h → Im h, `gKer ↦ h(g)`, homomorfismo biyectivo

Esto constituye el **Primer Teorema de Isomorfía**: `G/Ker h ≅ Im h`.

## Contenido

§ 0. Subgrupo inducido como grupo (`Subgroup.toFinGroup`)
§ 1. Núcleo (`homKer`, `mem_homKer_iff`)
§ 2. Imagen (`homImg`, `mem_homImg_iff`)
§ 3. El núcleo es normal (`homKer_isNormal`)
§ 4. π es sobreyectivo (`quotientHomomorphism_surjective`)
§ 5. Inclusión ι inyectiva (`homImgInclusion`, `homImgInclusion_injective`)
§ 6. Isomorfismo φ (`firstIsoMap`, `firstIsoMap_op`,
     `firstIsoMap_injective`, `firstIsoMap_surjective`, `firstIsoMap_bijective`)
-/

set_option autoImplicit false

namespace Peano
  namespace GroupTheory
    open Peano.FSet Peano.FSetFunction Peano.Group

    /-!
    ## § 0. Subgrupo inducido como grupo

    Un subgrupo `H ≤ G` hereda la operación, identidad e inverso de `G`,
    formando un `FinGroup α` con portador `H.carrier`.
    -/

    /-- Un subgrupo `H ≤ G` induce un `FinGroup α` cuya operación y estructura
        son las de `G` restringidas a `H`. -/
    def Subgroup.toFinGroup {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
        {G : FinGroup α} (H : Subgroup G) : FinGroup α where
      carrier  := H.carrier
      op       := { toFun      := fun a b => G.op a b
                    map_carrier := fun a b ha hb => H.op_closed a b ha hb }
      id       := G.id
      inv      := { toFun      := fun a => G.inv a
                    map_carrier := fun a ha => H.inv_closed a ha }
      id_in    := H.id_in
      op_assoc := fun a b c ha hb hc =>
        G.op_assoc a b c (H.subset a ha) (H.subset b hb) (H.subset c hc)
      op_id    := fun a ha => G.op_id a (H.subset a ha)
      op_inv   := fun a ha => G.op_inv a (H.subset a ha)

    /-!
    ## § 1. Núcleo de un homomorfismo
    -/

    /-- Lema de membresía en la imagen de un `MapOn`: aprovecha la definición de `MapOn.Im`. -/
    private theorem mem_Im_iff_aux {G J : FinGroup ℕ₀} (h : GroupHom G J) (y : ℕ₀) :
        y ∈ h.map.Im.elems ↔ ∃ g, g ∈ G.carrier.elems ∧ h.map g = y := by
      simp only [MapOn.Im, FSet.filter]
      rw [List.mem_filter, List.any_eq_true]
      constructor
      · rintro ⟨_, a, ha, hd⟩
        simp only [decide_eq_true_eq] at hd
        exact ⟨a, ha, hd⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨h.map.map_carrier a ha, a, ha, by simp⟩

    /-- El **núcleo** `Ker h = { g ∈ G | h(g) = e_J }` es un subgrupo de `G`. -/
    def homKer (G J : FinGroup ℕ₀) (h : GroupHom G J) : Subgroup G where
      carrier  := FSet.filter (fun g => decide (h.map g = J.id)) G.carrier
      nonempty := ⟨G.id, by
        simp only [FSet.filter]
        apply List.mem_filter.mpr
        exact ⟨G.id_in, by simp [h.map_id]⟩⟩
      subset   := fun g hg => by
        simp only [FSet.filter] at hg
        exact (List.mem_filter.mp hg).1
      op_closed := fun a b ha hb => by
        simp only [FSet.filter] at ha hb ⊢
        have ⟨ha_G, ha_dec⟩ := List.mem_filter.mp ha
        have ⟨hb_G, hb_dec⟩ := List.mem_filter.mp hb
        simp only [decide_eq_true_eq] at ha_dec hb_dec
        apply List.mem_filter.mpr
        refine ⟨op_mem G ha_G hb_G, ?_⟩
        simp only [decide_eq_true_eq]
        rw [h.map_op a b ha_G hb_G, ha_dec, hb_dec]
        exact (J.op_id J.id J.id_in).1
      id_in    := by
        simp only [FSet.filter]
        apply List.mem_filter.mpr
        exact ⟨G.id_in, by simp [h.map_id]⟩
      inv_closed := fun a ha => by
        simp only [FSet.filter] at ha ⊢
        have ⟨ha_G, ha_dec⟩ := List.mem_filter.mp ha
        simp only [decide_eq_true_eq] at ha_dec
        apply List.mem_filter.mpr
        refine ⟨inv_mem G ha_G, ?_⟩
        simp only [decide_eq_true_eq]
        rw [h.map_inv a ha_G, ha_dec]
        exact inv_id_eq J

    /-- Caracterización de la membresía en el núcleo:
        `g ∈ Ker h ↔ g ∈ G ∧ h(g) = e_J`. -/
    theorem mem_homKer_iff (G J : FinGroup ℕ₀) (h : GroupHom G J) (g : ℕ₀) :
        g ∈ (homKer G J h).carrier.elems ↔ g ∈ G.carrier.elems ∧ h.map g = J.id := by
      simp only [homKer, FSet.filter]
      rw [List.mem_filter, decide_eq_true_eq]

    /-!
    ## § 2. Imagen de un homomorfismo
    -/

    /-- La **imagen** `Im h = { h(g) | g ∈ G }` es un subgrupo de `J`. -/
    def homImg (G J : FinGroup ℕ₀) (h : GroupHom G J) : Subgroup J where
      carrier  := h.map.Im
      nonempty := ⟨J.id, by
        rw [mem_Im_iff_aux]
        exact ⟨G.id, G.id_in, h.map_id⟩⟩
      subset   := fun y hy => by
        simp only [MapOn.Im, FSet.filter] at hy
        exact (List.mem_filter.mp hy).1
      op_closed := fun y₁ y₂ hy₁ hy₂ => by
        rw [mem_Im_iff_aux] at hy₁ hy₂ ⊢
        obtain ⟨g₁, hg₁, rfl⟩ := hy₁
        obtain ⟨g₂, hg₂, rfl⟩ := hy₂
        exact ⟨G.op g₁ g₂, op_mem G hg₁ hg₂, h.map_op g₁ g₂ hg₁ hg₂⟩
      id_in    := by
        rw [mem_Im_iff_aux]
        exact ⟨G.id, G.id_in, h.map_id⟩
      inv_closed := fun y hy => by
        rw [mem_Im_iff_aux] at hy ⊢
        obtain ⟨g, hg, rfl⟩ := hy
        exact ⟨G.inv g, inv_mem G hg, h.map_inv g hg⟩

    /-- Caracterización de la membresía en la imagen:
        `y ∈ Im h ↔ ∃ g ∈ G, h(g) = y`. -/
    theorem mem_homImg_iff (G J : FinGroup ℕ₀) (h : GroupHom G J) (y : ℕ₀) :
        y ∈ (homImg G J h).carrier.elems ↔ ∃ g, g ∈ G.carrier.elems ∧ h.map g = y :=
      mem_Im_iff_aux h y

    /-!
    ## § 3. El núcleo es normal
    -/

    /-- El núcleo `Ker h` es subgrupo **normal** de `G`:
        si `g ∈ G` y `n ∈ Ker h`, entonces `g n g⁻¹ ∈ Ker h`.

        Prueba: `h(g n g⁻¹) = h(g) h(n) h(g)⁻¹ = h(g) e h(g)⁻¹ = e`. -/
    theorem homKer_isNormal (G J : FinGroup ℕ₀) (h : GroupHom G J) :
        (homKer G J h).IsNormal := by
      intro g n hg hn
      rw [mem_homKer_iff] at hn
      rw [mem_homKer_iff]
      obtain ⟨hn_G, hn_id⟩ := hn
      refine ⟨op_mem G (op_mem G hg hn_G) (inv_mem G hg), ?_⟩
      -- h(g·n·g⁻¹) = (h(g)·h(n))·h(g)⁻¹ = (h(g)·e)·h(g)⁻¹ = h(g)·h(g)⁻¹ = e
      rw [h.map_op (G.op g n) (G.inv g) (op_mem G hg hn_G) (inv_mem G hg),
          h.map_op g n hg hn_G, h.map_inv g hg, hn_id,
          (J.op_id (h.map g) (h.map.map_carrier g hg)).1,
          (J.op_inv (h.map g) (h.map.map_carrier g hg)).1]

    /-!
    ## § 4. π : G → G/Ker h es sobreyectivo

    El homomorfismo canónico `π = quotientHomomorphism G H` es sobreyectivo
    para **cualquier** subgrupo `H` (sin necesitar normalidad).
    Todo coseto `C` tiene preimagen su representante `cosetRepOf G H C`.
    -/

    /-- La proyección canónica `π : G → G/H` es **sobreyectiva**:
        todo coseto `C ∈ G/H` es de la forma `π(g)` para algún `g ∈ G`. -/
    theorem quotientHomomorphism_surjective (G : FinGroup ℕ₀) (H : Subgroup G) :
        (quotientHomomorphism G H).Surjective := by
      intro C hC
      exact ⟨cosetRepOf G H C, cosetRepOf_mem_G G H C hC,
        by simp only [quotientHomomorphism]; exact cosetRepOf_leftCoset_eq G H C hC⟩

    /-!
    ## § 5. ι : Im h ↪ J es homomorfismo inyectivo

    La inclusión de `Im h` en `J` es un homomorfismo de grupos
    (la operación en `(homImg G J h).toFinGroup` es la de `J` restringida).
    Es trivialmente inyectiva.
    -/

    /-- La **inclusión** `ι : Im h → J` como homomorfismo de grupos. -/
    def homImgInclusion (G J : FinGroup ℕ₀) (h : GroupHom G J) :
        GroupHom (Subgroup.toFinGroup (homImg G J h)) J where
      map     := { toFun      := fun y => y
                   map_carrier := fun y hy => (homImg G J h).subset y hy }
      map_op  := fun _ _ _ _ => rfl
      map_id  := rfl
      map_inv := fun _ _ => rfl

    /-- La inclusión `ι` es **inyectiva**. -/
    theorem homImgInclusion_injective (G J : FinGroup ℕ₀) (h : GroupHom G J) :
        (homImgInclusion G J h).map.Injective :=
      fun _ _ _ _ heq => heq

    /-!
    ## § 6. φ : G/Ker h → Im h es isomorfismo

    Definimos `φ(C) = h(rep(C))` donde `rep(C) = cosetRepOf G (Ker h) C`.
    Probaremos que φ:
    - Es bien definida: `φ(gKer) = h(g)` para todo `g ∈ G`
    - Preserva la operación (homomorfismo)
    - Es inyectiva
    - Es sobreyectiva
    - Es biyectiva (= isomorfismo de grupos)
    -/

    /-- El **isomorfismo** φ : G/Ker h → Im h, dado por `φ(C) = h(cosetRepOf C)`. -/
    noncomputable def firstIsoMap (G J : FinGroup ℕ₀) (h : GroupHom G J) :
        MapOn (quotientCarrier G (homKer G J h)) (homImg G J h).carrier where
      toFun   := fun C => h.map (cosetRepOf G (homKer G J h) C)
      map_carrier := fun C hC => by
        rw [mem_homImg_iff]
        exact ⟨cosetRepOf G (homKer G J h) C,
               cosetRepOf_mem_G G (homKer G J h) C hC, rfl⟩

    /-- **Bien-definición** de φ: para todo `g ∈ G`,
        `φ(leftCoset G K g) = h(g)` (independiente del representante). -/
    theorem firstIsoMap_welldefined (G J : FinGroup ℕ₀) (h : GroupHom G J)
        (g : ℕ₀) (hg : g ∈ G.carrier.elems) :
        (firstIsoMap G J h).toFun (leftCoset G (homKer G J h) g) = h.map g := by
      simp only [firstIsoMap]
      -- r = cosetRepOf G K (leftCoset G K g)
      let K  := homKer G J h
      let r  := cosetRepOf G K (leftCoset G K g)
      have hr_in : leftCoset G K g ∈ (quotientCarrier G K).elems :=
        leftCoset_mem_quotientCarrier G K g hg
      have hr_G : r ∈ G.carrier.elems := cosetRepOf_mem_G G K (leftCoset G K g) hr_in
      -- leftCoset K r = leftCoset K g  →  cosetRel G K r g
      have hrel : cosetRel G K r g :=
        cosetRel_of_leftCoset_eq G K r g hr_G hg
          (cosetRepOf_leftCoset_eq G K (leftCoset G K g) hr_in)
      -- cosetRel G K r g = G.inv r * g ∈ K.carrier.elems
      -- Por mem_homKer_iff: h(G.inv r * g) = J.id
      have hrel_id := ((mem_homKer_iff G J h (G.op (G.inv r) g)).mp hrel).2
      -- h(G.inv r * g) = J.inv(h(r)) * h(g) = J.id  →  h(r) = h(g)
      rw [h.map_op (G.inv r) g (inv_mem G hr_G) hg,
          h.map_inv r hr_G] at hrel_id
      -- hrel_id : J.op (J.inv (h.map r)) (h.map g) = J.id
      -- Multiplicando por h(r) a la izquierda: h(r) = h(g)
      have key : h.map r = h.map g := by
        have hr_img := h.map.map_carrier r hr_G
        have hg_img := h.map.map_carrier g hg
        have e : J.op (h.map r) (J.op (J.inv (h.map r)) (h.map g)) = h.map g := by
          rw [← J.op_assoc (h.map r) (J.inv (h.map r)) (h.map g)
                hr_img (inv_mem J hr_img) hg_img,
              (J.op_inv (h.map r) hr_img).1,
              (J.op_id (h.map g) hg_img).2]
        rw [hrel_id, (J.op_id (h.map r) hr_img).1] at e
        exact e
      exact key

    /-- φ **preserva la operación**:
        `φ(C₁ ·_{G/K} C₂) = φ(C₁) ·_J φ(C₂)`. -/
    theorem firstIsoMap_op (G J : FinGroup ℕ₀) (h : GroupHom G J)
        (C₁ C₂ : ℕ₀FSet)
        (hC₁ : C₁ ∈ (quotientCarrier G (homKer G J h)).elems)
        (hC₂ : C₂ ∈ (quotientCarrier G (homKer G J h)).elems) :
        (firstIsoMap G J h).toFun
          ((quotientOp G (homKer G J h) (homKer_isNormal G J h)).toFun C₁ C₂) =
          J.op ((firstIsoMap G J h).toFun C₁) ((firstIsoMap G J h).toFun C₂) := by
      have hr₁_G := cosetRepOf_mem_G G (homKer G J h) C₁ hC₁
      have hr₂_G := cosetRepOf_mem_G G (homKer G J h) C₂ hC₂
      -- quotientOp C₁ C₂ =_def leftCoset K (r₁·r₂), luego:
      -- φ(leftCoset K (r₁·r₂)) = h(r₁·r₂) = h(r₁)·h(r₂) = φ(C₁)·φ(C₂)
      calc (firstIsoMap G J h).toFun
              ((quotientOp G (homKer G J h) (homKer_isNormal G J h)).toFun C₁ C₂)
          = (firstIsoMap G J h).toFun
              (leftCoset G (homKer G J h)
                (G.op (cosetRepOf G (homKer G J h) C₁)
                      (cosetRepOf G (homKer G J h) C₂))) := rfl
        _ = h.map (G.op (cosetRepOf G (homKer G J h) C₁)
                        (cosetRepOf G (homKer G J h) C₂)) :=
              firstIsoMap_welldefined G J h _ (op_mem G hr₁_G hr₂_G)
        _ = J.op (h.map (cosetRepOf G (homKer G J h) C₁))
                 (h.map (cosetRepOf G (homKer G J h) C₂)) :=
              h.map_op _ _ hr₁_G hr₂_G
        _ = J.op ((firstIsoMap G J h).toFun C₁)
                 ((firstIsoMap G J h).toFun C₂) := rfl

    /-- φ es **inyectiva**:
        `φ(C₁) = φ(C₂)` implica `C₁ = C₂`. -/
    theorem firstIsoMap_injective (G J : FinGroup ℕ₀) (h : GroupHom G J) :
        (firstIsoMap G J h).Injective := by
      intro C₁ C₂ hC₁ hC₂ hφ
      -- hφ : h.map (cosetRepOf K C₁) = h.map (cosetRepOf K C₂)
      -- C₁ = leftCoset K r₁  y  C₂ = leftCoset K r₂  (por cosetRepOf_leftCoset_eq)
      rw [← cosetRepOf_leftCoset_eq G (homKer G J h) C₁ hC₁,
          ← cosetRepOf_leftCoset_eq G (homKer G J h) C₂ hC₂]
      have hr₁_G := cosetRepOf_mem_G G (homKer G J h) C₁ hC₁
      have hr₂_G := cosetRepOf_mem_G G (homKer G J h) C₂ hC₂
      -- Basta mostrar cosetRel G K r₁ r₂, es decir G.inv r₁ * r₂ ∈ K
      apply (leftCoset_eq_iff_cosetRel G (homKer G J h) _ _ hr₁_G hr₂_G).mpr
      unfold cosetRel
      rw [mem_homKer_iff]
      refine ⟨op_mem G (inv_mem G hr₁_G) hr₂_G, ?_⟩
      -- Convertir hφ a la forma explícita h.map r₁ = h.map r₂
      have hφ' : h.map (cosetRepOf G (homKer G J h) C₁) =
                 h.map (cosetRepOf G (homKer G J h) C₂) := hφ
      -- h(G.inv r₁ · r₂) = J.inv(h(r₁)) · h(r₂) = J.inv(h(r₂)) · h(r₂) = J.id
      rw [h.map_op (G.inv (cosetRepOf G (homKer G J h) C₁))
                   (cosetRepOf G (homKer G J h) C₂)
                   (inv_mem G hr₁_G) hr₂_G,
          h.map_inv (cosetRepOf G (homKer G J h) C₁) hr₁_G,
          hφ']
      exact (J.op_inv (h.map (cosetRepOf G (homKer G J h) C₂))
              (h.map.map_carrier _ hr₂_G)).2

    /-- φ es **sobreyectiva**:
        todo `y ∈ Im h` tiene preimagen en `G/Ker h`. -/
    theorem firstIsoMap_surjective (G J : FinGroup ℕ₀) (h : GroupHom G J) :
        (firstIsoMap G J h).Surjective := by
      let K := homKer G J h
      intro y hy
      rw [mem_homImg_iff] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      -- El coseto leftCoset K g mapea a h(g)
      exact ⟨leftCoset G K g,
             leftCoset_mem_quotientCarrier G K g hg,
             firstIsoMap_welldefined G J h g hg⟩

    /-- **Primer Teorema de Isomorfía**: φ : G/Ker h → Im h es **biyectivo**.
        Por tanto, `G / Ker h ≅ Im h` como grupos. -/
    theorem firstIsoMap_bijective (G J : FinGroup ℕ₀) (h : GroupHom G J) :
        (firstIsoMap G J h).Bijective :=
      ⟨firstIsoMap_injective G J h, firstIsoMap_surjective G J h⟩

  end GroupTheory
end Peano

export Peano.GroupTheory (
  -- § 0. Subgrupo como grupo
  Subgroup.toFinGroup
  -- § 1. Núcleo
  homKer
  mem_homKer_iff
  -- § 2. Imagen
  homImg
  mem_homImg_iff
  -- § 3. Normalidad del núcleo
  homKer_isNormal
  -- § 4. π sobreyectivo
  quotientHomomorphism_surjective
  -- § 5. ι inyectivo
  homImgInclusion
  homImgInclusion_injective
  -- § 6. Isomorfismo φ
  firstIsoMap
  firstIsoMap_welldefined
  firstIsoMap_op
  firstIsoMap_injective
  firstIsoMap_surjective
  firstIsoMap_bijective
)
