/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/Group.lean

import Peano.PeanoNat
import Peano.PeanoNat.FSet

set_option autoImplicit false

/-!
  Cosas a implementar:
  1] Habría que definir un functor en FSet y una función de FSet en FSet nos devuelva la imagen
     como un FSet (probablemente habría que abrir un nuevo archivo FSetFunctions.lean o algo así).
     def Im (f : MapOn A B) : ℕ₀FSet := ℕ₀FSet.ofList (f.toFun <$> A.elems)
  2] Entonces habría que llevar todo lo relacionado con MapOn a este nuevo archivo FSetFunctions.lean
  3] Deberíamos generalizar MapOn a funciones entre conjuntos finitos arbitrarios, no solo de ℕ₀ a ℕ₀. Esto implicaría cambiar la definición de MapOn para que sea algo como:
     structure MapOn (A B : ℕ₀FSet) where
       toFun : A.elems → B.elems
       map_underset : ∀ a, a ∈ A.elems → toFun a ∈ B.elems
     Esto haría que la composición y las propiedades de inyectividad/sobreyectividad sean más naturales.
  4] Más aún, deberíamos poder generalizar MapOn no solo a dos conjuntos finitos sino a una familia finita de ellos.
     finita de ellos. Esto implicaría definir algo como:
     structure MapOn (A : ℕ₀FSet) (B : ℕ₀FSet) where
       toFun : A.elems → B.elems
       map_underset : ∀ a, a ∈ A.elems → toFun a ∈ B.elems
     Esto haría que la composición y las propiedades de inyectividad/sobreyectividad sean más naturales.
  5]
-/

namespace Peano
  namespace Group
    open Peano.FSet

    /-!
    # § 1. Funciones y operaciones sobre conjuntos finitos
    -/

    /--
    Representa una función `f` entre dos conjuntos finitos `A` y `B`.
    En Lean, esto no es un tipo de función `A → B` sino una función del tipo universal `ℕ₀ → ℕ₀`
    junto con una prueba de que mapea los elementos de `A` en `B`.
    -/
    structure MapOn (A B : ℕ₀FSet) where
      toFun : ℕ₀ → ℕ₀
      map_underset : ∀ a, a ∈ A.elems → toFun a ∈ B.elems

    /-- Composición de dos `MapOn`. Si `f : MapOn A B` y `g : MapOn B C`,
        entonces `g.comp f` es un `MapOn A C`. -/
    def MapOn.comp {A B C : ℕ₀FSet} (g : MapOn B C) (f : MapOn A B) : MapOn A C where
      toFun := g.toFun ∘ f.toFun
      map_underset := fun a ha => g.map_underset (f.toFun a) (f.map_underset a ha)

    /-- Una función `f` es inyectiva sobre un conjunto `A`. -/
    def InjectiveOn (f : ℕ₀ → ℕ₀) (A : ℕ₀FSet) : Prop :=
      ∀ a b, a ∈ A.elems → b ∈ A.elems → f a = f b → a = b

    /-- Una función `f` es sobreyectiva de `A` a `B`. -/
    def SurjectiveOn (f : ℕ₀ → ℕ₀) (A B : ℕ₀FSet) : Prop :=
      ∀ b, b ∈ B.elems → ∃ a, a ∈ A.elems ∧ f a = b

    /-- Un `MapOn` es inyectivo si su `toFun` subyacente es inyectivo sobre el dominio. -/
    def MapOn.Injective {A B : ℕ₀FSet} (f : MapOn A B) : Prop :=
      InjectiveOn f.toFun A

    /-- Un `MapOn` es sobreyectivo si su `toFun` subyacente es sobreyectivo del dominio al codominio. -/
    def MapOn.Surjective {A B : ℕ₀FSet} (f : MapOn A B) : Prop :=
      SurjectiveOn f.toFun A B

    /-- Un `MapOn` es biyectivo si es inyectivo y sobreyectivo. -/
    structure MapOn.Bijective {A B : ℕ₀FSet} (f : MapOn A B) : Prop where
      inj : f.Injective
      surj : f.Surjective

    /-- La composición de dos `MapOn` inyectivos es inyectiva. -/
    theorem MapOn.comp_injective {A B C : ℕ₀FSet} {f : MapOn A B} {g : MapOn B C}
        (hf_inj : f.Injective) (hg_inj : g.Injective) : (g.comp f).Injective := by
      unfold MapOn.Injective InjectiveOn MapOn.comp
      intro a₁ a₂ ha₁ ha₂ h_comp_eq
      -- Por la inyectividad de g, g(f(a₁)) = g(f(a₂)) → f(a₁) = f(a₂)
      have h_fa₁_in_B : f.toFun a₁ ∈ B.elems := f.map_underset a₁ ha₁
      have h_fa₂_in_B : f.toFun a₂ ∈ B.elems := f.map_underset a₂ ha₂
      let h_f_eq := hg_inj (f.toFun a₁) (f.toFun a₂) h_fa₁_in_B h_fa₂_in_B h_comp_eq
      -- Por la inyectividad de f, f(a₁) = f(a₂) → a₁ = a₂
      exact hf_inj a₁ a₂ ha₁ ha₂ h_f_eq

    /-- La composición de dos `MapOn` sobreyectivos es sobreyectiva. -/
    theorem MapOn.comp_surjective {A B C : ℕ₀FSet} {f : MapOn A B} {g : MapOn B C}
        (hf_surj : f.Surjective) (hg_surj : g.Surjective) : (g.comp f).Surjective := by
      unfold MapOn.Surjective SurjectiveOn MapOn.comp
      intro c hc
      -- Por la sobreyectividad de g, para c ∈ C existe un b ∈ B tal que g(b) = c
      let ⟨b, hb_in_B, hg_b_eq_c⟩ := hg_surj c hc
      -- Por la sobreyectividad de f, para ese b ∈ B existe un a ∈ A tal que f(a) = b
      let ⟨a, ha_in_A, hf_a_eq_b⟩ := hf_surj b hb_in_B
      -- Por tanto, existe un a ∈ A tal que g(f(a)) = c
      exists a
      constructor
      · exact ha_in_A
      · dsimp
        rw [hf_a_eq_b]; exact hg_b_eq_c

    /-- La composición de dos `MapOn` biyectivos es biyectiva. -/
    theorem MapOn.comp_bijective {A B C : ℕ₀FSet} {f : MapOn A B} {g : MapOn B C}
        (hf_bij : f.Bijective) (hg_bij : g.Bijective) : (g.comp f).Bijective := by
      constructor
      · exact MapOn.comp_injective hf_bij.inj hg_bij.inj
      · exact MapOn.comp_surjective hf_bij.surj hg_bij.surj

    /-!
    # § 2. Principio del Palomar
    -/

    /-- Lema 1 (Palomar): una función inyectiva sobre un conjunto finito mapea
        el conjunto a una imagen de la misma cardinalidad. -/
    theorem card_image_of_injective {A B : ℕ₀FSet}
      (f : MapOn A B) (h_inj : f.Injective) :
        (ℕ₀FSet.ofList (f.toFun <$> A.elems)).card = A.card
          := sorry

    /-- Lema 2 (Palomar): si la imagen de una función sobre un conjunto finito
        tiene la misma cardinalidad que el dominio, la función es inyectiva. -/
    theorem injective_of_card_image {A B : ℕ₀FSet} (f : MapOn A B)
        (h_card : (ℕ₀FSet.ofList (f.toFun <$> A.elems)).card = A.card) : f.Injective := sorry

    /-- Lema 3 (Palomar): si una función es sobreyectiva, la cardinalidad de su
        imagen es igual a la cardinalidad del codominio. -/
    theorem card_image_of_surjective {A B : ℕ₀FSet} (f : MapOn A B) (h_surj : f.Surjective) :
        (ℕ₀FSet.ofList (f.toFun <$> A.elems)).card = B.card := sorry

    /-- Lema 4 (Palomar): si la imagen de una función (que mapea A en B) tiene la
        misma cardinalidad que el codominio B, la función es sobreyectiva. -/
    theorem surjective_of_card_image {A B : ℕ₀FSet} (f : MapOn A B)
        (h_card : (ℕ₀FSet.ofList (f.toFun <$> A.elems)).card = B.card) : f.Surjective := sorry

    /--
    Principio del palomar para funciones: para dos conjuntos finitos del mismo tamaño,
    una función entre ellos es inyectiva si y solo si es sobreyectiva.
    NOTA: La prueba formal de este teorema requiere una librería de conjuntos finitos
    más desarrollada (`FSet.lean`) con lemas sobre la cardinalidad de la imagen de una función.
    Aquí se presenta la estructura de la prueba, dejando los lemas de bajo nivel como `sorry`.
    -/
    theorem MapOn.injective_iff_surjective_of_card_eq {A B : ℕ₀FSet} (h_card_eq : A.card = B.card) (f : MapOn A B) :
        f.Injective ↔ f.Surjective := by
      -- La prueba se basa en que para una f: A → B con |A|=|B|:
      -- 1. f es inyectiva ↔ |Im(f)| = |A|
      have h_card_img_iff_inj : (ℕ₀FSet.ofList (f.toFun <$> A.elems)).card = A.card ↔ f.Injective :=
        Iff.intro (injective_of_card_image f) (card_image_of_injective f)
      -- 2. f es sobreyectiva ↔ Im(f) = B ↔ |Im(f)| = |B|
      have h_surj_iff_card_img : f.Surjective ↔ (ℕ₀FSet.ofList (f.toFun <$> A.elems)).card = B.card :=
        Iff.intro (card_image_of_surjective f) (surjective_of_card_image f)
      -- Como |A| = |B| por hipótesis, las dos condiciones de cardinalidad son equivalentes.
      rw [h_card_img_iff_inj, h_surj_iff_card_img, h_card_eq]

    /-- Corolario del principio del palomar: para conjuntos finitos del mismo tamaño, una función inyectiva es biyectiva. -/
    theorem MapOn.injective_iff_bijective_of_card_eq {A B : ℕ₀FSet} (h_card_eq : A.card = B.card) (f : MapOn A B) :
        f.Injective ↔ f.Bijective := by
      constructor
      · intro h_inj
        -- Si es inyectiva, por el palomar también es sobreyectiva.
        have h_surj := (injective_iff_surjective_of_card_eq h_card_eq f).mp h_inj
        -- Inyectiva y sobreyectiva es biyectiva por definición.
        exact { inj := h_inj, surj := h_surj }
      · intro h_bij
        -- Si es biyectiva, es inyectiva por definición.
        exact h_bij.inj

    /-- Corolario del principio del palomar: para conjuntos finitos del mismo tamaño, una función sobreyectiva es biyectiva. -/
    theorem MapOn.surjective_iff_bijective_of_card_eq {A B : ℕ₀FSet} (h_card_eq : A.card = B.card) (f : MapOn A B) :
        f.Surjective ↔ f.Bijective := by
      constructor
      · intro h_surj
        -- Si es sobreyectiva, por el palomar también es inyectiva.
        have h_inj := (injective_iff_surjective_of_card_eq h_card_eq f).mpr h_surj
        -- Inyectiva y sobreyectiva es biyectiva por definición.
        exact { inj := h_inj, surj := h_surj }
      · intro h_bij
        -- Si es biyectiva, es sobreyectiva por definición.
        exact h_bij.surj

    /--
    Representa una operación binaria `f: A × A → A` sobre un conjunto finito.
    Es una función universal `ℕ₀ → ℕ₀ → ℕ₀` con una prueba de que es cerrada sobre `A`.
    -/
    structure BinOpOn (A : ℕ₀FSet) where
      toFun : ℕ₀ → ℕ₀ → ℕ₀
      map_underset : ∀ a b, a ∈ A.elems → b ∈ A.elems → toFun a b ∈ A.elems

    /-!
    # § 3. Coerción a funciones
    -/

    -- Hacemos que MapOn y BinOpOn se puedan llamar como funciones
    instance {A B : ℕ₀FSet} : CoeFun (MapOn A B) (fun _ => ℕ₀ → ℕ₀) where
      coe f := f.toFun

    instance {A : ℕ₀FSet} : CoeFun (BinOpOn A) (fun _ => ℕ₀ → ℕ₀ → ℕ₀) where
      coe f := f.toFun

    /-!
    # § 4. Estructura de Grupo Finito
    -/

    structure FinGroup where
      underset : ℕ₀FSet
      op : BinOpOn underset
      id : ℕ₀
      inv : MapOn underset underset
      id_in :
        id ∈ underset.elems
      op_assoc :
        ∀ a b c,
          a ∈ underset.elems → b ∈ underset.elems → c ∈ underset.elems →
            op (op a b) c = op a (op b c)
      op_id :
        ∀ a,
          a ∈ underset.elems → op a id = a ∧ op id a = a
      op_inv :
        ∀ a,
          a ∈ underset.elems → op a (inv a) = id ∧ op (inv a) a = id

    /--
    En cualquier `FinGroup`, el elemento neutro es único.
    -/
    theorem id_unique (G : FinGroup) (e' : ℕ₀)
        (h_e'_in : e' ∈ G.underset.elems)
        (h_is_id : ∀ a, a ∈ G.underset.elems → G.op a e' = a ∧ G.op e' a = a) :
        e' = G.id := by
      -- La prueba se basa en que G.id = G.op G.id e' (por la propiedad de e') y e' = G.op G.id e' (por la propiedad de G.id).
      -- Por tanto, e' = G.id.
      let h_id_op_e' := (h_is_id G.id G.id_in).left
      let h_e'_op_id := (G.op_id e' h_e'_in).right
      exact h_e'_op_id.symm.trans h_id_op_e'

    /-!
    # § 5. Subgrupos
    !-/

    /--
    Un subgrupo de un grupo finito G es un subconjunto no vacío cerrado por la operación y la inversa, con la misma operación.
    -/
    structure Subgroup (G : FinGroup) where
      underset : ℕ₀FSet
      nonempty : ∃ a, a ∈ underset.elems
      subset : ∀ a, a ∈ underset.elems → a ∈ G.underset.elems
      op_closed : ∀ a b, a ∈ underset.elems → b ∈ underset.elems → G.op a b ∈ underset.elems
      id_in : G.id ∈ underset.elems
      inv_closed : ∀ a, a ∈ underset.elems → G.inv a ∈ underset.elems

    /-!
    # § 6. Homomorfismos
    !-/

    /--
    Un morfismo de grupos finitos es una función que respeta la operación, el neutro y la inversa.
    -/
    structure GroupHom (G H : FinGroup) where
      map : MapOn G.underset H.underset
      map_op : ∀ a b, a ∈ G.underset.elems → b ∈ G.underset.elems →
        map (G.op a b) = H.op (map a) (map b)
      map_id : map G.id = H.id
      map_inv : ∀ a, a ∈ G.underset.elems → map (G.inv a) = H.inv (map a)

    /-!
    # § 7. Grupo Simétrico (Permutaciones)
    -/

    -- Definición de Permutación: función biyectiva de A en A
    structure Perm (A : ℕ₀FSet) where
      map : MapOn A A
      bijective : map.Bijective



    /--
    El grupo simétrico sobre A: conjunto de todas las permutaciones de A, con composición.
    -/
    def Sym (A : ℕ₀FSet) : FinGroup where
      underset := sorry  -- El conjunto de todas las permutaciones de A, codificadas como ℕ₀
      op := {
        toFun := fun p₁ p₂ => sorry,
        map_underset := sorry
      }
      id := sorry      -- La permutación identidad
      inv := {
        toFun := fun p => sorry,
        map_underset := sorry
      }
      id_in := sorry
      op_assoc := sorry
      op_id := sorry
      op_inv := sorry

  end Group
end Peano
