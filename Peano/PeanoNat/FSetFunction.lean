/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT


  Cosas a implementar:
  Lee Las primeras 50 líneas de FSetFunction.lean. Hay que ir colocando las
  distintas definiciones entre Lists.lean, FSet.lean y el actual FSetFunction.
  lean. Quiero un plan completo y detallado para implementar todo esto en
  Lists_FSets_and_FSetFunctions.md:
  1] Habría que definir un functor en FSet y una función de FSet en FSet nos devuelva la imagen
     como un FSet (probablemente habría que abrir un nuevo archivo FSetFunctions.lean o algo así).
     def Im (f : MapOn A B) : ℕ₀FSet := ℕ₀FSet.ofList (f.toFun <$> A.elems)
  2] Entonces habría que llevar todo lo relacionado con MapOn a este nuevo archivo FSetFunctions.lean
  3] Deberíamos generalizar MapOn a funciones entre conjuntos finitos arbitrarios, no solo de ℕ₀ a ℕ₀. Esto implicaría cambiar la definición de MapOn para que sea algo como:
     structure MapOn (A B : ℕ₀FSet) where
       toFun : A.elems → B.elems
       map_carrier : ∀ a, a ∈ A.elems → toFun a ∈ B.elems
     Esto haría que la composición y las propiedades de inyectividad/sobreyectividad sean más naturales.
  4] Más aún, deberíamos poder generalizar MapOn no solo a dos conjuntos finitos sino a una familia finita de ellos.
     finita de ellos.
  5] lexLt y lexLe para Tuple n
      Serán ordenes lexicográficos sobre tuplas de naturales
  6] Ya podemos tener listas de tuplas de naturales tipo ℕ₀TupleList n, y con ellas
      podemos definit TupleFSet n := FSet ℕ₀Tuple n
      Esto nos permitiría trabajar con conjuntos finitos de tuplas de naturales de manera más cómoda
  7] FSetList: def FSetList := List ℕ₀FSet
     Esto nos permitiría trabajar con listas de conjuntos finitos de naturales de manera más cómoda, y podríamos definir funciones sobre ellas, como la función de imagen que mencioné en el punto 1.

  8] lexListFsetLt y lexListFsetLe para FSetList
     Serán órdenes lexicográficos sobre listas de conjuntos finitos de naturales
     8.1.] Primero por el cardinal, un conjunto es mas pequeño que otro si el cardinal es menor
     8.2.] Si tienen el mismo cardinal, entonces se comparan lexicográficamente entre sí
  9] FSetSet:
     structure FSetSet where
       elems : List ℕ₀FSet
       sorted : Sorted (λ A B => lexListFsetLt A B) elems
     Esto nos permitiría trabajar con conjuntos de conjuntos finitos de naturales, y podríamos definir funciones sobre ellos, como la función de imagen que mencioné en el punto 1 pero para conjuntos de conjuntos finitos.
   10] Nos hace falta un tipo tupla de conjuntos finitos de naturales, parametrizado por un natural
      inductive FSetTuple : ℕ₀ → Type where
        | 𝟘 : FSetTuple 0
        | σ n : ℕ₀FSet × FSetTuple n
   11] Tenemos ya conjuntos de FSet y tipos tupla de n FSet, pero nos falta un tipo de función entre ellos. Podríamos definir algo como:
     structure FSetFunction (n m : ℕ₀) where
       toFun : FSetTuple n → FSetTuple m
       map_carrier : ∀ t, t ∈ FSetTuple n → toFun t ∈ FSetTuple m
      Esto nos permitiría trabajar con funciones entre tuplas de conjuntos finitos de naturales, y podríamos definir funciones sobre ellas, como la función de imagen que mencioné en el punto 1 pero para tuplas de conjuntos finitos.
-/

import Peano.PeanoNat.Lists
import Peano.PeanoNat.FSet


namespace Peano
  open Peano
  open Peano.Lists
  open Peano.FSet

  namespace FSetFunction


  end FSetFunction
end Peano
