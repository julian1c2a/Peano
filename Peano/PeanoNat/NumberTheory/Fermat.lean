/-
# Plan de formalización: Teorema de Fermat (Peano/PeanoNat/NumberTheory/Fermat.lean)

## Objetivo
Demostrar el Pequeño Teorema de Fermat:

Para todo primo p y todo a ∈ ℕ₀ coprimo con p, se cumple:
  a ^ p ≡ a [MOD p]

## Estructura del plan

1. **Enunciado formal y contexto**
   - Definir el enunciado formal en Lean, usando la notación modular y la función potencia.
   - Contexto: p primo, a ∈ ℕ₀, Coprime a p.

2. **Reducción a Euler**
   - Enunciar y usar el teorema de Euler:
     Si Coprime a n, entonces a ^ φ(n) ≡ 1 [MOD n].
   - Para n = p primo, φ(p) = p - 1.
   - Por tanto, a ^ (p-1) ≡ 1 [MOD p].
   - Multiplicar ambos lados por a para obtener a ^ p ≡ a [MOD p].

3. **Dependencias inmediatas**
   - Teorema de Euler (ya planificado y en Totient.lean).
   - Lema: φ(p) = p - 1 para p primo (ya implementado).
   - Lema: Si a ^ (p-1) ≡ 1 [MOD p] ⇒ a ^ p ≡ a [MOD p] (aritmética modular).
   - Lema: Si p ∣ a ⇒ a ^ p ≡ a [MOD p] (caso no coprimo, trivial).

4. **Estrategia de demostración**
   - Caso 1: Coprime a p → usar Euler y el lema de potencia.
   - Caso 2: p ∣ a → a ≡ 0 [MOD p], a ^ p ≡ 0 [MOD p], luego a ^ p ≡ a [MOD p].
   - Unir ambos casos para el enunciado general.

5. **Formalización modular**
   - Usar la notación y lemmas de potencia, mod, y coprimalidad ya presentes.
   - Reutilizar la función totient y el resultado para primos.

## Archivos implicados

## Siguiente paso
-/
import Peano.PeanoNat.NumberTheory.Totient
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.NumberTheory.ModEq

set_option autoImplicit false

namespace Peano
   open Peano
   open Peano.Sub

   namespace Fermat

      /--
      ## Enunciado formal
      Para todo primo p y todo a ∈ ℕ₀:
      a ^ p ≡ a [MOD p]
      -/
      theorem fermat_little_theorem (a p : ℕ₀) (hp : Arith.Prime p) :

         mod (pow a p) p = mod a p :=
      by
         by_cases hcop : Coprime a p

         · -- CASO 1: a y p son coprimos
            -- Paso 1: φ(p) = p - 1 para p primo
            have hphi : Totient.totient p = sub p 𝟙 := Totient.totient_prime hp

            -- Paso 2: Teorema de Euler: a ^ φ(p) ≡ 1 [MOD p]
            -- (debe implementarse o importarse correctamente)
            -- have heuler : mod (pow a (Totient.totient p)) p = 𝟙 := sorry -- TODO: implementar o importar teorema de Euler
            sorry -- TODO: completar el caso coprimo usando Euler

         · -- CASO 2: p divide a (¬Coprime a p)
            sorry -- TODO: cuando p ∣ a, ambos lados son 0 mod p

   end Fermat
end Peano
