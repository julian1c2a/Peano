# Dependencias del Proyecto Peano

**Última actualización:** 2026-04-17
**Autor**: Julián Calderón Almendros

---

## Dependencias de Módulos Lean

Gráfico de dependencias entre los módulos `.lean` del proyecto.

Los módulos residen en `Peano/PeanoNat/` e importan como `Peano.PeanoNat.<Module>`.

```mermaid
graph TD;
    subgraph Peano Project Dependencies
        Peano --> Fermat;
        Peano --> ChineseRemainder;
        Peano --> ModEq;
        Peano --> Totient;
        Peano --> FSetFunction;
        Peano --> FSetFSet;
        Peano --> ListList;
        Peano --> NewtonBinom;
        Peano --> Binom;
        Peano --> Factorial;
        Peano --> Summation;
        Peano --> Product;
        Peano --> Fibonacci;
        Peano --> Pow;
        Peano --> Primes;
        Peano --> Arith;
        Peano --> Digits;
        Peano --> Pairing;
        Peano --> NumberSets;

        Fermat --> Totient;
        Fermat --> ModEq;
        Fermat --> Primes;
        ChineseRemainder --> ModEq;
        ChineseRemainder --> Arith;
        Totient --> NumberSets;
        ModEq --> Div;

        FSetFunction --> FSet;
        FSetFSet --> FSet;
        ListList --> List;
        FSet --> List;
        List --> Arith;

        NumberSets --> FSet;

        Counting --> FSetFunction;
        Perm --> FSetFunction;
        Sign --> Perm;
        Orbit --> Perm;
        Group --> Perm;
        Action --> Group;
        Cosets --> Group;
        Sylow --> Cosets;
        Sylow --> Action;

        NewtonBinom --> Binom;
        NewtonBinom --> Factorial;
        NewtonBinom --> Pow;
        NewtonBinom --> Summation;

        Binom --> Factorial;
        Binom --> Mul;

        Factorial --> Mul;
        Summation --> Add;
        Product --> Mul;
        Fibonacci --> Add;

        Pow --> Div;
        Primes --> Arith;
        Arith --> Div;
        Digits --> Log;
        Pairing --> Sqrt;

        Log --> Pow;
        Sqrt --> Pow;

        Div --> Mul;
        Mul --> Sub;
        Sub --> Add;
        Add --> WellFounded;
        WellFounded --> Lattice;
        Lattice --> Order;
        Tuple --> StrictOrder;
        Order --> StrictOrder;
        StrictOrder --> Axioms;
        Axioms --> PeanoNat;
        PeanoNat --> Prelim;
        Prelim --> ExistsUnique;
        Prelim --> Classical;
    end
```

**Nota**: Cada módulo también importa directamente los módulos de la cadena base (`PeanoNat`, `Axioms`, etc.) aunque no aparezcan todas las flechas. El gráfico muestra las dependencias directas más relevantes.

---

## Tabla de dependencias por módulo

| Módulo | Ruta | Importa directamente |
|---|---|---|
| `ExistsUnique` | `Peano/Prelim/ExistsUnique.lean` | (ninguno) |
| `Classical` | `Peano/Prelim/Classical.lean` | `Init.Classical`, `ExistsUnique` |
| `Prelim` | `Peano/Prelim.lean` | `ExistsUnique`, `Classical` |
| `PeanoNat` | `Peano/PeanoNat.lean` | `Prelim` |
| `Axioms` | `Peano/PeanoNat/Axioms.lean` | `PeanoNat` |
| `StrictOrder` | `Peano/PeanoNat/StrictOrder.lean` | `PeanoNat`, `Axioms` |
| `Order` | `Peano/PeanoNat/Order.lean` | `…StrictOrder` |
| `Tuple` | `Peano/PeanoNat/Tuple.lean` | `PeanoNat`, `StrictOrder` |
| `Lattice` | `Peano/PeanoNat/Lattice.lean` | `…Order` |
| `WellFounded` | `Peano/PeanoNat/WellFounded.lean` | `…Lattice`, `Init.Classical` |
| `Add` | `Peano/PeanoNat/Add.lean` | `…WellFounded` |
| `Sub` | `Peano/PeanoNat/Sub.lean` | `…Add` |
| `Mul` | `Peano/PeanoNat/Mul.lean` | `…Sub` |
| `Div` | `Peano/PeanoNat/Div.lean` | `…Mul` |
| `Arith` | `Peano/PeanoNat/Arith.lean` | `…Div`, `Init.Classical` |
| `Primes` | `Peano/PeanoNat/Primes.lean` | `…Arith` |
| `NumberSets` | `Peano/PeanoNat/NumberSets.lean` | `…FSet`, `…Arith` |
| `Pow` | `Combinatorics/Pow.lean` | `…Div` |
| `Factorial` | `Combinatorics/Factorial.lean` | `…Add`, `…Mul` |
| `Binom` | `Combinatorics/Binom.lean` | `…Factorial`, `…Sub`, `…Mul` |
| `Summation` | `Combinatorics/Summation.lean` | `…Add` |
| `Product` | `Combinatorics/Product.lean` | `…Mul` |
| `Fibonacci` | `Combinatorics/Fibonacci.lean` | `…Add` |
| `NewtonBinom` | `Combinatorics/NewtonBinom.lean` | `…Binom`, `…Pow`, `…Summation` |
| `Counting` | `Combinatorics/Counting.lean` | `…FSetFunction` |
| `Perm` | `Combinatorics/Perm.lean` | `…FSetFunction` |
| `Sign` | `Combinatorics/Sign.lean` | `…Perm` |
| `Orbit` | `Combinatorics/Orbit.lean` | `…Perm` |
| `Group` | `Combinatorics/Group.lean` | `…Perm` |
| `Action` | `GroupTheory/Action.lean` | `…Group` |
| `Cosets` | `GroupTheory/Sylow/Cosets.lean` | `…Group` |
| `Sylow` | `GroupTheory/Sylow/Sylow.lean` | `…Cosets`, `…Action` |
| `List` | `ListsAndSets/List.lean` | `…Arith` |
| `ListList` | `ListsAndSets/ListList.lean` | `…List` |
| `FSet` | `ListsAndSets/FSet.lean` | `…List` |
| `FSetFSet` | `ListsAndSets/FSetFSet.lean` | `…FSet` |
| `FSetFunction` | `ListsAndSets/FSetFunction.lean` | `…FSet` |
| `ModEq` | `NumberTheory/ModEq.lean` | `…Div` |
| `Totient` | `NumberTheory/Totient.lean` | `…NumberSets` |
| `ChineseRemainder` | `NumberTheory/ChineseRemainder.lean` | `…ModEq`, `…Arith` |
| `Fermat` | `NumberTheory/Fermat.lean` | `…Totient`, `…ModEq`, `…Primes` |
| `Log` | `PeanoNat/Log.lean` | `…Div`, `…Pow` |
| `Sqrt` | `PeanoNat/Sqrt.lean` | `…Mul`, `…Sub`, `…Pow` |
| `Digits` | `PeanoNat/Digits.lean` | `…Log` |
| `Pairing` | `PeanoNat/Pairing.lean` | `…Sqrt` |
| `Decidable` | `PeanoNat/Decidable.lean` | `…Order` (reexport) |
| `Isomorph` | `PeanoNat/Isomorph.lean` | `…Sub` (reexport) |
| `Peano.lean` | `Peano.lean` | todos los anteriores |

<!-- AUTO-UPDATE-2026-04-17-START -->
## Actualizacion de estado - 2026-04-17

- Estado del build: compila en el estado actual de la rama makingdecidable.
- Lagrange: cerrado en Sylow/Cosets con conteo por fibras y clases de cosets.
- GroupAction: sorries cerrados en orbit_stabilizer y orbits_partition.
- Sylow I: caso base n=0 cerrado; estructura separada en paso de Cauchy y paso de elevacion.
- Nota temporal: cauchy_minimal se apoya en un axioma explicito cauchy_minimal_axiom para continuar el desarrollo.
- Pendientes activos en Sylow: sylow_lift_from_cauchy, sylow_second, sylow_third.
- Objetivo proximo: reemplazar cauchy_minimal_axiom por demostracion interna y completar Sylow I.

<!-- AUTO-UPDATE-2026-04-17-END -->

