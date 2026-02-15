-- Peano.lean
-- Archivo principal que importa y re-exporta todos los módulos de la biblioteca de números naturales de Peano

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatDiv
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatWellFounded

-- Re-exportar todos los nombres del namespace Peano
-- para que estén disponibles cuando se importe Peano
export Peano (open)
