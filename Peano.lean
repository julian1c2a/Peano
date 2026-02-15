-- Peano.lean
-- Archivo principal que importa y re-exporta todos los módulos de la biblioteca de números naturales de Peano

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatDiv
import PeanoNatLib.PeanoNatArith
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatWellFounded

-- Re-exportar todos los nombres del namespace Peano
-- para que estén disponibles cuando se importe Peano
export Peano (open)
export Peano.Div (
	div_of_lt_nth_interval
	mod_of_lt_fst_interval
	mod_of_lt_snd_interval
	mod_of_lt_nth_interval
)
export Peano.NatArith (
	Divides
	MultipleOf
	DivisorOf
	Divisors
	Multiples
	multiples_to_divides
	divides_to_multiples
	multiples_iff_divides
	DList
	DivisorsList
	DList.Mem
	DList.append
	DList.length
	DList.NoDup
	DList.MemDec
	mem_cons
	mem_append
	one_divides
	divisorslist_one_mem
	divisorslist_self_mem
	IsGCD
	IsLCM
	Coprime
	Prime
	divides_refl
	divides_zero
	zero_divides_iff
	divides_trans
	divides_mul_right
	divides_mul_left
	divides_add
)
