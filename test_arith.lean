import Init.Classical
import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatDiv
import PeanoNatLib.PeanoNatMaxMin

open Peano
open Peano.Axioms
open Peano.Order
open Peano.StrictOrder
open Peano.Add
open Peano.Sub
open Peano.Div
open Peano.MaxMin
open Peano.Mul
open Peano.Div
open Peano.Arith

-- Test gcd
#eval gcd (Peano.ofNat 12) (Peano.ofNat 8)
#eval gcd (Peano.ofNat 100) (Peano.ofNat 35)
#eval gcd (Peano.ofNat 0) (Peano.ofNat 5)

-- Test lcm
#eval lcm (Peano.ofNat 12) (Peano.ofNat 8)
#eval lcm (Peano.ofNat 4) (Peano.ofNat 6)
