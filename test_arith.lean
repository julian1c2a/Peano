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
import PeanoNatLib.PeanoNatArith

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
#eval Ψ (gcd (Λ 12) (Λ 8))
#eval Ψ (gcd (Λ 100) (Λ 35))
#eval Ψ (gcd (Λ 0) (Λ 5))

-- Test lcm
#eval Ψ (lcm (Λ 12) (Λ 8))
#eval Ψ (lcm (Λ 4) (Λ 6))
