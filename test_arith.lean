import Peano

open Peano.NatArith

-- Test gcd
#eval gcd (Peano.ofNat 12) (Peano.ofNat 8)
#eval gcd (Peano.ofNat 100) (Peano.ofNat 35)
#eval gcd (Peano.ofNat 0) (Peano.ofNat 5)

-- Test lcm
#eval lcm (Peano.ofNat 12) (Peano.ofNat 8)
#eval lcm (Peano.ofNat 4) (Peano.ofNat 6)
