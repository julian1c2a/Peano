/-!
# ListLists.lean

Este módulo define:
- El orden lexicográfico genérico para `List α` (con instancias `LT`, `LE`, `DecidableLT`, `DecidableLE`).
- Alias para listas de tuplas y listas de listas: `NatsTupleList`, `GTupleList`, `HTupleList`, etc.
- El tipo suma `PeanoVal` que agrupa naturales, tuplas, listas, etc., y su lista `PeanoValList`.
- Un "orden global" sobre `PeanoVal` y sus listas, basado en pesos.

---

import Peano.PeanoNat.Lists
import Peano.PeanoNat.Tuple
import Peano.PeanoNat.Nats
import Peano.PeanoNat.HTuple

namespace PeanoNat

/-! ## Orden lexicográfico genérico para listas -/

def listLexLt {α : Type} [LT α] : List α → List α → Prop
| [], []         => False
| [], _ :: _     => True
| _ :: _, []     => False
| a :: as, b :: bs => a < b ∨ (a = b ∧ listLexLt as bs)

instance instLTList {α : Type} [LT α] : LT (List α) := ⟨listLexLt⟩

/-! Instancia LE (≤) para listas -/
def listLexLe {α : Type} [LT α] [DecidableEq α] : List α → List α → Prop :=
  fun as bs => (as < bs) ∨ as = bs

instance instLEList {α : Type} [LT α] [DecidableEq α] : LE (List α) := ⟨listLexLe⟩

/-! Instancias Decidable para < y ≤ en listas -/
instance instDecidableRelLtList {α} [LT α] [DecidableEq α] [DecidableRel (@LT.lt α _)] :
    DecidableRel (@LT.lt (List α) _) :=
  λ as bs =>
    match as, bs with
    | [], []         => isFalse (by intro h; cases h)
    | [], _ :: _     => isTrue (by left; trivial)
    | _ :: _, []     => isFalse (by intro h; cases h)
    | a :: as, b :: bs =>
      match (decidableLt a b), (decEq a b), (instDecidableRelLtList as bs) with
      | isTrue hab, _, _ => isTrue (by left; exact hab)
      | isFalse _, isTrue heq, hlt =>
        match hlt with
        | isTrue h => isTrue (by right; exact ⟨heq, h⟩)
        | isFalse _ => isFalse (by intro h; cases h; contradiction)
      | isFalse _, isFalse _, _ => isFalse (by intro h; cases h; contradiction)
  where
    decidableLt := @LT.lt α _
    decEq := @DecidableEq α _

instance instDecidableRelLeList {α} [LT α] [DecidableEq α] [DecidableRel (@LT.lt α _)] :
    DecidableRel (@LE.le (List α) _) :=
  λ as bs =>
    match instDecidableRelLtList as bs with
    | isTrue _ => isTrue (by left; assumption)
    | isFalse _ =>
      match decEq as bs with
      | isTrue heq => isTrue (by right; exact heq)
      | isFalse _ => isFalse (by intro h; cases h; contradiction)
  where
    decEq := @DecidableEq (List α) _

/-! ## Alias para listas de tuplas y listas de listas -/

abbrev NatsTupleList (ts : List Nats) := List (NatsTuple ts)
abbrev GTupleList (α : Type) (n : ℕ₀) := List (GTuple α n)
abbrev HTupleList (ts : List Type) := List (HTuple ts)
abbrev NatsList := List Nats
abbrev Nat0List := List ℕ₀
abbrev Nat1List := List ℕ₁
abbrev Nat2List := List ℕ₂

/-! ## Tipo suma PeanoVal y su lista -/

inductive PeanoVal
| nat0 (n : ℕ₀)
| nat1 (n : ℕ₁)
| nat2 (n : ℕ₂)
| nats (ns : Nats)
| tuple0 (t : GTuple ℕ₀ 2)
| tuple1 (t : GTuple ℕ₁ 2)
| tuple2 (t : GTuple ℕ₂ 2)
| natsTuple (ts : NatsTuple (List.replicate 2 Nats))
| htuple (ts : HTuple (List.replicate 2 Type))
| natsList (l : NatsList)
| nat0List (l : Nat0List)
| nat1List (l : Nat1List)
| nat2List (l : Nat2List)
| natsTupleList (l : NatsTupleList (List.replicate 2 Nats))
| gtupleList (l : GTupleList ℕ₀ 2)
| htupleList (l : HTupleList (List.replicate 2 Type))

deriving DecidableEq, Repr

abbrev PeanoValList := List PeanoVal

/-! ## Orden global por peso sobre PeanoVal -/

def peanoValWeight : PeanoVal → Nat
| .nat0 _ | .nat1 _ | .nat2 _ | .nats _ => 1
| .tuple0 _ | .tuple1 _ | .tuple2 _ | .natsTuple _ | .htuple _ => 2
| .natsList _ | .nat0List _ | .nat1List _ | .nat2List _ | .natsTupleList _ | .gtupleList _ | .htupleList _ => 3

instance : LT PeanoVal where
  lt a b :=
    let wa := peanoValWeight a
    let wb := peanoValWeight b
    wa < wb ∨ (wa = wb ∧ toString a < toString b)

instance : DecidableRel (@LT.lt PeanoVal _) :=
  λ a b =>
    let wa := peanoValWeight a
    let wb := peanoValWeight b
    match Nat.decLt wa wb, Nat.decEq wa wb with
    | isTrue hlt, _ => isTrue (by left; exact hlt)
    | isFalse _, isTrue heq =>
      match decEq (toString a) (toString b), decide (toString a < toString b) with
      | isFalse _, isTrue hlt => isTrue (by right; exact ⟨heq, hlt⟩)
      | _, _ => isFalse (by intro h; cases h; contradiction)
    | isFalse _, isFalse _ => isFalse (by intro h; cases h; contradiction)
  where
    decEq := @DecidableEq String _

end PeanoNat

/-! Exporta los principales nombres -/
export PeanoNat (
  listLexLt listLexLe
  NatsTupleList GTupleList HTupleList
  NatsList Nat0List Nat1List Nat2List
  PeanoVal PeanoValList peanoValWeight
)
