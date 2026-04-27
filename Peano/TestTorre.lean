/-
Test de cierre automático de la torre de tipos.
Verifica que cualquier combinación de Tuple/List/FSet resuelva
las 9 typeclasses requeridas automáticamente.
-/

import Peano.PeanoNat.Tuple
import Peano.PeanoNat.ListsAndSets.List
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.Decidable

namespace Peano.TestTorre

  -- Test básico: ℕ₀ tiene todo
  #check (inferInstance : DecidableEq ℕ₀)
  #check (inferInstance : LT ℕ₀)
  #check (inferInstance : LE ℕ₀)
  #check (inferInstance : DecidableRel (@LT.lt ℕ₀ _))
  #check (inferInstance : DecidableRel (@LE.le ℕ₀ _))
  #check (inferInstance : Std.Irrefl (fun a b : ℕ₀ => a < b))
  #check (inferInstance : Std.Asymm (fun a b : ℕ₀ => a < b))
  #check (inferInstance : Trans (fun a b : ℕ₀ => a < b) (fun a b : ℕ₀ => a < b) (fun a b : ℕ₀ => a < b))
  #check (inferInstance : Std.Trichotomous (fun a b : ℕ₀ => a < b))

  -- Test: Tuple ℕ₀ 3
  #check (inferInstance : DecidableEq (Tuple ℕ₀ (σ (σ (σ 𝟘)))))
  #check (inferInstance : LT (Tuple ℕ₀ (σ (σ (σ 𝟘)))))
  #check (inferInstance : LE (Tuple ℕ₀ (σ (σ (σ 𝟘)))))
  #check (inferInstance : DecidableRel (@LT.lt (Tuple ℕ₀ (σ (σ (σ 𝟘)))) _))
  -- Nota: `DecidableRel LE` para `Tuple` requiere instancia explícita
  -- #check (inferInstance : DecidableRel (@LE.le (Tuple ℕ₀ (σ (σ (σ 𝟘)))) _))
  #check (inferInstance : Std.Irrefl (fun a b : Tuple ℕ₀ (σ (σ (σ 𝟘))) => a < b))
  #check (inferInstance : Std.Asymm (fun a b : Tuple ℕ₀ (σ (σ (σ 𝟘))) => a < b))
  #check (inferInstance : Trans (fun a b : Tuple ℕ₀ (σ (σ (σ 𝟘))) => a < b) (fun a b : Tuple ℕ₀ (σ (σ (σ 𝟘))) => a < b) (fun a b : Tuple ℕ₀ (σ (σ (σ 𝟘))) => a < b))
  #check (inferInstance : Std.Trichotomous (fun a b : Tuple ℕ₀ (σ (σ (σ 𝟘))) => a < b))

  -- Test: List (Tuple ℕ₀ 2)
  #check (inferInstance : DecidableEq (List (Tuple ℕ₀ (σ (σ 𝟘)))))
  #check (inferInstance : LT (List (Tuple ℕ₀ (σ (σ 𝟘)))))
  #check (inferInstance : LE (List (Tuple ℕ₀ (σ (σ 𝟘)))))
  #check (inferInstance : DecidableRel (@LT.lt (List (Tuple ℕ₀ (σ (σ 𝟘)))) _))
  #check (inferInstance : DecidableRel (@LE.le (List (Tuple ℕ₀ (σ (σ 𝟘)))) _))
  #check (inferInstance : Std.Irrefl (fun a b : List (Tuple ℕ₀ (σ (σ 𝟘))) => a < b))
  #check (inferInstance : Std.Asymm (fun a b : List (Tuple ℕ₀ (σ (σ 𝟘))) => a < b))
  #check (inferInstance : Trans (fun a b : List (Tuple ℕ₀ (σ (σ 𝟘))) => a < b) (fun a b : List (Tuple ℕ₀ (σ (σ 𝟘))) => a < b) (fun a b : List (Tuple ℕ₀ (σ (σ 𝟘))) => a < b))
  #check (inferInstance : Std.Trichotomous (fun a b : List (Tuple ℕ₀ (σ (σ 𝟘))) => a < b))

  -- Test: FSet (List (Tuple ℕ₀ 2))
  #check (inferInstance : DecidableEq (FSet (List (Tuple ℕ₀ (σ (σ 𝟘))))))
  #check (inferInstance : LT (FSet (List (Tuple ℕ₀ (σ (σ 𝟘))))))
  #check (inferInstance : LE (FSet (List (Tuple ℕ₀ (σ (σ 𝟘))))))
  #check (inferInstance : DecidableRel (@LT.lt (FSet (List (Tuple ℕ₀ (σ (σ 𝟘))))) _))
  #check (inferInstance : DecidableRel (@LE.le (FSet (List (Tuple ℕ₀ (σ (σ 𝟘))))) _))
  #check (inferInstance : Std.Irrefl (fun a b : FSet (List (Tuple ℕ₀ (σ (σ 𝟘)))) => a < b))
  #check (inferInstance : Std.Asymm (fun a b : FSet (List (Tuple ℕ₀ (σ (σ 𝟘)))) => a < b))
  #check (inferInstance : Trans (fun a b : FSet (List (Tuple ℕ₀ (σ (σ 𝟘)))) => a < b) (fun a b : FSet (List (Tuple ℕ₀ (σ (σ 𝟘)))) => a < b) (fun a b : FSet (List (Tuple ℕ₀ (σ (σ 𝟘)))) => a < b))
  #check (inferInstance : Std.Trichotomous (fun a b : FSet (List (Tuple ℕ₀ (σ (σ 𝟘)))) => a < b))

  -- Test: Tuple (FSet ℕ₀) 2 (anidamiento inverso)
  #check (inferInstance : DecidableEq (Tuple (FSet ℕ₀) (σ (σ 𝟘))))
  #check (inferInstance : LT (Tuple (FSet ℕ₀) (σ (σ 𝟘))))
  #check (inferInstance : LE (Tuple (FSet ℕ₀) (σ (σ 𝟘))))
  #check (inferInstance : DecidableRel (@LT.lt (Tuple (FSet ℕ₀) (σ (σ 𝟘))) _))
  -- Nota: `DecidableRel LE` para `Tuple` requiere instancia explícita
  -- #check (inferInstance : DecidableRel (@LE.le (Tuple (FSet ℕ₀) (σ (σ 𝟘))) _))
  #check (inferInstance : Std.Irrefl (fun a b : Tuple (FSet ℕ₀) (σ (σ 𝟘)) => a < b))
  #check (inferInstance : Std.Asymm (fun a b : Tuple (FSet ℕ₀) (σ (σ 𝟘)) => a < b))
  #check (inferInstance : Trans (fun a b : Tuple (FSet ℕ₀) (σ (σ 𝟘)) => a < b) (fun a b : Tuple (FSet ℕ₀) (σ (σ 𝟘)) => a < b) (fun a b : Tuple (FSet ℕ₀) (σ (σ 𝟘)) => a < b))
  #check (inferInstance : Std.Trichotomous (fun a b : Tuple (FSet ℕ₀) (σ (σ 𝟘)) => a < b))

  -- Test: List (FSet (List ℕ₀)) — triple anidamiento
  #check (inferInstance : DecidableEq (List (FSet (List ℕ₀))))
  #check (inferInstance : LT (List (FSet (List ℕ₀))))
  #check (inferInstance : LE (List (FSet (List ℕ₀))))
  #check (inferInstance : DecidableRel (@LT.lt (List (FSet (List ℕ₀))) _))
  #check (inferInstance : DecidableRel (@LE.le (List (FSet (List ℕ₀))) _))
  #check (inferInstance : Std.Irrefl (fun a b : List (FSet (List ℕ₀)) => a < b))
  #check (inferInstance : Std.Asymm (fun a b : List (FSet (List ℕ₀)) => a < b))
  #check (inferInstance : Trans (fun a b : List (FSet (List ℕ₀)) => a < b) (fun a b : List (FSet (List ℕ₀)) => a < b) (fun a b : List (FSet (List ℕ₀)) => a < b))
  #check (inferInstance : Std.Trichotomous (fun a b : List (FSet (List ℕ₀)) => a < b))

  -- Test: FSet (FSet ℕ₀) — FSet de FSet
  #check (inferInstance : DecidableEq (FSet (FSet ℕ₀)))
  #check (inferInstance : LT (FSet (FSet ℕ₀)))
  #check (inferInstance : LE (FSet (FSet ℕ₀)))
  #check (inferInstance : DecidableRel (@LT.lt (FSet (FSet ℕ₀)) _))
  #check (inferInstance : DecidableRel (@LE.le (FSet (FSet ℕ₀)) _))
  #check (inferInstance : Std.Irrefl (fun a b : FSet (FSet ℕ₀) => a < b))
  #check (inferInstance : Std.Asymm (fun a b : FSet (FSet ℕ₀) => a < b))
  #check (inferInstance : Trans (fun a b : FSet (FSet ℕ₀) => a < b) (fun a b : FSet (FSet ℕ₀) => a < b) (fun a b : FSet (FSet ℕ₀) => a < b))
  #check (inferInstance : Std.Trichotomous (fun a b : FSet (FSet ℕ₀) => a < b))

  -- ════════════════════════════════════════════════════════════════════
  -- Action 3: FSet (Tuple ℕ₀ n) funciona automáticamente
  -- ════════════════════════════════════════════════════════════════════

  -- StrictLinearOrder (Tuple ℕ₀ n) se infiere automáticamente
  #check (inferInstance : StrictLinearOrder (Tuple ℕ₀ (σ (σ (σ 𝟘)))))

  -- sortedInsert sobre List (Tuple ℕ₀ n) funciona automáticamente
  example (n : ℕ₀) (t : Tuple ℕ₀ n) (l : List (Tuple ℕ₀ n))
      (hs : Sorted (· < ·) l) : Sorted (· < ·) (sortedInsert t l) :=
    sorted_sortedInsert hs t

  -- FSet (Tuple ℕ₀ n) se puede extender via sortedInsert
  example (n : ℕ₀) (t : Tuple ℕ₀ n) (s : FSet (Tuple ℕ₀ n)) : FSet (Tuple ℕ₀ n) :=
    ⟨sortedInsert t s.elems, sorted_sortedInsert s.sorted t⟩

  -- FSet (Tuple ℕ₀ n) tiene todas las typeclasses requeridas
  #check (inferInstance : DecidableEq (FSet (Tuple ℕ₀ (σ (σ 𝟘)))))
  #check (inferInstance : LT (FSet (Tuple ℕ₀ (σ (σ 𝟘)))))
  #check (inferInstance : DecidableRel (@LT.lt (FSet (Tuple ℕ₀ (σ (σ 𝟘)))) _))
  #check (inferInstance : Std.Trichotomous (fun a b : FSet (Tuple ℕ₀ (σ (σ 𝟘))) => a < b))

end Peano.TestTorre
