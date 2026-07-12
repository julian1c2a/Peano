/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/CosetAction.lean
--
-- H acts on G/K by left multiplication.  p ∤ |G/K| when K is a Sylow p-subgroup.
-- Fixed-point theorem for p-groups (by strong induction on |X|).
-- Exported: coset_conjugate_exists  (replaces private axiom sylow_second_incl).

import Peano.PeanoNat
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Primes
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Isomorph
import Peano.PeanoNat.ListsAndSets.FSet
import Peano.PeanoNat.ListsAndSets.EquivRel
import Peano.PeanoNat.ListsAndSets.FSetFunction
import Peano.PeanoNat.Combinatorics.Pow
import Peano.PeanoNat.Combinatorics.Group
import Peano.PeanoNat.Combinatorics.GroupTheory.Sylow.Cosets
import Peano.PeanoNat.Combinatorics.GroupTheory.Action

set_option autoImplicit false

namespace Peano
  namespace CosetAction

    open Peano.FSet
    open Peano.EquivRel
    open Peano.FSetFunction
    open Peano.Group
    open Peano.Mul
    open Peano.Pow
    open Peano.Arith
    open Peano.Cosets
    open Peano.Action
    open Peano.Primes

    private abbrev Prime := Peano.Primes.Prime

    /-! # § 1. Arithmetic helpers -/

    private theorem Λ_one : Λ 1 = 𝟙 := by
      change Λ 1 = σ 𝟘
      rw [isomorph_σ_Λ, isomorph_0_Λ]

    private theorem pow_prime_ne_zero {p : ℕ₀} (hp : Prime p) : ∀ n : ℕ₀, pow p n ≠ 𝟘 := by
      intro n
      induction n with
      | zero =>
        rw [pow_zero]
        exact Peano.Axioms.succ_neq_zero 𝟘
      | succ n' ih =>
        rw [pow_succ]
        intro h
        rcases (mul_eq_zero (pow p n') p).mp h with h1 | h2
        · exact ih h1
        · exact prime_ne_zero hp h2

    private theorem prime_dvd_of_dvd_prime_pow {p : ℕ₀} (hp : Prime p) :
        ∀ (n : ℕ₀) {d : ℕ₀}, d ∣ pow p n → d ≠ 𝟙 → p ∣ d := by
      intro n
      induction n with
      | zero =>
        intro d hd hne
        rw [pow_zero] at hd
        obtain ⟨k, hk⟩ := hd
        exact absurd (mul_eq_one hk.symm).1 hne
      | succ n' ih =>
        intro d hd hne
        rw [pow_succ] at hd
        rcases prime_coprime_or_dvd hp (n := d) with hdvd | hcop
        · exact hdvd
        · have hcop' : Coprime d p := coprime_symm hcop
          have hd' : d ∣ mul p (pow p n') := by rwa [mul_comm] at hd
          exact ih (coprime_dvd_of_dvd_mul hcop' hd') hne

    private theorem ndvd_of_ndvd_add_dvd {p a b : ℕ₀}
        (h : ¬ p ∣ add a b) (ha : p ∣ a) : ¬ p ∣ b :=
      fun hb => h (divides_add ha hb)

    /-! # § 2. List / FSet helpers -/

    private theorem lengthₚ_filter_split_bool {α : Type} (q : α → Bool) :
        ∀ l : List α,
          lengthₚ l = add (lengthₚ (l.filter q))
                         (lengthₚ (l.filter (fun x => !q x)))
      | [] => by simp [lengthₚ_nil, zero_add]
      | x :: xs => by
          have ih := lengthₚ_filter_split_bool q xs
          cases hq : q x with
          | false =>
            have h1 : (x :: xs).filter q = xs.filter q := by simp [hq]
            have h2 : (x :: xs).filter (fun y => !q y) = x :: xs.filter (fun y => !q y) := by
              simp [hq]
            simp only [h1, h2, lengthₚ_cons, ih, ← add_succ]
          | true =>
            have h1 : (x :: xs).filter q = x :: xs.filter q := by simp [hq]
            have h2 : (x :: xs).filter (fun y => !q y) = xs.filter (fun y => !q y) := by
              simp [hq]
            simp only [h1, h2, lengthₚ_cons, ih, ← succ_add]

    private theorem fset_card_filter_compl {q : ℕ₀ → Bool} {s : ℕ₀FSet} :
        s.card = add (FSet.filter q s).card ((FSet.filter (fun x => !q x) s).card) :=
      lengthₚ_filter_split_bool q s.elems

    private theorem list_filter_lt_of_neg {l : List ℕ₀} {x : ℕ₀} {q : ℕ₀ → Bool}
        (hx : x ∈ l) (hq : q x = false) :
        (l.filter q).length < l.length := by
      induction l with
      | nil => cases hx
      | cons a as ih =>
        simp only [List.mem_cons] at hx
        rcases hx with rfl | has
        · -- x = a
          have hfil : (x :: as).filter q = as.filter q := by simp [hq]
          rw [hfil, List.length_cons]
          exact Nat.lt_succ_of_le (List.length_filter_le q as)
        · -- x ∈ as
          cases ha : q a with
          | false =>
            have hfil : (a :: as).filter q = as.filter q := by simp [ha]
            rw [hfil, List.length_cons]
            exact Nat.lt_succ_of_lt (ih has)
          | true =>
            have hfil : (a :: as).filter q = a :: as.filter q := by simp [ha]
            rw [hfil, List.length_cons, List.length_cons]
            exact Nat.succ_lt_succ (ih has)

    private theorem card_eq_one_iff_singleton {s : ℕ₀FSet} :
        s.card = 𝟙 ↔ ∃ a, s.elems = [a] := by
      constructor
      · intro h
        have h' : Λ s.elems.length = 𝟙 := h
        have hlen : s.elems.length = 1 := Λ_inj s.elems.length 1 (h'.trans Λ_one.symm)
        obtain ⟨a, as, heq⟩ := List.exists_cons_of_ne_nil
          (show s.elems ≠ [] by intro hnil; rw [hnil] at hlen; exact absurd hlen (by decide))
        exact ⟨a, by
          rw [heq] at hlen
          cases as with
          | nil => rw [heq]
          | cons b bs => simp at hlen⟩
      · rintro ⟨a, ha⟩
        show lengthₚ s.elems = 𝟙
        rw [ha, lengthₚ_cons, lengthₚ_nil]
        rfl

    /-! # § 3. Subgroup as FinGroup -/

    private def subgroupFinGroup {G : FinGroup ℕ₀} (H : Subgroup G) : FinGroup ℕ₀ where
      carrier  := H.carrier
      op       := { toFun    := fun a b => G.op a b
                    map_carrier := fun a b ha hb => H.op_closed a b ha hb }
      id       := G.id
      inv      := { toFun    := fun a => G.inv a
                    map_carrier := fun a ha => H.inv_closed a ha }
      id_in    := H.id_in
      op_assoc := fun a b c ha hb hc =>
        G.op_assoc a b c (H.subset a ha) (H.subset b hb) (H.subset c hc)
      op_id    := fun a ha => G.op_id a (H.subset a ha)
      op_inv   := fun a ha => G.op_inv a (H.subset a ha)

    /-! # § 4. Coset representative -/

    private def cosetRep (G : FinGroup ℕ₀) (K : Subgroup G) (g : ℕ₀) : ℕ₀ :=
      match ((cosetEquivRel G K).classOf g).elems with
      | []     => g
      | r :: _ => r

    private theorem cosetRep_spec {G : FinGroup ℕ₀} {K : Subgroup G} {g : ℕ₀}
        (hg : g ∈ G.carrier.elems) :
        ∃ r rest, ((cosetEquivRel G K).classOf g).elems = r :: rest
                  ∧ cosetRep G K g = r := by
      have hg_class : g ∈ ((cosetEquivRel G K).classOf g).elems :=
        (cosetEquivRel G K).classOf_nonempty_of_mem g hg
      cases h : ((cosetEquivRel G K).classOf g).elems with
      | nil   => exact absurd (h ▸ hg_class) List.not_mem_nil
      | cons r rest =>
        exact ⟨r, rest, rfl, by simp [cosetRep, h]⟩

    private theorem cosetRep_in_classOf {G : FinGroup ℕ₀} {K : Subgroup G} {g : ℕ₀}
        (hg : g ∈ G.carrier.elems) :
        cosetRep G K g ∈ ((cosetEquivRel G K).classOf g).elems := by
      obtain ⟨r, rest, h_elems, h_rep⟩ := cosetRep_spec hg
      rw [h_rep, h_elems]; exact List.mem_cons_self

    private theorem cosetRep_mem {G : FinGroup ℕ₀} {K : Subgroup G} {g : ℕ₀}
        (hg : g ∈ G.carrier.elems) : cosetRep G K g ∈ G.carrier.elems :=
      (cosetEquivRel G K).classOf_subset_domain g (cosetRep G K g)
        (cosetRep_in_classOf hg)

    private theorem cosetRep_idem {G : FinGroup ℕ₀} {K : Subgroup G} {g : ℕ₀}
        (hg : g ∈ G.carrier.elems) :
        cosetRep G K (cosetRep G K g) = cosetRep G K g := by
      obtain ⟨r, rest, h_elems, h_rep⟩ := cosetRep_spec hg
      have hr_in : r ∈ ((cosetEquivRel G K).classOf g).elems := by
        rw [h_elems]; exact List.mem_cons_self
      have h_class_eq : (cosetEquivRel G K).classOf r = (cosetEquivRel G K).classOf g :=
        (cosetEquivRel G K).classOf_eq_of_mem_classOf g r hg hr_in
      have h_elems_r : ((cosetEquivRel G K).classOf r).elems = r :: rest :=
        congrArg FSet.elems h_class_eq ▸ h_elems
      rw [h_rep, show cosetRep G K r = r from by simp [cosetRep, h_elems_r]]

    private theorem cosetRep_eq_of_rel {G : FinGroup ℕ₀} {K : Subgroup G} {a b : ℕ₀}
        (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems)
        (hab : cosetRel G K a b) :
        cosetRep G K a = cosetRep G K b := by
      have hb_in_a : b ∈ ((cosetEquivRel G K).classOf a).elems :=
        (cosetEquivRel G K).mem_classOf_of_rel a b hb hab
      have h_class_eq : (cosetEquivRel G K).classOf b = (cosetEquivRel G K).classOf a :=
        (cosetEquivRel G K).classOf_eq_of_mem_classOf a b ha hb_in_a
      obtain ⟨r, rest, h_elems_a, h_rep_a⟩ := cosetRep_spec ha
      have h_elems_b : ((cosetEquivRel G K).classOf b).elems = r :: rest :=
        congrArg FSet.elems h_class_eq ▸ h_elems_a
      rw [h_rep_a, show cosetRep G K b = r from by simp [cosetRep, h_elems_b]]

    private theorem cosetRel_left_mul {G : FinGroup ℕ₀} {K : Subgroup G} {h a b : ℕ₀}
        (hh : h ∈ G.carrier.elems) (ha : a ∈ G.carrier.elems) (hb : b ∈ G.carrier.elems)
        (hab : cosetRel G K a b) :
        cosetRel G K (G.op h a) (G.op h b) := by
      unfold cosetRel
      have hhb : G.op h b ∈ G.carrier.elems := op_mem G hh hb
      rw [inv_op_eq G hh ha,
          G.op_assoc (G.inv a) (G.inv h) (G.op h b)
            (inv_mem G ha) (inv_mem G hh) hhb,
          ← G.op_assoc (G.inv h) h b (inv_mem G hh) hh hb,
          (G.op_inv h hh).2, (G.op_id b hb).2]
      exact hab

    /-! # § 5. CosetHeadsSet -/

    private def cosetHeadsSet (G : FinGroup ℕ₀) (K : Subgroup G) : ℕ₀FSet :=
      FSet.image (cosetRep G K) G.carrier

    private theorem mem_cosetHeadsSet {G : FinGroup ℕ₀} {K : Subgroup G} {r : ℕ₀} :
        r ∈ (cosetHeadsSet G K).elems ↔ ∃ g ∈ G.carrier.elems, cosetRep G K g = r :=
      mem_image_iff

    private theorem cosetHeadsSet_subset_G {G : FinGroup ℕ₀} {K : Subgroup G} {r : ℕ₀}
        (hr : r ∈ (cosetHeadsSet G K).elems) : r ∈ G.carrier.elems := by
      obtain ⟨g, hg, hgr⟩ := mem_cosetHeadsSet.mp hr
      rw [← hgr]; exact cosetRep_mem hg

    private theorem cosetRep_of_mem_cosetHeadsSet {G : FinGroup ℕ₀} {K : Subgroup G} {r : ℕ₀}
        (hr : r ∈ (cosetHeadsSet G K).elems) : cosetRep G K r = r := by
      obtain ⟨g, hg, hgr⟩ := mem_cosetHeadsSet.mp hr
      rw [← hgr]; exact cosetRep_idem hg

    /-! # § 6. Coset action -/

    private def cosetActFun (G : FinGroup ℕ₀) (K : Subgroup G) (h r : ℕ₀) : ℕ₀ :=
      cosetRep G K (G.op h r)

    private theorem cosetActFun_closed {G : FinGroup ℕ₀} {H K : Subgroup G} {h r : ℕ₀}
        (hh : h ∈ H.carrier.elems) (hr : r ∈ (cosetHeadsSet G K).elems) :
        cosetActFun G K h r ∈ (cosetHeadsSet G K).elems :=
      mem_cosetHeadsSet.mpr
        ⟨G.op h r, op_mem G (H.subset h hh) (cosetHeadsSet_subset_G hr), rfl⟩

    private theorem cosetActFun_id {G : FinGroup ℕ₀} {K : Subgroup G} {r : ℕ₀}
        (hr : r ∈ (cosetHeadsSet G K).elems) :
        cosetActFun G K G.id r = r := by
      unfold cosetActFun
      rw [(G.op_id r (cosetHeadsSet_subset_G hr)).2]
      exact cosetRep_of_mem_cosetHeadsSet hr

    private theorem cosetActFun_compat {G : FinGroup ℕ₀} {H K : Subgroup G} {h₁ h₂ r : ℕ₀}
        (hh₁ : h₁ ∈ H.carrier.elems) (hh₂ : h₂ ∈ H.carrier.elems)
        (hr : r ∈ (cosetHeadsSet G K).elems) :
        cosetActFun G K h₁ (cosetActFun G K h₂ r) = cosetActFun G K (G.op h₁ h₂) r := by
      unfold cosetActFun
      have hh₁G : h₁ ∈ G.carrier.elems := H.subset h₁ hh₁
      have hh₂G : h₂ ∈ G.carrier.elems := H.subset h₂ hh₂
      have hrG  : r  ∈ G.carrier.elems := cosetHeadsSet_subset_G hr
      have hr₂G  : G.op h₂ r ∈ G.carrier.elems := op_mem G hh₂G hrG
      have hr₂'G : cosetRep G K (G.op h₂ r) ∈ G.carrier.elems := cosetRep_mem hr₂G
      have hr₂'_rel : cosetRel G K (G.op h₂ r) (cosetRep G K (G.op h₂ r)) :=
        (cosetEquivRel G K).rel_of_mem_classOf (G.op h₂ r) (cosetRep G K (G.op h₂ r))
          (cosetRep_in_classOf hr₂G)
      have hr₂'_rel_sym : cosetRel G K (cosetRep G K (G.op h₂ r)) (G.op h₂ r) :=
        cosetRel_symm G K (G.op h₂ r) (cosetRep G K (G.op h₂ r)) hr₂G hr₂'G hr₂'_rel
      have hstep : cosetRep G K (G.op h₁ (cosetRep G K (G.op h₂ r))) =
                   cosetRep G K (G.op h₁ (G.op h₂ r)) :=
        cosetRep_eq_of_rel (op_mem G hh₁G hr₂'G) (op_mem G hh₁G hr₂G)
          (cosetRel_left_mul hh₁G hr₂'G hr₂G hr₂'_rel_sym)
      rw [hstep, (G.op_assoc h₁ h₂ r hh₁G hh₂G hrG).symm]

    private noncomputable def cosetAction (G : FinGroup ℕ₀) (H K : Subgroup G) :
        GroupAction (subgroupFinGroup H) (cosetHeadsSet G K) where
      act        := fun h r => cosetActFun G K h r
      act_closed := fun _ _ hh hr => cosetActFun_closed hh hr
      act_id     := fun _ hr => cosetActFun_id hr
      act_compat := fun _ _ _ hh₁ hh₂ hr => cosetActFun_compat hh₁ hh₂ hr

    /-! # § 7. Cardinality of cosetHeadsSet -/

    private theorem cosetHeadsSet_mul_card_eq_G {G : FinGroup ℕ₀} (K : Subgroup G) :
        mul K.carrier.card (cosetHeadsSet G K).card = G.carrier.card := by
      let f : MapOn G.carrier (cosetHeadsSet G K) := {
        toFun      := fun g => cosetRep G K g
        map_carrier := fun g hg => mem_cosetHeadsSet.mpr ⟨g, hg, rfl⟩ }
      have h_fiber : ∀ r, r ∈ (cosetHeadsSet G K).elems →
          (f.fiber r).card = K.carrier.card := by
        intro r hr
        have hr_G  : r ∈ G.carrier.elems := cosetHeadsSet_subset_G hr
        have h_idem : cosetRep G K r = r := cosetRep_of_mem_cosetHeadsSet hr
        have h_fiber_eq : f.fiber r = (cosetEquivRel G K).classOf r := by
          apply FSet.eq_of_mem_iff
          intro g
          constructor
          · intro hg_fib
            obtain ⟨hg_G, hg_rep⟩ := (MapOn.mem_fiber_iff f r g).mp hg_fib
            have hr_in_g : r ∈ ((cosetEquivRel G K).classOf g).elems :=
              hg_rep ▸ cosetRep_in_classOf hg_G
            have h_eq : (cosetEquivRel G K).classOf r = (cosetEquivRel G K).classOf g :=
              (cosetEquivRel G K).classOf_eq_of_mem_classOf g r hg_G hr_in_g
            rw [h_eq]
            exact (cosetEquivRel G K).classOf_nonempty_of_mem g hg_G
          · intro hg_r
            have hg_G : g ∈ G.carrier.elems :=
              (cosetEquivRel G K).classOf_subset_domain r g hg_r
            have hrel : cosetRel G K r g :=
              (cosetEquivRel G K).rel_of_mem_classOf r g hg_r
            have hrel_sym : cosetRel G K g r :=
              cosetRel_symm G K r g hr_G hg_G hrel
            have hg_rep : cosetRep G K g = r := by
              rw [cosetRep_eq_of_rel hg_G hr_G hrel_sym, h_idem]
            exact (MapOn.mem_fiber_iff f r g).mpr ⟨hg_G, hg_rep⟩
        rw [h_fiber_eq]
        exact classOf_cosetEquivRel_card_eq_subgroup_card G K r hr_G
      exact (FSetFunction.card_eq_mul_of_uniform_fibers f K.carrier.card h_fiber).symm

    private theorem cosetHeadsSet_card_eq_index {G : FinGroup ℕ₀} {K : Subgroup G}
        {p n k : ℕ₀}
        (hK  : K.carrier.card = pow p n)
        (hGK : mul (pow p n) k = G.carrier.card)
        (hpn_ne : pow p n ≠ 𝟘) :
        (cosetHeadsSet G K).card = k := by
      have h := cosetHeadsSet_mul_card_eq_G K
      rw [hK] at h
      have heq : mul (pow p n) (cosetHeadsSet G K).card = mul (pow p n) k :=
        h.trans hGK.symm
      exact mul_cancelation_left (pow p n) (cosetHeadsSet G K).card k hpn_ne heq

    /-! # § 8. Orbit helpers for the fixed-point theorem -/

    private theorem orb_card_ne_one_of_not_fixed {G : FinGroup ℕ₀} {X : ℕ₀FSet}
        (α : GroupAction G X) {x₀ : ℕ₀} (hx₀ : x₀ ∈ X.elems)
        (hnotfixed : ¬ ∀ g ∈ G.carrier.elems, α.act g x₀ = x₀) :
        (α.orb x₀).card ≠ 𝟙 := by
      intro hone
      obtain ⟨a, ha_elems⟩ := card_eq_one_iff_singleton.mp hone
      have hx₀_orb : x₀ ∈ (α.orb x₀).elems :=
        (mem_orb_iff α x₀ x₀ hx₀).mpr ⟨G.id, G.id_in, α.act_id x₀ hx₀⟩
      have hx₀_eq_a : x₀ = a := by
        rw [ha_elems] at hx₀_orb; exact List.mem_singleton.mp hx₀_orb
      apply hnotfixed
      intro g hg
      have hgx₀_orb : α.act g x₀ ∈ (α.orb x₀).elems :=
        (mem_orb_iff α x₀ (α.act g x₀) hx₀).mpr ⟨g, hg, rfl⟩
      rw [ha_elems] at hgx₀_orb
      exact (List.mem_singleton.mp hgx₀_orb).trans hx₀_eq_a.symm

    private theorem orb_card_dvd_Gcard {G : FinGroup ℕ₀} {X : ℕ₀FSet}
        (α : GroupAction G X) {x₀ : ℕ₀} (hx₀ : x₀ ∈ X.elems) :
        (α.orb x₀).card ∣ G.carrier.card :=
      ⟨(α.stab x₀ hx₀).carrier.card, (orbit_stabilizer α x₀ hx₀).symm⟩

    -- The action of G restricted to X \ Orb(x₀).
    private def restrictedAction {G : FinGroup ℕ₀} {X : ℕ₀FSet}
        (α : GroupAction G X) (x₀ : ℕ₀) (hx₀ : x₀ ∈ X.elems) :
        GroupAction G (FSet.filter (fun y => !G.carrier.elems.any
          (fun g => decide (α.act g x₀ = y))) X) where
      act := fun g y => α.act g y
      act_closed := by
        intro g y hg hy
        have hy_X : y ∈ X.elems := (List.mem_filter.mp hy).1
        have hy_notOrb : G.carrier.elems.any (fun k => decide (α.act k x₀ = y)) = false := by
          have h := (List.mem_filter.mp hy).2
          cases hany : G.carrier.elems.any (fun k => decide (α.act k x₀ = y)) with
          | false => rfl
          | true  => simp [hany] at h
        have hgy_X : α.act g y ∈ X.elems := α.act_closed g y hg hy_X
        refine List.mem_filter.mpr ⟨hgy_X, ?_⟩
        -- goal: !any(k, α.act k x₀ = α.act g y) = true
        cases hcase : G.carrier.elems.any (fun k => decide (α.act k x₀ = α.act g y)) with
        | false => simp
        | true  =>
          exfalso
          rw [List.any_eq_true] at hcase
          obtain ⟨k, hk, hkdec⟩ := hcase
          rw [decide_eq_true_eq] at hkdec
          have hginvG : G.inv g ∈ G.carrier.elems := inv_mem G hg
          have hy_inOrb :
              G.carrier.elems.any (fun k' => decide (α.act k' x₀ = y)) = true := by
            rw [List.any_eq_true]
            refine ⟨G.op (G.inv g) k, op_mem G hginvG hk, decide_eq_true_eq.mpr ?_⟩
            -- goal: α.act (G.op (G.inv g) k) x₀ = y
            rw [← α.act_compat (G.inv g) k x₀ hginvG hk hx₀, hkdec,
                α.act_compat (G.inv g) g y hginvG hg hy_X,
                (G.op_inv g hg).2]
            exact α.act_id y hy_X
          simp [hy_inOrb] at hy_notOrb
      act_id := fun y hy =>
        α.act_id y (List.mem_filter.mp hy).1
      act_compat := fun h₁ h₂ y hh₁ hh₂ hy =>
        α.act_compat h₁ h₂ y hh₁ hh₂ (List.mem_filter.mp hy).1

    /-! # § 9. Fixed-point theorem for p-groups -/

    private theorem pgroup_fixed_point :
        ∀ (n : Nat) {G : FinGroup ℕ₀} {X : ℕ₀FSet}
          (α : GroupAction G X) (p m : ℕ₀),
          Prime p → G.carrier.card = pow p m → ¬ p ∣ X.card →
          X.elems.length ≤ n →
          ∃ x, x ∈ X.elems ∧ ∀ g ∈ G.carrier.elems, α.act g x = x := by
      intro n
      induction n with
      | zero =>
        intro G X α p m _ _ hndvd hlen
        have hnil : X.elems.length = 0 := Nat.le_zero.mp hlen
        have hcard0 : X.card = 𝟘 := by
          show Λ X.elems.length = 𝟘
          rw [hnil, isomorph_0_Λ]
        exact absurd (hcard0 ▸ divides_zero p) hndvd
      | succ n ih =>
        intro G X α p m hp hGcard hndvd hlen
        have hnonempty : X.elems ≠ [] := by
          intro h
          have hcard0 : X.card = 𝟘 := by
            show Λ X.elems.length = 𝟘
            rw [show X.elems.length = 0 from h ▸ rfl, isomorph_0_Λ]
          exact absurd (hcard0 ▸ divides_zero p) hndvd
        obtain ⟨x₀, rest, h_x0⟩ := List.exists_cons_of_ne_nil hnonempty
        have hx₀_mem : x₀ ∈ X.elems := h_x0 ▸ List.mem_cons_self
        rcases Classical.em (∀ g ∈ G.carrier.elems, α.act g x₀ = x₀) with hfixed | hnotfixed
        · exact ⟨x₀, hx₀_mem, hfixed⟩
        · let inOrb : ℕ₀ → Bool :=
            fun y => G.carrier.elems.any (fun g => decide (α.act g x₀ = y))
          let X' : ℕ₀FSet := FSet.filter (fun y => !inOrb y) X
          let hα' : GroupAction G X' := restrictedAction α x₀ hx₀_mem
          have hx₀_inOrb : inOrb x₀ = true := by
            simp only [inOrb, List.any_eq_true]
            exact ⟨G.id, G.id_in, decide_eq_true_eq.mpr (α.act_id x₀ hx₀_mem)⟩
          have hX'_len : X'.elems.length ≤ n := by
            have h_lt : X'.elems.length < X.elems.length :=
              list_filter_lt_of_neg hx₀_mem (by simp [hx₀_inOrb])
            exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h_lt hlen)
          have horb_dvd : (α.orb x₀).card ∣ pow p m :=
            hGcard ▸ orb_card_dvd_Gcard α hx₀_mem
          have horb_ne1 : (α.orb x₀).card ≠ 𝟙 :=
            orb_card_ne_one_of_not_fixed α hx₀_mem hnotfixed
          have hp_orb : p ∣ (α.orb x₀).card :=
            prime_dvd_of_dvd_prime_pow hp m horb_dvd horb_ne1
          have hcard_split : X.card = add (α.orb x₀).card X'.card :=
            fset_card_filter_compl
          have hndvd' : ¬ p ∣ X'.card :=
            ndvd_of_ndvd_add_dvd (hcard_split ▸ hndvd) hp_orb
          obtain ⟨x', hx'_X', hx'_fixed⟩ :=
            ih hα' p m hp hGcard hndvd' hX'_len
          exact ⟨x', (List.mem_filter.mp hx'_X').1, hx'_fixed⟩

    /-! # § 10. Main theorem -/

    /-- If H and K are p-Sylow subgroups of G (with |G| = p^n · k, p ∤ k),
        then ∃ r ∈ G such that r⁻¹Hr ⊆ K. -/
    theorem coset_conjugate_exists
        (G : FinGroup ℕ₀) (H K : Subgroup G) (p n k : ℕ₀)
        (hp     : Prime p)
        (hH_card : H.carrier.card = pow p n)
        (hK_card : K.carrier.card = pow p n)
        (hGK    : mul (pow p n) k = G.carrier.card)
        (hndvd  : ¬ p ∣ k) :
        ∃ r, r ∈ G.carrier.elems ∧
          ∀ h, h ∈ H.carrier.elems → G.op (G.inv r) (G.op h r) ∈ K.carrier.elems := by
      have hpn_ne : pow p n ≠ 𝟘 := pow_prime_ne_zero hp n
      have hheads_card : (cosetHeadsSet G K).card = k :=
        cosetHeadsSet_card_eq_index hK_card hGK hpn_ne
      have hndvd_heads : ¬ p ∣ (cosetHeadsSet G K).card :=
        hheads_card ▸ hndvd
      have hH_fin_card : (subgroupFinGroup H).carrier.card = pow p n := hH_card
      obtain ⟨r, hr_heads, hr_fixed⟩ :=
        pgroup_fixed_point (cosetHeadsSet G K).elems.length
          (cosetAction G H K) p n hp hH_fin_card hndvd_heads (Nat.le_refl _)
      have hr_G : r ∈ G.carrier.elems := cosetHeadsSet_subset_G hr_heads
      refine ⟨r, hr_G, ?_⟩
      intro h hh_H
      have hh_G  : h ∈ G.carrier.elems := H.subset h hh_H
      have hhr_G : G.op h r ∈ G.carrier.elems := op_mem G hh_G hr_G
      -- Fixed: (cosetAction G H K).act h r = r, i.e. cosetRep G K (G.op h r) = r
      have hrep_hr : cosetRep G K (G.op h r) = r := by
        have hfixed := hr_fixed h hh_H
        unfold cosetAction cosetActFun at hfixed
        exact hfixed
      -- r ∈ classOf(G.op h r)
      have hrep_in_hr : r ∈ ((cosetEquivRel G K).classOf (G.op h r)).elems := by
        have hcoset := @cosetRep_in_classOf G K (G.op h r) hhr_G
        rw [hrep_hr] at hcoset
        exact hcoset
      -- classOf(G.op h r) = classOf r
      have h_eq : (cosetEquivRel G K).classOf (G.op h r) = (cosetEquivRel G K).classOf r := by
        apply FSet.eq_of_mem_iff
        intro z
        exact (cosetEquivRel G K).mem_classOf_iff_of_rel (G.op h r) r z hhr_G hr_G
          ((cosetEquivRel G K).rel_of_mem_classOf (G.op h r) r hrep_in_hr)
      -- G.op h r ∈ classOf r
      have hhr_in_r : G.op h r ∈ ((cosetEquivRel G K).classOf r).elems := by
        rw [← h_eq]
        exact (cosetEquivRel G K).classOf_nonempty_of_mem (G.op h r) hhr_G
      -- cosetRel G K r (G.op h r) → G.inv r · G.op h r ∈ K
      exact (cosetEquivRel G K).rel_of_mem_classOf r (G.op h r) hhr_in_r

  end CosetAction
end Peano

export Peano.CosetAction (
  coset_conjugate_exists
)
