/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano/PeanoNatAdd.lean

import Peano.PeanoNatLib
import Peano.PeanoNatAxioms
import Peano.PeanoNatStrictOrder
import Peano.PeanoNatOrder
import Peano.PeanoNatMaxMin
import Peano.PeanoNatWellFounded


namespace Peano
  open Peano


  namespace Add
      open Add
      open Peano.Axioms
      open Peano.StrictOrder
      open Peano.Order
      open Peano.MaxMin
      open Peano.WellFounded

    def add (n m : ℕ₀) : ℕ₀ :=
      match m with
      | 𝟘 => n
      | σ m' => σ (add n m')

    instance : Add ℕ₀ where
      add := Add.add

    def add_l (n m : ℕ₀) : ℕ₀ :=
      match n with
      | 𝟘 => m
      | σ n' => σ (add n' m)

    theorem add_zero (n : ℕ₀) : add n 𝟘 = n
      := by rfl

    theorem add_zero_l (n : ℕ₀) :
        add_l n 𝟘 = n
      := by
        induction n with
        | zero =>
          rfl
        | succ n' ih =>
          simp [add_l, add_zero]

    theorem zero_add (n : ℕ₀) : add 𝟘 n = n
      := by
        induction n with
        | zero => simp [add]
        | succ n' ih => simp [add]; exact ih

    theorem zero_add_l (n : ℕ₀) :
        add_l 𝟘 n = n
            := by
              induction n with
              | zero =>
                simp [add_l]
              | succ n' ih =>
                calc
                  add_l 𝟘 (σ n') = σ (add_l 𝟘 n') := by
                    simp [add_l]
                  _ = σ n' := rfl

    theorem add_zero_eq_add_l_zero (n : ℕ₀) :
      add n 𝟘 = add_l n 𝟘
        := by
          induction n with
          | zero => rfl
          | succ n' ih =>
            simp [add, add_l]

    theorem add_one (n : ℕ₀) : add n 𝟙 = σ n
      := by
        induction n with
        | zero => rfl
        | succ n' ih => unfold add; rw [<-ih]; rfl

    theorem add_one_l (n : ℕ₀) : add_l n 𝟙 = σ n
      := by
        induction n with
        | zero =>
            rfl
        | succ n' ih => -- ih: add_l n' 𝟙 = σ n'
            calc
              add_l (σ n') 𝟙 = σ (add n' 𝟙) := by simp [add_l]
              _ = σ (σ n') := by rw [add_one]

    theorem one_add (n : ℕ₀) : add 𝟙 n = σ n
      := by
        induction n with
        | zero => rfl
        | succ n' ih => unfold add; rw [<-ih]

    theorem one_add_l (n : ℕ₀) : add_l 𝟙 n = σ n
      := by
        induction n with
        | zero =>
            simp [add_l, one, add_zero]
        | succ n' ih =>
            calc
              add_l 𝟙 (σ n') = σ (add 𝟘 (σ n')) := by simp [add_l, one]
              _ = σ (σ (add 𝟘 n')) := by rfl
              _ = σ (σ n') := by simp [zero_add]

    theorem add_one_eq_add_l_one (n : ℕ₀) :
      add n 𝟙 = add_l n 𝟙
        := by
          induction n with
          | zero => rfl
          | succ n' ih =>
            calc
              add (σ n') (σ 𝟘) = σ (add (σ n') 𝟘) := by rfl
              _ = σ (σ n') := by rw [add_zero]
              _ = σ (add_l (σ n') 𝟘) := by simp [add_zero_l]

    theorem add_succ (n m : ℕ₀) :
      add n (σ m) = σ (add n m)
        := by rfl

    theorem add_succ_l (n m : ℕ₀) :
      add_l n (σ m) = σ (add_l n m)
        := by
        cases n with
        | zero =>
          simp [add_l]
        | succ n' =>
          simp [add_l, add_succ]

    theorem succ_add (n m : ℕ₀) :
      add (σ n) m = σ (add n m)
        := by
        induction m with
        | zero => rw [add, add]
        | succ n' ih => simp [add]; rw [ih]

    theorem succ_add_l (n m : ℕ₀) :
      add_l (σ n) m = σ (add_l n m)
        := by
      unfold add_l
      cases n with
      | zero =>
        calc
          σ (add 𝟘 m) = σ m := by rw [zero_add]
          _ = σ (
                  match 𝟘 with
                  | 𝟘 => m
                  | σ n' => σ (add n' m)
                )
                := by simp
      | succ n' =>
        dsimp
        rw [succ_add n' m]

    theorem add_succ_eq_add_l_succ (n m: ℕ₀) :
      add n (σ m) = add_l n (σ m)
        := by
        induction n with
        | zero => simp [add, add_l, zero_add]
        | succ n' ih =>
          calc
            add (σ n') (σ m) = σ (add (σ n') m)
                := by rw [add_succ]
            _ = σ (σ (add n' m))
                := by rw [succ_add]
            _ = σ (add n' (σ m))
                := by rw [add_succ]
            _ = σ (add_l n' (σ m))
                := by rw [ih]
            _ = add_l (σ n') (σ m)
                := by rw [succ_add_l]

    theorem add_eq_add_l (n m : ℕ₀) :
      add n m = add_l n m
        := by
          induction n with
          | zero => rw [zero_add, zero_add_l]
          | succ n' ih =>
            calc
              add (σ n') m = σ (add n' m) := by rw [succ_add]
              _ = σ (add_l n' m) := by rw [ih]
              _ = add_l (σ n') m := by rw [succ_add_l]

    theorem eq_fn_add_add_l :
      ∀ (n m : ℕ₀), add n m = add_l n m
        := by
          intro n m
          exact add_eq_add_l n m

    theorem add_comm (n m : ℕ₀) :
      add n m = add m n
        := by
        induction n with
        | zero =>
          rw [zero_add]
          rw [add_zero]
        | succ n' ih =>
          rw [succ_add]
          rw [ih]
          exact add_succ m n'

    theorem add_assoc (n m k : ℕ₀) :
      add n (add m k) = add (add n m) k
        := by
        induction n with
        | zero =>
          rw [zero_add]
          rw [zero_add]
        | succ n' ih =>
          rw [succ_add]
          rw [ih]
          rw [succ_add]
          rw [succ_add]

    theorem add_le (a b c : ℕ₀) :
      Le a b → Le a (add b c)
        := by
      intro h_le
      induction c with
      | zero => rw [add_zero]; exact h_le
      | succ c' ih =>
          exact
            le_trans a (add b c') (add b (σ c'))
                     ih (le_succ_self (add b c'))

    theorem add_le_r (a b c : ℕ₀) :
      Le a b → Le a (add c b)
        := by
        intro h_le
        have h_le_add : Le a (add b c) :=
          (add_le a b c) h_le
        rw [add_comm b c] at h_le_add
        exact h_le_add

    theorem le_self_add_r (a b : ℕ₀) :
      Le a (add a b)
        := by
        induction b with
        | zero =>
          rw [add_zero]
          exact le_refl a
        | succ b' ih =>
            have h_le_a_than_add_a_b' : Le a (add a b') := ih
            have h_le_a_than_s_add_a_b' : Le a (σ (add a b')) := by
              exact le_trans a (add a b') (σ (add a b')) ih (le_succ_self (add a b'))
            have h_le_a_than_add_a_s_b' : Le a (add a (σ b')) := by
              rw [add_succ]
              exact h_le_a_than_s_add_a_b'
            exact h_le_a_than_add_a_s_b'

    theorem le_self_add_r_forall (a : ℕ₀) :
      ∀ (b : ℕ₀), Le a (add a b)
        := by
        intro (b : ℕ₀)
        induction b with
        | zero =>
          rw [add_zero]
          exact le_refl a
        | succ b' ih =>
            have h_le_a_than_add_a_b' : Le a (add a b') := ih
            have h_le_a_than_s_add_a_b' : Le a (σ (add a b')) := by
              exact le_trans a (add a b') (σ (add a b')) ih (le_succ_self (add a b'))
            have h_le_a_than_add_a_s_b' : Le a (add a (σ b')) := by
              rw [add_succ]
              exact h_le_a_than_s_add_a_b'
            exact h_le_a_than_add_a_s_b'

    theorem lt_self_add_r (a b : ℕ₀) (h_b_neq_0 : b ≠ 𝟘):
      Lt a (add a b)
        := by
          induction b with
          | zero =>
            rw [add_zero]
            exfalso
            exact h_b_neq_0 rfl
          | succ b' ih =>
              cases b' with
              | zero =>
                rw [add_succ, add_zero]
                exact lt_succ_self a
              | succ b'' =>
                have h_b'_neq_0 : σ b'' ≠ 𝟘 := succ_neq_zero b''
                have h_lt_a_than_add_a_b' : Lt a (add a (σ b'')) := ih h_b'_neq_0
                have h_lt_a_than_s_add_a_b' : Lt a (σ (add a (σ b''))) := by
                  exact lt_trans a (add a (σ b'')) (σ (add a (σ b''))) h_lt_a_than_add_a_b' (lt_succ_self (add a (σ b'')))
                have h_lt_a_than_add_a_s_b' : Lt a (add a (σ (σ b''))) := by
                  rw [add_succ]
                  exact h_lt_a_than_s_add_a_b'
                exact h_lt_a_than_add_a_s_b'

    theorem lt_self_add_r_forall (a : ℕ₀) :
      ∀ (b : ℕ₀) , b ≠ 𝟘 → Lt a (add a b)
        := by
          intro (b : ℕ₀) h_b_neq_0
          induction b with
          | zero =>
            rw [add_zero]
            exfalso
            exact h_b_neq_0 rfl
          | succ b' ih =>
              cases b' with
              | zero =>
                rw [add_succ, add_zero]
                exact lt_succ_self a
              | succ b'' =>
                have h_b'_neq_0 : σ b'' ≠ 𝟘 := succ_neq_zero b''
                have h_lt_a_than_add_a_b' : Lt a (add a (σ b'')) := ih h_b'_neq_0
                have h_lt_a_than_s_add_a_b' : Lt a (σ (add a (σ b''))) := by
                  exact lt_trans a (add a (σ b'')) (σ (add a (σ b''))) h_lt_a_than_add_a_b' (lt_succ_self (add a (σ b'')))
                have h_lt_a_than_add_a_s_b' : Lt a (add a (σ (σ b''))) := by
                  rw [add_succ]
                  exact h_lt_a_than_s_add_a_b'
                exact h_lt_a_than_add_a_s_b'

    theorem le_self_add_l (a b : ℕ₀) :
      Le a (add b a)
        := by
          have h_add_b_a_eq_add_a_b : add b a = add a b
            := by rw [add_comm]
          rw [h_add_b_a_eq_add_a_b]
          exact le_self_add_r a b

    theorem le_self_add_l_forall (a : ℕ₀) :
      ∀ (b : ℕ₀), Le a (add b a)
        := by
          intro (b : ℕ₀)
          have h_add_b_a_eq_add_a_b : add b a = add a b
            := by rw [add_comm]
          rw [h_add_b_a_eq_add_a_b]
          exact le_self_add_r a b

    theorem lt_self_add_l (a b : ℕ₀) (h_b_neq_0 : b ≠ 𝟘) :
      Lt a (add b a)
        := by
          rw [add_comm b a]
          exact lt_self_add_r a b h_b_neq_0

    theorem lt_self_add_l_forall (a : ℕ₀) :
      ∀ (b : ℕ₀), b ≠ 𝟘 → Lt a (add b a)
        := by
          intro (b : ℕ₀) h_b_neq_0
          rw [add_comm b a]
          exact lt_self_add_r a b h_b_neq_0

    theorem add_lt (n m k : ℕ₀) :
      Lt n m → Lt n (add m k)
        := by
        intro h_lt
        induction k with
        | zero =>
          rw [add_zero]
          exact h_lt
        | succ k' ih =>
          rw [add_succ]
          exact lt_succ n (add m k') ih

    theorem add_cancelation (n m k : ℕ₀) :
      add n m = add n k → m = k
        := by
          intro h_eq
          induction n with
          | zero =>
            rw [zero_add, zero_add] at h_eq
            exact h_eq
          | succ n' ih =>
            rw [succ_add, succ_add] at h_eq
            injection h_eq with h_m_eq_k
            exact ih h_m_eq_k

    theorem cancelation_add (n m k : ℕ₀) :
      add m n = add k n → m = k
        := by
          intro h_eq
          induction n with
          | zero =>
            rw [add_zero, add_zero] at h_eq
            exact h_eq
          | succ n' ih =>
            rw [add_succ, add_succ] at h_eq
            injection h_eq with h_m_eq_k
            exact ih h_m_eq_k

    theorem add_lt_cancelation (n m k : ℕ₀) :
      add n m < add n k → m < k
        := by
          intro h_lt
          induction n with
          | zero =>
            rw [zero_add, zero_add] at h_lt
            exact h_lt
          | succ n' ih =>
            rw [succ_add, succ_add] at h_lt
            exact ih h_lt

    theorem add_le_cancelation (n m k : ℕ₀) :
      (add n m) ≤ (add n k) → m ≤ k
        := by
          intro h_le
          induction n with
          | zero =>
              rw [zero_add, zero_add] at h_le;
              exact h_le
          | succ n' ih =>
              rw [succ_add, succ_add] at h_le
              apply ih
              exact
                (
                  succ_le_succ_iff (add n' m) (add n' k)
                ).mp h_le

    theorem add_eq_zero_iff (a b : ℕ₀) :
      add a b = 𝟘 ↔ a = 𝟘 ∧ b = 𝟘
        := by
          constructor
          · intro h_eq
            induction a with
            | zero =>
              rw [zero_add] at h_eq;
              exact ⟨rfl, h_eq⟩
            | succ a' ih =>
              rw [succ_add] at h_eq;
              have h_contradiction : σ (add a' b) = 𝟘
                := h_eq
              have h_absurd : σ (add a' b) ≠ 𝟘
                := succ_neq_zero (add a' b)
              contradiction
          · intro ⟨h_a_eq_zero, h_b_eq_zero⟩;
            rw [h_a_eq_zero, h_b_eq_zero];
            rfl

    theorem le_then_le_add_zero (a b : ℕ₀) :
      Le a b → Le (add a 𝟘) (add b 𝟘)
        := by
          intro h_le
          induction b with
          | zero =>
              rw [add_zero, add_zero];
              exact h_le
          | succ b' ih =>
              rw [add_zero, add_zero]
              exact h_le

    theorem le_then_le_add_one (a b : ℕ₀) :
      Le a b → Le (add a 𝟙) (add b 𝟙)
        := by
          intro h_le
          induction b with
          | zero =>
              rw [add_one, add_one]
              apply (succ_le_succ_iff _ _).mpr
              exact h_le
          | succ b' ih =>
              rw [add_one, add_one]
              apply (succ_le_succ_iff _ _).mpr
              exact h_le

    theorem le_add_then_le_add_succ (a b n: ℕ₀) :
      Le (add a n) (add b n) → Le (add a (σ n)) (add b (σ n))
        := by
          intro h_le
          induction n with
          | zero =>
              rw [add_zero, add_zero] at h_le
              rw [add_succ, add_succ]
              rw [add_zero, add_zero]
              apply (succ_le_succ_iff a b).mpr
              exact h_le
          | succ n' ih =>
              rw [add_succ, add_succ]
              apply
                (
                  succ_le_succ_iff (add a (σ n')) (add b (σ n'))
                ).mpr
              exact h_le

   theorem le_then_le_add (a b c: ℕ₀) :
     Le a b → Le (add a c) (add b c)
       := by
       intro h_le
       induction c with
       | zero =>
           rw [add_zero, add_zero]
           exact (le_then_le_add_zero a b h_le)
       | succ c' ih =>
           rw [add_succ, add_succ]
           apply (succ_le_succ_iff _ _).mpr
           exact ih

    theorem le_add_zero_then_le (a b : ℕ₀) :
      Le (add a 𝟘) (add b 𝟘) → Le a b
        := by
          intro h_le
          rw [add_zero, add_zero] at h_le
          exact h_le

    theorem le_add_one_then_le (a b : ℕ₀) :
      Le (add a 𝟙) (add b 𝟙) → Le a b
        := by
          intro h_le
          rw [add_one, add_one] at h_le
          exact (succ_le_succ_iff a b).mp h_le

    theorem le_add_r_add_r_then_le (a b n: ℕ₀) :
      Le (add a n) (add b n) → (Le a b)
        := by
         intro h_le_add_implies_succ
         induction n with
         | zero =>
             rw [add_zero, add_zero] at h_le_add_implies_succ
             exact h_le_add_implies_succ
         | succ n' ih =>
             rw [add_succ, add_succ] at h_le_add_implies_succ
             have h_base_le : Le (add a n') (add b n')
                 := (succ_le_succ_iff _ _).mp
                       h_le_add_implies_succ
             exact ih h_base_le

    theorem le_add_l_add_l_then_le (a b n: ℕ₀) :
      Le (add n a) (add n b) → (Le a b)
        := by
          intro h_le_add_implies_succ
          induction n with
          | zero =>
              rw [zero_add, zero_add] at h_le_add_implies_succ
              exact h_le_add_implies_succ
          | succ n' ih =>
              rw [succ_add, succ_add] at h_le_add_implies_succ
              have h_base_le : Le (add n' a) (add n' b)
                  := (succ_le_succ_iff _ _).mp
                        h_le_add_implies_succ
              exact ih h_base_le

    theorem le_then_le_add_r_add_r_then_le (a b n: ℕ₀) :
      Le a b → Le (add a n) (add b n)
        := by
          intro h_le
          induction n with
          | zero =>
              rw [add_zero, add_zero]
              exact h_le
          | succ n' ih =>
              rw [add_succ, add_succ]
              apply (succ_le_succ_iff _ _).mpr
              exact ih

    theorem le_then_le_add_l_add_l_then_le (a b n: ℕ₀) :
        Le a b → Le (add n a) (add n b)
            := by
          intro h_le
          induction n with
          | zero =>
              rw [zero_add, zero_add]
              exact h_le
          | succ n' ih =>
              rw [succ_add, succ_add]
              apply (succ_le_succ_iff _ _).mpr
              exact ih

    theorem le_iff_le_add_r_add_r_forall (a b: ℕ₀) :
      ∀ (n : ℕ₀), Le a b ↔ Le (add a n) (add b n)
        := by
          intro n
          constructor
          · intro h_le
            exact le_then_le_add_r_add_r_then_le a b n h_le
          · intro h_le_add
            exact le_add_r_add_r_then_le a b n h_le_add

    theorem le_iff_le_add_l_add_l_forall (a b: ℕ₀) :
      ∀ (n : ℕ₀), Le a b ↔ Le (add n a) (add n b)
        := by
          intro n
          constructor
          · intro h_le
            exact le_then_le_add_l_add_l_then_le a b n h_le
          · intro h_le_add
            exact le_add_l_add_l_then_le a b n h_le_add

    theorem le_add_then_le (a b c: ℕ₀) :
      Le (add a c) (add b c) → Le a b
        := by
          intro h_le_add
          induction c with
          | zero =>
              rw [add_zero, add_zero] at h_le_add
              exact h_le_add
          | succ c' ih =>
              rw [add_succ, add_succ] at h_le_add
              have h_base_le : Le (add a c') (add b c')
                  := (succ_le_succ_iff _ _).mp h_le_add
              exact ih h_base_le

    theorem le_iff_le_add(a b c: ℕ₀) :
      Le a b ↔ Le (add a c) (add b c)
        := by
          constructor
          · intro h_le
            exact le_then_le_add a b c h_le
          · intro h_le_add
            exact le_add_then_le a b c h_le_add

    theorem le_iff_le_add_forall(a b : ℕ₀) :
      ∀ (k : ℕ₀), Le a b ↔ Le (add a k) (add b k)
        := by
          intro k
          constructor
          · intro h_le
            exact le_then_le_add a b k h_le
          · intro h_le_add
            exact le_add_then_le a b k h_le_add

    theorem le_add_cancel (a b : ℕ₀) :
        ∀ (k: ℕ₀), Le a b ↔ Le (add a k) (add b k)
          := by
          exact le_iff_le_add_forall a b

    theorem le_then_exists_zero_add (a : ℕ₀) :
      Le a (add a 𝟘) → Le a a
        := by
          intro h_le
          induction a with
          | zero =>
              rw [add_zero] at h_le
              exact Or.inr (Eq.refl 𝟘)
          | succ a' ih =>
              rw [add_zero] at h_le
              exact h_le

    theorem le_self_add (a p : ℕ₀) : Le a (add a p) := by
      induction p with
      | zero =>
        rw [add_zero]
        exact le_refl a
      | succ p' ih =>
        rw [add_succ]
        apply le_succ
        exact ih

    theorem τ_σ (n : ℕ₀) : τ (σ n) = n
      := by
        induction n with
        | zero => rfl
        | succ n' ih =>
         calc
          τ (σ (σ n')) = σ (τ (σ n')) := by rfl
          _ = σ n' := by rw [ih]

    theorem add_σn_m_eq_add_n_σm (n m : ℕ₀):
     add n (σ m) = σ (add n m)
       := by
       induction n with
       | zero =>
         rw [zero_add]
         rw [zero_add]
       | succ n' ih_n' =>
         rw [succ_add]
         rw [ih_n']
         rw [← succ_add]

    theorem add_σn_m_eq_σadd_n_m (n m : ℕ₀):
     add (σ n) m = σ (add n m)
       := by
       induction m with
       | zero =>
         rw [add_zero]
         rw [add_zero]
       | succ m' ih_m' =>
         rw [add_succ]
         rw [ih_m']
         rw [← add_succ]

    theorem σadd_n_m_eq_add_n_σm (n m : ℕ₀):
      σ (add n m) = add (σ n) m
        := by
          calc
            σ (add n m) = σ (add m n ) := by rw [add_comm]
            _ = add m (σ n) := by rw [add_σn_m_eq_add_n_σm]
            _ = add (σ n) m := by rw [add_comm]


    theorem τadd_n_m_eq_add_τn_m (n m : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) :
      τ (add n m) = add (τ n) m
        := by
          induction n with
          | zero =>
            exfalso
            exact h_n_neq_0 rfl
          | succ n' ih_n' =>
            calc
              τ (add (σ n') m) = τ (σ (add n' m)) := by rw [add_σn_m_eq_σadd_n_m]
              _ = add n' m := by rw [τ_σ]
              _ = add (τ (σ n')) m := by rw [τ_σ]

    theorem τadd_n_m_eq_add_n_τm (n m : ℕ₀) (h_m_neq_0 : m ≠ 𝟘) :
      τ (add n m) = add n (τ m)
        := by
      induction m with
      | zero =>
        exfalso
        exact h_m_neq_0 rfl
      | succ m' ih_m' =>
        calc
          τ (add n (σ m')) = τ (σ (add n m')) := by rw [add_σn_m_eq_add_n_σm]
          _ = add n m' := by rw [τ_σ]
          _ = add n (τ (σ m')) := by rw [τ_σ]

    theorem add_τn_m_eq_add_n_τm (n m : ℕ₀)  (h_n_neq_0 : n ≠ 𝟘) (h_m_neq_0 : m ≠ 𝟘) :
      add (τ n) m = add n (τ m)
        := by
      calc
        add (τ n) m = τ (add n m) := by rw [← τadd_n_m_eq_add_τn_m n m h_n_neq_0]
        _ = add n (τ m) := by rw [τadd_n_m_eq_add_n_τm n m h_m_neq_0]

    theorem le_self_add_forall (a : ℕ₀) :
      ∀ (p : ℕ₀), Le a (add a p)
        := by
      intro p
      induction p with
      | zero =>
        rw [add_zero]
        exact le_refl a
      | succ p' ih =>
        rw [add_succ]
        apply le_succ
        exact ih

    theorem lt_add_succ (a p : ℕ₀) :
      Lt a (σ (add a p))
        := by
        induction p with
        | zero =>
          rw [add_zero]
          exact lt_succ_self a
        | succ p' ih =>
          rw [add_succ]
          apply lt_trans a (σ (add a p')) (σ (σ (add a p')))
          · exact ih
          · exact lt_succ_self (σ (add a p'))

    theorem le_then_exists_add (a b : ℕ₀) :
      Le a b → ∃ (p : ℕ₀), b = add a p := by
        intro h_le
        induction b generalizing a with
        | zero =>
          have h_a_eq_zero: a = 𝟘
            := le_zero_eq_wp h_le
          exists 𝟘
          rw [h_a_eq_zero]
          rw [add_zero]
        | succ b' ih =>
          have h_cases :
              Le a b' ∨ a = σ b'
                  := le_succ_then_le_or_eq a b' h_le
          cases h_cases with
          | inl h_a_lt_b' =>
            obtain ⟨p_val, h_b_prime_eq_add⟩ :
                ∃ p, b' = add a p
                    := ih a h_a_lt_b'
            exists (σ p_val)
            rw [h_b_prime_eq_add]
            rw [← add_succ a p_val]
          | inr h_a_eq_b' =>        -- Case 2: a = b'
            exists 𝟘
            rw [h_a_eq_b']
            rw [add_zero]

    theorem le_then_exists_add_wp {a b : ℕ₀} (h_le_ab: Le a b) :
      ∃ (p : ℕ₀), b = add a p := by
        have h_exists_add := le_then_exists_add a b h_le_ab
        exact h_exists_add


    theorem lt_then_exists_add_succ (a b : ℕ₀) :
      Lt a b → ∃ (p : ℕ₀), b = add a (σ p) := by
        intro h_lt
        induction b generalizing a with
        | zero =>
          exfalso -- We want to prove False
          exact lt_zero a h_lt
        | succ b' ih =>
          have h_cases :
              Lt a b' ∨ a = b'
                  := (
                          lt_succ_iff_lt_or_eq a b'
                  ).mp h_lt
          cases h_cases with
          | inl h_a_lt_b' =>
            obtain ⟨p_val, h_b_prime_eq_add⟩ :
                ∃ p, b' = add a (σ p)
                    := ih a h_a_lt_b'
            exists (σ p_val)
            rw [h_b_prime_eq_add]
            rw [add_succ a (σ p_val)]
          | inr h_a_eq_b' =>        -- Case 2: a = b'
            exists 𝟘
            rw [h_a_eq_b']
            rw [add_succ b' 𝟘]
            rw [add_zero b']

    theorem lt_then_exists_add_succ_wp {a b : ℕ₀} (h_lt_ab: Lt a b) :
      ∃ (p : ℕ₀), b = add a (σ p) := by
        have h_exists_add := lt_then_exists_add_succ a b h_lt_ab
        exact h_exists_add

    theorem le_iff_exists_add (a b: ℕ₀) :
        (Le a b) ↔ (∃ (p : ℕ₀), b = add a p)
        := by
          constructor
          · intro h_le
            induction b generalizing a with
            | zero =>
              cases a with
              | zero =>
                exists 𝟘
              | succ a' =>
                exfalso
                apply lt_zero (σ a')
                exact lt_of_le_of_ne (σ a') 𝟘
                      h_le (succ_neq_zero a')
            | succ b' ih =>
              cases (le_succ_iff_le_or_eq a b').mp h_le with
              | inl h_a_le_b' => -- Caso Le a b'
                obtain ⟨p_val, h_b_prime_eq_add⟩
                    := ih a h_a_le_b'
                exists (σ p_val)
                rw [h_b_prime_eq_add, add_succ a p_val]
              | inr h_a_eq_succ_b' => -- Caso a = σ b'
                exists 𝟘
                rw [h_a_eq_succ_b', add_zero]
          · intro ⟨p, h_eq⟩
            rw [h_eq]
            exact le_self_add a p

    theorem lt_iff_exists_add_succ (a b : ℕ₀) :
      (Lt a b) ↔ (∃ (p : ℕ₀), b = add a (σ p))
        := by
          constructor
          · intro h_lt
            obtain ⟨p, h_eq⟩ :
              ∃ p, b = add a (σ p)
                := lt_then_exists_add_succ a b h_lt
            exists p
          · intro ⟨p, h_eq⟩
            rw [h_eq]
            exact lt_add_succ a p

    theorem isomorph_Ψ_add (n m : ℕ₀) :
      Ψ (add n m) = Nat.add (Ψ n) (Ψ m)
        := by
      induction m with
      | zero =>
        calc
          Ψ (add n 𝟘) = Ψ n := by
            rw [add_zero]
          _ = Nat.add (Ψ n) 0 := by
            rfl
      | succ m' ih_m' =>
        calc
          Ψ (add n (σ m')) = Ψ (σ (add n m')) := by
            rw [add_succ]
          _ = Nat.succ (Ψ (add n m')) := by
            rw [Ψ_σ_eq_σ_Λ]
          _ = Nat.succ (Nat.add (Ψ n) (Ψ m')) := by
            rw [ih_m']

    theorem isomorph_Λ_add (n m : Nat) :
      Λ (Nat.add n m) = add (Λ n) (Λ m)
      := by
      induction m with
      | zero =>
        calc
          Λ (Nat.add n 0) = Λ n := by
            rfl
          _ = add (Λ n) 𝟘 := by
            rfl
      | succ m' ih_m' =>
        calc
          Λ (Nat.add n (Nat.succ m')) =
            Λ (Nat.succ (Nat.add n m')) := by
              rfl
          _ = σ (Λ (Nat.add n m')) := by
            rw [Λ_σ_eq_σ_Ψ]
          _ = σ (add (Λ n) (Λ m')) := by
            rw [ih_m']
          _ = add (Λ n) (σ (Λ m')) := by
            rw [add_succ]

    theorem add_lt_add_left_iff (k a b : ℕ₀) :
        Lt (add k a) (add k b) ↔ Lt a b
        := by
          constructor
          · intro h_lt
            induction k with
            | zero =>
              rw [zero_add, zero_add] at h_lt
              exact h_lt
            | succ k' ih =>
              rw [succ_add, succ_add] at h_lt
              exact ih h_lt
          · intro h_a_lt_b
            obtain ⟨p, h_b_eq_add_a_sp⟩
                := (
                       lt_iff_exists_add_succ a b
                ).mp h_a_lt_b
            rw [h_b_eq_add_a_sp]
            rw [add_comm k (add a (σ p))]
            rw [← add_assoc a (σ p) k]
            rw [add_comm (σ p) k]
            rw [add_assoc a k (σ p)]
            rw [add_comm a k]
            exact lt_add_succ (add k a) p

    theorem lt_iff_add_cancel (a b : ℕ₀) :
        ∀ (k: ℕ₀), Lt (add a k) (add b k) ↔ Lt a b
          := by
            intro k
            calc
              Lt (add a k) (add b k) ↔ Lt (add k a) (add k b) := by rw [add_comm a k, add_comm b k]
              _ ↔ Lt a b := by rw [add_lt_add_left_iff]

    theorem lt_iff_add_lt :
        ∃ (m : ℕ₀), ∀ (x y : ℕ₀), add m x = add m y → x = y
            := by
        exists 𝟘
        intro x y h_eq
        induction x with
        | zero =>
          rw [zero_add] at h_eq
          rw [zero_add] at h_eq
          exact h_eq
        | succ x' ih =>
          rw [zero_add, zero_add] at h_eq
          cases y with
          | zero =>
            have h_contra := succ_neq_zero x'
            contradiction
          | succ y' =>
            injection h_eq with h_x_eq_y
            rw [h_x_eq_y]

    theorem τadd_n_σm_eq_add_n_m (n m : ℕ₀) :
       τ (add n (σ m)) = add n m
         := by
      induction n with
      | zero =>
        rw [zero_add]
        rw [τ_σ]
        rw [zero_add]
      | succ n' ih_n' =>
        calc
          τ (add (σ n') (σ m)) = τ (σ (add n' (σ m))) := by rw [succ_add]
          _ = add n' (σ m) := by rw [τ_σ]
          _ = σ (add n' m) := by rw [add_succ]
          _ = add (σ n') m := by rw [succ_add]

    theorem τadd_σn_m_eq_add_n_m (n m : ℕ₀) :
      τ (add (σ n) m) = add n m
         := by
      induction m with
      | zero =>
        rw [add_zero]
        rw [τ_σ]
        rw [add_zero]
      | succ m' ih_m' =>
        calc
          τ (add (σ n) (σ m')) = τ (σ (add (σ n) m')) := by rw [add_succ]
          _ = add (σ n) m' := by rw [τ_σ]
          _ = σ (add n m') := by rw [succ_add]
          _ = add n (σ m') := by rw [add_succ]


    theorem lt_n_add_n_σm (n m : ℕ₀) :
      Lt n (add n (σ m))
        := by
      induction m with
      | zero =>
        rw [add_succ, add_zero]
        exact lt_succ_self n
      | succ m' ih_m' =>
        rw [add_succ]
        exact lt_trans n (add n (σ m')) (σ (add n (σ m'))) (ih_m') (lt_succ_self (add n (σ m')))

    theorem lt_add_of_pos_right {a b : ℕ₀} (h_b_pos : Lt 𝟘 b)
        : Lt a (add a b)
            := by
      induction b with
      | zero =>
        exfalso
        exact nlt_self 𝟘 h_b_pos
      | succ b'=>
        exact lt_n_add_n_σm a b'

    theorem le_add_compat (a b c d: ℕ₀) :
      Le a b → Le c d → Le (add a c) (add b d)
        := by
      intro h_ab h_cd
      have h₁ : Le (add a c) (add b c) := le_then_le_add a b c h_ab
      have h₂ : Le (add b c) (add b d) := le_then_le_add_l_add_l_then_le c d b h_cd
      exact le_trans (add a c) (add b c) (add b d) h₁ h₂

    theorem le_add_compat_wp {a b c d: ℕ₀} (h_le_ab: Le a b) (h_le_cd : Le c d) :
      Le (add a c) (add b d)
        := by
      exact le_add_compat a b c d h_le_ab h_le_cd

    theorem lt_le_then_lt_add_compat (a b c d: ℕ₀) :
      Lt a b → Le c d → Lt (add a c) (add b d)
        := by
      intro h_lt_ab h_le_cd
      rcases (Le.eq_def c d).mp h_le_cd with h_lt_cd | h_c_eq_d
      -- Case 1: Lt c d
      · have h1 : Lt (add a c) (add b c) := by
          exact (lt_iff_add_cancel a b c).mpr h_lt_ab
        have h2 : Lt (add b c) (add b d) :=
          (add_lt_add_left_iff b c d).mpr h_lt_cd
        exact lt_trans (add a c) (add b c) (add b d) h1 h2
      -- Case 2: c = d
      · rw [←h_c_eq_d]
        rw [add_comm a c, add_comm b c] -- Lt (c+a) (c+b)
        exact (add_lt_add_left_iff c a b).mpr h_lt_ab

    theorem lt_le_then_add_add_compat_wp {a b c d: ℕ₀} (h_lt_ab: Lt a b) (h_le_cd : Le c d) :
      Lt (add a c) (add b d)
        := by
      exact lt_le_then_lt_add_compat a b c d h_lt_ab h_le_cd

    theorem le_lt_then_lt_add_compat (a b c d: ℕ₀) :
      Le a b → Lt c d → Lt (add a c) (add b d)
        := by
      intro h_le_ab h_lt_cd
      rcases (Le.eq_def a b).mp h_le_ab with h_a_lt_b_case | h_a_eq_b_case
      -- Case 1: Lt a b (h_a_lt_b_case)
      · have h1 : Lt (add a c) (add a d) := by
          exact (add_lt_add_left_iff a c d).mpr h_lt_cd
        have h2 : Lt (add a d) (add b d) := by
          exact (lt_iff_add_cancel a b d).mpr h_a_lt_b_case
        exact lt_trans (add a c) (add a d) (add b d) h1 h2
      -- Case 2: a = b (h_a_eq_b_case)
      · rw [←h_a_eq_b_case]
        exact (add_lt_add_left_iff a c d).mpr h_lt_cd

    theorem le_lt_then_lt_add_compat_wp {a b c d: ℕ₀} (h_le_ab: Le a b) (h_lt_cd : Lt c d) :
      Lt (add a c) (add b d)
        := by
      exact le_lt_then_lt_add_compat a b c d h_le_ab h_lt_cd

    theorem lt_lt_then_lt_add_compat (a b c d: ℕ₀) :
      Lt a b → Lt c d → Lt (add a c) (add b d)
        := by
      intro h_lt_ab h_lt_cd
      have h1 : Lt (add a c) (add b c) := by
        exact (lt_iff_add_cancel a b c).mpr h_lt_ab
      have h2 : Lt (add b c) (add b d) := by
        exact (add_lt_add_left_iff b c d).mpr h_lt_cd
      exact lt_trans (add a c) (add b c) (add b d) h1 h2

    theorem lt_lt_then_lt_add_compat_wp {a b c d: ℕ₀} (h_lt_ab: Lt a b) (h_lt_cd : Lt c d) :
      Lt (add a c) (add b d)
        := by
      exact lt_lt_then_lt_add_compat  a b c d h_lt_ab h_lt_cd

    theorem le_a_b_then_le_2a_2b (a b : ℕ₀) :
      Le a b → Le (add a a) (add b b)
        := by
      intro h_le
      exact le_add_compat a b a b h_le h_le

    theorem le_a_b_then_le_2a_2b_wp {a b : ℕ₀} (h_le: Le a b) :
      Le (add a a) (add b b)
        := by
      exact le_add_compat a b a b h_le h_le

    theorem lt_a_b_then_lt_2a_2b (a b : ℕ₀) :
      Lt a b → Lt (add a a) (add b b)
        := by
      intro h_lt
      exact lt_lt_then_lt_add_compat a b a b h_lt h_lt

    theorem lt_a_b_then_lt_2a_2b_wp {a b : ℕ₀} (h_lt: Lt a b) :
      Lt (add a a) (add b b)
        := by
      exact lt_lt_then_lt_add_compat a b a b h_lt h_lt

    theorem linear_equation_right (a b : ℕ₀) (h_le_ab: Le a b):
      ∃ (c: ℕ₀), add a c = b ∧ ∀ (c': ℕ₀), add a c' = b → c' = c
        := by
      have h_exists_add := le_then_exists_add a b h_le_ab
      obtain ⟨c, h_eq⟩ := h_exists_add
      exists c
      constructor
      · exact h_eq.symm
      · intro c' h_eq'
        have h_add_eq : add a c = add a c' := by
          rw [← h_eq, h_eq']
        exact (add_cancelation a c c' h_add_eq).symm

    theorem linear_inequation_left (a b : ℕ₀) (h_le_ab: Le a b):
      ∃ (c: ℕ₀), Le (add a c) b ∧ ∀ (c': ℕ₀), Le (add a c') b → Le c' c
        := by
      have h_exists_add := le_then_exists_add a b h_le_ab
      obtain ⟨c, h_eq⟩ := h_exists_add
      exists c
      constructor
      · rw [h_eq]
        exact le_refl (add a c)
      · intro c' h_le_add_c'_b
        rw [h_eq] at h_le_add_c'_b
        have h_comm_c' : Le (add c' a) (add c a) := by
          rw [add_comm c' a, add_comm c a]
          exact h_le_add_c'_b
        exact le_add_then_le c' c a h_comm_c'

    theorem linear_equation_left (a b : ℕ₀) (h_le_ab: Le a b):
      ∃ (c: ℕ₀), add c a = b ∧ ∀ (c': ℕ₀), add c' a = b → c' = c
        := by
      have h_exists_add := le_then_exists_add a b h_le_ab
      obtain ⟨c, h_eq⟩ := h_exists_add
      exists c
      constructor
      · rw [add_comm c a]
        exact h_eq.symm
      · intro c' h_eq'
        have h_add_eq : add c' a = add c a := by
          rw [h_eq', h_eq, add_comm c a]
        exact cancelation_add a c' c h_add_eq

    theorem linear_inequation_right (a b : ℕ₀) (h : Le a b) :
      ∃ c, Le a (add b c) ∧ ∀ c', Le a (add b c') → Le c c'
        := by
      induction b generalizing a with
      | zero =>
        have h_a_zero : a = 𝟘 := (le_zero_eq_zero a).mp h
        exists 𝟘
        constructor
        · rw [h_a_zero, add_zero]
          exact le_refl 𝟘
        · intro c' h_c'
          rw [h_a_zero, zero_add] at h_c'
          exact h_c'
      | succ b' ih =>
        cases a with
        | zero =>
          exists 𝟘
          constructor
          · rw [add_zero]
            exact zero_le (σ b')
          · intro c' h_c'
            exact zero_le c'
        | succ a' =>
          have h_le' : Le a' b' := succ_le_succ_then h
          obtain ⟨c, h_c_eq, h_c_unique⟩ := ih a' h_le'
          exists c
          constructor
          · rw [succ_add]
            apply (succ_le_succ_iff a' (add b' c)).mpr
            exact h_c_eq
          · intro c' h_c'
            have h_le_a'_add : Le a' (add b' c') := by
              rw [succ_add] at h_c'
              exact (succ_le_succ_iff a' (add b' c')).mp h_c'
            exact h_c_unique c' h_le_a'_add

    theorem lt_add_pos {a b : ℕ₀} (h_b_pos : b ≠ 𝟘) :
        Lt a (add a b)
            := by
        cases b with
        | zero => exact False.elim (h_b_pos rfl)
        | succ b' =>
          rw [add_succ]
          exact lt_n_add_n_σm a b'

    notation a "+" b => Peano.Add.add a b
    notation a "+l" b => Peano.Add.add_l a b

    theorem lt_0_then_le_1 (b : ℕ₀) (h_0_lt_b : Lt 𝟘 b) :
      Le 𝟙 b
        := by
      induction b with
      | zero => contradiction
      | succ b' ih =>
        cases b' with
        | zero => exact le_refl 𝟙
        | succ b'' =>
          have h_0_lt_b'' : Lt 𝟘 (σ b'') := lt_trans 𝟘 (σ b'') (σ (σ b'')) (lt_succ_self 𝟘) (lt_succ_self (σ b''))
          exact le_trans 𝟙 (σ b'') (σ (σ b'')) (ih h_0_lt_b'') (le_succ_self (σ b''))

  end Add

end Peano

export Peano.Add(
  add
  add_l
  add_zero
  add_zero_l
  zero_add
  zero_add_l
  add_zero_eq_add_l_zero
  add_one
  add_one_l
  one_add
  one_add_l
  add_one_eq_add_l_one
  add_succ
  add_succ_l
  succ_add
  succ_add_l
  add_succ_eq_add_l_succ
  add_eq_add_l
  eq_fn_add_add_l
  add_comm
  add_assoc
  add_le
  add_le_r
  add_lt
  add_cancelation
  cancelation_add
  add_lt_cancelation
  add_le_cancelation
  add_eq_zero_iff
  le_then_le_add
  le_add_then_le
  le_iff_le_add
  le_iff_le_add_forall
  le_self_add
  lt_add_succ
  lt_then_exists_add_succ
  le_iff_exists_add
  lt_iff_exists_add_succ
  lt_iff_add_cancel
  isomorph_Ψ_add
  isomorph_Λ_add
  le_then_exists_zero_add
  le_self_add_forall
  le_add_cancel
  le_then_le_add_zero
  le_then_le_add_one
  add_lt_add_left_iff
  lt_iff_add_lt
  le_add_r_add_r_then_le
  le_add_l_add_l_then_le
  le_then_le_add_r_add_r_then_le
  le_then_le_add_l_add_l_then_le
  le_iff_le_add_r_add_r_forall
  le_iff_le_add_l_add_l_forall
  add_σn_m_eq_add_n_σm
  add_σn_m_eq_σadd_n_m
  σadd_n_m_eq_add_n_σm
  τadd_n_m_eq_add_τn_m
  τadd_n_m_eq_add_n_τm
  add_τn_m_eq_add_n_τm
  τadd_n_σm_eq_add_n_m
  τadd_σn_m_eq_add_n_m
  lt_n_add_n_σm
  lt_add_of_pos_right
  le_add_compat
  le_add_compat_wp
  lt_le_then_lt_add_compat
  lt_le_then_add_add_compat_wp
  le_lt_then_lt_add_compat
  le_lt_then_lt_add_compat_wp
  lt_lt_then_lt_add_compat
  lt_lt_then_lt_add_compat_wp
  le_a_b_then_le_2a_2b
  le_a_b_then_le_2a_2b_wp
  lt_a_b_then_lt_2a_2b
  lt_a_b_then_lt_2a_2b_wp
  le_then_exists_add
  le_then_exists_add_wp
  linear_equation_right
  linear_inequation_left
  linear_equation_left
  linear_inequation_right
  lt_then_exists_add_succ_wp
  lt_add_pos
  lt_0_then_le_1
  le_self_add_r
  le_self_add_r_forall
  le_self_add_l
  le_self_add_l_forall
  lt_self_add_r
  lt_self_add_r_forall
  lt_self_add_l
  lt_self_add_l_forall
)
