import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatMul


namespace Peano
    open Peano

  namespace Div
      open Axioms
      open StrictOrder
      open Order
      open MaxMin
      open Add
      open Sub
      open Mul


  /--!
  Performs Euclidean division of `a` by `b`.
  Returns a pair `(quotient, remainder)` such that `a = quotient * b + remainder`
  and `remainder < b` (if `b ≠ 𝟘`).
  If `b = 𝟘`, returns `(𝟘, 𝟘)`.
  !--/

  theorem not_lt_and_not_eq_implies_gt (a b : ℕ₀) (h_not_lt : ¬ Lt a b) (h_not_eq : ¬ a = b) : Lt b a := by
    rcases trichotomy a b with hlt | heq | hgt
    · contradiction -- hlt contradicts h_not_lt
    · contradiction -- heq contradicts h_not_eq
    · exact hgt

  instance : SizeOf ℕ₀ where
    sizeOf := Ψ

  theorem lt_sizeOf (a b : ℕ₀) : Lt a b → sizeOf a < sizeOf b := by
    intro h_lt
    rw [isomorph_Ψ_lt] at h_lt
    exact h_lt


  def divMod (a b : ℕ₀) : ℕ₀ × ℕ₀ :=
    if h_b_is_zero : b = 𝟘 then (𝟘, 𝟘)
    else
      if h_a_is_zero : a = 𝟘 then  (𝟘, 𝟘)
      else
        if h_b_is_one : b = 𝟙 then (a, 𝟘)
        else -- h_b_is_one : b ≠ 𝟙 (y también h_b_is_zero : b ≠ 𝟘 del 'else' anterior)
          if h_a_lt_b : Lt a b then
              (𝟘, a)
          else -- h_a_lt_b_false : ¬ (Lt a b)
            if h_a_eq_b : a = b then
              (𝟙, 𝟘)
            else
              have h_b_lt_a : Lt b a := by
                apply not_lt_and_not_eq_implies_gt a b
                exact h_a_lt_b -- Esta es la hipótesis ¬(Lt a b)
                exact h_a_eq_b -- Esta es la hipótesis ¬(a = b)
              have h_le_b_a : Le b a := by
                apply lt_imp_le
                exact h_b_lt_a
              have h_sub_a_b_lt_a : Lt (sub a b) a := by
                apply sub_lt_self a b
                exact h_le_b_a -- b ≤ a
                exact h_b_is_zero -- b ≠ 𝟘
              let (a', b') : ℕ₀ × ℕ₀ := divMod (sub a b) b
              (σ a', b')
  termination_by sizeOf a
  decreasing_by
    simp only [sizeOf]
    apply lt_sizeOf
    exact h_sub_a_b_lt_a

  -- #eval divMod 𝟘 𝟘
  -- #eval divMod 𝟙 𝟘
  -- #eval divMod 𝟙 𝟙
  -- #eval divMod 𝟙 𝟚
  -- #eval divMod 𝟚 𝟘
  -- #eval divMod 𝟚 𝟙
  -- #eval divMod 𝟚 𝟚
  -- #eval divMod 𝟚 𝟛
  -- #eval divMod 𝟛 𝟘
  -- #eval divMod 𝟛 𝟙
  -- #eval divMod 𝟛 𝟚
  -- #eval divMod 𝟛 𝟛
  -- #eval divMod 𝟛 𝟜


  def div (a b : ℕ₀) : ℕ₀ :=
    (divMod a b).1

  notation a " / " b => div a b

  def mod (a b : ℕ₀) : ℕ₀ :=
    (divMod a b).2

  notation a " % " b => mod a b

  theorem divMod_eq__eq_a_0
    (a b : ℕ₀)
    (h_a_eq_zero : a = 𝟘)
    (h_b_neq_0 : b ≠ 𝟘) :
      a = (divMod a b).1 * b + (divMod a b).2
    := by
    unfold divMod
    split
    case isTrue h_b_is_zero =>
      subst h_b_is_zero
      contradiction
    case isFalse h_b_not_zero_again =>
      simp only [Prod.fst, Prod.snd, zero_mul, zero_add]
      exact h_a_eq_zero

  theorem divMod_eq__neq_a_0__eq_b_1
    (a b : ℕ₀)
    (h_a_eq_zero : a ≠ 𝟘)
    (h_b_eq_1 : b = 𝟙) :
      a = add (mul ((divMod a b).1) b) ((divMod a b).2)
    := by
    unfold divMod
    split
    case isTrue h_b_is_zero =>
      have h_b_not_zero : b ≠ 𝟘
        := by
          rw [h_b_eq_1]
          exact Ne.symm neq_1_0
      contradiction
    case isFalse h_b_not_zero_again =>
      simp only [Prod.fst, Prod.snd]
      rw [h_b_eq_1]
      simp only [mul_one, add_zero]

  theorem divMod_eq__neq_a_0__lt_1_b__lt_a_b
    (a b : ℕ₀)
    (h_neq_a_0 : a ≠ 𝟘)
    (h_lt_1_b : Lt 𝟙 b)
    (h_lt_a_b : Lt a b)  :
      a = add (mul ((divMod a b).1) b) ((divMod a b).2)
    := by
       unfold divMod
       split
       case isTrue h_b_is_zero =>
         have h_b_not_zero : b ≠ 𝟘 := by
           exact lt_1_b_then_b_neq_0 h_lt_1_b
         contradiction
       case isFalse h_b_not_zero_again =>
         by_cases h_b_is_one : b = 𝟙
         case pos =>
            have h_b_not_one : b ≠ 𝟙 := by
              exact lt_1_b_then_b_neq_1 h_lt_1_b
            contradiction
         case neg =>
            symm
            simp [Prod.fst]
            simp [divMod, h_b_not_zero_again, h_b_is_one, h_lt_a_b]
            simp only [zero_mul]
            simp only [zero_add]

  theorem divMod_eq__neq_a_0__lt_1_b__eq_a_b
    (a b : ℕ₀)
    (h_neq_a_0 : a ≠ 𝟘)
    (h_lt_1_b : Lt 𝟙 b)
    (h_eq_a_b : a = b) :
      a = add (mul ((divMod a b).1) b) ((divMod a b).2)
    := by
    unfold divMod
    split
    case isTrue h_b_is_zero =>
      have h_b_not_zero : b ≠ 𝟘
        := by exact lt_1_b_then_b_neq_0 h_lt_1_b
      contradiction
    case isFalse h_b_not_zero_again =>
      split
      case isTrue h_b_is_one =>
        exfalso
        have h_lt_1_b : Lt 𝟙 b := by exact h_lt_1_b
        have h_b_not_one : b ≠ 𝟙 := by exact lt_1_b_then_b_neq_1 h_lt_1_b
        contradiction
      case isFalse h_b_not_one =>
          split
          case isTrue h_lt_a_b =>
            exfalso
            have h_a_nlt_b : ¬ Lt a b := by
              rw [h_eq_a_b]
              exact lt_irrefl b
            contradiction
          case isFalse h_nlt_a_b =>
            simp only [Prod.fst]
            rw [h_eq_a_b]
            simp only [one_mul, add_zero]


  theorem sub_lt_of_lt_and_neq_zero {a b : ℕ₀} (h_lt : Lt b a) (h_b_neq_zero : b ≠ 𝟘) :
      Lt (sub a b) a
          := by
      have h_le : Le b a := lt_imp_le b a h_lt
      exact sub_lt_self a b h_le h_b_neq_zero

  theorem lt_add_of_pos_right (a b : ℕ₀) (h_b_pos : Lt 𝟘 b) :
      Lt a (add a b)
          := by
      induction b with
      | zero =>
        exfalso
        exact nlt_self 𝟘 h_b_pos
      | succ b' =>
        rw [add_succ]
        have h_le : Le a (add a b') := le_self_add_forall a b'
        exact le_then_lt_succ_wp h_le

  -- theorem divMod_eq__neq_a_0__lt_1_b__gt_a_b
  --   (a b : ℕ₀)
  --   (h_lt_1_b : Lt 𝟙 b)
  --   (h_lt_b_a : Lt b a):
  --     a = (divMod a b).1 * b + (divMod a b).2
  --   := by
  --     unfold divMod
  --     split
  --     case isTrue h_b_is_zero =>
  --       have h_b_not_zero : b ≠ 𝟘 := by exact lt_1_b_then_b_neq_0 h_lt_1_b
  --       contradiction
  --     case isFalse h_b_not_zero_again =>
  --       split
  --       case isTrue h_a_is_zero =>
  --         exfalso
  --         have h_a_neq_zero : a ≠ 𝟘 := by
  --           have h_lt_1_a : Lt 𝟙 a := lt_trans_wp h_lt_1_b h_lt_b_a
  --           exact lt_1_b_then_b_neq_0 h_lt_1_a
  --         contradiction
  --       case isFalse h_a_not_zero =>
  --         split
  --         case isTrue h_b_is_one =>
  --           exfalso
  --           have h_b_not_one : b ≠ 𝟙 := by exact lt_1_b_then_b_neq_1 h_lt_1_b
  --           contradiction
  --         case isFalse h_b_not_one =>
  --           split
  --           case isTrue h_lt_a_b =>
  --             exfalso
  --             have h_a_nlt_b : ¬ Lt a b := by exact lt_asymm_wp h_lt_b_a
  --             contradiction
  --           case isFalse h_nlt_a_b =>
  --             split
  --             case isTrue h_eq_a_b =>
  --               exfalso
  --               have h_a_neq_b : ¬ a = b := by
  --                 intro h
  --                 rw [h] at h_lt_b_a
  --                 exact lt_irrefl b h_lt_b_a
  --               contradiction
  --             case isFalse h_neq_a_b =>
  --               induction a with
  --               | zero =>
  --                 contradiction
  --               | succ a' =>
  --                 induction a' with
  --                 | zero =>
  --                   exfalso
  --                   have h_b_eq_zero : b = 𝟘 := by
  --                     apply lt_b_1_then_b_eq_0 -- Assuming this lemma exists and is correct
  --                     exact h_lt_b_a
  --                   have h_b_neq_zero : b ≠ 𝟘 := by
  --                     apply lt_1_b_then_b_neq_0
  --                     exact h_lt_1_b
  --                   exact h_b_neq_zero h_b_eq_zero
  --                 | succ a' ih_a' =>
  --                 -- We are in the case `a = σ(σ a')`.
  --                 -- The conditions h_lt_1_b : Lt 𝟙 b and h_lt_b_a : Lt b (σ(σ a')) hold.
  --                 -- These imply b ≠ 𝟘, σ(σ a') ≠ 𝟘, b ≠ 𝟙, ¬ Lt (σ(σ a')) b, ¬ σ(σ a') = b.
  --                 -- So divMod (σ(σ a')) b evaluates to (σ q, r) where (q, r) = divMod (sub (σ(σ a')) b) b.

  --                 -- Inductive hypothesis: ih_a' applies to sub (σ(σ a')) b.
  --                 -- The decreasing_by uses Lt (sub a b) a.
  --                 -- So the inductive hypothesis is available for sub (σ(σ a')) b.
  --                   have h_rec :
  --                       sub (σ(σ a')) b = (divMod (sub (σ(σ a')) b) b).1 * b + (divMod (sub (σ(σ a')) b) b).2
  --                           := by
  --                     apply divMod_eq__neq_a_0__lt_1_b__gt_a_b
  --                     · exact h_lt_1_b
  --                     · -- Prove Lt b (sub (σ(σ a')) b)
  --                       have h_le_b_ssa' : Le b (σ(σ a')) := lt_imp_le b (σ(σ a')) h_lt_b_a
  --                       have h_sub_pos : Lt 𝟘 (sub (σ(σ a')) b) := by
  --                         have h_le_b_ssa' : Le b (σ(σ a')) := lt_imp_le b (σ(σ a')) h_lt_b_a
  --                         have h_b_neq_zero : b ≠ 𝟘 := lt_1_b_then_b_neq_0 h_lt_1_b
  --                         apply sub_pos_of_lt
  --                         exact h_lt_b_a
  --                       have h_lt_b_sub : Lt b (sub (σ(σ a')) b) := by
  --                         have h_le_b_ssa' : Le b (σ(σ a')) := lt_imp_le b (σ(σ a')) h_lt_b_a
  --                         have h_b_neq_zero : b ≠ 𝟘 := lt_1_b_then_b_neq_0 h_lt_1_b
  --                         -- We need to prove b < (σ(σ a') - b) given b < σ(σ a') and b ≠ 0
  --                         -- This follows from the fact that if b < a and b ≠ 0, then b < a - b
  --                         -- We can use the fact that b + (a - b) = a when b ≤ a
  --                         -- and b < a implies b + b < a, so b < a - b
  --                         have h_add_lt : add b b < σ(σ a') := by
  --                           have h_one_lt_b : Lt 𝟙 b := h_lt_1_b
  --                           have h_b_ge_2 : Le (σ 𝟙) b := by
  --                             have h_succ_one_lt_b : Lt (σ 𝟙) b := by
  --                                     have : σ 𝟙 = add 𝟙 𝟙 := by rfl
  --                                     rw [this]
  --                                     have h_pos_one : Lt 𝟘 𝟙 := lt_0_1
  --                                     have h_pos_sb : Lt 𝟘 (σ b) := by

  --                                     exact lt_add_of_pos_right 𝟙 b h_pos_one
  --                             exact lt_imp_le (σ 𝟙) b h_succ_one_lt_b
  --                           have h_2b_gt_b : Lt b (add b b) := by
  --                             rw [add_comm b b]
  --                             exact lt_add_of_pos_right b b h_sub_pos
  --                           exact lt_trans_wp h_2b_gt_b (by
  --                             have : add b b = mul (σ 𝟙) b := by rw [succ_eq_add_one, one_add, mul_comm]; rfl
  --                             rw [this]
  --                             exact lt_mul_of_one_lt_left h_one_lt_b h_lt_b_a)
  --                         -- Now we can conclude b < σ(σ a') - b
  --                         exact lt_sub_of_add_lt h_add_lt
  --                       exact h_lt_b_sub

  --                   let (q, r) := divMod (sub (σ(σ a')) b) b

  --                   -- The definition of divMod (σ(σ a')) b in this branch is (σ q, r).
  --                   -- The goal is σ(σ a') = (σ q) * b + r.

  --                   have h_rec_qr :
  --                       sub (σ(σ a')) b = q * b + r
  --                           := h_rec

  --                   -- We know sub (σ(σ a')) b + b = σ(σ a') because Lt b (σ(σ a')) implies Le b (σ(σ a')).
  --                   have h_sub_add_b_eq_ssa' : sub (σ(σ a')) b + b = σ(σ a')
  --                       := sub_add_cancel_of_le h_le_b_ssa'

  --                   -- Now substitute h_rec_qr into h_sub_add_b_eq_sa'.
  --                   rw [h_rec_qr] at h_sub_add_b_eq_sa'
  --                   -- Now substitute h_rec_qr into h_sub_add_b_eq_ssa'.
  --                   rw [h_rec_qr] at h_sub_add_b_eq_ssa'

  --                   -- Rearrange the left side: (q * b + r) + b = (σ q) * b + r
  --                   have h_rearrange : (q * b + r) + b = (σ q) * b + r := by
  --                     rw [add_comm r b]
  --                     rw [← add_assoc (q * b) b r]
  --                     rw [← one_mul b]
  --                     rw [← mul_add q 𝟙 b]
  --                     rw [succ_eq_add_one q]
  --                     rfl

  --                   -- Combine h_sub_add_b_eq_ssa' and h_rearrange.
  --                   rw [h_rearrange] at h_sub_add_b_eq_ssa'
  --                   -- Goal: (σ q) * b + r = σ(σ a')
  --                   -- This is the desired equality.
  --                   exact Eq.symm h_sub_add_b_eq_ssa'





  -- theorem divMod_eq (a b : ℕ₀) (h_lt_a_b : Lt a b):
  --   b ≠ 𝟘 → a = (divMod a b).1 * b + (divMod a b).2
  --     := by
  --   intro h_b_not_zero
  --   unfold divMod
  --   split
  --   case isTrue h_b_is_zero =>
  --     contradiction -- b ≠ 𝟘 contradicts h_b_is_zero
  --   case isFalse h_b_not_zero_again =>
  --     split
  --     case isTrue h_b_is_one =>
  --       rw [h_b_is_one]
  --       simp only [mul_one, add_zero]
  --     case isFalse h_b_not_one =>
  --       have h_qr_eq_0a : (divMod a b) = (𝟘, a) := by
  --         simp [divMod, h_b_not_zero_again, h_b_not_one, h_lt_a_b]
  --       simp only [h_qr_eq_0a, zero_mul, zero_add]


  end Div

end Peano
