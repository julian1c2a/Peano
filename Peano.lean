/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano.lean
-- Módulo raíz: importa todos los módulos de PeanoNatLib y re-exporta
-- sus declaraciones públicas para consumo sin calificación.

import PeanoNatLib.PeanoNatLib
import PeanoNatLib.PeanoNatAxioms
import PeanoNatLib.PeanoNatStrictOrder
import PeanoNatLib.PeanoNatOrder
import PeanoNatLib.PeanoNatMaxMin
import PeanoNatLib.PeanoNatWellFounded
import PeanoNatLib.PeanoNatAdd
import PeanoNatLib.PeanoNatSub
import PeanoNatLib.PeanoNatMul
import PeanoNatLib.PeanoNatDiv
import PeanoNatLib.PeanoNatArith
import PeanoNatLib.PeanoNatPrimes

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano  (PeanoNatLib.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano (
  ExistsUnique
  choose
  choose_spec
  choose_unique
  choose_spec_unique
  choose_uniq
  ℕ₀
  ℕ₁
  ℕ₂
  idℕ₀
  idNat
  EqFnGen
  Comp
  EqFn
  EqFn2
  EqFnNat
  cero
  one
  two
  three
  Λ
  Ψ
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Axioms  (PeanoNatAxioms.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Axioms (
  is_zero
  is_succ
  return_branch
  noConfusion
  AXIOM_zero_is_an_PeanoNat
  AXIOM_succ_is_an_PeanoNat
  cero_neq_succ
  AXIOM_cero_neq_succ
  AXIOM_succ_is_funct_forall_n_in_PeanoNat
  AXIOM_uniqueness_on_image
  AXIOM_succ_inj
  succ_inj
  succ_inj_wp
  succ_inj_neg
  succ_inj_pos_wp
  succ_neq_zero
  AXIOM_zero_notin_ima_succ
  AXIOM_induction_on_PeanoNat
  BIs_zero
  BIs_succ
  category_by_constructor
  neq_succ
  is_zero_or_is_succ
  is_zero_xor_is_succ
  Comp_Λ_eq_Ψ
  Comp_Ψ_eq_Λ
  EqFn_induction
  EqFn_refl
  EqFn_symm
  EqFn_trans
  isomorph_0_Λ
  isomorph_0_Ψ
  isomorph_σ_Λ
  isomorph_σ_Ψ
  isomorph_τ_Λ
  isomorph_τ_Ψ
  isomorph_ρ_Ψ
  isomorph_Λ_ρ
  tau_eq_rho_if_ne_zero
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.StrictOrder  (PeanoNatStrictOrder.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.StrictOrder (
  Lt
  BLt
  Gt
  BGt
  lt_then_lt_succ
  lt_then_lt_succ_wp
  lt_iff_lt_σ_σ
  lt_iff_lt_τ_τ
  nlt_self
  nlt_0_0
  nlt_n_0
  nlt_n_0_false
  lt_0_n
  lt_then_neq
  neq_then_lt_or_gt
  lt_nor_gt_then_eq
  lt_succ_self
  lt_succ
  lt_succ_then_lt
  lt_succ_then_lt_wp
  succ_lt_succ_iff
  lt_zero
  trichotomy
  lt_asymm
  lt_asymm_wp
  strong_trichotomy
  lt_irrefl
  lt_trans
  lt_trans_wp
  lt_equiv_exists_σ
  lt_self_σ_self
  exists_greater_nat
  nexists_greater_forall
  lt_succ_iff_lt_or_eq
  BLt_iff_Lt
  BLt_then_Lt_wp
  BGt_iff_Gt
  nBLt_iff_nLt
  nBGt_iff_nGt
  isomorph_Λ_lt
  isomorph_Ψ_lt
  decidableLt
  decidableGt
  zero_lt_succ
  neq_01_then_gt_1
  lt_0_succ
  lt_1_succ_succ
  nlt_then_ltc_or_eq
  lt_or_eq_then_nltc
  lt_or_eq_iff_nltc
  succ_lt_succ_iff_forall
  lt_then_lt_succ_forall
  lt_succ_then_lt_forall
  lt_then_lt_succs
  succ_lt_succ_then
  lt_n_sm_then_lt_n_m_or_eq
  lt_n_sm_then_lt_n_m_or_eq_wp
  lt_sn_m_then_lt_n_m
  lt_0_1
  lt_1_b_then_b_neq_1
  lt_sn_m_then_lt_n_m_wp
  lt_1_b_then_b_neq_0
  lt_b_1_then_b_eq_0
  neq_0_then_lt_0
  lt_0_then_neq_0
  lt_then_lt_σ_σ_wp
  lt_σ_σ_then_lt_wp
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Order  (PeanoNatOrder.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Order (
  Le
  Ge
  Le'
  BLe
  BGe
  zero_le
  succ_le_succ_iff
  succ_le_succ_iff_wp
  succ_le_succ_then
  succ_le_succ_then_wp
  succ_le_succ_if
  succ_le_succ_if_wp
  succ_le_succ'_then_wp
  le_then_le_succ
  Le_iff_Le'
  le_zero_eq
  le_zero_eq_wp
  not_succ_le_zero
  BLe_iff_Le
  decidableLe
  le_of_eq
  le_of_eq_wp
  le_self_of_eq_self
  le_0_of_eq_0
  BGe_iff_Ge
  decidableGe
  le_refl
  lt_imp_le
  lt_imp_le_wp
  le_trans
  le_antisymm
  le_total
  le_iff_lt_succ
  lt_of_le_neq
  lt_of_le_neq_wp
  le_succ_self
  le_succ
  le_1_succ
  le_zero_eq_zero
  le_succ_zero_zero
  le_1_0_then_false
  le_succ_iff_le_or_eq
  le_succ_then_le_or_eq
  le_or_eq_then_le_succ
  isomorph_Ψ_le
  isomorph_Λ_le
  lt_of_le_of_ne
  lt_iff_le_not_le
  lt_succ_iff_lt_or_eq_alt
  le_succ_iff_le_or_eq_alt
  le_of_succ_le_succ
  nle_then_gt
  nle_then_gt_wp
  gt_then_nle
  gt_then_nle_wp
  le_1_m_then_m_neq_0
  le_1_m_then_m_neq_0_wp
  m_neq_0_proved_lt_1_m
  le_m_1_then_m_eq_0or1_wp
  le_n_m_then_m_neq_0
  le_n_m_n_neq_0_then_m_neq_0
  m_neq_0_proved_lt_1_m_wp
  le_0_succ_then_lt_0_succ
  le_0_succ_then_lt_0_succ_wp
  lt_0_succ_then_le_0_succ
  lt_0_succ_then_le_0_succ_wp
  le_0_succ_iff_lt_0_succ
  le_then_lt_succ
  le_then_lt_succ_wp
  le_succ_then_le_or_eq_wp
  le_or_eq_then_le_succ_wp
  le_succ_k_n_then_le_k_n
  lt_k_succ_n_then_le_k_n
  lt_k_succ_n_then_le_k_n_wp
  le_succ_k_n_then_lt_k_n
  le_succ_k_n_then_lt_k_n_wp
  le_succ_then_le
  le_succ_then_le_wp
  le_k_n_then_le_k_sn_wp
  le_n_m_then_le_n_sm
  le_n_m_then_le_n_sm_wp
  le_sn_m_then_le_n_m_or_succ
  le_sn_m_then_le_n_m_or_succ_wp
  le_then_lt_or_eq
  le_not_lt
  nle_σn_n
  le_σn_n_then_false
  lt_0n_then_le_1n
  lt_0n_then_le_1n_wp
  lt_nm_then_le_nm
  lt_nm_then_le_nm_wp
  le_then_ngt
  le_then_ngt_wp
  ngt_then_le
  ngt_then_le_wp
  le_succ_then_lt
  le_succ_then_lt_wp
  lt_then_le_succ_wp
  lt_then_le_succ
  well_ordering_principle
  ngt_iff_le
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.MaxMin  (PeanoNatMaxMin.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.MaxMin (
  max
  min
  min_max
  max_min
  max_idem
  min_idem
  min_abs_0
  min_0_abs
  max_not_0
  max_0_not
  eq_max_min_then_eq
  eq_then_eq_max_min
  eq_iff_eq_max_min
  min_of_min_max
  max_of_min_max
  max_is_any
  min_is_any
  lt_then_min
  min_then_le
  min_eq_of_gt
  max_eq_of_lt
  max_eq_of_gt
  if_neq_then_max_xor
  if_neq_then_min_xor
  neq_args_then_lt_min_max
  max_comm
  min_comm
  le_then_max_eq_right
  le_then_max_eq_left
  Lt_of_not_le
  le_max_left
  le_max_right
  max_le
  max_assoc
  le_then_min_eq_left
  le_then_min_eq_right
  min_le_left
  min_le_right
  le_min
  min_assoc
  nexists_max_abs
  min_eq_right
  min_eq_left
  max_eq_right
  max_eq_left
  max_distrib_min
  min_distrib_max
  isomorph_Λ_max
  isomorph_Λ_min
  isomorph_Ψ_max
  isomorph_Ψ_min
  le_a_le_b_then_le_min_a_b_left
  le_min_a_b_then_le_a_le_b_left
  le_a_le_b_then_le_min_a_b_right
  le_a_le_b_then_le_max_a_b_right
  le_max_a_b_then_le_a_le_b_right
  le_a_le_b_then_le_max_a_b_left
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.WellFounded  (PeanoNatWellFounded.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.WellFounded (
  acc_lt_wf
  well_founded_lt
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Add  (PeanoNatAdd.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Add (
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
  le_self_add_r
  le_self_add_r_forall
  lt_self_add_r
  lt_self_add_r_forall
  le_self_add_l
  le_self_add_l_forall
  lt_self_add_l
  lt_self_add_l_forall
  add_lt
  add_cancelation
  cancelation_add
  add_lt_cancelation
  add_le_cancelation
  add_eq_zero_iff
  le_then_le_add_zero
  le_then_le_add_one
  le_add_then_le_add_succ
  le_add_zero_then_le
  le_add_one_then_le
  le_add_r_add_r_then_le
  le_add_l_add_l_then_le
  le_then_le_add_r_add_r_then_le
  le_then_le_add_l_add_l_then_le
  le_iff_le_add_r_add_r_forall
  le_iff_le_add_l_add_l_forall
  le_add_then_le
  le_iff_le_add
  le_iff_le_add_forall
  le_add_cancel
  le_then_exists_zero_add
  le_self_add
  add_σn_m_eq_add_n_σm
  add_σn_m_eq_σadd_n_m
  add_τn_m_eq_add_n_τm
  le_self_add_forall
  lt_add_succ
  le_then_exists_add
  le_then_exists_add_wp
  lt_then_exists_add_succ
  lt_then_exists_add_succ_wp
  le_iff_exists_add
  lt_iff_exists_add_succ
  isomorph_Ψ_add
  isomorph_Λ_add
  add_lt_add_left_iff
  lt_iff_add_cancel
  lt_iff_add_lt
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
  linear_equation_right
  linear_inequation_left
  linear_equation_left
  linear_inequation_right
  lt_add_pos
  lt_0_then_le_1
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Sub  (PeanoNatSub.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Sub (
  subₕₖ
  sub
  subₕₖ_zero
  zero_subₕₖ
  sub_zero
  zero_sub
  subₕₖ_eq_zero
  sub_eq_zero
  subₕₖ_one
  sub_one
  one_sub
  subₕₖ_succ
  sub_succ
  subₕₖ_k_add_k
  sub_k_add_k
  subₕₖ_k_add_k_forall
  sub_k_add_k_forall
  add_k_subₕₖ_k
  add_k_sub_k
  add_k_sub_k_forall
  aux_ge_1
  nle_one_zero
  aux_neq_0
  succ_subₕₖ
  succ_sub
  sub_succ_succ_eq
  isomorph_Λ_sub
  isomorph_Ψ_sub
  sub_self
  subₕₖ_le_self
  subₕₖ_lt_self
  sub_lt_self
  sub_lt_self_wp
  sub_le_self
  subₕₖ_eq_iff_eq_add_of_le
  subₕₖ_le_subₕₖ_right
  subₕₖ_le_subₕₖ_left
  add_sub_assoc
  add_le_add_left
  sub_eq_of_le
  le_sub_iff_add_le_of_le
  sub_sub
  sub_lt_iff_lt_add_of_le
  sub_pos_iff_lt
  lt_b_a_then_sub_a_b_neq_0
  sub_pos_of_lt
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Mul  (PeanoNatMul.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Mul (
  mul
  mul_zero
  zero_mul
  succ_mul
  mul_succ
  mul_one
  one_mul
  mul_two
  two_mul
  mul_three
  three_mul
  mul_comm
  mul_ldistr
  mul_rdistr
  mul_cancelation_left
  mul_cancelation_right
  mul_assoc
  mul_eq_zero
  mul_eq_zero_wp
  obvio_1
  le_n_mul_n_σn
  mul_le_right
  mul_le_left
  mul_le_full_right
  mul_le_full_left
  mul_lt_left
  mul_lt_right
  mul_lt_full_left
  mul_lt_full_right
  mul_le_mono_right
  lt_σn_mul_σn_σσm
  mul_n_τm
  mul_τn_m
  lt_of_lt_of_le
  archimedean_property
  exists_unique_mul_le_and_lt_succ_mul
  mul_le_then_exists_max_factor
  le_le_mul_le_compat
  mul_pos
  lt_lt_mul_lt_compat
  le_lt_mul_lt_compat
  mul_sub
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Div  (PeanoNatDiv.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Div (
  lt_sizeOf
  divMod
  div
  mod
  divMod_eq
  mod_lt_divisor
  div_le_self
  gt_imp_neq_zero_one
  div_lt_self
  div_of_lt
  mod_of_lt
  div_of_lt_fst_interval
  div_of_lt_snd_interval
  le___mul__div_a_b__b____a
  div_of_lt_nth_interval
  mod_of_lt_fst_interval
  mod_of_lt_snd_interval
  mod_of_lt_nth_interval
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Arith  (PeanoNatArith.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Arith (
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
  divides_le
  antisymm_divides
  divides_sub
  divides_mod
  gcd
  lcm
  gcd_greatest
  gcd_divides_linear_combo
  bezout_natform
  gcd_divides_max
  gcd_divides_min
  Divides₁
  IsGCD₁
  gcd₁
  Coprime₁
  divides₁_refl
  divides₁_trans
  divides₁_antisymm
  gcd₁_val_eq
  gcd₁_comm
  gcd₁_divides_left
  gcd₁_divides_right
  gcd₁_divides_both
  mod_eq_zero_iff_divides
  Factors_of
  dividesb
  range_from_one
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Primes  (PeanoNatPrimes.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Primes (
  Irreducible
  HasExactlyTwoDivisors
  prime_ne_zero
  prime_ne_one
  one_lt_prime
  prime_ge_two
  not_prime_one
  not_prime_zero
  mul_eq_one
  prime_divisors
  prime_imp_irreducible
  irreducible_imp_prime
  prime_iff_irreducible
  not_has_two_divisors_one
  not_has_two_divisors_zero
  prime_iff_has_exactly_two_divisors
  coprime_symm
  gcd_eq_one_iff_coprime
  prime_not_dvd_imp_coprime
  prime_coprime_or_dvd
  coprime_dvd_of_dvd_mul
  PrimeList
  product_list
  product_nil
  product_cons
  product_append
  product_list_pos
  prime_dvd_product_list
  exists_prime_divisor
  exists_prime_factorization
  mem_dvd_product
  unique_prime_factorization
)
