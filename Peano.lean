import Peano.Prelim
import Peano.PeanoNat
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Tuple
import Peano.PeanoNat.Lattice
import Peano.PeanoNat.WellFounded
import Peano.PeanoNat.Add
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Mul
import Peano.PeanoNat.Div
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Fractions
import Peano.PeanoNat.Primes
import Peano.PeanoNat.NumberSets
import Peano.PeanoNat.Isomorph
import Peano.PeanoNat.Decidable
import Peano.PeanoNat.Log
import Peano.PeanoNat.Sqrt
import Peano.PeanoNat.Digits
import Peano.PeanoNat.Pairing
import Peano.PeanoNat.ListsAndSets
import Peano.PeanoNat.Combinatorics
import Peano.PeanoNat.NumberTheory
import Peano.PeanoNat.Foundation.Foundation

/-!
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Peano.lean
-- Módulo raíz: importa todos los módulos de Peano/ y re-exporta
-- sus declaraciones públicas para consumo sin calificación.


-- ─────────────────────────────────────────────────────────────────
-- namespace Peano  (Prelim/ExistsUnique.lean — constructivo)
-- ─────────────────────────────────────────────────────────────────
export Peano (
  ExistsUnique
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano  (Prelim/Classical.lean — noncomputable)
-- ─────────────────────────────────────────────────────────────────
export Peano (
  choose
  choose_spec
  choose_unique
  choose_spec_unique
  choose_uniq
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano  (PeanoNat.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano (
  ℕ₀
  ℕ₁
  ℕ₂
  idℕ₀
  idNat
  eqFnGen
  comp
  eqFn
  eqFn2
  eqFnNat
  zero
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
  isZero
  isSucc
  returnBranch
  noConfusion
  isNat_zero
  isNat_succ
  cero_neq_succ
  zero_ne_succ
  succ_isNat
  succ_congr
  succ_injective
  succ_inj
  succ_inj_wp
  succ_inj_neg
  succ_inj_pos_wp
  succ_neq_zero
  AXIOM_zero_notin_ima_succ
  induction_principle
  BIs_zero
  BIs_succ
  category_by_constructor
  neq_succ
  isZero_or_isSucc
  isZero_xor_isSucc
  comp_Λ_eq_Ψ
  comp_Ψ_eq_Λ
  eqFn_induction
  eqFn_refl
  eqFn_symm
  eqFn_trans
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
  lt₀
  blt₀
  gt₀
  bgt₀
  lt_then_lt_succ
  lt_then_lt_succ_wp
  lt_iff_lt_σ_σ
  lt_iff_lt_τ_τ
  nlt_self
  not_lt_zero
  nlt_n_0
  nlt_n_0_false
  pos_of_ne_zero
  ne_of_lt
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
  blt_iff_Lt
  blt_then_Lt_wp
  bgt_iff_Gt
  nblt_iff_nLt
  nbgt_iff_nGt
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
  le₀
  ge₀
  le'
  ble₀
  bge₀
  zero_le
  succ_le_succ_iff
  succ_le_succ_iff_wp
  succ_le_succ_then
  succ_le_succ_then_wp
  succ_le_succ_if
  succ_le_succ_if_wp
  succ_le_succ'_then_wp
  le_then_le_succ
  Le_iff_le'
  le_zero_eq
  le_zero_eq_wp
  not_succ_le_zero
  ble_iff_Le
  decidableLe
  le_of_eq
  le_of_eq_wp
  le_self_of_eq_self
  le_0_of_eq_0
  bge_iff_Ge
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
-- namespace Peano.Lattice  (PeanoNat/Lattice.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Lattice (
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
  eq_of_max_eq_min
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
  max_ne_min_of_ne
  if_neq_then_min_xor
  lt_max_of_ne
  max_comm
  min_comm
  le_then_max_eq_right
  le_then_max_eq_left
  lt_of_not_le
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
  not_exists_max
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
  add_cancel
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
  mul_add
  add_mul
  mul_cancelation_left
  mul_cancelation_right
  mul_assoc
  mul_eq_zero
  eq_zero_of_mul_eq_zero
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
  exists_factor_of_mul_le
  le_le_mul_le_compat
  mul_pos
  lt_lt_mul_lt_compat
  le_lt_mul_lt_compat
  mul_sub
  isomorph_Ψ_mul
  isomorph_Λ_mul
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Div  (PeanoNatDiv.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Div (
  lt_sizeOf
  divMod
  div
  mod
  divMod_spec
  mod_lt
  div_le_self
  gt_imp_neq_zero_one
  div_lt_self
  div_of_lt
  mod_of_lt
  div_of_lt_fst_interval
  div_eq_two
  le___mul__div_a_b__b____a
  div_of_lt_nth_interval
  mod_of_lt_fst_interval
  mod_of_lt_snd_interval
  mod_of_lt_nth_interval
  isomorph_Ψ_div
  isomorph_Ψ_mod
  isomorph_Λ_div
  isomorph_Λ_mod
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.List  (PeanoNatList.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.List (
  instDecidableEqN1
  instDecidableEqN2
  instLTN1
  instLEN1
  instLTN2
  instLEN2
  decidableLtN1
  decidableLeN1
  decidableLtN2
  decidableLeN2
  lexLt
  instLTProdN2N1
  decidableLexLt
  lengthₚ
  lengthₚ_nil
  lengthₚ_cons
  Sorted
  sorted_nil
  sorted_singleton
  decidableMemList
  Nat0List
  Nat1List
  Nat2List
  FactList
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.FSet  (PeanoNatFSet.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.FSet (
  ℕ₀FSet
  ℕ₁FSet
  ℕ₂FSet
  FactFSet
  ℕ₀FSet.empty
  ℕ₁FSet.empty
  ℕ₂FSet.empty
  FactFSet.empty
  ℕ₀FSet.singleton
  ℕ₁FSet.singleton
  ℕ₂FSet.singleton
  FactFSet.singleton
  FactFSet.card
  sortedInsert
  mem_sortedInsert_iff
  sorted_sortedInsert
  ℕ₀FSet.insert
  ℕ₀FSet.ofList
  ℕ₀FSet.filter
  succN1
  oneN1
  factListLookup
  factListAddFactor
  sortedByKey_factListAddFactor
  uniqueKeys_factListAddFactor
  UniqueKeys
  SortedByKey
  sortedByKey_imp_uniqueKeys
  FactFSet.lookup
  FactFSet.addFactor
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
  -- § 8 extensiones Mathlib — GCD
  gcd_comm
  gcd_divides_left
  gcd_divides_right
  gcd_dvd_left
  gcd_dvd_right
  dvd_gcd
  gcd_zero_right
  gcd_zero_left
  gcd_one_right
  gcd_one_left
  gcd_self
  gcd_eq_zero_iff
  gcd_ne_zero_left
  gcd_ne_zero_right
  dvd_gcd_iff
  gcd_assoc
  IsGCD_gcd
  div_mul_cancel
  -- § 8 extensiones Mathlib — LCM
  gcd_mul_lcm
  lcm_comm
  lcm_zero_left
  lcm_zero_right
  dvd_lcm_left
  dvd_lcm_right
  lcm_self
  -- § 8 extensiones Mathlib — Coprime
  coprime_comm
  coprime_one_right
  coprime_one_left
  -- ℕ₁
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
  factorsOf
  dividesb
  range_from_one
  isomorph_Ψ_gcd
  isomorph_Λ_gcd
  isomorph_Ψ_lcm
  isomorph_Λ_lcm
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Arith  (PeanoNat/Fractions.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Arith (
  dvd_of_mul_dvd
  gcd_div_self
  cross_mul_eq_imp_reduced_eq
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
  product_list_pos
  prime_dvd_product_list
  exists_prime_divisor
  exists_prime_factorization
  mem_dvd_product
  unique_prime_factorization
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.NumberSets  (PeanoNatNumberSets.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.NumberSets (
  IsPrime
  CoprimesOf
  DivisorsOf
  MultiplesOf
  isPrimeb
  coprimeb
  divisorsFSet
  primesFSet
  coprimesFSet
  multiplesFSet
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Pow  (PeanoNatPow.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Pow (
  pow
  pow_zero
  zero_pow
  one_pow
  pow_one
  pow_succ
  pow_gt
  pow_ge_one
  pow_lt_succ_base
  pow_lt_succ_base_strong
  pow_lt_succ_exp
  pow_add_eq_mul_pow
  mul_pow_n_m_pow_k_m_eq_pow_nk_m
  pow_pow_eq_pow_mul
  pow_ne_zero
  pow_two
  pow_eq_zero_iff
  one_lt_pow
  pow_eq_one_iff
  pow_lt_mono_exp
  pow_le_pow_right
  pow_lt_mono_base
  pow_le_pow_left
  pow_mul_comm
  isomorph_Ψ_pow
  isomorph_Λ_pow
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Factorial  (PeanoNatFactorial.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Factorial (
  factorial
  factorial_zero
  factorial_one
  factorial_two
  factorial_succ
  factorial_pos
  factorial_ne_zero
  factorial_ge_one
  factorial_le_succ
  factorial_le_mono
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Binom  (PeanoNatBinom.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Binom (
  binom
  binom_zero_zero
  binom_zero_succ
  binom_succ_zero
  binom_pascal
  binom_n_zero
  binom_n_one
  binom_eq_zero_of_gt
  binom_self
  binom_pos
  binom_one
  binom_succ_n_by_n
  binom_mul_factorials
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Summation  (Combinatorics/Summation.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Summation (
  finSum
  finSum_zero
  finSum_succ
  finSum_zero_fn
  finSum_add_fn
  finSum_mul_const
  finSum_mul_const_right
  finSum_le_of_le
  finSum_pos
  finSum_const
  finSum_succ_left
  finSum_reverse
  sum_list
  sum_list_nil
  sum_list_cons
  sum_list_append
  sum_list_singleton
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Product  (Combinatorics/Product.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Product (
  product_list
  product_nil
  product_cons
  product_append
  product_list_singleton
  finProd
  finProd_zero
  finProd_succ
  finProd_one_fn
  finProd_zero_fn
  finProd_succ_left
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Factorization  (Combinatorics/Product.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Factorization (
  factorValue
  factorValue_val
  product_factorization
  product_factorization_val
  product_factorization_empty
  product_factorization_singleton
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.NewtonBinom  (Combinatorics/NewtonBinom.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.NewtonBinom (
  sum_binom_eq_pow_two
  binomTerm
  binomTerm_zero
  binomTerm_self
  newton_binom
  pow_add_split
  exists_nm_growth
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Fibonacci  (Combinatorics/Fibonacci.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Fibonacci (
  fibPair
  fib
  fibList
  fib_zero
  fib_one
  fib_succ_succ
  fib_two
  fibList_zero
  fibList_succ
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Log  (PeanoNat/Log.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Log (
  logMod
  log
  logRem
  log_zero
  logRem_zero
  log_of_lt
  logRem_of_lt
  log_one
  logRem_one
  logMod_spec
  log_upper_bound
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Sqrt  (PeanoNat/Sqrt.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Sqrt (
  sqrtMod
  sqrt
  sqrtRem
  sqrt_zero
  sqrtRem_zero
  sqrt_one
  sqrtRem_one
  sqrtMod_spec
  sqrtRem_lt
  sqrt_upper_bound
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano  (PeanoNat/Tuple.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano (
  Tuple
  NatsTuple
  HTuple
  emptyTuple
  consTuple
  headTuple
  tailTuple
  mkTuple
  tupleDecEq
  tupleRepr
  emptyNatsTuple
  consNatsTuple
  headNatsTuple
  tailNatsTuple
  mkNatsTuple
  instDecidableEqNatsType
  instReprNatsType
  natsTupleDecEq
  natsTupleRepr
  emptyHTuple
  consHTuple
  headHTuple
  tailHTuple
  mkHTuple
  HTupleRepr
  instHTupleReprNil
  instHTupleReprCons
  htupleRepr
  lexLt
  lexLe
  instLTTuple
  instLETuple
  instDecidableRelLtTuple
  instDecidableRelLeTuple
  instDecidableRelLeTuple'
  instDecidableEqTuple
  lexLt_irrefl
  lexLt_trans
  lexLt_trich
  instStrictLinearOrderTuple
  instIrreflTuple
  instAsymmTuple
  instTransTuple
  instTrichotomousTuple
  instIrreflLTTuple
  natsVal
  natsLexLt
  natsLexLe
  instLTNatsTuple
  instLENatsTuple
  instDecidableRelLtNatsTuple
  instDecidableRelLeNatsTuple
  HTupleDecidableEq
  instHTupleDecEqNil
  instHTupleDecEqCons
  htupleDecEq
  HTupleLT
  instHTupleLTNil
  instHTupleLTCons
  instLTHTuple
  HTupleLE
  instHTupleLENil
  instHTupleLECons
  instLEHTuple
  hlexLt
  hlexLe
  HTupleDecidableLT
  instHTupleDecLTNil
  instHTupleDecLTCons
  instDecidableRelLtHTuple
  HTupleDecidableLE
  instHTupleDecLENil
  instHTupleDecLECons
  instDecidableRelLeHTuple
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Digits  (PeanoNat/Digits.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Digits (
  digits
  ofDigits
  toValues
  ofDigitsFin
  numDigits
  digits_zero
  ofDigits_nil
  ofDigits_cons
  toValues_nil
  toValues_cons
  numDigits_zero
  ofDigitsFin_digits
  digits_singleton_of_lt
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Pairing  (PeanoNat/Pairing.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Pairing (
  tri
  cantorPair
  pairAux
  cantorUnpair
  tri_zero
  tri_succ
  cantorPair_zero_zero
  cantorUnpair_zero
  pairAux_spec
  pairAux_bound
  cantorPair_cantorUnpair
  cantorUnpair_cantorPair
  cantorPair_injective
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.FSetFunction  (ListsAndSets/FSetFunction.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.FSetFunction (
  card_eq_mul_of_uniform_fibers
  MapOn
  MapOn.comp
  InjectiveOn
  SurjectiveOn
  MapOn.Injective
  MapOn.Surjective
  MapOn.Bijective
  MapOn.comp_injective
  MapOn.comp_surjective
  MapOn.comp_bijective
  MapOn.comp_assoc
  MapOn.id
  MapOn.id_injective
  MapOn.id_surjective
  MapOn.id_bijective
  MapOn.comp_id
  MapOn.id_comp
  MapOn.injective_of_comp_injective
  MapOn.surjective_of_comp_surjective
  MapOn.Im
  MapOn.rightInverse
  MapOn.rightInverse_prop
  MapOn.rightInverse_injective
  MapOn.leftInverse
  MapOn.leftInverse_prop
  MapOn.leftInverse_surjective
  MapOn.injective_of_has_leftInverse
  MapOn.injective_iff_has_leftInverse
  MapOn.surjective_of_has_rightInverse
  MapOn.surjective_iff_has_rightInverse
  MapOn.bijective_of_injective_leftInverse_injective
  MapOn.bijective_of_surjective_rightInverse_surjective
  MapOn.inverse
  MapOn.inverse_left_prop
  MapOn.inverse_right_prop
  MapOn.inverse_injective
  MapOn.inverse_surjective
  MapOn.inverse_bijective
  MapOn.inverse_inverse
  MapOn.comp_inverse_left
  MapOn.comp_inverse_right
  card_image_of_injective
  injective_of_card_image
  card_image_of_surjective
  surjective_of_card_image
  MapOn.injective_iff_surjective_of_card_eq
  MapOn.injective_iff_bijective_of_card_eq
  MapOn.surjective_iff_bijective_of_card_eq
  MapOn.leftInverse_eq_inverse_of_card_eq
  MapOn.leftInverse_right_prop_of_card_eq
  MapOn.rightInverse_eq_inverse_of_card_eq
  MapOn.rightInverse_left_prop_of_card_eq
  card_le_of_injective
  card_le_of_surjective
  not_injective_of_card_lt
  collision_of_card_lt
  card_eq_of_injections
  card_eq_of_surjections
  MapOn.Bijective.card_eq
  MapOn.endo_injective_iff_surjective
  MapOn.endo_injective_iff_bijective
  MapOn.endo_surjective_iff_bijective
  MapOn.endo_bijective_of_injective
  MapOn.endo_bijective_of_surjective
  MapOn.endo_leftInverse_eq_inverse
  MapOn.endo_leftInverse_right_prop
  MapOn.endo_rightInverse_eq_inverse
  MapOn.endo_rightInverse_left_prop
  Perm
  Perm.injective
  Perm.surjective
  Perm.id
  Perm.comp
  Perm.comp_id_fn
  Perm.id_comp_fn
  Perm.inv
  Perm.inv_left
  Perm.inv_right
  Perm.inv_inv
  Perm.comp_inv_left
  Perm.comp_inv_right
  Perm.comp_assoc
  MapOn.PreIm
  MapOn.mem_PreIm_iff
  MapOn.PreIm_full
  MapOn.card_PreIm_le
  MapOn.fiber
  MapOn.mem_fiber_iff
  MapOn.card_fiber_le_one_of_injective
  MapOn.restrict
  MapOn.restrict_injective
  MapOn.mem_Im_restrict
  BinOpOn
  FunTable
  FunTable.apply
  FunTable.applyElem
  FunTable.applyElem_mem
  FunTable.id
  FunTable.comp
  FunPerm
  FunPerm.id
  FunPerm.applyElem_injective
  sorted_nodup
  nodup_map_of_inj_on
  perm_of_nodup_subset_same_length
  perm_map_of_injective_on_nodup
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.EquivRel  (ListsAndSets/EquivRel.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.EquivRel (
  EquivRelOn
  EquivRelOn.classOf
  EquivRelOn.mem_classOf_iff
  EquivRelOn.classOf_nonempty_of_mem
  EquivRelOn.classOf_subset_domain
  EquivRelOn.rel_of_mem_classOf
  EquivRelOn.mem_classOf_of_rel
  EquivRelOn.classOf_eq_of_mem_classOf
  EquivRelOn.mem_classOf_iff_of_rel
  EquivRelOn.classOf_eq_or_disjoint
  EquivRelOn.ClassFamily
  EquivRelOn.canonicalClassFamily
  EquivRelOn.classes
  EquivRelOn.mem_classes_iff
  EquivRelOn.classOf_mem_classes_of_mem
  EquivRelOn.mem_classes_elim
  EquivRelOn.classes_cover
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.ModEq  (NumberTheory/ModEq.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.ModEq (
  mod_zero_right
  mod_zero_left
  mod_self
  mod_mod
  add_mod
  mul_mod
  ModEq
  modEq_refl
  modEq_symm
  modEq_trans
  modEq_add
  modEq_mul
  modEq_pow
  mod_eq_zero_iff_dvd
  modEq_zero_iff_dvd
  modEq_zero_of_dvd
  modEq_mod
  modEq_one
  modEq_add_right
  instDecidableModEq
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Totient  (NumberTheory/Totient.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Totient (
  lengthₚ_append
  lengthₚ_singleton
  lengthₚ_range_from_one
  lengthₚ_filter_le
  filter_append_singleton
  filter_all_true
  mem_range_from_one_pos
  mem_range_from_one_le
  totient
  totient_zero
  totient_one
  totient_two
  totient_le
  totient_pos
  totient_prime
  instDecidableEqTotient
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.CRT  (NumberTheory/ChineseRemainder.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.CRT (
  chinese_remainder
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Fermat  (NumberTheory/Fermat.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Fermat (
  fermat_little_theorem
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Wilson  (NumberTheory/Wilson.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Wilson (
  wilson
  modInv
  modInv_lt
  modInv_mul
  modInv_pos
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.GodelBeta  (Foundation/GodelBeta.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.GodelBeta (
  beta
  beta_lt
  beta_of_lt
  godel_beta_seq
  encodeList
  decodeList
  list_decode_length
  encode_decode
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.QuotientGroup  (GroupTheory/QuotientGroup.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.QuotientGroup (
  quotientCarrier
  mem_quotientCarrier_iff
  mem_quotientCarrier_is_leftCoset
  coset_nonempty_of_mem_quotientCarrier
  leftCoset_mem_cosetClasses
  leftCoset_mem_quotientCarrier
  leftCoset_id_mem_quotientCarrier
  cosetRel_of_leftCoset_eq
  leftCoset_eq_iff_cosetRel
  cosetRepOf
  cosetRepOf_eq_head
  cosetRepOf_mem_C
  cosetRepOf_mem_G
  cosetRepOf_leftCoset_eq
  quotientOp_welldefined
  quotientOp
  quotientInv
  quotientId
  quotientId_mem
  quotientOp_assoc
  quotientOp_id
  quotientOp_inv
  quotientGroup
  quotient_card
  quotientHomomorphism
  quotientHomomorphism_op
  quotientHomomorphism_kernel
  imageSubgroup
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.FirstIsomorphism  (GroupTheory/FirstIsomorphism.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.FirstIsomorphism (
  homKer
  mem_homKer_iff
  homImg
  mem_homImg_iff
  homKer_isNormal
  quotientHomomorphism_surjective
  homImgInclusion
  homImgInclusion_injective
  firstIsoMap
  firstIsoMap_welldefined
  firstIsoMap_op
  firstIsoMap_injective
  firstIsoMap_surjective
  firstIsoMap_bijective
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.SecondIsomorphism  (GroupTheory/SecondIsomorphism.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.SecondIsomorphism (
  subgroupHN
  mem_subgroupHN_iff
  H_le_subgroupHN
  N_le_subgroupHN
  N_in_subgroupHN
  N_normal_in_subgroupHN
  interHN_as_subgroup_H
  interHN_as_subgroup_H_isNormal
  secondIsoMap
  secondIsoMap_welldefined
  secondIsoMap_injective
  secondIsoMap_surjective
  secondIsoMap_bijective
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.ThirdIsomorphism  (GroupTheory/ThirdIsomorphism.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.ThirdIsomorphism (
  cosetRel_N_imp_K
  KmodN_normal
  thirdIsoMap
  thirdIsoMap_welldefined
  thirdIsoMap_op
  thirdIsoMap_id
  thirdIsoMap_inv
  thirdIsoGroupHom
  thirdIsoMap_surjective
  thirdIsoMap_kernel
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.CorrespondenceTheorem  (GroupTheory/CorrespondenceTheorem.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.CorrespondenceTheorem (
  preimageSubgroup
  mem_preimageSubgroup_iff
  N_le_preimageSubgroup
  imageSubgroup_preimage
  preimageSubgroup_image
  SubgroupAbove
  correspondencePhi
  correspondencePsi
  correspondencePhi_psi
  correspondencePsi_phi
  correspondenceInjective
  correspondenceSurjective
  preimage_subgroup_card
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Zassenhaus  (GroupTheory/Zassenhaus.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Zassenhaus (
  prodSubgroup
  mem_prodSubgroup_iff
  N_le_prodSubgroup
  S_le_prodSubgroup
  inter_N_K_normal_in_inter_H_K
  inter_H_M_normal_in_inter_H_K
  prodNKHM
  prodNKHM_normal
  prodN_HK
  prodN_HM
  prodN_HM_le_prodN_HK
  prodN_HM_normal_in_prodN_HK
  zassenhaus_bijection
  zassenhaus_bijection_symm
  zassenhaus_bijection_extremes
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Group  (Combinatorics/Group.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Group (
  FinGroup
  ℕ₀FinGroup
  id_unique
  inv_mem
  op_mem
  op_cancel_left
  op_cancel_right
  inv_inv_eq
  inv_id_eq
  inv_op_eq
  inv_unique
  gpow
  gpow_zero
  gpow_succ
  gpow_one
  gpow_mem
  gpow_add
  gpow_comm_single
  gpow_inv
  order
  order_pos
  gpow_order_eq_id
  order_ne_zero
  order_minimal
  order_le_card
  gpow_mul_order_eq_id
  gpow_mod_order
  Subgroup
  Subgroup.op_inv_closed
  subgroup_of_op_inv_closed
  trivialSubgroup
  improperSubgroup
  Subgroup.IsTrivial
  Subgroup.IsProper
  cyclicCarrier
  cyclicCarrier_id_in
  cyclicCarrier_mem_iff
  cyclicSubgroup
  cyclicSubgroup'
  Subgroup.IsNormal
  trivialSubgroup_normal
  improperSubgroup_normal
  Subgroup.inter
  Subgroup.inter_subset_left
  Subgroup.inter_subset_right
  Subgroup.inter_normal_of_normal
  GroupHom
  Subgroup.ext_carrier
  Subgroup.carrier_inj
  instDecidableEqSubgroup
  instLTSubgroup
  instStrictLinearOrderSubgroup
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Action  (GroupTheory/Action.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Action (
  GroupAction
  GroupAction.orb
  mem_orb_iff
  GroupAction.stab
  orbit_stabilizer
  orbits_partition
  conjugAction
  class_equation_split
  class_equation
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.NormalSubgroup  (GroupTheory/NormalSubgroup.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.NormalSubgroup (
  centralizer
  mem_centralizer_iff
  center
  mem_center_iff
  center_isNormal
  central_subgroup_isNormal
  normalizer
  mem_normalizer_iff
  H_subset_normalizer
  isNormal_iff_normalizer_eq_G
  rightCoset
  mem_rightCoset_iff
  isNormal_iff_leftCoset_eq_rightCoset
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Cosets  (Sylow/Cosets.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Cosets (
  leftCoset
  mem_leftCoset_iff
  coset_card_eq_subgroup_card
  cosetRel
  cosetRel_refl
  cosetRel_symm
  cosetRel_trans
  cosetEquivRel
  mem_classOf_cosetEquivRel_iff_leftCoset
  classOf_cosetEquivRel_eq_leftCoset
  classOf_cosetEquivRel_card_eq_subgroup_card
  cosetClassFamily
  mem_some_cosetClassFamily_class
  cosetClasses
  card_eq_subgroup_card_of_mem_cosetClasses
  mem_some_cosetClasses
  cosetClass_eq_classOf_of_mem
  leftCoset_subset_of_rel
  leftCoset_eq_of_rel
  lagrange
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.CosetAction  (Sylow/CosetAction.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.CosetAction (
  coset_conjugate_exists
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Sylow  (Sylow/Sylow.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Sylow (
  cauchy_minimal
  sylow_lift_from_cauchy
  sylow_first
  sylow_second
  sylow_third
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.PeanoSystem  (Foundation/PeanoSystem.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.PeanoSystem (
  PeanoSystem
  PeanoMorphism
  isPeanoIso
  compMorph
  idMorph
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.Initiality  (Foundation/Initiality.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.Initiality (
  ℕ₀_prim_rec
  ℕ₀_PeanoSystem
  ℕ₀_to
  ℕ₀_to_zero
  ℕ₀_to_succ
  ℕ₀_to_morph
  ℕ₀_initial
  ℕ₀_morph_unique
  morph_fn
  morph_fn_zero
  morph_fn_succ
  morph_fn_unique
  morph_as_morph
  morph_fn_comp_id
  peano_unique
  ℕ₀_rec_principle
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.CantorPairing  (Foundation/CantorPairing.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.CantorPairing (
  triag
  pair
  antidiag
  fst
  snd
  triag_zero
  triag_succ
  triag_strict_mono
  triag_le_of_le
  triag_le_pair
  pair_lt_triag_succ
  antidiag_exists
  antidiag_unique
  antidiag_spec
  antidiag_pair
  pair_fst
  pair_snd
  pair_surj
)

-- ─────────────────────────────────────────────────────────────────
-- namespace Peano.PureAxioms  (Foundation/PureAxioms.lean)
-- ─────────────────────────────────────────────────────────────────
export Peano.PureAxioms (
  PurePA
  pa_parity
)
