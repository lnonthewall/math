module

public import SemaevRCB
public import CarryAutomaton

/-!
# Umbrella Module & Compile-Time Axiom Audit

Imports both standalone libraries (`SemaevRCB` for Paper 1 and `CarryAutomaton` for Paper 2) and
machine-verifies at compile time via `#guard_msgs in #print axioms` that every headline theorem
depends exclusively on Lean's standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`), with zero non-standard or reduction-trust dependencies.
-/

/-! ## Paper 1 (`SemaevRCB`) Headline Theorems -/

/-- info: 'SemaevRCB.formalBorderRank_flattening_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.formalBorderRank_flattening_lower_bound

/-- info: 'SemaevRCB.symEps3_equiv_I2_eps3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.symEps3_equiv_I2_eps3

/-- info: 'SemaevRCB.minors2x3_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.minors2x3_eval

/-- info: 'SemaevRCB.I2_eps3_borderRank_ge_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I2_eps3_borderRank_ge_nine

/-- info: 'SemaevRCB.symEps3_hasSym12FormalBorderRankLe_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.symEps3_hasSym12FormalBorderRankLe_nine

/-- info: 'SemaevRCB.I2_eps3_rank_nine_imp_char_ne_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I2_eps3_rank_nine_imp_char_ne_three

/-- info: 'SemaevRCB.minors2x3_all_char_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.minors2x3_all_char_dichotomy

/-- info: 'SemaevRCB.rcb_minors_char3_corollary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_minors_char3_corollary

/-- info: 'SemaevRCB.rank_9_implies_isSquare_neg_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rank_9_implies_isSquare_neg_three

/-- info: 'SemaevRCB.nonHesse_equiangular_idempotents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.nonHesse_equiangular_idempotents

/-- info: 'SemaevRCB.eps3_exact_rank_and_borderRank_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.eps3_exact_rank_and_borderRank_five

/-- info: 'SemaevRCB.det_koszulFlat_Im_eps3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.det_koszulFlat_Im_eps3

/-- info: 'SemaevRCB.Im_eps3_exact_formalBorderRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Im_eps3_exact_formalBorderRank

/-- info: 'SemaevRCB.Im_eps3_exact_rank_of_primCubeRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Im_eps3_exact_rank_of_primCubeRoot

/-- info: 'SemaevRCB.symEps3Block_isSym12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.symEps3Block_isSym12

/-- info: 'SemaevRCB.symEps3Block_equiv_Im_eps3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.symEps3Block_equiv_Im_eps3

/-- info: 'SemaevRCB.symEps3Block_exact_sym12FormalBorderRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.symEps3Block_exact_sym12FormalBorderRank

/-- info: 'SemaevRCB.symEps3Block_exact_sym12Rank_of_primCubeRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.symEps3Block_exact_sym12Rank_of_primCubeRoot

/-- info: 'SemaevRCB.T_RCB_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.T_RCB_eval

/-- info: 'SemaevRCB.rcb_cross_product_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_cross_product_identity

/-- info: 'SemaevRCB.T_RCB_sym12Congruent_symEps3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.T_RCB_sym12Congruent_symEps3

/-- info: 'SemaevRCB.rcb_unconditionally_complete_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_unconditionally_complete_iff

/-- info: 'SemaevRCB.Psi_RCB_equiv_kroneckerDouble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Psi_RCB_equiv_kroneckerDouble

/-- info: 'SemaevRCB.Psi_RCB_rank_ge_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Psi_RCB_rank_ge_eight

/-- info: 'SemaevRCB.Psi_RCB_hasTensorRankLe_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Psi_RCB_hasTensorRankLe_eight

/-- info: 'SemaevRCB.Psi_RCB_borderRank_ge_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Psi_RCB_borderRank_ge_six

/-- info: 'SemaevRCB.Psi_RCB_hasFormalBorderRankLe_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Psi_RCB_hasFormalBorderRankLe_six

/-- info: 'SemaevRCB.rcb_border_rank_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_border_rank_nine

/-- info: 'SemaevRCB.rcb_rank_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_rank_dichotomy

/-- info: 'SemaevRCB.rcb_rank_rat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_rank_rat

/-- info: 'SemaevRCB.rcb_rank_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_rank_real

/-- info: 'SemaevRCB.rcb_rank_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_rank_complex

/-- info: 'SemaevRCB.rcb_rank_algebraicClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_rank_algebraicClosure

/-- info: 'SemaevRCB.rcb_rank_zmod_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.rcb_rank_zmod_prime

/-! ### `SemaevRCB.SaturatedFlattening` Headline Theorems -/

/-- info: 'SemaevRCB.linearMap_rank_sum_saturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.linearMap_rank_sum_saturation

/-- info: 'SemaevRCB.matrix_trace_eq_rank_of_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.matrix_trace_eq_rank_of_idempotent

/-- info: 'SemaevRCB.matrix_sum_one_saturated_idempotents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.matrix_sum_one_saturated_idempotents

/-- info: 'SemaevRCB.trace_obstruction_saturated_flattening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.trace_obstruction_saturated_flattening

/-- info: 'SemaevRCB.det_one_add_X_smul_of_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.det_one_add_X_smul_of_idempotent

/-- info: 'SemaevRCB.det_add_smul_saturated_summand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.det_add_smul_saturated_summand

/-- info: 'SemaevRCB.det_add_smul_saturated_flattening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.det_add_smul_saturated_flattening

/-- info: 'SemaevRCB.det_stdTraceGram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.det_stdTraceGram

/-- info: 'SemaevRCB.det_equiangularMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.det_equiangularMat

/-- info: 'SemaevRCB.equiangular_idempotent_basis_discriminant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.equiangular_idempotent_basis_discriminant

/-- info: 'SemaevRCB.no_equiangular_idempotent_basis_orderedField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.no_equiangular_idempotent_basis_orderedField

/-! ### `SemaevRCB.GeneralMinorsAndChar3` (Trace, Char-3 Hierarchy, & 14-Term KGP) Headline Theorems -/

/-- info: 'SemaevRCB.koszulFlat_Im_eps3_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.koszulFlat_Im_eps3_mul_inv

/-- info: 'SemaevRCB.koszulFlat_Im_eps3_normalized_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.koszulFlat_Im_eps3_normalized_trace

/-- info: 'SemaevRCB.Im_eps3_char3_rank_ge_floor_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Im_eps3_char3_rank_ge_floor_add_one

/-- info: 'SemaevRCB.Im_eps3_even_char3_strict_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Im_eps3_even_char3_strict_gap

/-- info: 'SemaevRCB.symEps3Block_char3_strict_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.symEps3Block_char3_strict_gap

/-- info: 'SemaevRCB.I3_eps3_hasTensorRankLe_fourteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I3_eps3_hasTensorRankLe_fourteen

/-- info: 'SemaevRCB.I3_eps3_exact_rank_fourteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I3_eps3_exact_rank_fourteen

/-- info: 'SemaevRCB.I4_eps3_hasTensorRankLe_nineteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I4_eps3_hasTensorRankLe_nineteen

/-- info: 'SemaevRCB.I5_eps3_hasTensorRankLe_twentyfour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I5_eps3_hasTensorRankLe_twentyfour

/-- info: 'SemaevRCB.I6_eps3_hasTensorRankLe_twentyeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I6_eps3_hasTensorRankLe_twentyeight

/-- info: 'SemaevRCB.I4_eps3_char3_exact_rank_nineteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I4_eps3_char3_exact_rank_nineteen

/-- info: 'SemaevRCB.I6_eps3_char3_exact_rank_twentyeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.I6_eps3_char3_exact_rank_twentyeight

/-! ### `SemaevRCB.ExteriorArithmetic` Headline Theorems -/

/-- info: 'SemaevRCB.Omega_p_isSym12_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.Omega_p_isSym12_of_even

/-- info: 'SemaevRCB.U_pm_isSym12_of_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.U_pm_isSym12_of_even

/-- info: 'SemaevRCB.psiFlat_pure_rank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.psiFlat_pure_rank_le

/-- info: 'SemaevRCB.psiFlat_pm_pure_rank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.psiFlat_pm_pure_rank_le

/-- info: 'SemaevRCB.kneserMat_mul_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.kneserMat_mul_adj

/-- info: 'SemaevRCB.kneserMat_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.kneserMat_mul_inv

/-- info: 'SemaevRCB.psiFlat_Omega_signed_kneser_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.psiFlat_Omega_signed_kneser_block

/-- info: 'SemaevRCB.psiFlat_Omega_invertible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.psiFlat_Omega_invertible

/-- info: 'SemaevRCB.psiFlat_pm_U_invertible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.psiFlat_pm_U_invertible

/-- info: 'SemaevRCB.psiFlat_Omega_coord_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.psiFlat_Omega_coord_trace

/-- info: 'SemaevRCB.psiFlat_pm_coord_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.psiFlat_pm_coord_trace

/-- info: 'SemaevRCB.shared_exterior_prime_char_rank_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.shared_exterior_prime_char_rank_ge

/-- info: 'SemaevRCB.pfaffian5_shared3_char5_rank_ge_51' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SemaevRCB.pfaffian5_shared3_char5_rank_ge_51

/-! ## Paper 2 (`CarryAutomaton`) Headline Theorems -/

/-- info: 'CarryAutomaton.M_rel_edge_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.M_rel_edge_card

/-- info: 'CarryAutomaton.M_rel_two_by_two_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.M_rel_two_by_two_obstruction

/-- info: 'CarryAutomaton.M_rel_no_single_valued' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.M_rel_no_single_valued

/-- info: 'CarryAutomaton.M_rel_core_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.M_rel_core_factorization

/-- info: 'CarryAutomaton.K_coreRel_biclique_iff_three_conds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.K_coreRel_biclique_iff_three_conds

/-- info: 'CarryAutomaton.maxCocyclePairs_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.maxCocyclePairs_card

/-- info: 'CarryAutomaton.maxCocyclePairs_shape_gf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.maxCocyclePairs_shape_gf

/-- info: 'CarryAutomaton.K_coreRel_maxBicliques_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.K_coreRel_maxBicliques_card

/-- info: 'CarryAutomaton.M_rel_biclique_area_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.M_rel_biclique_area_le

/-- info: 'CarryAutomaton.modular_quotient_carry_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.modular_quotient_carry_identity

/-- info: 'CarryAutomaton.mechanismIICStar_isPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.mechanismIICStar_isPartition

/-- info: 'CarryAutomaton.bc_M_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.bc_M_lower

/-- info: 'CarryAutomaton.prod_load_M_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.prod_load_M_lower

/-- info: 'CarryAutomaton.weighted_sum_M_lower_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.weighted_sum_M_lower_real

/-- info: 'CarryAutomaton.weighted_sum_M_attained_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.weighted_sum_M_attained_real

/-- info: 'CarryAutomaton.bc_M_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.bc_M_eq_iff

/-- info: 'CarryAutomaton.prod_load_M_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.prod_load_M_eq_iff

/-- info: 'CarryAutomaton.abstract_balanced_star_blowup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.abstract_balanced_star_blowup

/-- info: 'CarryAutomaton.local_load_lower_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.local_load_lower_K

/-- info: 'CarryAutomaton.local_load_lower_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.local_load_lower_M

/-- info: 'CarryAutomaton.starBlowupPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.starBlowupPartition

/-- info: 'CarryAutomaton.starBlowupPartition_isPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.starBlowupPartition_isPartition

/-- info: 'CarryAutomaton.starBlowupPartition_hasMaxLoadLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.starBlowupPartition_hasMaxLoadLe

/-- info: 'CarryAutomaton.exists_optimal_local_partition_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.exists_optimal_local_partition_K

/-- info: 'CarryAutomaton.exists_optimal_local_partition_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.exists_optimal_local_partition_M

/-- info: 'CarryAutomaton.no_equivariant_cover_K4_load_le_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.no_equivariant_cover_K4_load_le_3

/-- info: 'CarryAutomaton.prop_A1_s3_grid_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.prop_A1_s3_grid_obstruction

/-- info: 'CarryAutomaton.M_rel_group_circulant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.M_rel_group_circulant

/-- info: 'CarryAutomaton.K_coreRel_group_circulant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.K_coreRel_group_circulant

/-- info: 'CarryAutomaton.rank_K_coreMat_char_ne_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.rank_K_coreMat_char_ne_two

/-- info: 'CarryAutomaton.rank_M_mat_char_ne_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.rank_M_mat_char_ne_two

/-- info: 'CarryAutomaton.rank_K_coreMat_char_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.rank_K_coreMat_char_two

/-- info: 'CarryAutomaton.rank_K_coreMat_char_two_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.rank_K_coreMat_char_two_choose

/-- info: 'CarryAutomaton.rank_M_mat_char_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.rank_M_mat_char_two

/-- info: 'CarryAutomaton.walsh_conj_K_coreMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.walsh_conj_K_coreMat

/-- info: 'CarryAutomaton.D_sign_conj_Htilde_eq_G_alpha_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.D_sign_conj_Htilde_eq_G_alpha_int

/-- info: 'CarryAutomaton.spectralNorm2_H_alpha_eq_envelope_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.spectralNorm2_H_alpha_eq_envelope_iff

/-- info: 'CarryAutomaton.centeredSpectralGap_K_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.centeredSpectralGap_K_core

/-- info: 'CarryAutomaton.centeredSpectralGap_M_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.centeredSpectralGap_M_mat

/-- info: 'CarryAutomaton.disj_embedded_in_K_coreRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.disj_embedded_in_K_coreRel

/-- info: 'CarryAutomaton.zero_cover_K_coreRel_card_le_eight_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.zero_cover_K_coreRel_card_le_eight_s

/-- info: 'CarryAutomaton.margin_witness_K_coreRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.margin_witness_K_coreRel

/-- info: 'CarryAutomaton.centered_spectral_biclique_cover_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.centered_spectral_biclique_cover_div_le

/-- info: 'CarryAutomaton.K_coreRel_spectral_avg_degree_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CarryAutomaton.K_coreRel_spectral_avg_degree_lower_bound
