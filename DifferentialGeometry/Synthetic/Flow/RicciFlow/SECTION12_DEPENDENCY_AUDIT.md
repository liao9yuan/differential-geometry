# Section 12 Dependency Audit

This file inventories the first-party Lean dependency tree for `DifferentialGeometry/Synthetic/Flow/RicciFlow/HamiltonThreeManifold.lean`, the Section 12 final assembly target. It deliberately excludes Mathlib and generated `.olean` dependencies.

## Scope

- Root: `DifferentialGeometry/Synthetic/Flow/RicciFlow/HamiltonThreeManifold.lean`
- First-party modules in closure: 41
- Theorem/lemma declarations in closure: 690
- All declaration-like entries found: 1066

## Immediate Refactor Conclusions

- Product, chain, and power rules should be proved once in a general scalar calculus layer, not carried as one-off hypotheses for Lemma 10.5 or later P4 lemmas.
- `ScalarParabolicCalculus` and `ScalarParabolicDoubleDivergenceCalculus` are useful scaffolding, but the long-term target should prove their fields from a concrete `dt`, `grad`, `divergence`, and `laplacian = div grad` calculation.
- Existing reusable pieces already present: `TimeDerivativeData.dt_apply_mul`, `divergence_smul`, `scalarDoubleDivergenceAt_eq_laplacian`, `heat_product_rule_of_doubleDivergence`, and `heat_power_rule_of_doubleDivergence`.
- Tensor maximum-principle consumers should use `tensor_wmp_preserve_cone_of_initial` instead of locally repackaging pointwise initial cone hypotheses as `IsInitiallyInCone`.
- Missing generic scalar calculus pieces: `grad_mul`, `grad_power`, `laplacian_mul`, `laplacian_power`, and a concrete positive-power API, probably over `Real` with `rpow` and positivity hypotheses.
- Case-specific Ricci-flow evolution identities should consume these generic scalar rules, not restate product-rule or chain-rule assumptions.

## First-Party Import Closure

- `DifferentialGeometry/Synthetic/Flow/RicciFlow/HamiltonThreeManifold.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/ImprovedPinching.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/Pinching.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/CurvatureAlgebra.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RicciNorm.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/ScalarCurvature.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Connection.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Basic.lean`
- `DifferentialGeometry/Synthetic/Algebra/VectorFieldAlgebra.lean`
- `DifferentialGeometry/Synthetic/Algebra/TensorAlgebra.lean`
- `DifferentialGeometry/Synthetic/Algebra/Metric.lean`
- `DifferentialGeometry/Synthetic/Analysis/NablaOnTensors.lean`
- `DifferentialGeometry/Synthetic/Analysis/TimeOnTensors.lean`
- `DifferentialGeometry/Synthetic/Geometry/Connection.lean`
- `DifferentialGeometry/Synthetic/Geometry/ConnectionExtended.lean`
- `DifferentialGeometry/Synthetic/Operator/Variation.lean`
- `DifferentialGeometry/Synthetic/Analysis/NablaTimeInteraction.lean`
- `DifferentialGeometry/Synthetic/Operator/Laplacian.lean`
- `DifferentialGeometry/Synthetic/Operator/Hessian.lean`
- `DifferentialGeometry/Synthetic/Operator/Gradient.lean`
- `DifferentialGeometry/Synthetic/Operator/CovariantDerivative.lean`
- `DifferentialGeometry/Synthetic/Geometry/CurvatureContractions.lean`
- `DifferentialGeometry/Synthetic/Algebra/MetricTrace.lean`
- `DifferentialGeometry/Synthetic/Operator/SpatialConstant.lean`
- `DifferentialGeometry/Synthetic/Analysis/Parabolic/ScalarCalculus.lean`
- `DifferentialGeometry/Synthetic/Analysis/Parabolic/ScalarMaximumPrinciple.lean`
- `DifferentialGeometry/Synthetic/Operator/Divergence.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/RicciReaction.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/RiemannFromRicci3D.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/Compactness.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/BlowUp.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/Existence.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Calculus.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannEvolution.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannVariation.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannLaplacian.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Ricci.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Lichnerowicz.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Gradient.lean`
- `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Laplacian.lean`
- `DifferentialGeometry/Synthetic/Analysis/Parabolic/TensorMaximumPrinciple.lean`

## Final Section 12 Gateways

- `hamilton_three_manifold_exists_constant_positive_metric`: final target; consumes `Nonempty HamiltonSection12AssemblyData`.
- `hamilton_three_manifold_from_section12_claims`: final convenience wrapper from `HamiltonSection12Claims`.
- `hamilton_section12_assembly_from_claims`: packs claims into assembly data.
- `hamilton_three_manifold_from_typed_input`: typed-input wrapper using `HamiltonSyntheticAnalyticInputs` plus `HamiltonSection12ClaimBuilderInput`.
- `HamiltonSection12ClaimBuilderInput`: current collaborator-facing claim bundle for analytic/global inputs.

## Theorem And Lemma Inventory

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/HamiltonThreeManifold.lean`

- L109 `theorem ricci_nonnegative_preserved_by_tensor_wmp`
- L142 `theorem ricciPinchingTensorAt_eval`
- L160 `theorem ricci_pinching_tensor_nonnegative_preserved_by_tensor_wmp`
- L186 `theorem ricciPinched_of_pinching_tensor_nonnegative`
- L207 `theorem ricci_pinched_preserved_by_tensor_wmp`
- L241 `theorem ricci_pinched_preserved_by_tensor_wmp_of_sub_nonneg_iff`
- L274 `theorem positive_initial_scalar_from_typed_positive_ricci`
- L284 `theorem finite_time_from_typed_positive_ricci`
- L298 `theorem finite_time_bound_from_typed_positive_ricci`
- L312 `theorem curvature_blow_up_from_typed_maximal_time`
- L326 `theorem scalar_unbounded_from_typed_maximal_time`
- L342 `theorem point_selection_rescaling_from_typed_maximal_time`
- L368 `theorem curvature_blow_up_from_typed_finite_time`
- L383 `theorem scalar_unbounded_from_typed_finite_time`
- L401 `theorem rescaling_certificate_from_typed_input`
- L442 `theorem rescaling_convergence_data_from_typed_input`
- L503 `theorem limit_scalar_positive_everywhere_from_strong_mp`
- L534 `theorem limit_ricci_nonnegative_from_cgh_curvature_convergence`
- L560 `theorem original_limit_diffeomorphism_from_compact_limit_at_index`
- L588 `theorem limit_constant_positive_from_einstein`
- L608 `theorem limit_compact_from_constant_positive`
- L631 `theorem hamilton_limit_scalar_normalized_from_cgh_convergence`
- L1233 `theorem section12_claims_from_typed_input`
- L1317 `theorem hamilton_three_manifold_from_typed_input_explicit_interfaces`
- L1406 `theorem hamilton_three_manifold_from_typed_input`
- L1442 `theorem hamilton_three_manifold_from_typed_input_with_p3_eigenvalue_packages`
- L1468 `theorem hamilton_three_manifold_from_typed_input_with_p1_named_calculus`
- L1493 `theorem hamilton_section12_assembly_from_claims`
- L1567 `theorem hamilton_three_manifold_exists_constant_positive_metric`
- L1586 `theorem hamilton_three_manifold_from_section12_claims`
- L1601 `theorem hamilton_section12_claims_smoke`
- L1636 `theorem hamilton_three_manifold_from_black_boxes`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/ImprovedPinching.lean`

- L72 `theorem quotientEvolutionRHS_eval`
- L111 `theorem quotientEvolutionIdentity_algebraic_of_rewritten_contributions`
- L154 `theorem quotientEvolutionIdentity_of_scalar_parabolic_calculus`
- L215 `theorem hamiltonPinchingEvolutionRHS_eval`
- L252 `theorem hamiltonPinchingReactionExpression_nonpositive_of_Q_lower_bound`
- L275 `theorem hamiltonPinchingWeightedReaction_nonpositive_of_Q_lower_bound`
- L392 `theorem shifted_heat_eq_reaction_of_quotient_evolution`
- L448 `theorem hamilton_improved_pinching_shifted_subsolution`
- L503 `theorem improved_pinching_P_bound_from_wmp`
- L513 `theorem improved_ricci_pinching_ratio_bound_from_wmp`
- L524 `theorem improved_ricci_pinching_ratio_bound_from_hamilton_producer`
- L548 `theorem hamiltonImprovedPinchingQuantity_eval`
- L561 `theorem hamiltonImprovedPinchingQuantity_eq_from_ricci`
- L584 `theorem pinching_ratio_eq_P_mul_decay_of_denominator_decay`
- L615 `theorem HamiltonPinchingQuotientRealizationData.ratio_decay_eq`
- L630 `theorem ratio_decay_relation_of_quotient_realization`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/Pinching.lean`

- L33 `theorem ricciPositive_nonnegative`
- L73 `theorem improved_pinching_from_interface`
- L93 `theorem ricciEigenNormSq3_le_scalar_sq_of_nonnegative`
- L125 `theorem hamiltonCubicQ3_factorized`
- L147 `theorem ricciEigenRiemannReaction3_cubicQ_relation`
- L158 `theorem hamilton3D_cubic_reaction_simplification_of_eigen_reaction`
- L188 `theorem hamiltonCubicQ3_ordered_gaps`
- L195 `theorem ricciEigenPairwiseGapSq3_ordered_gaps`
- L201 `theorem hamiltonCubicQOrderedGaps3_sub_zSq_pairwise`
- L207 `theorem hamiltonCubicQOrderedGaps3_ge_zSq_pairwise`
- L219 `theorem hamiltonCubicQOrderedGaps3_lower_bound`
- L257 `theorem hamiltonCubicQ3_lower_bound_ordered_eigenvalues`
- L304 `theorem hamiltonCubicQ3_lower_bound_ordered_nonnegative_eigenvalues`
- L374 `theorem hamiltonCubicQ_eq_hamiltonCubicQ3_of_eigenvalue_realization`
- L390 `theorem hamiltonCubicQ_lower_bound_of_ordered_nonnegative_eigenvalue_realization`
- L433 `theorem tracefreeRicciPinchingQuantity_eval`
- L447 `theorem tracefreeRicciPinchingQuantity_expand_abstractTraceDimension`
- L466 `theorem tracefreeRicciPinchingQuantity_eq_ricciNorm_div_scalarSq_sub_nInv`
- L498 `theorem tracefreeRicciPinchingQuantity_eq_ricciNorm_div_scalarSq_sub_nInv_of_dimensionThree`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/CurvatureAlgebra.lean`

- L32 `theorem isDimensionThree_abstractTraceDimension`
- L37 `theorem isDimensionThree_nInv_normalization`
- L71 `theorem riemannFromRicci3DRHS_eval`
- L107 `theorem riemannFromRicci3DFormula_half`
- L118 `theorem riemannFromRicci3DFormula_apply`
- L139 `theorem riemannFromRicci3DFormula_of_formula`
- L155 `theorem isHalfCoefficient_inv_two`
- L163 `theorem coeff_cancel_of_ne`
- L173 `theorem isThirdCoefficient_of_mul_three_eq_one`
- L184 `theorem einsteinRiemannCoefficient_sixth`
- L211 `theorem einsteinRicciFormula_of_tracefree_ricci_tensor_eq_zero`
- L263 `theorem ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_ricciForm_tensor_symm`
- L282 `theorem rawCovDeriv_ricciForm_tensor_eq_covDerivRc`
- L296 `theorem covDeriv02TraceCovector_ricciForm_tensor_apply`
- L312 `theorem covDeriv02TraceCovector_swap_ricciForm_tensor_apply`
- L346 `theorem covDivergence02Endomorphism_swap_ricciForm_metric_apply`
- L367 `theorem ricciDivergenceAtSecond_eq_trace_swap_ricci_divergence_endomorphism`
- L386 `theorem contractedBianchiDivPattern_apply_eq_neg_ricciDivergenceAtSecond_of_neg_trace_swap_ricci_divergence`
- L413 `theorem Rc_symm_of_metric_adjoint_trace_invariant`
- L445 `theorem ricciForm_tensor_symm_of_Rc_symm`
- L473 `theorem ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_Rc_symm`
- L492 `theorem ricciForm_tensor_symm_of_metric_adjoint_trace_invariant`
- L512 `theorem ricciDivergenceAtSecond_eq_ricciDivergenceAt_of_metric_adjoint_trace_invariant`
- L548 `theorem covDerivRmEndomorphism_apply`
- L563 `theorem covDerivRc_eq_trace_covDerivRmEndomorphism`
- L591 `theorem grad_R_eq_trace_covDerivRicciEndomorphism`
- L607 `theorem covDerivRicciEndomorphism_metric_apply`
- L638 `theorem contractedBianchiGradPattern_apply_eq_grad_R_of_trace_covDerivRicciEndomorphism`
- L673 `theorem contractedSecondBianchi_apply`
- L692 `theorem contractedSecondBianchiIdentity_from_divergence_formula`
- L711 `theorem contractedSecondBianchiIdentity_from_traced_second_bianchi`
- L841 `theorem contractedBianchiDivPattern_apply_cyclic_tensor_sum`
- L876 `theorem contractedBianchiDivPattern_apply_cycle_left_eq_divFubiniPattern`
- L896 `theorem contractedBianchiDivPattern_apply_cycle_right_eq_gradPattern`
- L915 `theorem contractedBianchi_named_patterns_traced_cyclic_sum_from_slot_audit`
- L951 `theorem contractedBianchi_named_patterns_traced_cyclic_sum`
- L973 `theorem contractedBianchiDivPattern_apply_eq_neg_ricciDivergence`
- L995 `theorem contractedBianchiDivPattern_apply_eq_neg_ricciDivergence_of_second_slot`
- L1022 `theorem contractedBianchiGradPattern_apply_eq_grad_R`
- L1041 `theorem contractedBianchiDivFubiniPattern_apply_eq_divPattern`
- L1186 `theorem traced_second_bianchi_from_double_metric_trace_data`
- L1222 `theorem contractedSecondBianchiIdentity_from_double_metric_trace_data`
- L1239 `theorem contractedSecondBianchiIdentity_from_named_double_trace_patterns`
- L1277 `theorem contractedSecondBianchiIdentity_from_named_patterns_and_metric_fubini`
- L1318 `theorem contractedSecondBianchiIdentity_from_second_bianchi_named_patterns`
- L1390 `theorem hasContractedSecondBianchiNamedPatternCalculus_of_trace_divergence_trace_adjoint_and_grad_trace`
- L1456 `theorem einsteinDivergenceFormula_of_einsteinRicciFormula`
- L1493 `theorem tracefreeRicciDivergenceAt_eq_ricciDivergence_sub`
- L1516 `theorem tracefreeRicciDivergenceAt_zero_of_tracefree_ricci_tensor_eq_zero`
- L1534 `theorem scalar_spatial_constant_of_contracted_bianchi_and_tracefree_ricci_zero_via_divergence`
- L1572 `theorem scalar_spatial_constant_of_contracted_bianchi_and_einstein_divergence`
- L1601 `theorem scalar_spatial_constant_of_contracted_bianchi_and_tracefree_ricci_zero`
- L1634 `theorem einsteinRiemannCoefficient_algebra`
- L1645 `theorem riemannFromRicci3DFormula_constant_curvature_of_einstein`
- L1685 `theorem curvature_control_from_interface`
- L1697 `theorem curvature_control_by_scalar_from_interface`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RicciNorm.lean`

- L39 `theorem tracefree_ricci_tensor_eval`
- L64 `theorem tracefree_ricci_norm_sq_expand`
- L88 `theorem tracefree_ricci_norm_sq_expand_scalar`
- L115 `theorem tracefree_ricci_norm_sq_expand_closed`
- L160 `theorem tracefree_ricci_norm_sq_expand_abstractTraceDimension`
- L205 `theorem ricci_norm_evolution_from_interface`
- L242 `theorem tracefree_ricci_norm_evolution_from_interface`
- L278 `theorem ricci_norm_heat_eq_of_dt_laplacian_components`
- L305 `theorem ricci_norm_heat_eq_lemma67`
- L324 `theorem ricci_norm_heat_operator_eq_of_dt_laplacian_components`
- L385 `theorem tracefreeRicciNormHamilton3DRHS_eval`
- L401 `theorem scalarHeatOperator_eval`
- L418 `theorem tracefree_ricci_norm_hamilton3D_heat_operator_from_interface`
- L444 `theorem tracefree_ricci_norm_hamilton3D_heat_operator_from_time_laplacian`
- L455 `theorem tracefree_ricci_norm_hamilton3D_time_laplacian_from_interface`
- L477 `theorem hamilton3D_cubic_reaction_simplification`
- L502 `theorem hamilton3D_tracefree_norm_rhs_of_cubic_reaction`
- L577 `theorem scalarLaplacianAlongTimeSlice_eval`
- L609 `theorem ricciNormSqAlongFlow_eval`
- L640 `theorem scalarCurvatureAlongFlow_eval`
- L661 `theorem scalar_heat_eq_of_full_evolution`
- L720 `theorem tracefreeRicciNormSqAlongFlow_eval`
- L739 `theorem tracefree_ricci_norm_dt_eq_of_ricci_norm_dt_and_scalar_dt`
- L857 `theorem tracefree_ricci_norm_laplacian_eq_of_ricci_norm_laplacian_and_scalar_square`
- L936 `theorem hamilton3D_tracefree_norm_evolution_eq_of_components`
- L991 `theorem hamilton3D_tracefree_norm_eq_of_dt_lap_components`
- L1086 `theorem hamilton3D_tracefree_norm_eq_of_cubic_reaction_components`
- L1182 `theorem hamilton3D_tracefree_norm_eq_of_heat_components`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/ScalarCurvature.lean`

- L64 `theorem tensor_02_endo_add`
- L76 `theorem tensor_02_endo_smul`
- L84 `theorem tensor_02_endo_neg`
- L90 `theorem tensor_02_endo_sub`
- L97 `theorem tensor_02_endo_metric`
- L132 `theorem tensor_inner_02_add_left`
- L146 `theorem tensor_inner_02_smul_left`
- L156 `theorem tensor_inner_02_neg_left`
- L163 `theorem tensor_inner_02_sub_left`
- L171 `theorem tensor_inner_02_add_right`
- L185 `theorem tensor_inner_02_smul_right`
- L197 `theorem tensor_inner_02_neg_right`
- L204 `theorem tensor_inner_02_sub_right`
- L212 `theorem tensor_inner_02_symm`
- L218 `theorem tensor_inner_02_metric_metric`
- L226 `theorem tensor_inner_02_sub_sub`
- L272 `theorem tensor_02_endo_ricciForm`
- L286 `theorem tensor_inner_02_ricciForm`
- L301 `theorem tensor_trace_cube_02_ricciForm`
- L314 `theorem tensor_inner_02_ricciForm_metric`
- L329 `theorem tensor_inner_02_metric_ricciForm`
- L376 `theorem ricci_raise_variation`
- L478 `theorem scalar_curvature_evolution`
- L559 `theorem ricciTraceIdentity_from_rhs_evolution`
- L588 `theorem scalar_curvature_evolution_full`
- L622 `theorem scalar_curvature_evolution_full_from_rhs`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Connection.lean`

- L54 `theorem connection_evolution_combined`
- L140 `theorem connection_evolution`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Basic.lean`

- L72 `theorem inverse_metric_var_form_flat_eq_neg_metric_var`
- L159 `theorem Rm_tensor_eval`
- L231 `theorem ricciForm_tensor_eval`
- L243 `theorem ricciForm_tensor_smul_eval`
- L285 `theorem IsRicciFlow.levi_civita`
- L298 `theorem IsRicciFlow.evolution`
- L317 `theorem IsRicciFlow.inverse_metric_variation`
- L342 `theorem IsRicciFlow.metric_compat`
- L355 `theorem IsRicciFlow.torsion_free`

### `DifferentialGeometry/Synthetic/Algebra/VectorFieldAlgebra.lean`

- L106 `theorem eval_lift`
- L112 `theorem lift_add`
- L118 `theorem lift_mul`
- L124 `theorem isSmoothFam_const`
- L129 `theorem isSmoothFam_add`
- L135 `theorem isSmoothFam_mul`
- L141 `theorem isSmoothFam_neg`
- L167 `theorem bracket_spec`
- L209 `theorem action_add_left`
- L213 `theorem action_smul_left`
- L217 `theorem action_add_right`
- L222 `theorem action_smul_right`
- L228 `theorem action_algebraMap`
- L232 `theorem action_one`
- L235 `theorem action_zero_left`
- L238 `theorem action_zero_right`
- L241 `theorem action_neg_right`
- L245 `theorem action_sub_right`
- L249 `theorem action_neg_left`
- L253 `theorem action_sub_left`
- L258 `theorem action_mul_algebraMap`
- L264 `theorem eq_of_action_eq`
- L282 `theorem action_bracket`
- L288 `theorem bracket_antisymm`
- L295 `theorem bracket_add_left`
- L302 `theorem bracket_add_right`
- L311 `theorem bracket_smul_left`
- L322 `theorem bracket_smul_right`
- L333 `theorem jacobi_identity`
- L342 `theorem bracket_self`
- L347 `theorem bracket_zero_left`
- L352 `theorem bracket_zero_right`
- L357 `theorem bracket_neg_left`
- L363 `theorem bracket_neg_right`
- L379 `theorem dt_add`
- L383 `theorem dt_mul`
- L388 `theorem t_const_R`
- L392 `theorem time_algebraMap_apply`
- L395 `theorem dt_sub`
- L398 `theorem dt_neg`
- L401 `theorem dt_zero`
- L405 `theorem dt_smul_const`
- L426 `theorem TimeDerivativeData.eval_zero`
- L434 `theorem TimeDerivativeData.isSmoothFam_sub`
- L441 `theorem TimeDerivativeData.isSmoothFam_sum`
- L458 `theorem TimeDerivativeData.isSmoothFam_const_mul`
- L465 `theorem TimeDerivativeData.dt_apply_add`
- L472 `theorem TimeDerivativeData.dt_apply_const`
- L478 `theorem TimeDerivativeData.dt_apply_mul`
- L487 `theorem TimeDerivativeData.dt_apply_const_mul`
- L495 `theorem TimeDerivativeData.dt_apply_neg`
- L507 `theorem TimeDerivativeData.dt_apply_sub`
- L516 `theorem TimeDerivativeData.dt_apply_sum`
- L540 `theorem TimeDerivativeData.dt_apply_matrix_product`
- L574 `theorem TimeDerivativeData.dt_apply_matrix_product_eq_const`
- L601 `theorem TimeDerivativeData.dt_apply_matrix_inverse_left`

### `DifferentialGeometry/Synthetic/Algebra/TensorAlgebra.lean`

- L86 `theorem tensor_ext`
- L120 `theorem swap_covariant_eval`
- L124 `theorem swap_contravariant_eval`
- L252 `theorem tensor_prod_eval`
- L312 `theorem endo_to_tensor_eval`
- L383 `theorem toScalar_fromScalar`
- L385 `theorem fromVector_eval`
- L400 `theorem delta_tensor_eval`
- L419 `theorem contract_outerProduct`
- L424 `theorem contract_comm`
- L428 `theorem contract_add`
- L432 `theorem contract_smul`
- L454 `theorem data_eval_single_contract`
- L471 `theorem tensor_eval_add`
- L476 `theorem tensor_eval_smul`
- L481 `theorem vectorToData_add`
- L487 `theorem vectorToData_smul`
- L509 `theorem contract_general_add`
- L525 `theorem contract_general_smul`
- L540 `theorem contract_general_0_0`
- L564 `theorem contract_general_13_middle_trace_eval`
- L606 `theorem tensor_contract_twice_swap`
- L615 `theorem tensor_contract_twice_swap_of_fubini`
- L666 `theorem tensor_contract_swap_covariant_succ_of_naturality`
- L675 `theorem tensor_contract_swap_contravariant_succ_of_naturality`
- L682 `theorem tensor_contract_swap_covariant_succ`
- L689 `theorem tensor_contract_swap_contravariant_succ`
- L696 `theorem hasTensorContractSwapNaturality_of_naturality`
- L742 `theorem TimeTrComm.of_pi`

### `DifferentialGeometry/Synthetic/Algebra/Metric.lean`

- L75 `theorem MetricDuality.g_tensor_smul_eval`
- L88 `theorem MetricDuality.inverse_eval`
- L93 `theorem MetricDuality.g_symm`
- L102 `theorem MetricDuality.g_inv_symm`
- L119 `theorem MetricDuality.g_inv_symm_tensor`
- L138 `theorem MetricDuality.g_add_left`
- L146 `theorem MetricDuality.g_smul_left`
- L156 `theorem MetricDuality.g_add_right`
- L160 `theorem MetricDuality.g_smul_right`
- L169 `theorem MetricDuality.sharpSpec`
- L176 `theorem MetricDuality.g_sharp`
- L182 `theorem MetricDuality.sharp_flat`
- L188 `theorem MetricDuality.flat_injective`
- L194 `theorem MetricDuality.sharp_add`
- L203 `theorem MetricDuality.sharp_smul`
- L247 `theorem nabla_g_zero`
- L278 `theorem nabla_dual_flat`
- L303 `theorem nabla_g_inv_zero`
- L401 `theorem raise_index_add`
- L415 `theorem raise_index_smul`
- L429 `theorem raise_index_zero`
- L438 `theorem raise_index_neg`
- L447 `theorem raise_index_sub`
- L456 `theorem metric_trace_add`
- L465 `theorem metric_trace_smul`
- L474 `theorem metric_trace_zero`
- L483 `theorem metric_trace_neg`
- L493 `theorem metric_trace_sub`
- L512 `theorem lower_index_eval_11`
- L614 `theorem nabla_raise_index_comm`
- L704 `theorem nabla_metric_trace_comm`
- L741 `theorem t_const_V`
- L747 `theorem t_const_scalar`
- L755 `theorem dt_metric_const_args`
- L767 `theorem t_metric_one_varying_left`
- L778 `theorem t_metric_one_varying_right`
- L806 `theorem t_metric_partial_variations`
- L817 `theorem t_metric_fixed_both_varying`

### `DifferentialGeometry/Synthetic/Analysis/NablaOnTensors.lean`

- L39 `theorem nabla_dual_map_add`
- L48 `theorem nabla_dual_leibniz`
- L310 `theorem nabla_tensor_eval`
- L322 `theorem nabla_scalar`
- L330 `theorem nabla_add`
- L340 `theorem nabla_smul`
- L350 `theorem nabla_smul_left`
- L382 `theorem nabla_vector`
- L408 `theorem nabla_add_left`
- L589 `theorem covariantDerivativeTensor_eval_cons`
- L603 `theorem nabla_delta`
- L619 `theorem nabla_swap`
- L660 `theorem nabla_tensor_prod`
- L766 `theorem nabla_contract`

### `DifferentialGeometry/Synthetic/Analysis/TimeOnTensors.lean`

- L86 `theorem dt_tensor_eval`
- L93 `theorem dt_tensor_const`
- L102 `theorem dt_tensor_add`
- L116 `theorem dt_tensor_neg`
- L127 `theorem dt_tensor_sub`
- L142 `theorem dt_tensor_smul`
- L156 `theorem dt_tensor_smul_const`
- L168 `theorem dt_tensor_prod`
- L187 `theorem dt_tensor_swap`
- L205 `theorem dt_tr`

### `DifferentialGeometry/Synthetic/Geometry/Connection.lean`

- L41 `theorem conn_zero_left`
- L49 `theorem conn_neg_left`
- L56 `theorem conn_sub_left`
- L61 `theorem conn_zero_right`
- L68 `theorem conn_neg_right`
- L74 `theorem conn_sub_right`
- L94 `theorem Rm_antisymm`
- L100 `theorem Rm_add_Z`
- L107 `theorem Rm_add_X`
- L114 `theorem Rm_add_Y`
- L121 `theorem Rm_smul_Z`
- L139 `theorem Rm_smul_Y`
- L151 `theorem Rm_smul_X`
- L175 `theorem first_bianchi`
- L231 `theorem levi_civita_uniqueness`
- L268 `theorem Rm_metric_antisymm`
- L335 `theorem second_bianchi`
- L422 `theorem ricci_identity`

### `DifferentialGeometry/Synthetic/Geometry/ConnectionExtended.lean`

- L23 `theorem MetricDuality.g_neg_left`
- L27 `theorem MetricDuality.g_neg_right`
- L31 `theorem MetricDuality.g_sub_left`
- L35 `theorem MetricDuality.g_sub_right`
- L64 `theorem Rm_symm_blocks`
- L113 `theorem R_XY_eval`
- L123 `theorem R_XY_scalar`
- L136 `theorem R_XY_vector`
- L158 `theorem nabla_02_eval`
- L176 `theorem tensor_ricci_identity_02`
- L291 `theorem RicciEndomorphism_spec`
- L433 `theorem koszul_connection_spec`
- L445 `theorem koszul_torsion_free`
- L474 `theorem koszul_metric_compat`
- L501 `theorem levi_civita_exists`
- L510 `theorem levi_civita_unique`
- L531 `theorem koszul_connection_add_right`
- L557 `theorem koszul_connection_add_left`
- L584 `theorem koszul_connection_smul_left`
- L634 `theorem koszul_connection_leibniz`
- L714 `theorem covDerivRm_sum_endo`

### `DifferentialGeometry/Synthetic/Operator/Variation.lean`

- L30 `lemma metric_zero_right`
- L33 `lemma metric_zero_left`
- L59 `lemma metric_var_form_eval`
- L69 `lemma metric_var_form_symm`
- L150 `theorem connection_variation`
- L366 `theorem raise_variation_const`
- L381 `theorem raise_variation`
- L415 `theorem tr_g_variation`

### `DifferentialGeometry/Synthetic/Analysis/NablaTimeInteraction.lean`

- L36 `theorem t_nabla_tensor`
- L140 `theorem conn_var_tensor_eval`
- L227 `theorem t_nabla_eval`
- L292 `theorem conn_var_tensor_add`
- L331 `theorem conn_var_tensor_smul`
- L380 `theorem t_linear_map`
- L408 `theorem t_conn_apply`

### `DifferentialGeometry/Synthetic/Operator/Laplacian.lean`

- L42 `lemma laplacian_add`
- L56 `lemma laplacian_sub`
- L78 `lemma laplacian_smul`

### `DifferentialGeometry/Synthetic/Operator/Hessian.lean`

- L30 `theorem hessian_symm`
- L69 `lemma covariant_differential_add_vec`
- L84 `lemma covariant_differential_smul_vec`
- L157 `lemma hessianForm_add`
- L182 `lemma hessianForm_smul`
- L200 `theorem hessianForm_eval`
- L250 `theorem grad_smul_algebraMap`

### `DifferentialGeometry/Synthetic/Operator/Gradient.lean`

- L31 `lemma g_grad`
- L36 `lemma grad_add`
- L45 `lemma grad_sub`

### `DifferentialGeometry/Synthetic/Operator/CovariantDerivative.lean`

- L73 `lemma rawCovDeriv_add_left`
- L81 `lemma rawCovDeriv_smul_left`
- L93 `lemma rawCovDeriv_add_right`
- L102 `lemma rawCovDeriv_smul_right`
- L130 `theorem covDeriv_eval`
- L151 `theorem metric_covDerivOp_zero`
- L175 `lemma genericCovDeriv_add`
- L184 `lemma genericCovDeriv_smul`
- L204 `lemma genericCovDeriv_contract`
- L238 `theorem covDeriv02TraceCovector_apply`
- L299 `theorem covariantDivergence02At_eval`
- L314 `theorem covDivergence02Endomorphism_add`
- L346 `theorem covariantDivergence02At_add`
- L364 `theorem covariantDivergence02At_zero`
- L392 `theorem covDivergence02Endomorphism_const_smul`
- L423 `theorem covariantDivergence02At_const_smul`
- L443 `theorem covariantDivergence02At_neg`
- L466 `theorem covariantDivergence02At_sub`
- L489 `theorem covariantDivergence02At_smul_metric`

### `DifferentialGeometry/Synthetic/Geometry/CurvatureContractions.lean`

- L125 `theorem loweredRmTensor_eval`
- L136 `theorem loweredRmTensor_apply`
- L148 `theorem Rm_lowered_antisymm_first_pair`
- L158 `theorem Rm_lowered_antisymm_second_pair`
- L169 `theorem Rm_lowered_block_symm`
- L183 `theorem Rm_lowered_first_bianchi`
- L202 `theorem loweredRmTensor_first_bianchi`
- L217 `theorem loweredRmTensor_antisymm_first_pair`
- L230 `theorem loweredRmTensor_antisymm_second_pair`
- L244 `theorem loweredRmTensor_block_symm`
- L291 `theorem LoweredCovDerivRmTensorData.eval_apply`
- L316 `theorem covDerivRmLoweredTensor_eval`
- L340 `theorem covDerivRm_first_bianchi`
- L386 `theorem covDerivRm_lowered_first_bianchi`
- L405 `theorem covDerivRmLoweredTensor_first_bianchi`
- L423 `theorem covDerivRm_antisymm_first_pair`
- L439 `theorem covDerivRm_lowered_antisymm_first_pair`
- L450 `theorem covDerivRmLoweredTensor_antisymm_first_pair`
- L468 `theorem covDerivRm_lowered_antisymm_second_pair`
- L515 `theorem covDerivRmLoweredTensor_antisymm_second_pair`
- L535 `theorem covDerivRm_lowered_block_symm`
- L585 `theorem covDerivRmLoweredTensor_block_symm`
- L617 `theorem covDerivRm_lowered_cyclic_sum`
- L646 `theorem covariantCycle012Left05_eval`
- L664 `theorem covariantCycle012Right05_eval`
- L677 `theorem covDerivRmLoweredTensor_cyclic_sum_tensor`

### `DifferentialGeometry/Synthetic/Algebra/MetricTrace.lean`

- L43 `theorem doubleMetricTrace04_eval`
- L54 `theorem doubleMetricTrace04_add`
- L65 `theorem doubleMetricTrace04_smul`
- L75 `theorem doubleMetricTrace04_zero`
- L84 `theorem doubleMetricTrace04_neg`
- L98 `theorem doubleMetricTrace04_sub`
- L118 `theorem doubleMetricTrace05_eval`
- L129 `theorem doubleMetricTrace05_add`
- L140 `theorem doubleMetricTrace05_smul`
- L150 `theorem doubleMetricTrace05_zero`
- L159 `theorem doubleMetricTrace05_neg`
- L171 `theorem doubleMetricTrace05_sub`
- L202 `theorem doubleMetricTrace04_fubini_apply`
- L213 `theorem doubleMetricTrace05_fubini_apply`
- L302 `theorem tensor_eq_of_fubini`
- L310 `theorem apply_eq_of_fubini`
- L319 `theorem tensor_add`
- L327 `theorem tensor_smul`
- L335 `theorem tensor_zero`
- L342 `theorem tensor_neg`
- L350 `theorem tensor_sub`
- L358 `theorem apply_add`
- L369 `theorem apply_smul`
- L379 `theorem apply_zero`
- L387 `theorem apply_neg`
- L397 `theorem apply_sub`
- L425 `theorem doubleMetricTrace05Pattern_fubini`
- L434 `theorem contractedBianchiDivMetricTraceFubini`

### `DifferentialGeometry/Synthetic/Operator/SpatialConstant.lean`

- L30 `lemma isSpatialConstant_algebraMap`
- L36 `lemma grad_zero_of_const`
- L47 `lemma grad_smul_const`
- L56 `lemma laplacian_zero_of_const`
- L91 `lemma laplacian_const_smul`

### `DifferentialGeometry/Synthetic/Analysis/Parabolic/ScalarCalculus.lean`

- L97 `theorem scalarDoubleDivergenceAt_eq_laplacian`
- L219 `theorem heat_product_rule_of_doubleDivergence`
- L231 `theorem heat_power_rule_of_doubleDivergence`

### `DifferentialGeometry/Synthetic/Analysis/Parabolic/ScalarMaximumPrinciple.lean`

- L37 `theorem scalar_wmp_preserve_nonpositive`
- L52 `theorem scalar_wmp_preserve_upper_bound`

### `DifferentialGeometry/Synthetic/Operator/Divergence.lean`

- L58 `lemma covariant_differential_smul_leibniz`
- L92 `lemma cov_diff_vec_eq_endo`
- L149 `lemma raise_lower_id_11`
- L221 `theorem divergence_eq_tr_conn_endo`
- L238 `theorem divergence_smul`
- L294 `theorem integration_by_parts`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/RicciReaction.lean`

- L179 `theorem ricciReactionContractionResidual_eq_zero`
- L205 `theorem ricciReactionContractionIdentity_from_dim3_calculus`
- L269 `theorem ricciReactionContractionResidual_eq_zero_of_eigenvalue_package`
- L328 `theorem hamiltonCubicQ_eq_hamiltonCubicQ3_of_ricciReactionEigenvalueRealization`
- L401 `theorem MetricDuality.eq_of_forall_g_basis_eq`
- L413 `theorem ricciEndomorphism_apply_basis_of_diagonalization`
- L432 `theorem scalarCurvature_eq_ricciEigenScalar3_of_diagonalization`
- L449 `theorem ricci_norm_sq_eq_ricciEigenNormSq3_of_diagonalization`
- L498 `theorem ricci_trace_cube_eq_ricciEigenTraceCube3_of_diagonalization`
- L578 `theorem ricciEigenframeRiemannReaction3D_eq_ricciEigenRiemannReaction3_of_sectional_trace`
- L774 `theorem isRicciReactionEigenvalueRealized_of_diagonalization`
- L793 `theorem isRicciReactionEigenvalueRealized_of_sectional_trace`
- L814 `theorem isRicciReactionEigenvalueRealized_of_orthonormal_trace3`
- L833 `theorem isRicciReactionEigenvalueRealized_of_trace_eigenframe_package`
- L863 `theorem isRicciReactionEigenvalueGeometric_of_eigenvalue_realization`
- L880 `theorem isRicciReactionEigenvalueGeometric_of_sectional_trace`
- L904 `theorem isRicciReactionEigenvalueGeometric_of_orthonormal_trace3`
- L927 `theorem isRicciReactionEigenvalueGeometric_of_trace_eigenframe_package`
- L952 `theorem isRicciReactionEigenvalueGeometric_of_diagonalization`
- L1097 `theorem hamilton3D_tracefree_norm_heat_eq_of_contraction_calculus`
- L1204 `theorem hamilton3D_tracefree_norm_heat_eq_of_trace_eigenframe_packages`
- L1310 `theorem hamilton3D_tracefree_norm_heat_eq_of_trace_eigenframe_evolution_components`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/RiemannFromRicci3D.lean`

- L149 `theorem riemannFromRicci3DRHSTensor_eval`
- L157 `theorem riemannFromRicci3DRHS_antisymm_first`
- L166 `theorem riemannFromRicci3DRHS_antisymm_last`
- L175 `theorem riemannFromRicci3DRHS_block_symm_of_ricci_symm`
- L199 `theorem riemannFromRicci3DRHS_first_bianchi_of_ricci_symm`
- L253 `theorem riemannFromRicci3DResidualTensor_eval`
- L268 `theorem riemannFromRicci3DResidual_antisymm_first`
- L291 `theorem riemannFromRicci3DResidual_antisymm_last`
- L315 `theorem riemannFromRicci3DResidual_block_symm_of_ricci_symm`
- L342 `theorem riemannFromRicci3DResidual_first_bianchi_of_ricci_symm`
- L481 `theorem symmetricEigenbasis3_apply`
- L499 `theorem ricciEndomorphism_isSymmetric_of_metric_eq_inner_and_Rc_symm`
- L522 `theorem supplies`
- L602 `theorem realTrace_hasOrthonormalBasisTraceFormula3`
- L639 `theorem realTrace_hasMetricAdjointTraceInvariant`
- L681 `theorem sectionalComponent3D_swap`
- L730 `theorem ricciForm_tensor_eq_sum_Rm_lowered_of_orthonormal_trace3`
- L752 `theorem Rm_lowered_self_first_pair_eq_zero`
- L764 `theorem Rm_lowered_self_second_pair_eq_zero`
- L776 `theorem Rm_lowered_trace_term_eq_sectionalComponent3D`
- L785 `theorem ricciForm_tensor_eq_sectional_sum_of_orthonormal_trace3`
- L841 `theorem scalarCurvature_eq_sum_lambda_of_orthonormal_trace3`
- L1161 `theorem riemannFromRicci3DResidualTensor_01_01_of_sectional_trace`
- L1197 `theorem riemannFromRicci3DResidualTensor_02_02_of_sectional_trace`
- L1233 `theorem riemannFromRicci3DResidualTensor_12_12_of_sectional_trace`
- L1269 `theorem isHalfCoefficient_eq_of_two_cancel`
- L1281 `theorem riemannFromRicci3DResidualTensor_01_02_of_mixed_trace`
- L1308 `theorem riemannFromRicci3DResidualTensor_01_12_of_mixed_trace`
- L1335 `theorem riemannFromRicci3DResidualTensor_02_12_of_mixed_trace`
- L1363 `theorem hasRiemannFromRicci3DCalculus_of_residual_zero`
- L1380 `theorem hasRiemannFromRicci3DCalculus_of_residual_tensor_zero`
- L1400 `theorem tensor04_eq_zero_of_basis_components`
- L1414 `theorem tensor04_eq_zero_of_basis_distinct_pair_components`
- L1463 `theorem tensor04_eq_zero_of_basis_ordered_pair_components`
- L1500 `theorem tensor04_eq_zero_of_basis_ordered_block_components`
- L1539 `theorem hasRiemannFromRicci3DCalculus_of_basis_components`
- L1563 `theorem hasRiemannFromRicci3DCalculus_of_distinct_pair_basis_components`
- L1599 `theorem hasRiemannFromRicci3DCalculus_of_ordered_pair_basis_components`
- L1637 `theorem hasRiemannFromRicci3DCalculus_of_ordered_block_basis_components`
- L1681 `theorem hasRiemannFromRicci3DCalculus_of_fin_three_ordered_block_components`
- L1735 `theorem hasRiemannFromRicci3DCalculus_of_fin_three_components_trace_adjoint`
- L1961 `theorem hasRiemannFromRicci3DCalculus_of_fin_three_component_package`
- L2088 `theorem hasRiemannFromRicci3DCalculus_of_trace_eigenframe_package`
- L2104 `theorem riemannFromRicci3DResidual_eq_zero`
- L2146 `theorem riemannFromRicci3DFormula_from_data_package`
- L2170 `theorem riemannFromRicci3DFormula_from_dim3_calculus`
- L2187 `theorem riemannFromRicci3DFormula_from_fin_three_component_package`
- L2207 `theorem riemannFromRicci3DFormula_from_trace_eigenframe_package`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/Compactness.lean`

- L125 `theorem point_selection_hypothesis_from_time_unbounded`
- L192 `theorem point_selection_rescaling_from_interface`
- L231 `theorem scalar_convergence_witness_limit_eq_zero_of_squeeze`
- L292 `theorem scalar_limit_eq_of_constant_samples`
- L314 `theorem scalar_limit_eq_one_from_rescaling_curvature_convergence`
- L338 `theorem limit_scalar_normalized_from_cgh_convergence`
- L398 `theorem tracefree_ratio_limit_eq_zero_of_squeeze`
- L416 `theorem tracefree_ratio_quantity_limit_eq_zero_of_squeeze`
- L438 `theorem limit_tracefree_ricci_norm_sq_eq_zero_of_ratio_limit_zero`
- L453 `theorem limit_tracefree_ricci_norm_sq_eq_zero_of_squeezed_ratio`
- L488 `theorem limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_decay`
- L516 `theorem limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_wmp_decay`
- L542 `theorem limit_tracefree_norm_zero_from_improved_pinching`
- L566 `theorem limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer`
- L630 `theorem limit_tracefree_ricci_norm_sq_eq_zero_on_region_of_uniform_decay`
- L718 `theorem compact_limit_diffeomorphism_from_interface`
- L761 `theorem perelman_noncollapsed_at_scale_from_interface`
- L794 `theorem myers_compactness_from_positive_ricci_interface`
- L805 `theorem limit_compact_from_constant_positive_consumer`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/BlowUp.lean`

- L46 `theorem finite_time_singularity_from_positive_scalar`
- L53 `theorem finite_time_singularity_bound_from_positive_scalar`
- L82 `theorem maximal_time_nonextendable_from_interface`
- L104 `theorem finite_time_curvature_blow_up_from_maximality`
- L114 `theorem finite_time_curvature_blow_up_from_finite_time`
- L136 `theorem scalar_unbounded_from_curvature_blowup`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Calculus.lean`

- L85 `theorem RicciFlowData.dt_R`
- L99 `theorem RicciFlowData.dt_R_full_from_rhs`
- L125 `theorem RicciFlowData.dt_R_full_from_laplace_reaction`
- L144 `theorem RicciFlowData.dt_grad`
- L155 `theorem RicciFlowData.dt_grad_sq`
- L169 `theorem RicciFlowData.dt_laplacian`
- L186 `theorem RicciFlowData.dt_Rc`
- L194 `theorem RicciFlowData.dt_Rc_laplace_reaction`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannEvolution.lean`

- L133 `theorem riemann_variation_formula`
- L216 `theorem riemann_tensor_evolution`
- L299 `theorem conn_var_eq_A_rf`
- L372 `theorem A_rf_scalar_flat_eq`
- L393 `theorem Q_hamilton_scalar_flat_eq_of_metric_compatible`
- L434 `theorem nabla_ricciForm_tensor_eval`
- L467 `theorem ricci_second_cov_deriv_eq_nabla_tensor`
- L509 `theorem ricci_second_cov_deriv_commutator`
- L557 `theorem ricci_cov_deriv_symm_of_Rc_symm`
- L575 `theorem ricci_second_cov_deriv_symm_last_of_Rc_symm`
- L596 `theorem covariant_derivative_A_rf_scalar_flat_eq`
- L623 `theorem Q_hamilton_scalar_flat_second_cov_deriv_eq_of_metric_compatible`
- L731 `theorem Q_rm_eq_hamilton`
- L827 `theorem hamilton_decomposition`
- L1035 `theorem A_rf_scalar_add_U`
- L1053 `theorem A_rf_scalar_smul_U`
- L1070 `theorem A_rf_scalar_add_W`
- L1088 `theorem A_rf_scalar_smul_W`
- L1105 `theorem A_rf_scalar_add_omega`
- L1124 `theorem A_rf_scalar_smul_omega`
- L1347 `theorem Q_hamilton_add_X`
- L1378 `theorem Q_hamilton_smul_X`
- L1407 `theorem Q_hamilton_add_Y`
- L1438 `theorem Q_hamilton_smul_Y`
- L1467 `theorem Q_hamilton_add_Z`
- L1501 `theorem Q_hamilton_smul_Z`
- L1534 `theorem Q_hamilton_add_omega`
- L1574 `theorem Q_hamilton_smul_omega`
- L1697 `theorem Q_rm_independent_eval`
- L1710 `theorem Q_rm_independent_flat_second_cov_deriv_eq_of_metric_compatible`
- L1736 `theorem Q_rm_ricciSlot_flat_eq_ricciHessian`
- L1762 `theorem Q_rm_ricciSlot_flat_eq_commutedRicciHessian`
- L1813 `theorem Q_rm_independent_eq_Q_rm`
- L1877 `theorem riemann_tensor_evolution_hamilton`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannVariation.lean`

- L46 `theorem conn_var_vector_eval`
- L83 `theorem riemann_variation_raw`
- L452 `theorem conn_var_add_left`
- L479 `theorem conn_var_sub_left`
- L533 `theorem riemann_variation_torsion_free`
- L613 `theorem variation_eq_dt`
- L653 `theorem variation_scalar_eq_dt_tensor`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Ricci.lean`

- L29 `theorem ricci_evolution_pointwise_extraction`
- L89 `theorem ricci_laplace_reaction_rhs_eval`
- L113 `theorem ricci_evolution_from_equation`
- L136 `theorem ricci_evolution_from_equation_eval`
- L161 `theorem ricci_evolution_from_lichnerowicz_equation`
- L185 `theorem ricci_evolution_from_lichnerowicz_equation_eval`
- L306 `theorem riemann_to_ricci_trace_eq_trace_of_slice`
- L318 `theorem riemann_to_ricci_trace_Rm_tensor_eval`
- L368 `theorem riemann_to_ricci_rough_trace_eval`
- L416 `theorem riemann_to_ricci_quadratic_trace_of_decomposition`
- L551 `theorem riemannRicciReactionTensor_eval`
- L570 `theorem ricci_comp_RcEndo_metric_apply`
- L591 `theorem riemannRicciReactionTensor_eq_trace_ricci_comp_RcEndo`
- L612 `theorem neg_RcEndo_ricciEndomorphism_metric_apply_eq_second_reaction`
- L680 `theorem ricciSquareTensor_eval`
- L698 `theorem ricciSquareTensor_eq_Rc_ricciEndomorphism_of_Rc_symm`
- L743 `theorem trace_neg_RcEndo_ricciEndomorphism_eq_neg_ricciSquare_of_Rc_symm`
- L779 `theorem commutedReactionPairEndomorphism_metric_apply`
- L802 `theorem trace_commuted_reaction_pair_eq_riemannRicci_sub_ricciSquare`
- L827 `theorem trace_commutedReactionPairEndomorphism_eq_riemannRicci_sub_ricciSquare`
- L875 `theorem finiteBasisVectorOfDualFunctional_eval`
- L958 `theorem qHamiltonRicciSlotEndomorphism_of_finite_basis_eval`
- L988 `theorem RiemannToRicciCanonicalQuadraticTrace_of_finite_basis_trace`
- L1028 `theorem RiemannToRicciCanonicalQuadraticTrace_of_finite_basis_hessian_residual`
- L1146 `theorem finiteBasisTimeDerivativeVector_eval`
- L1234 `theorem finiteBasisTimeDerivativeLinearMap_eval`
- L1315 `theorem riemann_to_ricci_trace_dt_tensor_eval`
- L1355 `theorem riemann_to_ricci_trace_dt_tensor_eval_of_slice`
- L1387 `theorem ricci_time_trace_commutation_from_endomorphism_trace`
- L1478 `theorem ricci_time_trace_commutation_from_coordinate_trace`
- L1523 `theorem ricci_time_trace_commutation_from_coordinate_trace_of_slice`
- L1566 `theorem ricci_dt_trace_from_coordinate_trace`
- L1608 `theorem ricci_dt_trace_from_coordinate_trace_of_slice`
- L1649 `theorem ricci_pointwise_explicit_evolution_from_riemann_trace`
- L1734 `theorem ricci_pointwise_explicit_evolution_from_riemann_trace_coordinate_dt`
- L1792 `theorem ricci_pointwise_explicit_evolution_from_riemann_trace_slice_dt`
- L1841 `theorem ricci_riemann_evolution_hamilton_input`
- L1907 `theorem ricci_pointwise_explicit_evolution_from_hamilton_riemann_trace`
- L1988 `theorem ricci_pointwise_explicit_evolution_from_hamilton_riemann_canonical_trace`
- L2062 `theorem ricci_explicit_evolution_from_pointwise`
- L2094 `theorem ricci_explicit_evolution_from_riemann_trace`
- L2150 `theorem ricci_explicit_evolution_from_riemann_trace_coordinate_dt`
- L2207 `theorem ricci_explicit_evolution_from_riemann_trace_slice_dt`
- L2258 `theorem ricci_pointwise_explicit_evolution_of_explicit`
- L2285 `theorem ricci_lichnerowicz_evolution_from_explicit`
- L2309 `theorem ricci_evolution_from_explicit_lichnerowicz_equation_eval`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Lichnerowicz.lean`

- L33 `theorem lichnerowicz_laplacian_02_eval`
- L44 `theorem lichnerowicz_laplacian_from_interface`
- L63 `theorem ricci_lichnerowicz_reaction_02_eval`
- L82 `theorem ricci_lichnerowicz_laplacian_rhs_eval`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Gradient.lean`

- L37 `theorem gradient_evolution`
- L102 `theorem gradient_squared_evolution`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Laplacian.lean`

- L40 `theorem hessian_raise_variation`
- L121 `theorem laplacian_evolution`

### `DifferentialGeometry/Synthetic/Analysis/Parabolic/TensorMaximumPrinciple.lean`

- L41 `theorem tensor_wmp_preserve_cone`

## Interface And Data Declarations

Definitions, structures, classes, and axioms are not theorem declarations, but many are actual Section 12 obligations or data carriers. This list is included to make placeholder/interface pressure visible.

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/HamiltonThreeManifold.lean`

- L31 `structure HamiltonThreeManifoldGeometricContext`
- L48 `structure HamiltonThreeManifoldTypedInput`
- L66 `structure HamiltonThreeManifoldTypedConclusion`
- L78 `def typed_conclusion_of_diffeomorphic_constant_positive_limit`
- L92 `def ricciNonnegativeCone`
- L97 `def ricciNonnegativeParabolicProblem`
- L136 `def ricciPinchingTensorAt`
- L151 `def ricciPinchingParabolicProblem`
- L237 `def SubNonnegIffLe`
- L266 `class PositiveInitialScalarFromRicciPositive`
- L427 `structure HamiltonSection12RescalingConvergenceData`
- L486 `structure LimitScalarPositivityProblem`
- L515 `class RicciNonnegativeClosedUnderCGHCurvatureConvergence`
- L668 `structure HamiltonSection12AssemblyData`
- L716 `structure HamiltonSection12Claims`
- L756 `class HamiltonP1ContractedSecondBianchiTheorem`
- L812 `class HamiltonP1NamedCalculusInputs`
- L839 `class HamiltonP2RiemannFromRicci3DTheorem`
- L957 `class HamiltonP3CubicReactionGeometryTheorem`
- L1012 `class HamiltonP3ReactionCalculusInputs`
- L1035 `def hamiltonP3ReactionCalculusInputs_of_eigenvalue_packages`
- L1050 `def hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages`
- L1064 `def hamiltonP3ReactionCalculusInputs_of_trace_eigenframe_packages`
- L1085 `def hamiltonP3CubicReactionGeometryTheorem_of_trace_eigenframe_packages`
- L1118 `structure HamiltonSection12ClaimBuilderInput`
- L1357 `class HamiltonSyntheticAnalyticInputs`
- L1530 `def hamilton_three_manifold_from_section12_assembly`
- L1547 `def hamilton_three_manifold_typed_conclusion_of_section12_claims`
- L1616 `structure HamiltonThreeManifoldInput`
- L1624 `structure HamiltonThreeManifoldConclusion`
- L1630 `class HamiltonThreeManifoldBlackBoxes`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/ImprovedPinching.lean`

- L44 `def hamiltonPinchingReactionExpression`
- L63 `def quotientEvolutionRHS`
- L90 `def QuotientEvolutionIdentity`
- L205 `def hamiltonPinchingEvolutionRHS`
- L236 `def HamiltonPinchingEvolutionEquation`
- L299 `structure ImprovedRicciPinchingEstimateAlongFlow`
- L325 `structure HamiltonImprovedPinchingProducerData`
- L367 `structure HamiltonPinchingQuotientEvolutionData`
- L408 `def hamilton_improved_pinching_producer_data_of_quotient_evolution`
- L464 `def improved_ricci_pinching_estimate_along_flow_of_subsolution_data`
- L488 `def improved_ricci_pinching_estimate_along_flow_of_hamilton_producer`
- L545 `def hamiltonImprovedPinchingQuantity`
- L557 `def hamiltonImprovedPinchingQuantityFromRicci`
- L601 `structure HamiltonPinchingQuotientRealizationData`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/Pinching.lean`

- L24 `def RicciPositive`
- L46 `def RicciPinched`
- L58 `structure HamiltonPinchingTerms`
- L65 `def PinchingReactionLowerBound`
- L70 `def ImprovedPinchingEstimate`
- L85 `def ricciEigenScalar3`
- L89 `def ricciEigenNormSq3`
- L101 `def ricciEigenTraceCube3`
- L105 `def hamiltonCubicQ3`
- L112 `def ricciEigenPairwiseGapSq3`
- L116 `def tracefreeRicciEigenNormSq3`
- L120 `def hamiltonCubicQFactorized3`
- L135 `def ricciEigenRiemannReaction3`
- L179 `def hamiltonCubicQOrderedGaps3`
- L185 `def orderedEigenPairwiseGapSq3`
- L330 `def hamiltonCubicQ`
- L356 `structure HamiltonCubicQEigenvalueRealization`
- L422 `def tracefreeRicciPinchingQuantity`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/CurvatureAlgebra.lean`

- L29 `structure IsDimensionThree`
- L52 `def IsHalfCoefficient`
- L61 `def riemannFromRicci3DRHS`
- L84 `def RiemannFromRicciFormula`
- L94 `structure RiemannFromRicci3DFormula`
- L170 `def IsThirdCoefficient`
- L198 `def EinsteinRicciFormula`
- L232 `def ricciDivergenceAt`
- L248 `def ricciDivergenceAtSecond`
- L536 `def covDerivRmEndomorphism`
- L579 `def covDerivRicciEndomorphism`
- L661 `def ContractedSecondBianchiIdentity`
- L748 `structure ContractedSecondBianchiDoubleTraceData`
- L783 `class HasContractedSecondBianchiCyclicTraceSlotAudit`
- L814 `class HasContractedSecondBianchiNamedPatternCalculus`
- L1075 `def contractedSecondBianchiDoubleTraceData_of_named_patterns`
- L1115 `def contractedSecondBianchiDoubleTraceData_of_named_patterns_and_metric_fubini`
- L1156 `def contractedSecondBianchiDoubleTraceData_from_second_bianchi_named_patterns`
- L1348 `structure ContractedBianchiSlotAuditObligations`
- L1442 `def EinsteinDivergenceFormula`
- L1626 `def ConstantSectionalCurvatureFormula`
- L1665 `def sectional_curvature_numerator`
- L1671 `def NonnegativeRicci`
- L1681 `def CurvatureControlledByRicci`
- L1693 `def CurvatureControlledByScalar3D`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RicciNorm.lean`

- L28 `def tracefree_ricci_tensor`
- L52 `def tracefree_ricci_norm_sq`
- L188 `def RicciNormEvolutionEquation`
- L225 `def TracefreeRicciNormEvolutionEquation`
- L380 `def tracefreeRicciNormHamilton3DRHS`
- L396 `def scalarHeatOperator`
- L408 `def TracefreeRicciNormHamilton3DHeatOperatorEquation`
- L434 `def TracefreeRicciNormHamilton3DTimeLaplacianEquation`
- L564 `def scalarLaplacianAlongTimeSlice`
- L595 `def ricciNormSqAlongFlow`
- L626 `def scalarCurvatureAlongFlow`
- L706 `def tracefreeRicciNormSqAlongFlow`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/ScalarCurvature.lean`

- L54 `def tensor_02_endo`
- L104 `def abstractTraceDimension`
- L108 `def tensor_inner_02`
- L117 `def tensor_trace_cube_02`
- L247 `def ricci_norm_sq`
- L259 `def ricci_trace_cube`
- L361 `def MetricBilinProductRule`
- L434 `def ScalarCurvatureProductRule`
- L526 `def RicciTraceIdentity`
- L549 `def RicciTraceIdentityForRHS`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Connection.lean`

- L23 `def ricci_cov_deriv`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Basic.lean`

- L39 `def inverse_metric_var_form`
- L57 `def InverseMetricProductRule`
- L98 `def Rm_tensor`
- L183 `def ricciForm_tensor`
- L268 `def IsRicciFlow`
- L407 `def NablaTimeProductRule`

### `DifferentialGeometry/Synthetic/Algebra/VectorFieldAlgebra.lean`

- L22 `structure DerivationEmbedding`
- L40 `structure TimeDerivativeData`
- L64 `class TimeRegularFam`
- L159 `def action`
- L163 `def bracket`
- L185 `def commutatorEndo`
- L422 `def TimeDerivativeData.dt_apply`
- L693 `def SpatialTemporalComm`

### `DifferentialGeometry/Synthetic/Algebra/TensorAlgebra.lean`

- L39 `def evalLinear`
- L45 `def scalarToData`
- L50 `def vectorToData`
- L55 `def covectorToData`
- L81 `def tensor_eval`
- L100 `def swap_covariant`
- L105 `def swap_contravariant`
- L138 `def tensor_prod`
- L270 `def covector_from_tensor`
- L291 `def endo_to_tensor`
- L326 `structure AbstractTrace`
- L379 `def toScalar`
- L380 `def fromScalar`
- L381 `def fromVector`
- L398 `def delta_tensor`
- L404 `def outerProduct`
- L416 `def contract`
- L448 `def eval_endo`
- L504 `def contract_general`
- L558 `def ContractGeneral13MiddleTraceEval`
- L583 `def tensor_contract_twice`
- L594 `def TensorContractFubini`
- L603 `class HasTensorContractFubini`
- L642 `def TensorContractSwapNaturality`
- L654 `class HasTensorContractSwapNaturality`
- L710 `def NablaTrComm`
- L728 `def TimeTrComm`

### `DifferentialGeometry/Synthetic/Algebra/Metric.lean`

- L24 `def flat_covector`
- L52 `structure MetricDuality`
- L71 `def MetricDuality.g`
- L81 `def MetricDuality.flat`
- L165 `def SharpSpec`
- L172 `def MetricDuality.sharp`
- L217 `class HasMetricAdjointTraceInvariant`
- L235 `def IsMetricCompatible`
- L345 `def NablaTensorContractComm`
- L363 `def lower_index`
- L370 `def raise_index`
- L377 `def metric_trace`

### `DifferentialGeometry/Synthetic/Analysis/NablaOnTensors.lean`

- L26 `def nabla_dual`
- L102 `def nabla_tensor`
- L457 `def covariantDerivativeTensor`

### `DifferentialGeometry/Synthetic/Analysis/TimeOnTensors.lean`

- L32 `def dt_tensor`

### `DifferentialGeometry/Synthetic/Geometry/Connection.lean`

- L25 `def IsTorsionFree`
- L28 `def IsLeviCivita`
- L90 `def Rm`
- L330 `def covDerivRm`
- L419 `def secondCovDerivCommutator`
- L441 `def RcEndo`
- L452 `def Rc`

### `DifferentialGeometry/Synthetic/Geometry/ConnectionExtended.lean`

- L104 `def R_XY`
- L235 `def RcCovector`
- L259 `def RicciEndomorphism`
- L306 `def ScalarCurvature`
- L328 `def covDerivRc`
- L340 `def grad_R`
- L362 `def koszul_rhs`
- L388 `def koszul_covector`
- L427 `def koszul_connection`

### `DifferentialGeometry/Synthetic/Operator/Variation.lean`

- L52 `def metric_var_form`
- L96 `def h_cov_deriv`

### `DifferentialGeometry/Synthetic/Analysis/NablaTimeInteraction.lean`

- L124 `def conn_var_tensor`

### `DifferentialGeometry/Synthetic/Operator/Laplacian.lean`

- L30 `def laplacian`
- L92 `def SecondCovDerivTensor`

### `DifferentialGeometry/Synthetic/Operator/Hessian.lean`

- L27 `def Hess`
- L48 `def covariant_differential`
- L100 `def hessianForm`

### `DifferentialGeometry/Synthetic/Operator/Gradient.lean`

- L20 `def df_covector`
- L27 `def grad`

### `DifferentialGeometry/Synthetic/Operator/CovariantDerivative.lean`

- L69 `def rawCovDeriv`
- L122 `def covDerivOp`
- L149 `def metricToForm`
- L168 `def genericCovDeriv`
- L193 `def genericCovDeriv_tensor_prod`
- L226 `def covDeriv02TraceCovector`
- L252 `def covDivergence02Endomorphism`
- L288 `def covariantDivergence02At`

### `DifferentialGeometry/Synthetic/Geometry/CurvatureContractions.lean`

- L30 `def Rm_lowered`
- L39 `structure LoweredRmTensorData`
- L47 `def loweredRmTensor`
- L260 `def loweredRmTensorData`
- L272 `def covDerivRm_lowered`
- L283 `structure LoweredCovDerivRmTensorData`
- L305 `def covDerivRmLoweredTensor`
- L604 `def loweredCovDerivRmTensorData`
- L642 `def covariantCycle012Left05`
- L660 `def covariantCycle012Right05`
- L709 `def covDerivRmLoweredTensorAt`

### `DifferentialGeometry/Synthetic/Algebra/MetricTrace.lean`

- L35 `def doubleMetricTrace04`
- L110 `def doubleMetricTrace05`
- L184 `def DoubleMetricTrace04Fubini`
- L194 `def DoubleMetricTrace05Fubini`
- L225 `structure DoubleMetricTrace05Pattern`
- L250 `def contractedBianchiDivPattern`
- L263 `def contractedBianchiDivFubiniPattern`
- L273 `def contractedBianchiGradPattern`
- L280 `def tensor`
- L287 `def apply`
- L295 `def Fubini`
- L418 `class HasDoubleMetricTrace05PatternFubini`

### `DifferentialGeometry/Synthetic/Operator/SpatialConstant.lean`

- L24 `def IsSpatialConstant`

### `DifferentialGeometry/Synthetic/Analysis/Parabolic/ScalarCalculus.lean`

- L36 `structure ScalarParabolicCalculus`
- L75 `def scalarDoubleDivergenceAt`
- L121 `def scalarHeatOperatorFromDoubleDivergence`
- L145 `def scalarParabolicProblemFromDoubleDivergence`
- L181 `structure ScalarParabolicDoubleDivergenceCalculus`
- L244 `def ScalarParabolicDoubleDivergenceCalculus.toScalarParabolicCalculus`

### `DifferentialGeometry/Synthetic/Analysis/Parabolic/ScalarMaximumPrinciple.lean`

- L16 `structure ScalarParabolicProblem`
- L21 `def IsScalarSubsolution`
- L25 `def IsInitiallyNonpositive`
- L30 `class ScalarWeakMaximumPrinciple`
- L67 `class ScalarStrongMaximumPrinciple`

### `DifferentialGeometry/Synthetic/Operator/Divergence.lean`

- L26 `def cov_diff_vec`
- L36 `def divergence`
- L49 `def df_covector`
- L78 `def conn_endo`
- L275 `structure IntegralOperator`
- L281 `def DivergenceTheorem`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/RicciReaction.lean`

- L88 `def ricciReactionContractionResidual`
- L107 `structure RicciReactionContractionDataPackage`
- L136 `class HasRicciReactionContractionCalculus`
- L159 `def hasRicciReactionContractionCalculus_of_residual_zero`
- L244 `structure RicciReactionEigenvaluePackage`
- L306 `structure RicciReactionEigenvalueRealization`
- L344 `def ricciReactionEigenvaluePackage_of_eigenvalue_realization`
- L368 `def IsRicciReactionEigenvalueRealized`
- L383 `def hasRicciReactionContractionCalculus_of_eigenvalue_realizations`
- L563 `def ricciEigenframeRiemannReaction3D`
- L670 `def ricciReactionEigenvalueRealization_of_diagonalization`
- L703 `def ricciReactionEigenvalueRealization_of_sectional_trace`
- L729 `def ricciReactionEigenvalueRealization_of_orthonormal_trace3`
- L756 `def ricciReactionEigenvalueRealization_of_trace_eigenframe_package`
- L852 `def IsRicciReactionEigenvalueGeometric`
- L977 `def hasRicciReactionContractionCalculus_of_eigenvalue_packages`
- L999 `def hasRicciReactionContractionCalculus_of_trace_eigenframe_package`
- L1039 `def hasRicciReactionContractionCalculus_of_data_package`
- L1058 `def ricciReactionContractionDataPackage_of_residual_zero`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/DimensionThree/RiemannFromRicci3D.lean`

- L81 `def riemannFromRicci3DRHSTensor`
- L224 `def riemannFromRicci3DResidual`
- L240 `def riemannFromRicci3DResidualTensor`
- L378 `structure RiemannFromRicci3DDataPackage`
- L399 `class HasRiemannFromRicci3DCalculus`
- L418 `def IsMetricOrthonormalBasis3`
- L430 `class HasOrthonormalBasisTraceFormula3`
- L443 `structure RicciDiagonalization3D`
- L468 `def symmetricEigenbasis3`
- L475 `def symmetricEigenvalues3`
- L529 `def ricciDiagonalization3D_of_real_inner_product`
- L571 `def ricciDiagonalization3D_of_real_inner_product_and_Rc_symm`
- L670 `def sectionalComponent3D`
- L870 `structure RicciSectionalTraceFormula3D`
- L906 `def ricciSectionalTraceFormula3D_of_trace_equations`
- L1020 `structure RicciMixedCurvatureFormula3D`
- L1043 `structure RicciOffDiagonalTraceFormula3D`
- L1073 `def ricciOffDiagonalTraceFormula3D_of_orthonormal_trace3`
- L1131 `def ricciMixedCurvatureFormula3D_of_offDiagonal_trace`
- L1783 `structure RiemannFromRicci3DFinThreeComponentPackage`
- L1828 `structure RiemannFromRicci3DTraceEigenframePackage`
- L1854 `def riemannFromRicci3DTraceEigenframePackage_of_diagonalization`
- L1896 `def riemannFromRicci3DTraceEigenframePackage_of_real_inner_product`
- L1937 `def riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product`
- L1960 `class consumed`
- L1979 `def ricciSectionalTraceFormula3D_of_orthonormal_trace3`
- L2006 `def riemannFromRicci3DFinThreeComponentPackage_of_eigenframe`
- L2063 `def riemannFromRicci3DFinThreeComponentPackage_of_trace_eigenframe_package`
- L2119 `def riemannFromRicci3DDataPackage_from_dim3_calculus`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/Compactness.lean`

- L22 `structure ConvergenceWitness`
- L31 `structure EventuallyPositiveWitness`
- L44 `class ScalarConvergenceSqueezeToZero`
- L59 `class EventuallyImp`
- L72 `structure PointedRicciFlowSequence`
- L76 `def ricciFlowRiemannTensorAt`
- L81 `def ricciFlowRicciTensorAt`
- L87 `def ricciFlowScalarCurvatureAt`
- L93 `def ricciFlowRicciNormSqAt`
- L99 `def ricciFlowTracefreeRicciNormSqAt`
- L106 `def PointSelectionHypothesis`
- L115 `class ScalarSpatialPromotionFromTime`
- L143 `structure ParabolicRescalingData`
- L177 `class PointSelectionAndRescalingTheorem`
- L204 `structure RicciFlowLimitCandidate`
- L208 `structure SmoothCGHConvergenceData`
- L221 `structure CurvatureConvergenceProfile`
- L244 `structure CurvatureConvergenceConclusion`
- L358 `class CurvatureConvergenceUnderSmoothCGH`
- L375 `structure CurvatureRatioConvergenceConclusion`
- L605 `structure UniformTracefreeRatioDecayOnRegion`
- L656 `class CurvatureRatioConvergenceUnderSmoothCGH`
- L677 `class HamiltonCompactnessTheorem`
- L687 `structure CompactLimitDiffeomorphismConclusion`
- L702 `class CompactLimitDiffeomorphismUnderSmoothCGH`
- L735 `structure KappaNoncollapsedAtScale`
- L749 `class PerelmanNoncollapsingAtScale`
- L772 `class PerelmanNoncollapsing`
- L777 `structure MyersCompactnessConclusion`
- L785 `class MyersPositiveRicciCompactness`
- L825 `class MyersTheoremInterface`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/BlowUp.lean`

- L17 `def BoundedAboveOn`
- L22 `def UnboundedAboveOn`
- L35 `class PositiveScalarFiniteTimeTheorem`
- L61 `class RicciFlowExtensionCriterion`
- L73 `class MaximalTimeWitness`
- L92 `class CurvatureBlowUpAlternative`
- L127 `class ScalarBlowUpFromCurvatureBlowUp`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Global/Existence.lean`

- L24 `structure RicciFlowSolutionToken`
- L28 `class ShortTimeExistence`
- L32 `structure MaximalRicciFlow`
- L37 `class MaximalIntervalExistence`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Calculus.lean`

- L45 `structure RicciFlowData`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannEvolution.lean`

- L35 `def riemann_variation_tensor`
- L179 `def Q_rm`
- L282 `def A_rf_scalar`
- L350 `def Q_hamilton_scalar`
- L421 `def ricci_second_cov_deriv`
- L1641 `def Q_rm_independent`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannVariation.lean`

- L37 `def conn_var_vector`
- L514 `def nabla_conn_var_scalar`
- L634 `def riemann_variation_scalar`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannLaplacian.lean`

- L164 `def rough_laplacian_Rm_endo`
- L232 `def rough_laplacian_Rm`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Ricci.lean`

- L64 `def RicciEvolutionEquation`
- L85 `def ricci_laplace_reaction_rhs`
- L96 `def RicciLichnerowiczEvolutionEquation`
- L221 `def RicciExplicitLichnerowiczEvolutionEquation`
- L252 `def RicciPointwiseExplicitEvolutionEquation`
- L282 `def riemann_to_ricci_trace`
- L293 `def RicciSlotTraceEval`
- L348 `def riemann_to_ricci_rough_trace`
- L394 `structure RiemannToRicciQuadraticTraceDecomposition`
- L444 `def riemannRicciReactionTensor`
- L637 `def ricciSquareTensor`
- L766 `def commutedReactionPairEndomorphism`
- L849 `def RiemannToRicciCanonicalQuadraticTrace`
- L868 `def finiteBasisVectorOfDualFunctional`
- L927 `def qHamiltonRicciSlotEndomorphism_of_finite_basis`
- L1075 `def riemannToRicciQuadraticTraceDecomposition_of_canonical`
- L1113 `structure RiemannTimeDerivativeSliceEndomorphism`
- L1139 `def finiteBasisTimeDerivativeVector`
- L1191 `def finiteBasisTimeDerivativeLinearMap`
- L1253 `def riemannTimeDerivativeSliceEndomorphism_of_finite_basis`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Lichnerowicz.lean`

- L29 `def lichnerowicz_laplacian_02`
- L40 `def IsLichnerowiczLaplacian02`
- L58 `def ricci_lichnerowicz_reaction_02`
- L76 `def ricci_lichnerowicz_laplacian_rhs`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Gradient.lean`

- L88 `def MetricFullProductRule`

### `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Laplacian.lean`

- L94 `def LaplacianProductRule`

### `DifferentialGeometry/Synthetic/Analysis/Parabolic/TensorMaximumPrinciple.lean`

- L15 `structure TensorCone`
- L19 `structure TensorParabolicProblem`
- L25 `def IsTensorSubsolution`
- L29 `def IsInitiallyInCone`
- L34 `class TensorWeakMaximumPrinciple`

