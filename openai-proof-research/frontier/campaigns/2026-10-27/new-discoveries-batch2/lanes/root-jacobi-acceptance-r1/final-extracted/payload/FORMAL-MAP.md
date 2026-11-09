# Exact formal-interface map

All mathematical files are frozen byte-identical sources. Audit elaborators WholeInventory, generated WholeAudit, and SourceClaimInterfaces are outside this set.

## MidpointAlgebra

Namespace(s): JacobiShifted.Midpoint.

Source-level named interfaces (not the generated-origin inventory): `ZPoly`, `q`, `R`, `C`, `x`, `w`, `C_re`, `C_im`, `x_re`, `x_im`, `w_re`, `w_im`, `pair_mul`, `pair_eq_iff`, `pair_normal`, `w_sq`, `w_mul_pair`, `delta`, `partial_re`, `partial_im`, `derivative_q`, `partial_mul`, `derivation`, `derivation_apply`, `partial_x`, `partial_w`, `rho`, `rho_re`, `rho_im`, `rho_x`, `rho_w`, `rho_involution`, `rhoEquiv`, `rho_partial`, `flip`, `flip_apply`, `flip_X`, `flip_q`, `flip_involution`, `derivative_flip`, `tau`, `tau_re`, `tau_im`, `tau_x`, `tau_w`, `tau_involution`, `tauEquiv`, `tau_partial`, `midpoint`, `midpoint_apply`, `midpoint_x`, `midpoint_w`, `midpoint_C`, `InW`, `inW_iff`, `inW_ideal_span`, `inW_zero`, `inW_add`, `inW_neg`, `inW_mul_right`, `inW_partial`.

## BinaryDigits

Namespace(s): JacobiShifted.BinaryFiltration.

Source-level named interfaces (not the generated-origin inventory): `sigma`, `sigma_zero`, `sigma_one`, `sigma_pos`, `sigma_double`, `sigma_odd`, `sigma_odd_pred`, `sigma_add_le`.

## Filtration

Namespace(s): JacobiShifted.BinaryFiltration.

Source-level named interfaces (not the generated-origin inventory): `Exponent`, `P`, `weight`, `sigma_coords_pos`, `weight_add_le`, `weight_double`, `Weighted`, `weighted_zero`, `weighted_add`, `weighted_neg`, `weightedSubgroup`, `weighted_sum`, `weighted_monomial`, `support_nonzero`, `weighted_support_monomial`, `double_monomial_product`, `weighted_two_mul`, `weighted_monomial_square`, `square_add_identity`, `weighted_sum_square`, `weighted_square`, `coefficientOperator`, `coefficientOperator_coeff`, `additive_nat_mul`, `weighted_coefficientOperator`.

## Riccati

Namespace(s): JacobiShifted.BinaryFiltration.

Source-level named interfaces (not the generated-origin inventory): `coefficient_product_expansion`, `coefficient_square_expansion`, `weighted_involution_products`, `spectral_fixed_iff`, `spectral_fixed_even_iff`, `spectral_pair_identity`, `spectral_endpoints_zero`, `weighted_convolution`, `initial`, `initial_eq_variables`, `weighted_initial`, `riccati_weighted`, `riccati_initial_weighted`, `bidegree`, `bidegree_zero_coordinate`, `bidegree_one_coordinate`, `odd_bidegree_weight`, `weighted_odd_coefficient`, `riccati_odd_coefficient`, `riccati_degree_odd_coefficient`.

## MidpointSequence

Namespace(s): JacobiShifted.Midpoint.

Source-level named interfaces (not the generated-origin inventory): `Param`, `P`, `history`, `h`, `h_zero`, `history_agrees`, `h_recurrence`, `h_weighted`, `h_odd_coefficient_divisible`.

## ParameterDegree

Namespace(s): JacobiShifted.ParameterDegree.

Source-level named interfaces (not the generated-origin inventory): `coefficientOperator_totalDegree`, `initial_totalDegree`, `h_totalDegree`, `h_coeff_eq_zero`, `exponent_degree`, `h_bidegree_eq_zero`, `top_mul`.

## CatalanTop

Namespace(s): JacobiShifted.ParameterDegree.

Source-level named interfaces (not the generated-origin inventory): `sum_range_parity`, `oddTop`, `oddTop_zero`, `oddTop_recurrence`, `oddTop_catalan`, `h_odd_top`, `h_odd_top_coeff`.

## SourceDefs

Namespace(s): JacobiShifted.

Source-level named interfaces (not the generated-origin inventory): `QPoly`, `GPoly`, `embed`, `scalar`, `midpointX`, `midpointY`, `hankelNumerator`, `sourceC`, `inverseFactorCoeff`, `sourceFCoeff`, `sourceAugmentCoeff`, `powerCoeff`, `sourceLogCoeff`, `sourceKappa`, `TwoLocal`, `dyadicExponent`, `SourceClaim`, `sourceKappa_zero`, `inverseFactorCoeff_zero`.

## LiteralFinite

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `literalC`, `literalF`, `augment`, `finitePower`, `literalLog`, `map_literalC`, `map_literalF`, `map_augment`, `map_finitePower`, `map_literalLog`, `sourceEmbed`, `literalC_source`, `literalF_source`, `finitePower_source`, `literalLog_source`.

## MidpointParity

Namespace(s): JacobiShifted.Midpoint.

Source-level named interfaces (not the generated-origin inventory): `additive_sign`, `RhoParity`, `rhoParity_zero`, `rhoParity_add`, `rhoParity_neg`, `rhoParity_sum`, `rhoParity_mul`, `rhoParity_delta`, `rhoParity_monomial`, `rhoParity_P`, `h_rhoParity`, `TauParity`, `tauParity_zero`, `tauParity_add`, `tauParity_neg`, `tauParity_sum`, `tauParity_mul`, `tauParity_delta`, `tauParity_monomial`, `tauParity_P`, `h_tauParity`, `WCoefficients`, `inW_sum`, `wCoefficients_zero`, `wCoefficients_add`, `wCoefficients_neg`, `wCoefficients_sum`, `wCoefficients_mul`, `wCoefficients_delta`, `wCoefficients_monomial`, `wCoefficients_P`, `h_wCoefficients`, `h_coefficient_re_divisible`, `h_rho_coefficient`, `h_tau_coefficient`, `h_coefficient_mem_w`.

## MidpointNormalForm

Namespace(s): JacobiShifted.Midpoint.

Source-level named interfaces (not the generated-origin inventory): `polynomial_neg_fixed_zero`, `h_even_j_im_zero`, `h_odd_j_re_zero`, `h_odd_order_coordinates`, `flip_coeff`, `even_coeff_odd_zero`, `odd_coeff_even_zero`, `evenExtract`, `oddExtract`, `evenExtract_coeff`, `oddExtract_coeff`, `evenExtract_spec`, `odd_divX_even`, `oddExtract_spec`, `q_ne_zero`, `even_quotient`, `normalForm`, `normalForm_ring`, `integral_normalForm`, `integral_im_coeff_divisible`, `oddExtract_preserves_divisibility`, `oddExtract_zero`, `h_odd_normalForm`, `h_odd_extraction_divisible`, `h_odd_normalForm_ring`.

## MidpointRational

Namespace(s): JacobiShifted.MidpointRational.

Source-level named interfaces (not the generated-origin inventory): `QPoly`, `q`, `QAlg`, `C`, `x`, `w`, `C_re`, `C_im`, `x_re`, `x_im`, `w_re`, `w_im`, `pair_mul`, `pair_eq_iff`, `pair_normal`, `w_sq`, `w_mul_pair`, `delta`, `partial_re`, `partial_im`, `derivative_q`, `partial_mul`, `derivation`, `derivation_apply`, `partial_x`, `partial_w`, `rho`, `rho_re`, `rho_im`, `rho_x`, `rho_w`, `rho_involution`, `rhoEquiv`, `rho_partial`, `flip`, `flip_apply`, `flip_X`, `flip_q`, `flip_involution`, `derivative_flip`, `tau`, `tau_re`, `tau_im`, `tau_x`, `tau_w`, `tau_involution`, `tauEquiv`, `tau_partial`, `midpoint`, `midpoint_apply`, `midpoint_x`, `midpoint_w`, `midpoint_C`, `zmap`, `zmap_coeff`, `zmap_X`, `zmap_derivative`, `zmap_comp`, `zmap_injective`, `lift`, `lift_re`, `lift_im`, `lift_x`, `lift_w`, `lift_C`, `lift_injective`, `lift_delta`, `zmap_flip`, `lift_tau`, `lift_midpoint`.

## LiteralMidpoint

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `A`, `G`, `gaussianMap`, `gaussianMap_re`, `gaussianMap_im`, `gaussianEmbed`, `rationalBase`, `paramEmbed`, `coeffEmbed`, `rationalScalar`, `t`, `tInv`, `t_mul_tInv`, `xi`, `eta`, `midpointA`, `midpointG`, `tauA`, `tauG`, `conjugate`, `conjugate_re`, `conjugate_im`, `midpoint_rationalBase`, `tau_rationalBase`, `midpoint_paramEmbed`, `tau_paramEmbed`, `midpoint_coeffEmbed`, `tau_coeffEmbed`, `midpoint_xi`, `midpoint_eta`, `tau_xi`, `tau_eta`, `C`, `F`, `L`, `midpoint_C`, `midpoint_F`, `midpoint_L`, `tau_C`, `tau_F`, `tau_L`, `literal_imaginary_normalization`.

## LiteralDifferential

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `deltaA`, `deltaA_coeff`, `deltaA_monomial`, `deltaA_C`, `deltaA_mul`, `delta_rationalBase`, `deltaA_paramEmbed`, `deltaA_one`, `deltaG`, `deltaG_re`, `deltaG_im`, `deltaG_mul`, `deltaG_coeffEmbed`, `imaginaryUnit`, `imaginaryUnit_sq`, `deltaG_imaginaryUnit`, `deltaG_one`, `delta_t`, `delta_tInv`, `xi_eta_curve`, `deltaA_rationalScalar`, `half_twice`, `t_square`, `deltaG_xi`, `tInv_square`, `deltaG_eta`, `differential`, `differential_apply`, `deltaG_natCast`, `deltaG_logistic_pow`.

## LiteralHankel

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `hankelDivided`, `a`, `parameter`, `hankelNumerator_succ`, `hankelDivided_recurrence`, `a_recurrence`, `deltaG_a`, `C_divided`, `deltaG_monomial`, `deltaG_monomial_second`, `dxTerm`, `dyTerm`, `deltaG_C_split`, `dxTerm_shift`, `dyTerm_shift`, `deltaG_C_next`, `potentialCurve`, `deltaG_C_second`, `imaginaryUnit_twice`, `literal_hankel_R1`.

## LiteralPotential

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `imaginaryUnit_mul_injective`, `xi_product`, `eta_product`, `S`, `potentialCurve_eq`, `literal_hankel_midpoint_R1`.

## LiteralInverseFactor

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `inverseFactor_succ_zero`, `inverseFactor_shift`, `inverseFactor_recurrence`, `inverseFactor_vanish`, `weight`, `weight_recurrence`, `weight_succ_zero`, `weight_vanish`, `deltaG_weight`, `F_weighted`, `C_zero`, `deltaG_C_zero`, `deltaG_F`, `deltaG_F_next`, `literal_F_R2`.

## RiccatiScale

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `subVar`, `scale`, `integralOp`, `integralOp_C`, `integralOp_mul_X`, `deltaA_X`, `deltaA_subVar`, `scale_C`, `scale_delta`, `scaledH`, `scaledH_zero`, `scaledH_one`, `scaledH_recurrence`, `F_zero`, `L_one`, `logarithmic_derivative_one`, `imaginary_logarithmic_derivative_one`, `literal_source_linear_bridge`.

## ScaledTop

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `rationalScalar_eq_C`, `subVar_homogeneous`, `scale_homogeneous`, `scale_homogeneousComponent`, `scaledH_coeff_eq_zero`, `scaledH_odd_top`, `linear_power_pure`, `S_linear`, `scaledH_odd_pure_u`.

## OddTriangular

Namespace(s): JacobiShifted.MidpointRational.

Source-level named interfaces (not the generated-origin inventory): `TwoLocal`, `twoLocal_iff_odd_den`, `twoLocal_zero`, `twoLocal_int`, `twoLocal_add`, `twoLocal_mul`, `twoLocal_neg`, `twoLocal_sub`, `twoLocal_div_odd_nat`, `Bounded`, `bounded_self`, `bounded_zero`, `bounded_mono`, `bounded_add`, `bounded_sub`, `bounded_term`, `finiteDegree`, `T`, `T_add`, `T_sub`, `T_smul`, `coeff_X_derivative`, `T_coeff`, `T_bounded`, `T_surjective_bounded`, `T_kernel`, `T_injective`, `T_bijective`, `inverseT`, `T_inverseT`, `inverseT_T`, `inverseT_unique`, `inverseT_zero`, `inverseT_add`, `inverseT_smul`, `inverseT_bounded`, `T_finiteDegree_bijective`, `T_twoLocal`, `inverseT_twoLocal`.

## MidpointPrimitive

Namespace(s): JacobiShifted.MidpointRational.

Source-level named interfaces (not the generated-origin inventory): `realIntegral`, `sum_even`, `derivative_odd_term`, `derivative_realIntegral`, `realIntegral_zero_eval`, `flip_even_comp`, `flip_realIntegral`, `delta_realIntegral`, `delta_quadratic`, `delta_quadratic_expanded`, `primitive`, `primitive_re`, `primitive_im`, `primitive_delta`, `primitive_tau`, `primitive_midpoint`, `zmap_twoLocal_of_dvd`, `primitive_midpoint_twoLocal`, `imaginary_kernel`, `delta_kernel`, `normalized_kernel`, `normalized_unique`, `primitive_unique`, `normalForm_primitive_existsUnique`.

## OddPrimitiveSequence

Namespace(s): JacobiShifted.MidpointRational.

Source-level named interfaces (not the generated-origin inventory): `h_extracted_divisible`, `h_odd_primitive_existsUnique`, `h_odd_primitive_midpoint`, `h_odd_primitive_midpoint_even`, `h_zero_parameter`, `h_zero_parameter_primitive`, `h_odd_primitive_closed`.

## BinomialMoments

Namespace(s): JacobiShifted.

Source-level named interfaces (not the generated-origin inventory): `binomialOddSum`, `oddProduct`, `momentCoeff`, `oddProduct_pos`, `oddProduct_succ`, `momentCoeff_zero`, `momentCoeff_succ`, `binomialOddSum_pos`, `binomialOddSum_ne_zero`, `norm_odd`, `norm_oddProduct`, `norm_momentCoeff`, `norm_nat_le_one`, `norm_momentCoeff_le_one`, `norm_momentCoeff_le_factorial`, `factorial_norm_le`, `momentCoeff_tendsto`, `bounded_mul_summable`, `binomialMoment`, `moment_summable`, `norm_binomialMoment_le_one`, `choose_moment_identity`, `weighted_summable`, `binomialMoment_recurrence`, `moment_even_product`, `moment_zero`, `coeff_summable`, `coeffTail`, `tail_summable`, `norm_coeffTail`, `coeffTail_zero`, `coeffTail_step`, `coeffTail_one`, `coeffTail_two`, `norm_coeffTail_div_succ`, `norm_coeffTail_div_small`.

## FiniteTransform

Namespace(s): JacobiShifted.

Source-level named interfaces (not the generated-origin inventory): `oddIntegral`, `oddIntegral_monomial`, `oddIntegral_C_mul`, `oddIntegral_C_mul_X_pow`, `oddIntegral_boundary`, `oddIntegral_beta_recurrence`, `oddIntegral_one`, `oddIntegral_binomial`, `oddIntegral_one_add_X`, `oddIntegral_neg_binomial`.

## BinomialOddSum

Namespace(s): JacobiShifted.

Source-level named interfaces (not the generated-origin inventory): `oddIntegral_beta`, `oddIntegral_scaled_beta`, `binomialOddSum_transform`, `coeff_eq_tail_sub`, `tail_binomial_transform`, `tailUnitSum`, `tail_binomial_factor`, `tailUnitSum_norm`, `rat_valuation_zero_of_norm_one`, `binomialOddSum_normalized_norm`, `binomialOddSum_valuation`.

## PurePrimitive

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `rationalBase_two`, `purePrimitive`, `t_quadratic`, `delta_t_pow`, `delta_odd_term`, `binomial_t_sum`, `delta_purePrimitive`, `tau_purePrimitive`, `midpoint_purePrimitive`.

## FiniteLogChain

Namespace(s): JacobiShifted.SourceBridge.FiniteChain.

Source-level named interfaces (not the generated-origin inventory): `liftD`, `coeff_liftD`, `liftD_C`, `liftD_mul`, `liftD_pow`, `coeff_mul_range`, `coeff_finitePower`, `coeff_pow_vanish`, `truncLog`, `log_scalar`, `liftD_truncLog`, `geometric`, `truncated_chain`, `coeff_truncLog`, `finiteLog`, `finite_log_chain`, `cancel_zero`, `cancel_left`.

## LiteralLogRiccati

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `U`, `L_zero`, `literal_log_finiteLog`, `literal_log_chain`, `sourceSeries`, `logDerivativeSeries`, `literal_log_chain_series`, `literal_R2_series`, `literal_riccati_series`, `literal_riccati_coeff`, `U_one`, `U_recurrence`.

## LogRiccatiIdentification

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `deltaG_gaussianEmbed`, `deltaG_phase`, `imaginaryUnit_neg_mul`, `phase_successor`, `logarithmic_derivative_all`, `U_eq_scaledH`, `phase_odd`, `imaginary_logarithmic_derivative_odd`, `literal_source_log_riccati_bridge`, `literal_source_odd_log_bridge`, `imaginary_logarithmic_derivative_odd_coeff`.

## LiteralPureCoefficient

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `odd_sign_product`, `literal_pure_derivative`, `literal_pure_primitive`, `sourceLogCoeff_pure_u`, `sourceKappa_pure_u`.

## DyadicArithmetic

Namespace(s): JacobiShifted.DyadicArithmetic.

Source-level named interfaces (not the generated-origin inventory): `factorial_valuation`, `factorial_valuation_mono`, `exponent_balance`, `centralBinom_valuation`, `catalan_ne_zero`, `catalan_valuation`, `twoLocal_iff_valuation_nonneg`.

## HalfSubstitution

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `substitutionNumerator`, `substitutionWeight`, `exponent_bidegree`, `scale_monomial`, `scale_coeff_expansion`.

## SourceUpperBound

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `coefficientPrimitive`, `coefficientPrimitive_spec`, `coefficientPrimitive_bound`, `odd_source_index`, `transportedPrimitive`, `delta_transportedPrimitive`, `tau_transportedPrimitive`, `literal_transportedPrimitive`, `sourceKappa_coeff_expansion`, `twoLocal_finset_sum`, `power_balance`, `transported_term_twoLocal`, `sourceKappa_twoLocal`.

## SourceSharpness

Namespace(s): JacobiShifted.SourceBridge.

Source-level named interfaces (not the generated-origin inventory): `sourceKappa_pure_u_ne_zero`, `sourceKappa_pure_u_valuation`, `sourceKappa_pure_u_sharp`.

## SourceClaim

Namespace(s): JacobiShifted.

Source-level named interfaces (not the generated-origin inventory): `source_claim`.

## Endpoint

```lean
import SourceClaim

set_option autoImplicit false
set_option warningAsError true

#check JacobiShifted.source_claim
#print axioms JacobiShifted.source_claim
#print JacobiShifted.SourceClaim
#print JacobiShifted.sourceKappa
#print JacobiShifted.dyadicExponent
#print JacobiShifted.TwoLocal
#check JacobiShifted.SourceBridge.sourceKappa_twoLocal
#check JacobiShifted.SourceBridge.sourceKappa_pure_u_valuation
#check JacobiShifted.SourceBridge.sourceKappa_pure_u_sharp
#check (JacobiShifted.source_claim : ∀ r : ℕ, 1 ≤ r →
  (∀ m : Fin 2 →₀ ℕ,
    JacobiShifted.TwoLocal ((2 : ℚ)^JacobiShifted.dyadicExponent r *
      (JacobiShifted.sourceKappa r).coeff m)) ∧
  ¬ JacobiShifted.TwoLocal ((2 : ℚ)^(JacobiShifted.dyadicExponent r - 1) *
    (JacobiShifted.sourceKappa r).coeff (Finsupp.single 0 r)))

```
The actual reports print the abbreviated endpoint, definition expansion, literal source definitions, and the fully quantified type ascription. Every generated/private origin declaration is separately enumerated in verification/declarations.json and checked in WholeAudit.
