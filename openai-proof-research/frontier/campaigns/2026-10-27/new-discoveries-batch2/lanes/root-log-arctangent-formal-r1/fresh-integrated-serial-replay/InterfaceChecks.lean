import Transfer
import MeanDerivatives
set_option warningAsError true
set_option autoImplicit false
#check @LogArctangentSource.mean
#print axioms LogArctangentSource.mean
#check @LogArctangentSource.powerMean
#print axioms LogArctangentSource.powerMean
#check @LogArctangentSource.resultant
#print axioms LogArctangentSource.resultant
#check @LogArctangentSource.SourceClaim
#print axioms LogArctangentSource.SourceClaim
#check @LogArctangentSource.mean_self
#print axioms LogArctangentSource.mean_self
#check @LogArctangentSource.mean_symm
#print axioms LogArctangentSource.mean_symm
#check @LogArctangentSource.mean_pos_of_lt
#print axioms LogArctangentSource.mean_pos_of_lt
#check @LogArctangentSource.mean_pos
#print axioms LogArctangentSource.mean_pos
#check @LogArctangentSource.mean_homogeneous
#print axioms LogArctangentSource.mean_homogeneous
#check @LogArctangentSource.powerMean_symm
#print axioms LogArctangentSource.powerMean_symm
#check @LogArctangentSource.powerMean_pos
#print axioms LogArctangentSource.powerMean_pos
#check @LogArctangentSource.powerMean_self
#print axioms LogArctangentSource.powerMean_self
#check @LogArctangentSource.powerMean_homogeneous
#print axioms LogArctangentSource.powerMean_homogeneous
#check @LogArctangentSource.powerMean_strict_mono
#print axioms LogArctangentSource.powerMean_strict_mono
#check @LogArctangentSource.powerMean_strict_mono_left
#print axioms LogArctangentSource.powerMean_strict_mono_left
#check @LogArctangentSource.powerMean_strict_mono_right
#print axioms LogArctangentSource.powerMean_strict_mono_right
#check @LogArctangentSource.powerMean_between
#print axioms LogArctangentSource.powerMean_between
#check @LogArctangentSource.resultant_symm
#print axioms LogArctangentSource.resultant_symm
#check @LogArctangentSource.resultant_pos
#print axioms LogArctangentSource.resultant_pos
#check @LogArctangentSource.resultant_homogeneous
#print axioms LogArctangentSource.resultant_homogeneous
#check @LogArctangentSource.d
#print axioms LogArctangentSource.d
#check @LogArctangentSource.alpha
#print axioms LogArctangentSource.alpha
#check @LogArctangentSource.beta
#print axioms LogArctangentSource.beta
#check @LogArctangentSource.d_bounds
#print axioms LogArctangentSource.d_bounds
#check @LogArctangentSource.parameters
#print axioms LogArctangentSource.parameters
#check @LogArctangentSource.stolarsky
#print axioms LogArctangentSource.stolarsky
#check @LogArctangentSource.fixedS
#print axioms LogArctangentSource.fixedS
#check @LogArctangentSource.centeredLogGap
#print axioms LogArctangentSource.centeredLogGap
#check @LogArctangentSource.stolarsky_symm
#print axioms LogArctangentSource.stolarsky_symm
#check @LogArctangentSource.stolarsky_base_pos
#print axioms LogArctangentSource.stolarsky_base_pos
#check @LogArctangentSource.stolarsky_pos
#print axioms LogArctangentSource.stolarsky_pos
#check @LogArctangentSource.stolarsky_power
#print axioms LogArctangentSource.stolarsky_power
#check @LogArctangentSource.powerMean_power
#print axioms LogArctangentSource.powerMean_power
#check @LogArctangentSource.stolarsky_stabilization
#print axioms LogArctangentSource.stolarsky_stabilization
#check @LogArctangentSource.stolarsky_homogeneous_lt
#print axioms LogArctangentSource.stolarsky_homogeneous_lt
#check @LogArctangentSource.stolarsky_homogeneous
#print axioms LogArctangentSource.stolarsky_homogeneous
#check @LogArctangentSource.fixedS_pos
#print axioms LogArctangentSource.fixedS_pos
#check @LogArctangentSource.fixedS_symm
#print axioms LogArctangentSource.fixedS_symm
#check @LogArctangentSource.fixedS_homogeneous
#print axioms LogArctangentSource.fixedS_homogeneous
#check @LogArctangentSource.fixedS_stabilization_positive
#print axioms LogArctangentSource.fixedS_stabilization_positive
#check @LogArctangentSource.stolarsky_swap
#print axioms LogArctangentSource.stolarsky_swap
#check @LogArctangentSource.fixedS_stabilization_negative
#print axioms LogArctangentSource.fixedS_stabilization_negative
#check @LogArctangentSource.mean_log_ratio
#print axioms LogArctangentSource.mean_log_ratio
#check @LogArctangentSource.fixedS_self
#print axioms LogArctangentSource.fixedS_self
#check @LogArctangentSource.fixedS_formula
#print axioms LogArctangentSource.fixedS_formula
#check @LogArctangentSource.centered_representation
#print axioms LogArctangentSource.centered_representation
#check @LogArctangentSource.gap_log_ratio
#print axioms LogArctangentSource.gap_log_ratio
#check @LogArctangentSource.subinterval_ratio
#print axioms LogArctangentSource.subinterval_ratio
#check @LogArctangentSource.transfer_of_stabilization
#print axioms LogArctangentSource.transfer_of_stabilization
#check @LogArctangentSource.sourceClaim_of_strictMono_gap
#print axioms LogArctangentSource.sourceClaim_of_strictMono_gap
#check @LogArctangentMean.d
#print axioms LogArctangentMean.d
#check @LogArctangentMean.A
#print axioms LogArctangentMean.A
#check @LogArctangentMean.B
#print axioms LogArctangentMean.B
#check @LogArctangentMean.U
#print axioms LogArctangentMean.U
#check @LogArctangentMean.V
#print axioms LogArctangentMean.V
#check @LogArctangentMean.E
#print axioms LogArctangentMean.E
#check @LogArctangentMean.d_sq
#print axioms LogArctangentMean.d_sq
#check @LogArctangentMean.d_nonneg
#print axioms LogArctangentMean.d_nonneg
#check @LogArctangentMean.d_bounds
#print axioms LogArctangentMean.d_bounds
#check @LogArctangentMean.d_ne
#print axioms LogArctangentMean.d_ne
#check @LogArctangentMean.Ap
#print axioms LogArctangentMean.Ap
#check @LogArctangentMean.Bp
#print axioms LogArctangentMean.Bp
#check @LogArctangentMean.hasDerivAt_A
#print axioms LogArctangentMean.hasDerivAt_A
#check @LogArctangentMean.hasDerivAt_B
#print axioms LogArctangentMean.hasDerivAt_B
#check @LogArctangentMean.deriv_A
#print axioms LogArctangentMean.deriv_A
#check @LogArctangentMean.deriv_B
#print axioms LogArctangentMean.deriv_B
#check @LogArctangentMean.contDiff_A
#print axioms LogArctangentMean.contDiff_A
#check @LogArctangentMean.contDiff_B
#print axioms LogArctangentMean.contDiff_B
#check @LogArctangentMean.contDiff_Ap
#print axioms LogArctangentMean.contDiff_Ap
#check @LogArctangentMean.contDiff_Bp
#print axioms LogArctangentMean.contDiff_Bp
#check @LogArctangentMean.contDiff_U
#print axioms LogArctangentMean.contDiff_U
#check @LogArctangentMean.contDiff_V
#print axioms LogArctangentMean.contDiff_V
#check @LogArctangentMean.contDiff_E
#print axioms LogArctangentMean.contDiff_E
