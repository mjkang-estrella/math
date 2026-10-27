import SourceDefs
import TailBound
import Weights
import Stationarity
import Moments
import QuotientBridge
import SourceTail
import IntegerPolynomials
import PolynomialSources
import FiniteCheck
import FiniteBridge
import SmallCertificatesA
import SmallCertificatesB
import SmallCertificatesC
import SmallCertificatesD
import SmallCertificatesE
import SmallCertificatesF
import SmallCertificatesG
import SourceEndpoint

#check Davis.falling
#print axioms Davis.falling
#check Davis.weight
#print axioms Davis.weight
#check Davis.P
#print axioms Davis.P
#check Davis.quotient
#print axioms Davis.quotient
#check Davis.remainder
#print axioms Davis.remainder
#check Davis.SourceConjecture319187
#print axioms Davis.SourceConjecture319187
#check Davis.falling_pos
#print axioms Davis.falling_pos
#check Davis.weight_nonneg
#print axioms Davis.weight_nonneg
#check Davis.P_pos
#print axioms Davis.P_pos
#check Davis.varianceTarget
#print axioms Davis.varianceTarget
#check Davis.momentCoefficient
#print axioms Davis.momentCoefficient
#check Davis.comparisonNumerator
#print axioms Davis.comparisonNumerator
#check Davis.comparisonNumerator_pos
#print axioms Davis.comparisonNumerator_pos
#check Davis.target_pos
#print axioms Davis.target_pos
#check Davis.target_quadratic_pos
#print axioms Davis.target_quadratic_pos
#check Davis.tail_variance_bound
#print axioms Davis.tail_variance_bound
#check Davis.falling_succ
#print axioms Davis.falling_succ
#check Davis.weight_reverse
#print axioms Davis.weight_reverse
#check Davis.weight_step
#print axioms Davis.weight_step
#check Davis.weight_balance
#print axioms Davis.weight_balance
#check Davis.finite_flux
#print axioms Davis.finite_flux
#check Davis.finite_stationarity
#print axioms Davis.finite_stationarity
#check Davis.centralMoment
#print axioms Davis.centralMoment
#check Davis.raw_moment_identity
#print axioms Davis.raw_moment_identity
#check Davis.moment_identity
#print axioms Davis.moment_identity
#check Davis.centralMoment_two_nonneg
#print axioms Davis.centralMoment_two_nonneg
#check Davis.moment_four_ge_sq
#print axioms Davis.moment_four_ge_sq
#check Davis.weighted_reflect
#print axioms Davis.weighted_reflect
#check Davis.weighted_mean
#print axioms Davis.weighted_mean
#check Davis.weighted_center_zero
#print axioms Davis.weighted_center_zero
#check Davis.P_step_sum
#print axioms Davis.P_step_sum
#check Davis.P_step_centered
#print axioms Davis.P_step_centered
#check Davis.remainder_ratio_moment
#print axioms Davis.remainder_ratio_moment
#check Davis.source_tail
#print axioms Davis.source_tail
#check Davis.coeffAdd
#print axioms Davis.coeffAdd
#check Davis.coeffScale
#print axioms Davis.coeffScale
#check Davis.coeffMul
#print axioms Davis.coeffMul
#check Davis.coeffEval
#print axioms Davis.coeffEval
#check Davis.coeffEval_add
#print axioms Davis.coeffEval_add
#check Davis.coeffEval_scale
#print axioms Davis.coeffEval_scale
#check Davis.coeffEval_mul
#print axioms Davis.coeffEval_mul
#check Davis.coeffEval_nonneg
#print axioms Davis.coeffEval_nonneg
#check Davis.coeffEval_pos
#print axioms Davis.coeffEval_pos
#check Davis.coeffTranslate
#print axioms Davis.coeffTranslate
#check Davis.coeffEval_translate
#print axioms Davis.coeffEval_translate
#check Davis.coeffRangeSum
#print axioms Davis.coeffRangeSum
#check Davis.coeffEval_rangeSum
#print axioms Davis.coeffEval_rangeSum
#check Davis.fallingCoeffs
#print axioms Davis.fallingCoeffs
#check Davis.scaledPCoeffs
#print axioms Davis.scaledPCoeffs
#check Davis.inequalityCoeffs
#print axioms Davis.inequalityCoeffs
#check Davis.coeffEval_falling
#print axioms Davis.coeffEval_falling
#check Davis.coeffEval_scaledP
#print axioms Davis.coeffEval_scaledP
#check Davis.coeffEval_inequality
#print axioms Davis.coeffEval_inequality
#check Davis.shiftNumerator
#print axioms Davis.shiftNumerator
#check Davis.certificateCoeffs
#print axioms Davis.certificateCoeffs
#check Davis.certificateCheck
#print axioms Davis.certificateCheck
#check Davis.source_threshold_ge_shift
#print axioms Davis.source_threshold_ge_shift
#check Davis.certificate_implies_positive
#print axioms Davis.certificate_implies_positive
#check Davis.source_bound_of_certificate
#print axioms Davis.source_bound_of_certificate
#check Davis.certificate_5
#print axioms Davis.certificate_5
#check Davis.certificate_6
#print axioms Davis.certificate_6
#check Davis.certificate_7
#print axioms Davis.certificate_7
#check Davis.certificate_8
#print axioms Davis.certificate_8
#check Davis.certificate_9
#print axioms Davis.certificate_9
#check Davis.certificate_10
#print axioms Davis.certificate_10
#check Davis.certificate_11
#print axioms Davis.certificate_11
#check Davis.certificate_12
#print axioms Davis.certificate_12
#check Davis.certificate_13
#print axioms Davis.certificate_13
#check Davis.certificate_14
#print axioms Davis.certificate_14
#check Davis.certificate_15
#print axioms Davis.certificate_15
#check Davis.certificate_16
#print axioms Davis.certificate_16
#check Davis.certificate_17
#print axioms Davis.certificate_17
#check Davis.certificate_18
#print axioms Davis.certificate_18
#check Davis.certificate_19
#print axioms Davis.certificate_19
#check Davis.certificate_20
#print axioms Davis.certificate_20
#check Davis.certificate_21
#print axioms Davis.certificate_21
#check Davis.certificate_22
#print axioms Davis.certificate_22
#check Davis.certificate_23
#print axioms Davis.certificate_23
#check Davis.certificate_24
#print axioms Davis.certificate_24
#check Davis.certificate_25
#print axioms Davis.certificate_25
#check Davis.certificate_26
#print axioms Davis.certificate_26
#check Davis.certificate_27
#print axioms Davis.certificate_27
#check Davis.certificate_28
#print axioms Davis.certificate_28
#check Davis.certificate_29
#print axioms Davis.certificate_29
#check Davis.certificate_30
#print axioms Davis.certificate_30
#check Davis.certificate_31
#print axioms Davis.certificate_31
#check Davis.certificate_32
#print axioms Davis.certificate_32
#check Davis.certificate_33
#print axioms Davis.certificate_33
#check Davis.certificate_34
#print axioms Davis.certificate_34
#check Davis.certificate_35
#print axioms Davis.certificate_35
#check Davis.certificate_36
#print axioms Davis.certificate_36
#check Davis.certificate_37
#print axioms Davis.certificate_37
#check Davis.certificate_38
#print axioms Davis.certificate_38
#check Davis.certificate_39
#print axioms Davis.certificate_39
#check Davis.certificate_40
#print axioms Davis.certificate_40
#check Davis.certificate_41
#print axioms Davis.certificate_41
#check Davis.certificate_42
#print axioms Davis.certificate_42
#check Davis.small_certificates
#print axioms Davis.small_certificates
#check Davis.source_strict_bound
#print axioms Davis.source_strict_bound
#check Davis.source_conjecture_319187
#print axioms Davis.source_conjecture_319187
