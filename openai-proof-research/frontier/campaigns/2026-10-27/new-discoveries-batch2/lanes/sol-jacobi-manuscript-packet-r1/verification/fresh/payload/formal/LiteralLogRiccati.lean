import RiccatiScale
import FiniteLogChain

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge

/-- The derivative of the literal finite logarithm. -/
def U (n : ℕ) : G := deltaG (L n)

@[simp] theorem L_zero : L 0=0 := by simp [L, literalLog]
@[simp] theorem U_zero : U 0=0 := by simp [U]

theorem literal_log_finiteLog (n : ℕ) :
    L n=FiniteChain.finiteLog (coeffEmbed.comp MvPolynomial.C) F n := rfl

/-- All-order coefficientwise chain rule for the actual source logarithm. -/
theorem literal_log_chain (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), F j*U (n-j))=deltaG (F n) := by
  have hc := FiniteChain.finite_log_chain deltaG deltaG_mul deltaG_one
    (coeffEmbed.comp MvPolynomial.C) (fun q => deltaG_coeffEmbed (MvPolynomial.C q))
    F F_zero n
  simpa only [← literal_log_finiteLog, U] using hc

def sourceSeries : PowerSeries G := PowerSeries.mk F
def logDerivativeSeries : PowerSeries G := PowerSeries.mk U

theorem literal_log_chain_series :
    sourceSeries*logDerivativeSeries=FiniteChain.liftD deltaG sourceSeries := by
  apply PowerSeries.ext
  intro n
  rw [FiniteChain.coeff_mul_range, FiniteChain.coeff_liftD]
  simpa only [sourceSeries, logDerivativeSeries, PowerSeries.coeff_mk] using literal_log_chain n

theorem literal_R2_series :
    PowerSeries.C imaginaryUnit*FiniteChain.liftD deltaG sourceSeries+
      PowerSeries.X*(FiniteChain.liftD deltaG (FiniteChain.liftD deltaG sourceSeries)-
        PowerSeries.C (gaussianEmbed S)*sourceSeries)=0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    have hz : PowerSeries.coeff 0 (FiniteChain.liftD deltaG sourceSeries)=0 := by
      rw [FiniteChain.coeff_liftD]
      simp [sourceSeries]
    simp only [map_add, PowerSeries.coeff_C_mul, hz, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X,
      zero_mul, add_zero, map_zero]
  | succ n =>
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      map_sub, FiniteChain.coeff_liftD, sourceSeries, PowerSeries.coeff_mk, map_zero]
    have h := literal_F_R2 n
    rw [potentialCurve_eq] at h
    linear_combination h

/-- Riccati equation obtained by differentiating the proved chain and cancelling F. -/
theorem literal_riccati_series :
    PowerSeries.C imaginaryUnit*logDerivativeSeries+
      PowerSeries.X*(FiniteChain.liftD deltaG logDerivativeSeries+
        logDerivativeSeries^2-PowerSeries.C (gaussianEmbed S))=0 := by
  apply FiniteChain.cancel_zero sourceSeries _ (by simp [sourceSeries])
  have hdf := literal_log_chain_series.symm
  have hdd : FiniteChain.liftD deltaG (FiniteChain.liftD deltaG sourceSeries)=
      sourceSeries*(FiniteChain.liftD deltaG logDerivativeSeries+logDerivativeSeries^2) := by
    rw [hdf, FiniteChain.liftD_mul deltaG deltaG_mul, hdf]
    ring
  have h := literal_R2_series
  rw [hdd, hdf] at h
  calc
    _ = PowerSeries.C imaginaryUnit*(sourceSeries*logDerivativeSeries)+
      PowerSeries.X*(sourceSeries*(FiniteChain.liftD deltaG logDerivativeSeries+
        logDerivativeSeries^2)-PowerSeries.C (gaussianEmbed S)*sourceSeries) := by ring
    _ = 0 := h

theorem literal_riccati_coeff (n : ℕ) :
    imaginaryUnit*U (n+1)+deltaG (U n)+
      (∑ j ∈ Finset.range (n+1), U j*U (n-j))-
      (if n=0 then gaussianEmbed S else 0)=0 := by
  have h := congrArg (PowerSeries.coeff (n+1)) literal_riccati_series
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    map_sub, FiniteChain.coeff_liftD, PowerSeries.coeff_C, map_zero] at h
  simp only [pow_two, FiniteChain.coeff_mul_range,
    logDerivativeSeries, PowerSeries.coeff_mk] at h
  linear_combination h

@[simp] theorem U_one : U 1= -imaginaryUnit*gaussianEmbed S := by
  simpa only [U, scaledH_one] using logarithmic_derivative_one

theorem U_recurrence (n : ℕ) (hn : 1≤n) :
    imaginaryUnit*U (n+1)= -deltaG (U n)-
      ∑ j ∈ Finset.range (n+1), U j*U (n-j) := by
  have h := literal_riccati_coeff n
  rw [ite_eq_right (by omega), sub_zero] at h
  linear_combination h

end JacobiShifted.SourceBridge
