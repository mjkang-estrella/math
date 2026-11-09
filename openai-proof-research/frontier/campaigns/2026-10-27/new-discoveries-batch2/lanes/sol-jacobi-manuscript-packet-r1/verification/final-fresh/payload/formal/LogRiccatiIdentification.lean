import LiteralLogRiccati

set_option autoImplicit false
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

noncomputable section
namespace JacobiShifted.SourceBridge

@[simp] theorem deltaG_gaussianEmbed (a : A) :
    deltaG (gaussianEmbed a)=gaussianEmbed (deltaA a) := by
  apply QuadraticAlgebra.ext <;> simp [gaussianEmbed]

@[simp] theorem deltaG_phase (n : ℕ) : deltaG ((-imaginaryUnit)^n)=0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, deltaG_mul, ih]

theorem imaginaryUnit_neg_mul : imaginaryUnit*(-imaginaryUnit)=1 := by
  calc
    _ = -imaginaryUnit^2 := by ring
    _ = 1 := by rw [imaginaryUnit_sq]; ring

theorem phase_successor (n : ℕ) :
    imaginaryUnit*(-imaginaryUnit)^(n+1)=(-imaginaryUnit)^n := by
  rw [pow_succ, mul_left_comm, imaginaryUnit_neg_mul, mul_one]

/-- Coefficientwise uniqueness identifies the literal logarithm with the integral recurrence. -/
theorem logarithmic_derivative_all (n : ℕ) :
    deltaG (L n)=(-imaginaryUnit)^n*gaussianEmbed (scaledH n) := by
  change U n=_
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      by_cases hn : n=0
      · subst n; simp
      have hn1 : 1≤n := by omega
      have hid : U n=(-imaginaryUnit)^n*gaussianEmbed (scaledH n) := ih n (by omega)
      have hs : (∑ j ∈ Finset.range (n+1), U j*U (n-j))=
          (-imaginaryUnit)^n*gaussianEmbed
            (∑ j ∈ Finset.range (n+1), scaledH j*scaledH (n-j)) := by
        simp only [map_sum, map_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j≤n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
        rw [ih j (by omega), ih (n-j) (by omega)]
        calc
          _ = ((-imaginaryUnit)^j*(-imaginaryUnit)^(n-j))*
              (gaussianEmbed (scaledH j)*gaussianEmbed (scaledH (n-j))) := by ring
          _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjn]
      apply imaginaryUnit_mul_injective
      dsimp only
      rw [U_recurrence n hn1, hs, hid, deltaG_mul,
        deltaG_phase, zero_mul, zero_add, deltaG_gaussianEmbed]
      calc
        _ = (-imaginaryUnit)^n*gaussianEmbed (scaledH (n+1)) := by
          rw [scaledH_recurrence n hn1, map_sub, map_neg]
          ring
        _ = _ := by rw [← mul_assoc, phase_successor]

/-- The requested identity includes the zero coefficient. -/
theorem U_eq_scaledH (n : ℕ) : U n=(-imaginaryUnit)^n*gaussianEmbed (scaledH n) :=
  logarithmic_derivative_all n

/-- Natural powers give the exact Gaussian phase at every positive odd order. -/
theorem phase_odd (r : ℕ) (hr : 1≤r) :
    (-imaginaryUnit)^(2*r-1)=gaussianEmbed ((-1 : A)^r)*imaginaryUnit := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  have he : 2*(k+1)-1=2*k+1 := by omega
  have hneg : (-imaginaryUnit)^2=(-1 : G) := by
    calc
      _ = imaginaryUnit^2 := by ring
      _ = _ := imaginaryUnit_sq
  rw [he, pow_succ, pow_mul, hneg]
  have hc : gaussianEmbed ((-1 : A)^(k+1))=(-1 : G)^(k+1) := by simp only [map_pow, map_neg, map_one]
  rw [hc, pow_succ]
  ring

/-- Imaginary coefficient of the actual literal finite logarithm, at every odd order. -/
theorem imaginary_logarithmic_derivative_odd (r : ℕ) (hr : 1≤r) :
    deltaA (L (2*r-1)).im=(-1 : A)^r*scaledH (2*r-1) := by
  have h := congrArg QuadraticAlgebra.im (logarithmic_derivative_all (2*r-1))
  rw [phase_odd r hr] at h
  change deltaA (L (2*r-1)).im=
    ((⟨(-1 : A)^r,0⟩ : G)*⟨0,1⟩*⟨scaledH (2*r-1),0⟩).im at h
  simpa only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mul,
    zero_mul, mul_zero, mul_one, add_zero, zero_add] using h

/-- Exact normalization and evaluation remain bundled with the derivative identification. -/
theorem literal_source_log_riccati_bridge (n : ℕ) :
    midpointG (F n)=sourceFCoeff n ∧ midpointG (L n)=sourceLogCoeff n ∧
    deltaG (L n)=(-imaginaryUnit)^n*gaussianEmbed (scaledH n) ∧
    tauA (L n).im= -(L n).im ∧ midpointA (L n).im=(sourceLogCoeff n).im := by
  exact ⟨midpoint_F n, midpoint_L n, logarithmic_derivative_all n,
    literal_imaginary_normalization n⟩

theorem literal_source_odd_log_bridge (r : ℕ) (hr : 1≤r) :
    deltaA (L (2*r-1)).im=(-1 : A)^r*scaledH (2*r-1) ∧
    tauA (L (2*r-1)).im= -(L (2*r-1)).im ∧
    midpointA (L (2*r-1)).im=(sourceLogCoeff (2*r-1)).im := by
  exact ⟨imaginary_logarithmic_derivative_odd r hr,
    literal_imaginary_normalization (2*r-1)⟩

/-- Arbitrary parameter bidegrees commute with the literal odd derivative identity. -/
theorem imaginary_logarithmic_derivative_odd_coeff (r : ℕ) (hr : 1≤r)
    (m : Fin 2 →₀ ℕ) :
    MidpointRational.delta ((L (2*r-1)).im.coeff m)=
      (-1 : MidpointRational.QAlg)^r*(scaledH (2*r-1)).coeff m := by
  have h := congrArg (fun p : A => p.coeff m)
    (imaginary_logarithmic_derivative_odd r hr)
  rw [deltaA_coeff] at h
  have hc : (-1 : A)^r=MvPolynomial.C ((-1 : MidpointRational.QAlg)^r) := by simp
  rw [hc, MvPolynomial.coeff_C_mul] at h
  exact h

end JacobiShifted.SourceBridge
