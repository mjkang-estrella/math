import ComplexAnalytic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MittagModulus

section Linear
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem betaAverage_map (β : ℝ) (k : ℕ) (L : E →L[ℝ] G) {f : ℝ → E}
    (hf : Continuous f) :
    betaAverage β k (fun y => L (f y)) = fun x => L (betaAverage β k f x) := by
  funext x
  have hi : IntervalIntegrable (fun u : ℝ => u ^ k • f (x * u)) MeasureTheory.volume 0 1 :=
    ((continuous_id.pow k).smul (hf.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simp only [betaAverage, map_add, map_smul]
  rw [← L.intervalIntegral_comp_comm hi]
  simp only [map_smul]

theorem finiteBetaAverage_map (β : ℝ) (n : ℕ) (L : E →L[ℝ] G) {f : ℝ → E}
    (hf : Continuous f) :
    finiteBetaAverage β n (fun y => L (f y)) =
      fun x => L (finiteBetaAverage β n f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finiteBetaAverage, ih]
    exact betaAverage_map β n L (finiteBetaAverage_continuous β n hf)
end Linear

noncomputable def pairLeft (d : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ).flip (starRingEnd ℂ d))

noncomputable def pairRight (c : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((ContinuousLinearMap.mul ℝ ℂ c).comp Complex.conjCLE.toContinuousLinearMap)

theorem finiteBetaAverage_pair_left (β : ℝ) (n : ℕ) {f : ℝ → ℂ}
    (hf : Continuous f) (d : ℂ) (x : ℝ) :
    finiteBetaAverage β n (fun y => (f y * starRingEnd ℂ d).re) x =
      (finiteBetaAverage β n f x * starRingEnd ℂ d).re := by
  exact congrFun (finiteBetaAverage_map β n (pairLeft d) hf) x

theorem finiteBetaAverage_pair_right (β : ℝ) (n : ℕ) {f : ℝ → ℂ}
    (hf : Continuous f) (c : ℂ) (x : ℝ) :
    finiteBetaAverage β n (fun y => (c * starRingEnd ℂ (f y)).re) x =
      (c * starRingEnd ℂ (finiteBetaAverage β n f x)).re := by
  exact congrFun (finiteBetaAverage_map β n (pairRight c) hf) x

theorem finiteBetaAverage_normSq (β : ℝ) (n : ℕ) {f : ℝ → ℂ}
    (hf : Continuous f) (x : ℝ) :
    Complex.normSq (finiteBetaAverage β n f x) =
      finiteBetaAverage β n (fun v => finiteBetaAverage β n
        (fun w => (f v * starRingEnd ℂ (f w)).re) x) x := by
  simp only [finiteBetaAverage_pair_right β n hf, finiteBetaAverage_pair_left β n hf]
  rw [Complex.mul_conj, Complex.ofReal_re]

/-- The actual half-order cross kernel, using no presumed Gaussian representation. -/
noncomputable def halfCross (v w t : ℝ) : ℝ :=
  ((mittagLeffler (1 / 2) 1 ((Real.sqrt t : ℂ) * Complex.I * (Real.sqrt v : ℂ))) *
    starRingEnd ℂ (mittagLeffler (1 / 2) 1
      ((Real.sqrt t : ℂ) * Complex.I * (Real.sqrt w : ℂ)))).re

theorem halfTransform_continuous (z : ℂ) :
    Continuous (fun v : ℝ => mittagLeffler (1 / 2) 1 (z * (Real.sqrt v : ℂ))) := by
  exact (mittagLeffler_continuous (by norm_num : (0 : ℝ) < 1 / 2) zero_lt_one).comp
    (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt))

theorem squaredApprox_eq_doubleAverage {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (N : ℕ) (t : ℝ) :
    squaredApprox a N t = finiteBetaAverage (2 * a) (N + 2)
      (fun v => finiteBetaAverage (2 * a) (N + 2) (fun w => halfCross v w t)
        (((N : ℝ) + 1) ^ (1 - 2 * a)))
      (((N : ℝ) + 1) ^ (1 - 2 * a)) := by
  unfold squaredApprox
  rw [approxTransform_eq_finiteBetaAverage ha ha2 N,
    finiteBetaAverage_normSq (2 * a) (N + 2) (halfTransform_continuous _)]
  rfl

theorem halfCross_continuous_left (w t : ℝ) :
    Continuous (fun v => halfCross v w t) := by
  exact Complex.continuous_re.comp
    ((halfTransform_continuous ((Real.sqrt t : ℂ) * Complex.I)).mul_const _)

theorem halfCross_continuous_right (v t : ℝ) :
    Continuous (fun w => halfCross v w t) := by
  exact Complex.continuous_re.comp (continuous_const.mul
    (Complex.conjCLE.continuous.comp
      (halfTransform_continuous ((Real.sqrt t : ℂ) * Complex.I))))

theorem averaged_halfCross_continuous_left (β : ℝ) (n : ℕ) (x t : ℝ) :
    Continuous (fun v => finiteBetaAverage β n (fun w => halfCross v w t) x) := by
  change Continuous (fun v => finiteBetaAverage β n (fun w =>
    (mittagLeffler (1 / 2) 1 ((Real.sqrt t : ℂ) * Complex.I * (Real.sqrt v : ℂ)) *
      starRingEnd ℂ (mittagLeffler (1 / 2) 1
        ((Real.sqrt t : ℂ) * Complex.I * (Real.sqrt w : ℂ)))).re) x)
  simp only [finiteBetaAverage_pair_right β n (halfTransform_continuous _)]
  exact Complex.continuous_re.comp
    ((halfTransform_continuous ((Real.sqrt t : ℂ) * Complex.I)).mul_const _)

/-- Still conditional: the genuine two-scale half-order kernel must be positive.
All finite-product averaging and passage to the literal source are proved here. -/
theorem sourceClaim_of_halfCross_positive
    (hcross : ∀ v w : ℝ, 0 ≤ v → 0 ≤ w → PositiveMixedDifferences (halfCross v w)) :
    SourceClaim370772 := by
  apply sourceClaim_of_positiveMixedApprox
  intro a ha ha2 N
  let c : ℝ := ((N : ℝ) + 1) ^ (1 - 2 * a)
  have hc : c ∈ Set.Icc 0 c := ⟨Real.rpow_nonneg (by positivity) _, le_rfl⟩
  have havg : PositiveMixedDifferences
      (fun t => finiteBetaAverage (2 * a) (N + 2)
        (fun v => finiteBetaAverage (2 * a) (N + 2) (fun w => halfCross v w t) c) c) := by
    apply finiteBetaAverage_positiveMixedDifferences (by positivity : 0 ≤ 2 * a)
      (by linarith : 2 * a ≤ 1) (N + 2)
      (fun t => averaged_halfCross_continuous_left (2 * a) (N + 2) c t)
    · intro v hv
      exact finiteBetaAverage_positiveMixedDifferences (by positivity : 0 ≤ 2 * a)
        (by linarith : 2 * a ≤ 1) (N + 2) (fun t => halfCross_continuous_right v t)
        (fun w hw => hcross v w hv.1 hw.1) c hc
    · exact hc
  have he : squaredApprox a N = fun t => finiteBetaAverage (2 * a) (N + 2)
      (fun v => finiteBetaAverage (2 * a) (N + 2) (fun w => halfCross v w t) c) c :=
    funext (squaredApprox_eq_doubleAverage ha ha2 N)
  rw [he]
  exact havg

end MittagModulus
