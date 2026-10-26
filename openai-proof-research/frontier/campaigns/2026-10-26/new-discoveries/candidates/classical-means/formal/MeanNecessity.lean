import MeanAlgebra

open Set Real Filter
open scoped Topology
namespace ClassicalMeanRange

noncomputable def normalizedDefect (n c : ℝ) : ℝ :=
  (2 * c ^ 2 - 1) ^ (n / 2) + c ^ (-n) - c ^ n - 1

noncomputable def firstDeriv (n c : ℝ) : ℝ :=
  2 * n * c * (2 * c ^ 2 - 1) ^ (n / 2 - 1) -
    n * c ^ (-n - 1) - n * c ^ (n - 1)

lemma hasDeriv_normalizedDefect (n : ℝ) {c : ℝ} (hc : 1 ≤ c) :
    HasDerivAt (normalizedDefect n) (firstDeriv n c) c := by
  have hc0 : c ≠ 0 := by linarith
  have hbase : 2 * c ^ 2 - 1 ≠ 0 := by nlinarith
  have hq : HasDerivAt (fun t : ℝ => 2 * t ^ 2 - 1) (4 * c) c := by
    convert (((hasDerivAt_id c).pow 2).const_mul 2).sub_const 1 using 1
    · rfl
    · change 4 * c = 2 * ((2 : ℝ) * c ^ (2 - 1 : ℕ) * 1)
      norm_num
      ring
  have hqn := hq.rpow_const (p := n / 2) (Or.inl hbase)
  have hcn := Real.hasDerivAt_rpow_const (x := c) (p := -n) (Or.inl hc0)
  have hcp := Real.hasDerivAt_rpow_const (x := c) (p := n) (Or.inl hc0)
  unfold normalizedDefect
  convert ((hqn.add hcn).sub hcp).sub_const 1 using 1
  dsimp only [firstDeriv]
  ring

lemma normalizedDefect_one (n : ℝ) : normalizedDefect n 1 = 0 := by
  norm_num [normalizedDefect]

lemma firstDeriv_one (n : ℝ) : firstDeriv n 1 = 0 := by
  norm_num [firstDeriv]
  ring

lemma hasDeriv_firstDeriv_one (n : ℝ) :
    HasDerivAt (firstDeriv n) (4 * n * (n - 1)) 1 := by
  have hq : HasDerivAt (fun t : ℝ => 2 * t ^ 2 - 1) 4 1 := by
    convert (((hasDerivAt_id (1 : ℝ)).pow 2).const_mul 2).sub_const 1 using 1 <;> norm_num
  have hqn := hq.rpow_const (p := n / 2 - 1) (Or.inl (by norm_num))
  have ht := ((hasDerivAt_id (1 : ℝ)).const_mul (2 * n)).mul hqn
  have hu := (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := -n - 1)
    (Or.inl one_ne_zero)).const_mul n
  have hv := (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := n - 1)
    (Or.inl one_ne_zero)).const_mul n
  unfold firstDeriv
  convert (ht.sub hu).sub hv using 1
  · ext c
    rfl
  · norm_num
    ring

/-- Every exponent strictly between zero and one fails on actual normalized pairs. -/
theorem exists_normalized_failure {n : ℝ} (hn0 : 0 < n) (hn1 : n < 1) :
    ∃ c : ℝ, 1 < c ∧ normalizedDefect n c < 0 := by
  have hsecond : deriv (firstDeriv n) 1 < 0 := by
    rw [(hasDeriv_firstDeriv_one n).deriv]
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hs := eventually_nhdsWithin_sign_eq_of_deriv_neg hsecond (firstDeriv_one n)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hs
  let b : ℝ := 1 + ε / 2
  have hb : 1 < b := by dsimp [b]; linarith
  have hanti : StrictAntiOn (normalizedDefect n) (Set.Icc 1 b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 1 b)
    · intro c hc
      exact (hasDeriv_normalizedDefect n hc.1).continuousAt.continuousWithinAt
    · intro c hc
      rw [interior_Icc] at hc
      rw [(hasDeriv_normalizedDefect n hc.1.le).deriv]
      apply sign_eq_neg_one_iff.mp
      have hdist : c ∈ Metric.ball 1 ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith [hc.1] : 0 < c - 1)]
        dsimp [b] at hc
        linarith [hc.2]
      have he := hεsub hdist
      exact he.trans (sign_eq_neg_one_iff.mpr (by linarith [hc.1]))
  refine ⟨b, hb, ?_⟩
  have h := hanti ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩ hb
  simpa only [normalizedDefect_one] using h

end ClassicalMeanRange
