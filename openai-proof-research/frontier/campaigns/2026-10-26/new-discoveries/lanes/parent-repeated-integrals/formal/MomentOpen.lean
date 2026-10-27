import MomentDefs

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology Matrix

namespace RepeatedIntegrals

noncomputable section

/-! ## A fixed smooth bump function -/

/-- A fixed `C^∞` bump function on the line: it equals `1` on a neighborhood of `1/2`,
is supported strictly inside `(0, 1)`, and satisfies `0 ≤ χ ≤ 1` everywhere. -/
def bump : ContDiffBump ((1 / 2 : ℝ)) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The scalar bump function. -/
def chi : ℝ → ℝ := fun t => bump t

theorem chi_nonneg (t : ℝ) : 0 ≤ chi t := bump.nonneg

theorem chi_le_one (t : ℝ) : chi t ≤ 1 := bump.le_one

theorem chi_contDiff : ContDiff ℝ ∞ chi := bump.contDiff

theorem chi_pos {t : ℝ} (h : t ∈ Metric.ball ((1 / 2 : ℝ)) (1 / 4)) : 0 < chi t :=
  bump.pos_of_mem_ball h

theorem chi_eq_zero {t : ℝ} (h : (1 / 4 : ℝ) ≤ dist t (1 / 2)) : chi t = 0 :=
  bump.zero_of_le_dist h

theorem chi_eq_zero_of_lt {t : ℝ} (h : t < 1 / 4) : chi t = 0 := by
  refine chi_eq_zero ?_
  rw [Real.dist_eq, abs_of_neg (show t - 1 / 2 < 0 by linarith)]
  linarith

theorem chi_eq_zero_of_gt {t : ℝ} (h : 3 / 4 < t) : chi t = 0 := by
  refine chi_eq_zero ?_
  rw [Real.dist_eq, abs_of_pos (show t - 1 / 2 > 0 by linarith)]
  linarith

/-! ## The polynomial perturbation -/

/-- The polynomial perturbation `t ↦ ∑ j, c j * t ^ j.val`. -/
def weightPoly {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ → ℝ := fun t => ∑ j, c j * t ^ j.val

theorem contDiff_weightPoly {n : ℕ} (c : Fin (n + 1) → ℝ) : ContDiff ℝ ∞ (weightPoly c) :=
  ContDiff.sum fun j _ =>
    (contDiff_const (c := c j)).mul ((contDiff_id (𝕜 := ℝ) (n := ∞)).pow j.val)

/-- A nonzero coefficient vector gives a polynomial perturbation that does not vanish
everywhere on the ball `ball (1/2) (1/4)`, because a nonzero polynomial has finitely
many roots while that ball is infinite. -/
theorem exists_ball_weightPoly_ne_zero {n : ℕ} {c : Fin (n + 1) → ℝ} (hc : c ≠ 0) :
    ∃ t ∈ Metric.ball ((1 / 2 : ℝ)) (1 / 4), weightPoly c t ≠ 0 := by
  set P : Polynomial ℝ := ∑ j ∈ Finset.univ, Polynomial.monomial j.val (c j) with hPdef
  have hPne : P ≠ 0 := by
    intro hP0
    obtain ⟨j0, hj0⟩ : ∃ j0, c j0 ≠ 0 := by
      by_contra hcon
      refine hc (funext fun j => ?_)
      by_contra hj
      exact hcon ⟨j, hj⟩
    have hcoeff : P.coeff j0.val = c j0 := by
      rw [hPdef, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single j0]
      · simp
      · intro i _ hi
        have hval : i.val ≠ j0.val := fun h => hi (Fin.ext h)
        simp [Polynomial.coeff_monomial, hval]
      · intro hmem
        exact absurd (Finset.mem_univ j0) hmem
    rw [hP0, Polynomial.coeff_zero] at hcoeff
    exact hj0 hcoeff.symm
  have hroots : {x : ℝ | P.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hPne
  have hball : (Metric.ball ((1 / 2 : ℝ)) (1 / 4)).Infinite := by
    rw [Real.ball_eq_Ioo]
    exact Set.Ioo_infinite (by norm_num)
  obtain ⟨t0, ht0⟩ := (hball.sdiff hroots).nonempty
  refine ⟨t0, ht0.1, fun hw => ht0.2 ?_⟩
  have heval : P.eval t0 = weightPoly c t0 := by
    rw [hPdef, Polynomial.eval_finsetSum]
    simp [Polynomial.eval_monomial, weightPoly]
  show P.eval t0 = 0
  rw [heval]
  exact hw

/-! ## The Gram matrix of the bump -/

/-- The `(i, j)` entry integrates `t ^ (i + j)` against the bump. -/
def gramMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => ∫ t in (0 : ℝ)..1, t ^ (i.val + j.val) * chi t

theorem gramMatrix_mulVec {n : ℕ} (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (gramMatrix n *ᵥ c) i = ∫ t in (0 : ℝ)..1, chi t * t ^ i.val * weightPoly c t := by
  have hint : ∀ t : ℝ, ∑ j, c j * (t ^ (i.val + j.val) * chi t)
      = chi t * t ^ i.val * weightPoly c t := by
    intro t
    simp only [weightPoly, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc (gramMatrix n *ᵥ c) i = ∑ j, gramMatrix n i j * c j := rfl
    _ = ∑ j, c j * ∫ t in (0 : ℝ)..1, t ^ (i.val + j.val) * chi t := by
          refine Finset.sum_congr rfl fun j _ => ?_
          show (∫ t in (0 : ℝ)..1, t ^ (i.val + j.val) * chi t) * c j = _
          ring
    _ = ∑ j, ∫ t in (0 : ℝ)..1, c j * (t ^ (i.val + j.val) * chi t) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact (intervalIntegral.integral_const_mul (c j)
            (fun t => t ^ (i.val + j.val) * chi t)).symm
    _ = ∫ t in (0 : ℝ)..1, ∑ j, c j * (t ^ (i.val + j.val) * chi t) := by
          refine (intervalIntegral.integral_finsetSum (fun j _ => ?_)).symm
          exact ((contDiff_const (c := c j)).mul
            (((contDiff_id (𝕜 := ℝ) (n := ∞)).pow (i.val + j.val)).mul chi_contDiff)).continuous.intervalIntegrable 0 1
    _ = ∫ t in (0 : ℝ)..1, chi t * t ^ i.val * weightPoly c t := by
          refine intervalIntegral.integral_congr (fun t _ => hint t)

/-- The Gram matrix of the bump is positive definite: a nonzero coefficient vector `c`
gives `∫ χ t * (∑ c_i t^i)^2 dt > 0`, since the integrand is nonnegative, continuous,
and strictly positive at some point of the bump's positivity interval (a nonzero
polynomial cannot vanish on an interval). -/
theorem integral_chi_weightPoly_sq_pos {n : ℕ} {c : Fin (n + 1) → ℝ} (hc : c ≠ 0) :
    0 < ∫ t in (0 : ℝ)..1, chi t * (weightPoly c t) ^ 2 := by
  obtain ⟨t0, ht0ball, ht0ne⟩ := exists_ball_weightPoly_ne_zero hc
  have ht0Icc : t0 ∈ Icc (0 : ℝ) 1 := by
    rw [Real.ball_eq_Ioo] at ht0ball
    obtain ⟨h1, h2⟩ := ht0ball
    exact ⟨by linarith, by linarith⟩
  refine intervalIntegral.integral_pos (by norm_num)
    ((chi_contDiff.mul ((contDiff_weightPoly c).pow 2)).continuous.continuousOn)
    (fun x _ => mul_nonneg (chi_nonneg x) (sq_nonneg _))
    ⟨t0, ht0Icc, mul_pos (chi_pos ht0ball) (sq_pos_iff.mpr ht0ne)⟩

/-- The Gram matrix of the bump is positive definite, hence invertible. -/
theorem gramMatrix_posDef (n : ℕ) : (gramMatrix n).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · show (gramMatrix n)ᴴ = gramMatrix n
    have hstar : ∀ x : ℝ, star x = x := fun x => by simp
    ext i j
    simp only [Matrix.conjTranspose_apply, gramMatrix]
    rw [hstar]
    exact congrArg (fun k : ℕ => ∫ t in (0 : ℝ)..1, t ^ k * chi t) (add_comm j.val i.val)
  · intro x hx
    have hstarx : star x = x := by
      funext i
      simp
    rw [hstarx]
    have hEq : x ⬝ᵥ (gramMatrix n *ᵥ x)
        = ∫ t in (0 : ℝ)..1, chi t * (weightPoly x t) ^ 2 := by
      have hint : ∀ t : ℝ, ∑ i, x i * (chi t * t ^ i.val * weightPoly x t)
          = chi t * weightPoly x t * weightPoly x t := by
        intro t
        calc ∑ i, x i * (chi t * t ^ i.val * weightPoly x t)
            = (∑ i, x i * t ^ i.val) * (chi t * weightPoly x t) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
          _ = chi t * weightPoly x t * weightPoly x t := by
              simp only [weightPoly]; ring
      calc x ⬝ᵥ (gramMatrix n *ᵥ x) = ∑ i, x i * (gramMatrix n *ᵥ x) i := rfl
        _ = ∑ i, x i * ∫ t in (0 : ℝ)..1, chi t * t ^ i.val * weightPoly x t := by
              exact Finset.sum_congr rfl fun i _ => by rw [gramMatrix_mulVec x i]
        _ = ∑ i, ∫ t in (0 : ℝ)..1, x i * (chi t * t ^ i.val * weightPoly x t) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              exact (intervalIntegral.integral_const_mul (x i)
                (fun t => chi t * t ^ i.val * weightPoly x t)).symm
        _ = ∫ t in (0 : ℝ)..1, ∑ i, x i * (chi t * t ^ i.val * weightPoly x t) := by
              refine (intervalIntegral.integral_finsetSum fun i _ => ?_).symm
              exact ((contDiff_const (c := x i)).mul
                ((chi_contDiff.mul ((contDiff_id (𝕜 := ℝ) (n := ∞)).pow i.val)).mul
                  (contDiff_weightPoly x))).continuous.intervalIntegrable 0 1
        _ = ∫ t in (0 : ℝ)..1, chi t * weightPoly x t * weightPoly x t := by
              refine intervalIntegral.integral_congr (fun t _ => hint t)
        _ = ∫ t in (0 : ℝ)..1, chi t * (weightPoly x t) ^ 2 := by
              refine intervalIntegral.integral_congr (fun t _ => by ring)
    rw [hEq]
    exact integral_chi_weightPoly_sq_pos hx

/-! ## Moment linearity and the perturbed density -/

theorem intervalIntegrable_moments {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (k : ℕ) :
    IntervalIntegrable (fun t => t ^ k * ρ t) volume 0 1 :=
  (((contDiff_id (𝕜 := ℝ) (n := ∞)).pow k).mul hρ).continuous.intervalIntegrable 0 1

theorem densityMoments_add {n : ℕ} {ρ1 ρ2 : ℝ → ℝ} (h1 : ContDiff ℝ ∞ ρ1)
    (h2 : ContDiff ℝ ∞ ρ2) :
    densityMoments n (fun t => ρ1 t + ρ2 t) = densityMoments n ρ1 + densityMoments n ρ2 := by
  funext i
  show ∫ t in (0 : ℝ)..1, t ^ i.val * (ρ1 t + ρ2 t)
      = (∫ t in (0 : ℝ)..1, t ^ i.val * ρ1 t) + (∫ t in (0 : ℝ)..1, t ^ i.val * ρ2 t)
  have hsplit : ∫ t in (0 : ℝ)..1, t ^ i.val * (ρ1 t + ρ2 t)
      = ∫ t in (0 : ℝ)..1, t ^ i.val * ρ1 t + t ^ i.val * ρ2 t :=
    intervalIntegral.integral_congr (fun t _ => mul_add _ _ _)
  rw [hsplit]
  exact intervalIntegral.integral_add (intervalIntegrable_moments h1 i.val)
    (intervalIntegrable_moments h2 i.val)

theorem densityMoments_smul {n : ℕ} {a : ℝ} {ρ : ℝ → ℝ} :
    densityMoments n (fun t => ρ t * a) = a • densityMoments n ρ := by
  funext i
  have hrw : densityMoments n (fun t => ρ t * a) i = a * densityMoments n ρ i := by
    show ∫ t in (0 : ℝ)..1, t ^ i.val * (ρ t * a) = a * ∫ t in (0 : ℝ)..1, t ^ i.val * ρ t
    have hmv : ∫ t in (0 : ℝ)..1, t ^ i.val * (ρ t * a)
        = ∫ t in (0 : ℝ)..1, a * (t ^ i.val * ρ t) :=
      intervalIntegral.integral_congr (fun t _ => by ring)
    rw [hmv, intervalIntegral.integral_const_mul a (fun t => t ^ i.val * ρ t)]
  rw [hrw, Pi.smul_apply, smul_eq_mul]

/-- The perturbed density `ρ0 + χ * weightPoly c`. -/
def perturb {n : ℕ} (ρ0 : ℝ → ℝ) (c : Fin (n + 1) → ℝ) : ℝ → ℝ :=
  fun t => ρ0 t + chi t * weightPoly c t

/-- If `ρ0` is at least `m0 > 0` on `[0, 1]` and the total coefficient mass of `c` is at
most `m0 / 2`, the perturbed density `ρ0 + χ * weightPoly c` is again a good density:
smoothness is clear, positivity follows from `0 ≤ χ ≤ 1`, `|t| ≤ 1` and the smallness of
`c`, and the endpoint germs are preserved because `χ` vanishes near both endpoints. -/
theorem goodDensity_perturb {n : ℕ} {ρ0 : ℝ → ℝ} (hρ0 : GoodDensity ρ0) {m0 : ℝ}
    (hm0pos : 0 < m0) (hm0le : ∀ t ∈ Icc (0 : ℝ) 1, m0 ≤ ρ0 t) {c : Fin (n + 1) → ℝ}
    (hcsum : ∑ j, |c j| ≤ m0 / 2) : GoodDensity (perturb ρ0 c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hρ0.1.add (chi_contDiff.mul (contDiff_weightPoly c))
  · intro t ht
    show 0 < ρ0 t + chi t * weightPoly c t
    have h1 : |weightPoly c t| ≤ ∑ j, |c j| := by
      calc |weightPoly c t| = |∑ j, c j * t ^ j.val| := rfl
        _ ≤ ∑ j, |c j * t ^ j.val| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |c j| * |t ^ j.val| := Finset.sum_congr rfl fun j _ => abs_mul _ _
        _ ≤ ∑ j, |c j| * 1 := by
              have htab : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
              refine Finset.sum_le_sum fun j _ => ?_
              have h3 : |t ^ j.val| = |t| ^ j.val := abs_pow _ _
              have h4 : |t| ^ j.val ≤ 1 :=
                (pow_le_pow_left₀ (abs_nonneg t) htab _).trans_eq (one_pow _)
              rw [h3]
              exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
        _ = ∑ j, |c j| := by simp
    have habs : |chi t * weightPoly c t| ≤ m0 / 2 := by
      calc |chi t * weightPoly c t| = chi t * |weightPoly c t| := by
            rw [abs_mul, abs_of_nonneg (chi_nonneg t)]
        _ ≤ 1 * |weightPoly c t| :=
            mul_le_mul_of_nonneg_right (chi_le_one t) (abs_nonneg _)
        _ ≤ |weightPoly c t| := by simp
        _ ≤ ∑ j, |c j| := h1
        _ ≤ m0 / 2 := hcsum
    have hlow : -(m0 / 2) ≤ chi t * weightPoly c t := (abs_le.mp habs).1
    have h3 := hm0le t ht
    linarith
  · have h1 : perturb ρ0 c =ᶠ[𝓝 (0 : ℝ)] ρ0 := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)] with t ht
      show ρ0 t + chi t * weightPoly c t = ρ0 t
      rw [chi_eq_zero_of_lt ht]
      ring
    exact h1.trans hρ0.2.2.1
  · have h1 : perturb ρ0 c =ᶠ[𝓝 (1 : ℝ)] ρ0 := by
      filter_upwards [Ioi_mem_nhds (show (3 / 4 : ℝ) < 1 by norm_num)] with t ht
      show ρ0 t + chi t * weightPoly c t = ρ0 t
      rw [chi_eq_zero_of_gt ht]
      ring
    exact h1.trans hρ0.2.2.2

/-- The moments of the perturbed density are the moments of `ρ0` plus the Gram matrix
applied to the coefficient vector. -/
theorem densityMoments_perturb {n : ℕ} {ρ0 : ℝ → ℝ} (hρ0 : ContDiff ℝ ∞ ρ0)
    (c : Fin (n + 1) → ℝ) :
    densityMoments n (perturb ρ0 c) = densityMoments n ρ0 + gramMatrix n *ᵥ c := by
  funext i
  show ∫ t in (0 : ℝ)..1, t ^ i.val * (ρ0 t + chi t * weightPoly c t)
      = densityMoments n ρ0 i + (gramMatrix n *ᵥ c) i
  have hsplit : ∫ t in (0 : ℝ)..1, t ^ i.val * (ρ0 t + chi t * weightPoly c t)
      = ∫ t in (0 : ℝ)..1, t ^ i.val * ρ0 t + t ^ i.val * (chi t * weightPoly c t) :=
    intervalIntegral.integral_congr (fun t _ => mul_add _ _ _)
  have hint2 : IntervalIntegrable (fun t => t ^ i.val * (chi t * weightPoly c t))
      volume 0 1 :=
    (((contDiff_id (𝕜 := ℝ) (n := ∞)).pow i.val).mul
      (chi_contDiff.mul (contDiff_weightPoly c))).continuous.intervalIntegrable 0 1
  have hadd := intervalIntegral.integral_add (intervalIntegrable_moments hρ0 i.val) hint2
  have hswap : ∫ t in (0 : ℝ)..1, t ^ i.val * (chi t * weightPoly c t)
      = ∫ t in (0 : ℝ)..1, chi t * t ^ i.val * weightPoly c t :=
    intervalIntegral.integral_congr (fun t _ => by ring)
  calc densityMoments n (perturb ρ0 c) i
      = ∫ t in (0 : ℝ)..1, t ^ i.val * ρ0 t + t ^ i.val * (chi t * weightPoly c t) := hsplit
    _ = (∫ t in (0 : ℝ)..1, t ^ i.val * ρ0 t)
        + ∫ t in (0 : ℝ)..1, t ^ i.val * (chi t * weightPoly c t) := hadd
    _ = densityMoments n ρ0 i + ∫ t in (0 : ℝ)..1, chi t * t ^ i.val * weightPoly c t :=
          congrArg (fun X => densityMoments n ρ0 i + X) hswap
    _ = densityMoments n ρ0 i + (gramMatrix n *ᵥ c) i := by
          rw [gramMatrix_mulVec c i]

/-! ## Convexity of the smooth moment set -/

/-- **Convexity.** For every `n`, the set of moment vectors of good densities is convex:
positive convex combinations of good densities are good densities, the endpoint germs
hold on the intersection of the two endpoint neighborhoods, and the moment map is
linear on the relevant combinations. -/
theorem smoothMomentSet_convex (n : ℕ) : Convex ℝ (smoothMomentSet n) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [smoothMomentSet, Set.mem_ofPred_eq] at hx hy
  obtain ⟨ρ1, h1, rfl⟩ := hx
  obtain ⟨ρ2, h2, rfl⟩ := hy
  refine ⟨fun t => ρ1 t * a + ρ2 t * b, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h1.1.mul contDiff_const |>.add (h2.1.mul contDiff_const)
  · intro t ht
    exact add_pos (mul_pos (h1.2.1 t ht) ha) (mul_pos (h2.2.1 t ht) hb)
  · filter_upwards [h1.2.2.1, h2.2.2.1] with t e1 e2
    have e1' : ρ1 t = 1 := e1
    have e2' : ρ2 t = 1 := e2
    show ρ1 t * a + ρ2 t * b = 1
    rw [e1', e2']
    linarith
  · filter_upwards [h1.2.2.2, h2.2.2.2] with t e1 e2
    have e1' : ρ1 t = 1 := e1
    have e2' : ρ2 t = 1 := e2
    show ρ1 t * a + ρ2 t * b = 1
    rw [e1', e2']
    linarith
  · have key : densityMoments n (fun t => ρ1 t * a + ρ2 t * b)
        = a • densityMoments n ρ1 + b • densityMoments n ρ2 := by
      rw [densityMoments_add (h1.1.mul contDiff_const) (h2.1.mul contDiff_const),
        densityMoments_smul, densityMoments_smul]
    exact key

/-! ## Openness of the smooth moment set -/

/-- **Openness.** For every `n`, the set of moment vectors of good densities is open.

At any good density `ρ0` with positive minimum `m0` on `[0, 1]`, perturb by
`χ · ∑ c_i t^i` where `χ` is the fixed bump supported in `(1/4, 3/4)`. The moment map
on coefficient vectors is the Gram matrix of the bump, which is positive definite
(a nonzero polynomial cannot vanish on an interval), hence invertible; a full
sup-norm ball of perturbation vectors around the original moment vector is therefore
realized, and sufficiently small coefficients keep the density positive (using
`0 ≤ χ ≤ 1`, `|t| ≤ 1`) and equal to `ρ0` near both endpoints (using `χ = 0` there).
No residual assumptions remain. -/
theorem smoothMomentSet_isOpen (n : ℕ) : IsOpen (smoothMomentSet n) := by
  rw [isOpen_iff_forall_mem_open]
  intro y0 hy0
  simp only [smoothMomentSet, Set.mem_ofPred_eq] at hy0
  obtain ⟨ρ0, hρ0, hy0⟩ := hy0
  -- positive minimum of ρ0 on [0, 1]
  obtain ⟨m0, hm0pos, hm0le⟩ :=
    isCompact_Icc.exists_forall_le' hρ0.1.continuous.continuousOn
      (fun t ht => hρ0.2.1 t ht)
  -- the Gram matrix is invertible
  have hApos := gramMatrix_posDef n
  have hAdet : IsUnit (gramMatrix n).det :=
    (Matrix.isUnit_iff_isUnit_det (gramMatrix n)).mp (Matrix.PosDef.isUnit hApos)
  -- bound on the rows of the inverse
  set B : ℝ := 1 + ∑ i' : Fin (n + 1), ∑ j, |(gramMatrix n)⁻¹ i' j| with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    have h0 : 0 ≤ ∑ i' : Fin (n + 1), ∑ j, |(gramMatrix n)⁻¹ i' j| :=
      Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  set eps : ℝ := m0 / (2 * ((n + 1 : ℕ) : ℝ)) with hepsdef
  have hepspos : 0 < eps := by
    rw [hepsdef]
    have hcast : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    exact div_pos hm0pos (by linarith)
  set r : ℝ := eps / B with hrdef
  have hrpos : 0 < r := div_pos hepspos hBpos
  refine ⟨Metric.ball y0 r, ?_, Metric.isOpen_ball, Metric.mem_ball_self hrpos⟩
  intro y hy
  simp only [smoothMomentSet, Set.mem_ofPred_eq]
  -- extract pointwise bound from the sup-metric ball
  have hdist : ∀ j, |y j - y0 j| < r := by
    intro j
    have h1 := (dist_pi_lt_iff hrpos).mp hy j
    rwa [Real.dist_eq] at h1
  -- the coefficient vector realizing the perturbation
  set c := (gramMatrix n)⁻¹ *ᵥ (y - y0) with hcdef
  have hAmul : gramMatrix n *ᵥ c = y - y0 := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (gramMatrix n) hAdet,
      Matrix.one_mulVec]
  -- all coefficients of c are at most eps in absolute value
  have hcbound : ∀ i, |c i| ≤ eps := by
    intro i
    have h1 : |c i| ≤ ∑ j, |(gramMatrix n)⁻¹ i j| * |(y - y0) j| := by
      rw [hcdef]
      calc |((gramMatrix n)⁻¹ *ᵥ (y - y0)) i|
          = |∑ j, (gramMatrix n)⁻¹ i j * (y - y0) j| := rfl
        _ ≤ ∑ j, |(gramMatrix n)⁻¹ i j * (y - y0) j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |(gramMatrix n)⁻¹ i j| * |(y - y0) j| :=
              Finset.sum_congr rfl fun j _ => abs_mul _ _
    have h2 : ∑ j, |(gramMatrix n)⁻¹ i j| * |(y - y0) j|
        ≤ ∑ j, |(gramMatrix n)⁻¹ i j| * r := by
      refine Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_left (le_of_lt (hdist j)) (abs_nonneg _)
    have h3 : ∑ j, |(gramMatrix n)⁻¹ i j|
        ≤ ∑ i' : Fin (n + 1), ∑ j, |(gramMatrix n)⁻¹ i' j| := by
      have step1 : ∑ i' ∈ {i}, ∑ j, |(gramMatrix n)⁻¹ i' j|
          = ∑ j, |(gramMatrix n)⁻¹ i j| := Finset.sum_singleton _ _
      have step2 : ∑ i' ∈ {i}, ∑ j, |(gramMatrix n)⁻¹ i' j|
          ≤ ∑ i' : Fin (n + 1), ∑ j, |(gramMatrix n)⁻¹ i' j| :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun x _ => Finset.mem_univ x)
          (fun x _ _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      exact step1.symm.le.trans step2
    have hSB : ∑ i' : Fin (n + 1), ∑ j, |(gramMatrix n)⁻¹ i' j| ≤ B := by
      rw [hBdef]
      linarith
    calc |c i| ≤ ∑ j, |(gramMatrix n)⁻¹ i j| * |(y - y0) j| := h1
      _ ≤ ∑ j, |(gramMatrix n)⁻¹ i j| * r := h2
      _ = r * ∑ j, |(gramMatrix n)⁻¹ i j| := by
            rw [← Finset.sum_mul, mul_comm]
      _ ≤ r * (∑ i' : Fin (n + 1), ∑ j, |(gramMatrix n)⁻¹ i' j|) :=
            mul_le_mul_of_nonneg_left h3 hrpos.le
      _ ≤ r * B := mul_le_mul_of_nonneg_left hSB hrpos.le
      _ = eps := by
            rw [hrdef]
            exact div_mul_cancel₀ eps (ne_of_gt hBpos)
  -- the perturbed density is good and has the prescribed moments
  have hcsum : ∑ j, |c j| ≤ m0 / 2 := by
    calc ∑ j, |c j| ≤ ∑ j : Fin (n + 1), eps := Finset.sum_le_sum fun j _ => hcbound j
      _ = (n + 1 : ℕ) • eps := by
            exact (Finset.sum_const eps).trans (by rw [Finset.card_univ, Fintype.card_fin])
      _ = m0 / 2 := by
            have hnpos : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
            rw [nsmul_eq_mul, hepsdef]
            field_simp
  refine ⟨perturb ρ0 c, goodDensity_perturb hρ0 hm0pos hm0le hcsum, ?_⟩
  calc densityMoments n (perturb ρ0 c)
      = densityMoments n ρ0 + gramMatrix n *ᵥ c := densityMoments_perturb hρ0.1 c
    _ = densityMoments n ρ0 + (y - y0) := by rw [hAmul]
    _ = y := by rw [hy0]; ring

end

end RepeatedIntegrals
