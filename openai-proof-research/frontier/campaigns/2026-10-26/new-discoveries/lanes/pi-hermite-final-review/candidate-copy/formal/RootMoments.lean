import TailScalar

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

open Polynomial Filter
open scoped Topology

def realRoot (n : ℕ) (i : Fin (hermitePoly n).roots.toList.length) : ℝ :=
  (hermitePoly n).roots.toList.get i

theorem sum_realRoot (n : ℕ) (f : ℝ → ℝ) :
    ∑ i, f (realRoot n i) = ((hermitePoly n).roots.map f).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ (hermitePoly n).roots.toList.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]
  change (((hermitePoly n).roots.toList : Multiset ℝ).map f).sum = _
  rw [Multiset.coe_toList]

def rootMoment (n k : ℕ) (x : ℝ) : ℝ :=
  ∑ i, ((x - realRoot n i)⁻¹) ^ k

def hermiteRatio (n : ℕ) (x : ℝ) : ℝ :=
  (hermitePoly n).derivative.eval x / (hermitePoly n).eval x

theorem hermiteRatio_eq_rootMoment (n : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    hermiteRatio n x = rootMoment n 1 x := by
  rw [hermiteRatio, (hermitePoly_splits n).eval_derivative_div_eval_of_ne_zero hx]
  simp only [rootMoment, pow_one, one_div]
  exact (sum_realRoot n (fun r => (x - r)⁻¹)).symm

theorem realRoot_ne (n : ℕ) (x : ℝ) (hx : (hermitePoly n).eval x ≠ 0)
    (i : Fin (hermitePoly n).roots.toList.length) : x - realRoot n i ≠ 0 := by
  intro he
  have hm : realRoot n i ∈ (hermitePoly n).roots := by
    apply Multiset.mem_toList.mp
    exact List.get_mem _ _
  have hv := (Polynomial.mem_roots (hermitePoly_ne_zero n)).mp hm
  apply hx
  simpa [sub_eq_zero.mp he] using hv

theorem rootMoment_hasDerivAt (n k : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    HasDerivAt (rootMoment n k) (-(k : ℝ) * rootMoment n (k + 1) x) x := by
  have hd : ∀ i : Fin (hermitePoly n).roots.toList.length,
      HasDerivAt (fun t : ℝ => ((t - realRoot n i)⁻¹) ^ k)
        (-(k : ℝ) * ((x - realRoot n i)⁻¹) ^ (k + 1)) x := by
    intro i
    have h := (((hasDerivAt_id x).sub_const (realRoot n i)).inv (realRoot_ne n x hx i)).pow k
    convert h using 1
    · rfl
    · simp only [id_eq, Pi.inv_apply]
      cases k with
      | zero => simp
      | succ k => simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
                  rw [div_eq_mul_inv, ← inv_pow]
                  simp only [pow_succ]
                  ring
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hd i) using 1
  · rfl
  · simp only [rootMoment, Finset.mul_sum]

def ratioJet1 (n : ℕ) (x : ℝ) : ℝ :=
  2 * x * hermiteRatio n x - 2 * (n : ℝ) - hermiteRatio n x ^ 2

def ratioJet2 (n : ℕ) (x : ℝ) : ℝ :=
  2 * hermiteRatio n x + 2 * (x - hermiteRatio n x) * ratioJet1 n x

def ratioJet3 (n : ℕ) (x : ℝ) : ℝ :=
  4 * ratioJet1 n x - 2 * ratioJet1 n x ^ 2 +
    2 * (x - hermiteRatio n x) * ratioJet2 n x

theorem hermiteRatio_hasDerivAt (n : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    HasDerivAt (hermiteRatio n) (ratioJet1 n x) x := by
  have h := ((hermitePoly n).derivative.hasDerivAt x).div
    ((hermitePoly n).hasDerivAt x) hx
  have ho := congrArg (fun p : Polynomial ℝ => p.eval x) (hermitePoly_ode n)
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_zero] at ho
  have hdd : (hermitePoly n).derivative.derivative.eval x =
      2 * x * (hermitePoly n).derivative.eval x -
        2 * (n : ℝ) * (hermitePoly n).eval x := by linarith
  convert h using 1
  · rfl
  · unfold ratioJet1 hermiteRatio
    rw [hdd]
    field_simp

theorem ratioJet1_hasDerivAt (n : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    HasDerivAt (ratioJet1 n) (ratioJet2 n x) x := by
  have h := hermiteRatio_hasDerivAt n x hx
  convert ((((hasDerivAt_id x).const_mul 2).mul h).sub_const (2 * (n : ℝ))).sub
    (h.pow 2) using 1
  · rfl
  · simp only [ratioJet2, id_eq]
    ring

theorem ratioJet2_hasDerivAt (n : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    HasDerivAt (ratioJet2 n) (ratioJet3 n x) x := by
  have h := hermiteRatio_hasDerivAt n x hx
  have h1 := ratioJet1_hasDerivAt n x hx
  convert (h.const_mul 2).add ((((hasDerivAt_id x).sub h).const_mul 2).mul h1) using 1
  · rfl
  · simp only [ratioJet3, Pi.sub_apply, id_eq]
    ring

theorem hermite_nonzero_eventually (n : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    ∀ᶠ t in 𝓝 x, (hermitePoly n).eval t ≠ 0 :=
  ((hermitePoly n).continuousAt).eventually (eventually_ne_nhds hx)

theorem ratioJet1_eq_moment (n : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    ratioJet1 n x = -rootMoment n 2 x := by
  have he : hermiteRatio n =ᶠ[𝓝 x] rootMoment n 1 := by
    filter_upwards [hermite_nonzero_eventually n x hx] with t ht
    exact hermiteRatio_eq_rootMoment n t ht
  have hd := he.deriv_eq
  rw [(hermiteRatio_hasDerivAt n x hx).deriv,
    (rootMoment_hasDerivAt n 1 x hx).deriv] at hd
  simpa using hd

theorem ratioJet2_eq_moment (n : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    ratioJet2 n x = 2 * rootMoment n 3 x := by
  have he : ratioJet1 n =ᶠ[𝓝 x] fun t => -rootMoment n 2 t := by
    filter_upwards [hermite_nonzero_eventually n x hx] with t ht
    exact ratioJet1_eq_moment n t ht
  have hd := he.deriv_eq
  have hdneg : HasDerivAt (fun t => -rootMoment n 2 t)
      (-(-(2 : ℝ) * rootMoment n 3 x)) x := by
    convert (rootMoment_hasDerivAt n 2 x hx).neg using 1
  rw [(ratioJet1_hasDerivAt n x hx).deriv,
    hdneg.deriv] at hd
  convert hd using 1; ring

theorem ratioJet3_eq_moment (n : ℕ) (x : ℝ)
    (hx : (hermitePoly n).eval x ≠ 0) :
    ratioJet3 n x = -6 * rootMoment n 4 x := by
  have he : ratioJet2 n =ᶠ[𝓝 x] fun t => 2 * rootMoment n 3 t := by
    filter_upwards [hermite_nonzero_eventually n x hx] with t ht
    exact ratioJet2_eq_moment n t ht
  have hd := he.deriv_eq
  rw [(ratioJet2_hasDerivAt n x hx).deriv,
    ((rootMoment_hasDerivAt n 3 x hx).const_mul 2).deriv] at hd
  convert hd using 1; ring

theorem hermiteRatio_at_stationary (n : ℕ) (x : ℝ)
    (hp : (hermitePoly n).eval x ≠ 0) (hs : weightedSlope n x = 0) :
    hermiteRatio n x = x := by
  have h := (mul_eq_zero.mp hs).resolve_right (Real.exp_ne_zero _)
  simp only [eval_sub, eval_mul, eval_X] at h
  exact (div_eq_iff hp).mpr (by linarith)

theorem stationary_peak_inequality (n : ℕ) (x : ℝ)
    (hp : (hermitePoly n).eval x ≠ 0) (hs : weightedSlope n x = 0) :
    3 * (2 * (n : ℝ) + 1) ≤ peakPolynomial (2 * (n : ℝ) + 1 - x ^ 2) := by
  have hr := hermiteRatio_at_stationary n x hp hs
  have h1 := ratioJet1_eq_moment n x hp
  have h2 := ratioJet2_eq_moment n x hp
  have h3 := ratioJet3_eq_moment n x hp
  have hj1 : ratioJet1 n x = 1 - (2 * (n : ℝ) + 1 - x ^ 2) := by
    unfold ratioJet1
    rw [hr]
    ring
  have hj2 : ratioJet2 n x = 2 * x := by
    simp [ratioJet2, hr]
  have hj3 : ratioJet3 n x = 2 - 2 * (2 * (n : ℝ) + 1 - x ^ 2) ^ 2 := by
    rw [ratioJet3, hr, hj1]
    ring
  apply moment_peak_inequality
    (fun i : Fin (hermitePoly n).roots.toList.length => (x - realRoot n i)⁻¹)
    (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 1 - x ^ 2) x
  · change rootMoment n 2 x = _
    linarith
  · change rootMoment n 3 x = _
    linarith
  · change rootMoment n 4 x = _
    nlinarith
  · ring

theorem no_stationary_peak_beyond_square_cutoff (n : ℕ) (x : ℝ) (hn : 3 ≤ n)
    (hx : 2 * (n : ℝ) + 1 - Real.pi + Real.pi ^ 2 / (4 * (2 * (n : ℝ) + 1)) ≤ x ^ 2)
    (hy : weightedHermite n x ≠ 0) (hs : weightedSlope n x = 0) : False := by
  have hp : (hermitePoly n).eval x ≠ 0 := by
    intro he
    apply hy
    simp [weightedHermite, hermiteValue, he]
  exact peak_obstruction _ x (by exact_mod_cast (show 7 ≤ 2 * n + 1 by omega)) hx
    (stationary_peak_inequality n x hp hs)

end HermiteEnvelope
