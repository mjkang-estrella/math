import Mathlib

open Set Real Filter
open scoped Topology

namespace FractionalBinomial

lemma sum_range_blocks (f : ℕ → ℝ) (N d : ℕ) :
    (∑ m∈Finset.range (N*d), f (m+1)) =
      ∑ i∈Finset.range N, ∑ r∈Finset.range d, f (i*d+r+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

lemma sum_Icc_one (f : ℕ → ℝ) (n : ℕ) :
    (∑ r∈Finset.Icc 1 n, f r) = ∑ r∈Finset.range n, f (r+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

noncomputable def gammaApprox (d N : ℕ) (x : ℝ) : ℝ :=
  (d:ℝ)*x*Real.log (N*d)+Real.log (Nat.factorial (N*d))-(N*d)*Real.log d-
    ∑ i∈Finset.range N, ∑ r∈Finset.range d, Real.log (x+i+((r:ℝ)+1)/(d:ℝ))

lemma gammaApprox_eq (d N : ℕ) (hd : 0<d) {x : ℝ} (hx : 0<x) :
    gammaApprox d N x = Real.BohrMollerup.logGammaSeq ((d:ℝ)*x) (N*d)+
      Real.log ((d:ℝ)*x) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hfactor (i r : ℕ) :
      Real.log ((d:ℝ)*x+(i*d+r+1:ℕ)) = Real.log d+Real.log (x+i+((r:ℝ)+1)/(d:ℝ)) := by
    have hp : 0<x+(i:ℝ)+((r:ℝ)+1)/(d:ℝ) := by positivity
    have hid : (d:ℝ)*x+(i*d+r+1:ℕ) = (d:ℝ)*(x+i+((r:ℝ)+1)/(d:ℝ)) := by
      push_cast
      field_simp
      ring
    rw [hid, Real.log_mul hdR.ne' hp.ne']
  have hsum : (∑ m∈Finset.range (N*d), Real.log ((d:ℝ)*x+(m+1:ℕ))) =
      (N*d:ℕ)*Real.log d+∑ i∈Finset.range N, ∑ r∈Finset.range d,
        Real.log (x+i+((r:ℝ)+1)/(d:ℝ)) := by
    rw [sum_range_blocks (fun m => Real.log ((d:ℝ)*x+(m:ℝ))) N d]
    simp_rw [hfactor]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  unfold gammaApprox Real.BohrMollerup.logGammaSeq
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, add_zero]
  rw [hsum]
  push_cast
  ring

lemma gammaApprox_tendsto (d : ℕ) (hd : 0<d) {x : ℝ} (hx : 0<x) :
    Tendsto (fun N => gammaApprox d N x) atTop (𝓝 (Real.log (Real.Gamma ((d:ℝ)*x+1)))) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hxR : 0<(d:ℝ)*x := mul_pos hdR hx
  have hN : Tendsto (fun N : ℕ => N*d) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_right N hd) tendsto_id
  have h := (Real.BohrMollerup.tendsto_log_gamma hxR).comp hN
  have h' := h.add_const (Real.log ((d:ℝ)*x))
  have heq : Real.log (Real.Gamma ((d:ℝ)*x))+Real.log ((d:ℝ)*x) =
      Real.log (Real.Gamma ((d:ℝ)*x+1)) := by
    rw [Real.Gamma_add_one hxR.ne', Real.log_mul hxR.ne' (Real.Gamma_pos_of_pos hxR).ne']
    ring
  rw [heq] at h'
  exact h'.congr' (Filter.Eventually.of_forall (fun N => (gammaApprox_eq d N hd hx).symm))

noncomputable def gammaApproxD (d N : ℕ) (x : ℝ) : ℝ :=
  (d:ℝ)*Real.log (N*d)-
    ∑ i∈Finset.range N, ∑ r∈Finset.range d, (x+i+((r:ℝ)+1)/(d:ℝ))⁻¹

noncomputable def gammaApproxDD (d N : ℕ) (x : ℝ) : ℝ :=
  ∑ i∈Finset.range N, ∑ r∈Finset.range d, 1/(x+i+((r:ℝ)+1)/(d:ℝ))^2

lemma gammaApprox_hasDeriv (d N : ℕ) (hd : 0<d) {x : ℝ} (hx : 0<x) :
    HasDerivAt (gammaApprox d N) (gammaApproxD d N x) x := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hterm (i r : ℕ) : HasDerivAt (fun t : ℝ => Real.log (t+i+((r:ℝ)+1)/(d:ℝ)))
      ((x+i+((r:ℝ)+1)/(d:ℝ))⁻¹) x := by
    have hp : 0<x+(i:ℝ)+((r:ℝ)+1)/(d:ℝ) := by positivity
    simpa using (((hasDerivAt_id x).add_const (i:ℝ)).add_const (((r:ℝ)+1)/(d:ℝ))).log hp.ne'
  have hsum := HasDerivAt.sum (fun i (_ : i∈Finset.range N) =>
    HasDerivAt.sum (fun r (_ : r∈Finset.range d) => hterm i r))
  have hlin := (((hasDerivAt_id x).const_mul (d:ℝ)).mul_const (Real.log (N*d))).add_const
    (Real.log (Nat.factorial (N*d))-(N*d)*Real.log d)
  convert hlin.sub hsum using 1
  · ext t
    simp only [gammaApprox, Pi.sub_apply, Finset.sum_apply, id_eq]
    ring
  · dsimp [gammaApproxD]
    ring

lemma gammaApproxD_hasDeriv (d N : ℕ) (hd : 0<d) {x : ℝ} (hx : 0<x) :
    HasDerivAt (gammaApproxD d N) (gammaApproxDD d N x) x := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hterm (i r : ℕ) : HasDerivAt (fun t : ℝ => (t+i+((r:ℝ)+1)/(d:ℝ))⁻¹)
      (-(1/(x+i+((r:ℝ)+1)/(d:ℝ))^2)) x := by
    have hp : 0<x+(i:ℝ)+((r:ℝ)+1)/(d:ℝ) := by positivity
    convert! (((hasDerivAt_id x).add_const (i:ℝ)).add_const (((r:ℝ)+1)/(d:ℝ))).inv hp.ne' using 1
    simp only [neg_div, id_eq]
  have hsum := HasDerivAt.sum (fun i (_ : i∈Finset.range N) =>
    HasDerivAt.sum (fun r (_ : r∈Finset.range d) => hterm i r))
  have hlin := hasDerivAt_const x ((d:ℝ)*Real.log (N*d))
  convert hlin.sub hsum using 1
  · ext t
    simp only [gammaApproxD, Pi.sub_apply, Finset.sum_apply]
  · simp only [gammaApproxDD, Finset.sum_neg_distrib, zero_sub, neg_neg]

/-- The finite-grid statement is supplied by a separate combinatorial certificate. -/
def GridMajorizes : Prop := ∀ (j l : ℕ), 0<j → 0<l → ∀ φ : ℝ → ℝ,
  AntitoneOn φ (Icc 0 1) →
  (∑ r∈Finset.Icc 1 j, φ ((r:ℝ)/j))+(∑ r∈Finset.Icc 1 l, φ ((r:ℝ)/l)) ≤
    ∑ r∈Finset.Icc 1 (j+l), φ ((r:ℝ)/(j+l))

lemma gammaApproxDD_superadd (hgrid : GridMajorizes) (j l N : ℕ)
    (hj : 0<j) (hl : 0<l) {x : ℝ} (hx : 0<x) :
    gammaApproxDD j N x+gammaApproxDD l N x ≤ gammaApproxDD (j+l) N x := by
  unfold gammaApproxDD
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hφ : AntitoneOn (fun t : ℝ => 1/(x+i+t)^2) (Icc 0 1) := by
    intro a ha b _ hab
    have hapos : 0<x+(i:ℝ)+a := by have := ha.1; positivity
    apply one_div_le_one_div_of_le (pow_pos hapos 2)
    nlinarith
  have h := hgrid j l hj hl (fun t : ℝ => 1/(x+i+t)^2) hφ
  simp only [sum_Icc_one, Nat.cast_add, Nat.cast_one] at h
  simpa only [Nat.cast_add] using h

lemma ratioApprox_convex (hgrid : GridMajorizes) (j l N : ℕ) (hj : 0<j) (hl : 0<l) :
    ConvexOn ℝ (Ioi 0) (fun x => gammaApprox (j+l) N x-gammaApprox j N x-gammaApprox l N x) := by
  have hk : 0<j+l := by omega
  have hd1 (x : ℝ) (hx : 0<x) :=
    ((gammaApprox_hasDeriv (j+l) N hk hx).sub (gammaApprox_hasDeriv j N hj hx)).sub
      (gammaApprox_hasDeriv l N hl hx)
  have hd2 (x : ℝ) (hx : 0<x) :=
    ((gammaApproxD_hasDeriv (j+l) N hk hx).sub (gammaApproxD_hasDeriv j N hj hx)).sub
      (gammaApproxD_hasDeriv l N hl hx)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (fun x hx => (hd1 x hx).continuousAt.continuousWithinAt)
    (f' := fun x => gammaApproxD (j+l) N x-gammaApproxD j N x-gammaApproxD l N x)
    (f'' := fun x => gammaApproxDD (j+l) N x-gammaApproxDD j N x-gammaApproxDD l N x)
  · intro x hx
    exact (hd1 x (by simpa using hx)).hasDerivWithinAt
  · intro x hx
    exact (hd2 x (by simpa using hx)).hasDerivWithinAt
  · intro x hx
    have h := gammaApproxDD_superadd hgrid j l N hj hl (by simpa using hx)
    linarith

/-- The classical scaled gamma-ratio log-convexity, reduced to finite grids. -/
theorem scaledGammaLog_convex_of_grid (hgrid : GridMajorizes) (j l : ℕ)
    (hj : 0<j) (hl : 0<l) :
    ConvexOn ℝ (Ioi 0) (fun x => Real.log (Real.Gamma ((j+l:ℕ)*x+1))-
      Real.log (Real.Gamma ((j:ℝ)*x+1))-Real.log (Real.Gamma ((l:ℝ)*x+1))) := by
  have hk : 0<j+l := by omega
  have hlim (x : ℝ) (hx : 0<x) :=
    ((gammaApprox_tendsto (j+l) hk hx).sub (gammaApprox_tendsto j hj hx)).sub
      (gammaApprox_tendsto l hl hx)
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : 0<a*x+b*y := (convex_Ioi 0) hx hy ha hb hab
  have hleft := hlim (a*x+b*y) hz
  have hright := ((hlim x hx).const_mul a).add ((hlim y hy).const_mul b)
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall (fun N => by
    simpa only [smul_eq_mul] using (ratioApprox_convex hgrid j l N hj hl).2 hx hy ha hb hab)

theorem scaledGammaLog_convex_nonneg_of_grid (hgrid : GridMajorizes) (j l : ℕ) :
    ConvexOn ℝ (Ioi 0) (fun x => Real.log (Real.Gamma ((j+l:ℕ)*x+1))-
      Real.log (Real.Gamma ((j:ℝ)*x+1))-Real.log (Real.Gamma ((l:ℝ)*x+1))) := by
  by_cases hj : j=0
  · subst j
    simpa using (convexOn_const (0:ℝ) (convex_Ioi (0:ℝ)))
  by_cases hl : l=0
  · subst l
    simpa using (convexOn_const (0:ℝ) (convex_Ioi (0:ℝ)))
  exact scaledGammaLog_convex_of_grid hgrid j l (Nat.pos_of_ne_zero hj) (Nat.pos_of_ne_zero hl)

end FractionalBinomial
