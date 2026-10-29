module
public import BesselAnalytic
public section
noncomputable section
open scoped Topology
open Filter
namespace BesselRatio
@[expose] def scaled (ν a : ℝ) (x : ℝ) : ℝ := I ν (a*x)
@[expose] def W (u v a b x : ℝ) : ℝ :=
  x * (deriv (scaled u a) x * scaled v b x - scaled u a x * deriv (scaled v b) x)
@[expose] def C (u v a b : ℝ) : ℝ :=
  (a/2)^u * (b/2)^v / (Real.Gamma (u+1) * Real.Gamma (v+1))

/-- UNPROVED obligation, a closed proposition about the literal Gamma series. -/
@[expose] def ScaledODE : Prop :=
  ∀ (ν a x : ℝ), -1 < ν → 0 < a → 0 < x →
    HasDerivAt (fun y => y * deriv (scaled ν a) y)
      ((a^2*x + ν^2/x) * scaled ν a x) x

/-- UNPROVED obligation; no arbitrary solution is substituted for I. -/
@[expose] def WDerivative : Prop :=
  ∀ (u v a b x : ℝ), -1 < u → -1 < v → 0 < a → 0 < b → 0 < x →
    HasDerivAt (W u v a b)
      (((u^2-v^2)/x - (b^2-a^2)*x) * scaled u a x * scaled v b x) x

/-- UNPROVED literal unequal-order endpoint, including negative order sums. -/
@[expose] def UnequalEndpoint : Prop :=
  ∀ (u v a b : ℝ), -1 < v → v < u → 0 < a → 0 < b →
    Tendsto (fun x => W u v a b x / (C u v a b * x^(u+v)))
      (𝓝[>] 0) (𝓝 (u-v))

/-- UNPROVED literal equal-order endpoint. -/
@[expose] def EqualEndpoint : Prop :=
  ∀ (v a b : ℝ), -1 < v → 0 < a → 0 < b →
    Tendsto (W v v a b) (𝓝[>] 0) (𝓝 0)

/-- UNPROVED bridge from the normalized Euler coefficient to literal W. -/
@[expose] def WFactorization : Prop :=
  ∀ (u v a b x : ℝ), -1 < u → -1 < v → 0 < a → 0 < b → 0 < x →
    W u v a b x = (a/2)^u * (b/2)^v * x^(u+v) * wCoefficient u v a b x

theorem scaled_hasDerivAt {ν a x : ℝ} (hν : -1 < ν) (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (scaled ν a) (deriv (scaled ν a) x) x := by
  apply DifferentiableAt.hasDerivAt
  exact (I_hasDerivAt hν (mul_pos ha hx)).differentiableAt.comp x
    ((hasDerivAt_id x).const_mul a).differentiableAt

theorem C_pos {u v a b : ℝ} (hu : -1 < u) (hv : -1 < v)
    (ha : 0 < a) (hb : 0 < b) : 0 < C u v a b := by
  unfold C
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _))
    (mul_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by linarith)))

/-- Literal quotient derivative, already closed without assuming an ODE. -/
theorem ratio_hasDerivAt {u v a b x : ℝ} (hu : -1 < u) (hv : -1 < v)
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    HasDerivAt (fun y => scaled u a y / scaled v b y)
      (W u v a b x / (x * (scaled v b x)^2)) x := by
  have hg : scaled v b x ≠ 0 := (I_pos hv (mul_pos hb hx)).ne'
  have hd := (scaled_hasDerivAt hu ha hx).div (scaled_hasDerivAt hv hb hx) hg
  convert hd using 1
  unfold W
  field_simp

end BesselRatio
