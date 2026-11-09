module
public import BesselInterfaces
public section
noncomputable section
open scoped Topology
open Filter
namespace BesselRatio

theorem scaled_euler {ν a x : ℝ} (hν : -1 < ν) (ha : 0 < a) (hx : 0 < x) :
    x * deriv (scaled ν a) x = (a*x/2)^ν * euler ν ((a*x)^2) := by
  have hz : 0 < a*x/2 := by positivity
  have hd := (I_hasDerivAt hν (mul_pos ha hx)).comp x ((hasDerivAt_id x).const_mul a)
  have hr : (a*x/2)^(ν-1) * (a*x/2) = (a*x/2)^ν := by
    rw [← Real.rpow_add_one hz.ne']; congr 1; ring
  rw [show deriv (scaled ν a) x = _ from hd.deriv]
  dsimp [euler]
  calc
    _ = (ν * S ν ((a*x)^2)) * ((a*x/2)^(ν-1) * (a*x/2)) +
      (a*x/2)^ν * (2 * (a*x)^2 * deriv (S ν) ((a*x)^2)) := by ring
    _ = _ := by rw [hr]; ring

theorem wFactorization : WFactorization := by
  intro u v a b x hu hv ha hb hx
  have hf := scaled_euler hu ha hx
  have hg := scaled_euler hv hb hx
  have hfa : (a*x/2)^u = (a/2)^u * x^u := by
    rw [show a*x/2 = (a/2)*x by ring, Real.mul_rpow (by positivity) hx.le]
  have hgb : (b*x/2)^v = (b/2)^v * x^v := by
    rw [show b*x/2 = (b/2)*x by ring, Real.mul_rpow (by positivity) hx.le]
  unfold W wCoefficient
  rw [mul_sub, ← mul_assoc, hf]
  rw [show x * (scaled u a x * deriv (scaled v b) x) =
    scaled u a x * (x * deriv (scaled v b) x) by ring, hg]
  simp only [scaled, I_eq_rpow_mul_S (mul_pos ha hx), I_eq_rpow_mul_S (mul_pos hb hx)]
  rw [hfa, hgb, Real.rpow_add hx]
  ring

theorem unequalEndpoint : UnequalEndpoint := by
  intro u v a b hv huv ha hb
  have hu : -1 < u := lt_trans hv huv
  have hG : Real.Gamma (u+1) * Real.Gamma (v+1) ≠ 0 :=
    (mul_pos (Real.Gamma_pos_of_pos (by linarith))
      (Real.Gamma_pos_of_pos (by linarith))).ne'
  have hlim := ((wCoefficient_limit hu hv a b).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).mul_const
    (Real.Gamma (u+1) * Real.Gamma (v+1))
  have heq : (fun x => W u v a b x / (C u v a b * x^(u+v))) =ᶠ[𝓝[>] 0]
      (fun x => wCoefficient u v a b x * (Real.Gamma (u+1) * Real.Gamma (v+1))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [wFactorization u v a b x hu hv ha hb hx]
    unfold C
    have hA := (Real.rpow_pos_of_pos (by positivity : 0 < a/2) u).ne'
    have hB := (Real.rpow_pos_of_pos (by positivity : 0 < b/2) v).ne'
    have hX := (Real.rpow_pos_of_pos hx (u+v)).ne'
    field_simp
  apply Tendsto.congr' heq.symm
  simpa only [div_mul_cancel₀ _ hG] using hlim

theorem W_eventually_pos {u v a b : ℝ} (hv : -1 < v) (huv : v < u)
    (ha : 0 < a) (hb : 0 < b) : ∀ᶠ x in 𝓝[>] 0, 0 < W u v a b x := by
  have hu : -1 < u := lt_trans hv huv
  have hl := (unequalEndpoint u v a b hv huv ha hb).eventually (eventually_gt_nhds (sub_pos.mpr huv))
  filter_upwards [hl, self_mem_nhdsWithin] with x hx hx0
  exact (div_pos_iff.mp hx).elim (fun h => h.1) (fun h =>
    False.elim ((not_lt_of_ge (le_of_lt (mul_pos (C_pos hu hv ha hb)
      (Real.rpow_pos_of_pos hx0 _)))) h.2))

theorem wCoefficient_equal (v a b x : ℝ) :
    wCoefficient v v a b x = 2*x^2 *
      (a^2 * deriv (S v) ((a*x)^2) * S v ((b*x)^2) -
       b^2 * S v ((a*x)^2) * deriv (S v) ((b*x)^2)) := by
  unfold wCoefficient euler
  ring

theorem equalEndpoint : EqualEndpoint := by
  intro v a b hv ha hb
  let bracket := fun x : ℝ => a^2 * deriv (S v) ((a*x)^2) * S v ((b*x)^2) -
       b^2 * S v ((a*x)^2) * deriv (S v) ((b*x)^2)
  have ca : ContinuousAt (fun x : ℝ => (a*x)^2) 0 := (continuousAt_id.const_mul a).pow 2
  have cb : ContinuousAt (fun x : ℝ => (b*x)^2) 0 := (continuousAt_id.const_mul b).pow 2
  have hsa : ContinuousAt (fun x : ℝ => S v ((a*x)^2)) 0 := by
    have h : ContinuousAt (S v) ((a*0)^2) := by simpa using (S_analytic hv 0).continuousAt
    exact h.comp (f := fun x : ℝ => (a*x)^2) ca
  have hsb : ContinuousAt (fun x : ℝ => S v ((b*x)^2)) 0 := by
    have h : ContinuousAt (S v) ((b*0)^2) := by simpa using (S_analytic hv 0).continuousAt
    exact h.comp (f := fun x : ℝ => (b*x)^2) cb
  have hda : ContinuousAt (fun x : ℝ => deriv (S v) ((a*x)^2)) 0 := by
    have h : ContinuousAt (deriv (S v)) ((a*0)^2) := by simpa using (S_analytic hv 0).deriv.continuousAt
    exact h.comp (f := fun x : ℝ => (a*x)^2) ca
  have hdb : ContinuousAt (fun x : ℝ => deriv (S v) ((b*x)^2)) 0 := by
    have h : ContinuousAt (deriv (S v)) ((b*0)^2) := by simpa using (S_analytic hv 0).deriv.continuousAt
    exact h.comp (f := fun x : ℝ => (b*x)^2) cb
  have hc : ContinuousAt bracket 0 := ((hda.const_mul _).mul hsb).sub ((hsa.const_mul _).mul hdb)
  have hp : Tendsto (fun x : ℝ => x^(2*v+2)) (𝓝[>] 0) (𝓝 0) := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero (by linarith)
  have hl := (hp.mul (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ))))).const_mul
    (2 * (a/2)^v * (b/2)^v)
  have he : W v v a b =ᶠ[𝓝[>] 0] (fun x => (2 * (a/2)^v * (b/2)^v) * (x^(2*v+2) * bracket x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [wFactorization v v a b x hv hv ha hb hx, wCoefficient_equal]
    rw [Real.rpow_add hx (2*v) 2, Real.rpow_two]
    dsimp [bracket]
    rw [show v+v = 2*v by ring]
    ring
  apply Tendsto.congr' he.symm
  simpa using hl
end BesselRatio
