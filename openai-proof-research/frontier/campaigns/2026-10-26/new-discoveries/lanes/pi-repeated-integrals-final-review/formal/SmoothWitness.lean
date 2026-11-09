import Primitives
import MomentTransform

open Set Filter
open scoped ContDiff Topology

namespace RepeatedIntegrals

noncomputable section

theorem smooth_within_eq {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin k f (Icc (0 : ℝ) 1) x = iteratedDeriv k f x := by
  exact iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
    (hf.of_le (by simp)).contDiffAt hx

theorem smooth_zero_jet_integral {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j k : ℕ)
    (h0 : ∀ i ≤ j + k, iteratedDeriv i f 0 = 0) :
    iteratedDeriv j f 1 = ∫ t in (0 : ℝ)..1,
      ((1 - t) ^ k / k.factorial) * iteratedDeriv (j + k + 1) f t := by
  have hi := source_jet_integral (f := f) j k
    (hf.of_le (by simp)).contDiffOn
    (fun i hi => (smooth_within_eq hf i (by norm_num)).trans (h0 i hi))
  rw [smooth_within_eq hf j (by norm_num)] at hi
  rw [hi]
  apply intervalIntegral.integral_congr
  intro t ht
  change ((1 - t) ^ k / k.factorial) *
    iteratedDerivWithin (j + k + 1) f (Icc (0 : ℝ) 1) t = _
  rw [smooth_within_eq hf (j + k + 1) (by simpa using ht)]

theorem repeatedPrimitive_terminal (n : ℕ) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (j : Fin (n + 1)) :
    iteratedDeriv j.val (repeatedPrimitive (n + 1) ρ) 1 =
      endpointMomentTransform n (densityMoments n ρ) j := by
  have hi := smooth_zero_jet_integral (repeatedPrimitive_smooth (n + 1) hρ)
    j.val (n - j.val)
    (fun i hi => repeatedPrimitive_initial n i (by omega) hρ)
  have htop : iteratedDeriv (n + 1) (repeatedPrimitive (n + 1) ρ) = ρ := by
    simpa only [Nat.add_zero, repeatedPrimitive] using
      repeatedPrimitive_iterated (n + 1) 0 hρ
  rw [show j.val + (n - j.val) + 1 = n + 1 by omega, htop] at hi
  rw [hi, endpointMomentTransform_density n hρ.continuous j,
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t _
  change ((1 - t) ^ (n - j.val) / ((n - j.val).factorial : ℝ)) * ρ t = _
  ring

theorem repeatedPrimitive_goodWitness (n : ℕ) {ρ : ℝ → ℝ} (hρ : GoodDensity ρ) :
    GoodWitness n (endpointMomentTransform n (densityMoments n ρ))
      (repeatedPrimitive (n + 1) ρ) := by
  have htop : iteratedDeriv (n + 1) (repeatedPrimitive (n + 1) ρ) = ρ := by
    simpa only [Nat.add_zero, repeatedPrimitive] using
      repeatedPrimitive_iterated (n + 1) 0 hρ.1
  refine ⟨repeatedPrimitive_smooth _ hρ.1,
    fun j hj => repeatedPrimitive_initial n j hj hρ.1,
    repeatedPrimitive_terminal n hρ.1, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [htop]
    exact hρ.2.1 t ⟨ht.1.le, ht.2.le⟩
  · rw [htop]
    exact hρ.2.2.1.eq_of_nhds
  · rw [htop]
    exact hρ.2.2.2.eq_of_nhds
  · exact fun j hj => repeatedPrimitive_higher_endpoint n j hj hρ

theorem goodWitness_mem_sourceW {n : ℕ} {b : MomentSpace n} {f : ℝ → ℝ}
    (hf : GoodWitness n b f) : b ∈ SourceW n := by
  have hmono : StrictMonoOn (iteratedDeriv n f) (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hf.1.continuous_iteratedDeriv n (by simp)).continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [← iteratedDeriv_succ]
    exact hf.2.2.2.1 x hx
  have heq : Set.EqOn (iteratedDerivWithin n f (Icc (0 : ℝ) 1))
      (iteratedDeriv n f) (Icc (0 : ℝ) 1) := fun _ hx => smooth_within_eq hf.1 n hx
  refine ⟨f, (hf.1.of_le (by simp)).contDiffOn, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [heq hx, heq hy]
    exact hmono.monotoneOn hx hy hxy
  · rintro ⟨c, hc⟩
    have hlt := hmono (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
      (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num)
    rw [← heq (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1),
      ← heq (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1),
      hc 0 (by norm_num), hc 1 (by norm_num)] at hlt
    exact (lt_irrefl _ hlt)
  · intro j hj
    rw [smooth_within_eq hf.1 j (by norm_num)]
    exact hf.2.1 j hj
  · intro j
    rw [smooth_within_eq hf.1 j.val (by norm_num)]
    exact hf.2.2.1 j

theorem smoothMomentImage_subset_sourceW (n : ℕ) :
    endpointMomentTransform n '' smoothMomentSet n ⊆ SourceW n := by
  rintro b ⟨y, ⟨ρ, hρ, hy⟩, rfl⟩
  rw [← hy]
  exact goodWitness_mem_sourceW (repeatedPrimitive_goodWitness n hρ)

end

end RepeatedIntegrals
