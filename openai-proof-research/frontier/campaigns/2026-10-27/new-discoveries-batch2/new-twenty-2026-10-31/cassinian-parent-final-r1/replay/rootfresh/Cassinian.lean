import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Star
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
open Set Complex
namespace Cassinian331705
noncomputable section
def slit : Set ℂ := {z | z.im = 0 ∧ 1 ≤ z.re}
def G : Set ℂ := slitᶜ
def y : ℂ := ⟨4,1⟩
def z : ℂ := ⟨2,1/2⟩
def cassinian (U : Set ℂ) (a b : ℂ) : ℝ :=
  sSup ((fun p : ℂ => ‖a-b‖ / (‖a-p‖ * ‖b-p‖)) '' frontier U)
def ball (U : Set ℂ) (a : ℂ) (r : ℝ) : Set ℂ := {b ∈ U | cassinian U a b < r}
lemma slit_closed : IsClosed slit :=
  (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_const continuous_re)
lemma G_open : IsOpen G := slit_closed.isOpen_compl
lemma zero_mem : (0:ℂ) ∈ G := by norm_num [G,slit]
lemma star : StarConvex ℝ (0:ℂ) G := by
  intro w hw a b ha hb hab
  simp only [G, mem_compl_iff, slit, mem_ofPred_eq] at *
  simp only [smul_zero, zero_add, Complex.smul_im, Complex.smul_re, smul_eq_mul]
  intro h
  by_cases h0 : b = 0
  · norm_num [h0] at h
  have hi : w.im = 0 := (mul_eq_zero.mp h.1).resolve_left h0
  have ble : b ≤ 1 := by linarith
  have hr0 : 0 ≤ w.re := by nlinarith [h.2]
  have hr : 1 ≤ w.re := by nlinarith [h.2, mul_nonneg (sub_nonneg.mpr ble) hr0]
  exact hw ⟨hi,hr⟩
lemma dense_G : Dense G := by
  intro w
  by_cases hw : w ∈ G
  · exact subset_closure hw
  apply Metric.mem_closure_iff.mpr
  intro e he
  have hm : w ∈ slit := by simpa [G] using hw
  have him : w.im = 0 := hm.1
  refine ⟨w + (e/2:ℝ) * I, ?_, ?_⟩
  · simp [G,slit,him,ne_of_gt (half_pos he)]
  · rw [dist_eq_norm]
    have : w - (w + (e/2:ℝ) * I) = -((e/2:ℝ) * I) := by ring
    rw [this, norm_neg, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos he)]
    linarith
lemma frontier_G : frontier G = slit := by
  rw [G_open.frontier_eq, dense_G.closure_eq, G]
  simp
lemma G_connected : IsConnected G := (star.isPathConnected zero_mem).isConnected
lemma polynomial_bound (s : ℝ) (hs : 1 ≤ s) : 68/9 < s^2*((s-4)^2+1) := by
  have hss : 1 ≤ s^2 := by nlinarith
  by_cases h1 : s ≤ 5/4
  · have h : 121/16 ≤ (s-4)^2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hss) (sq_nonneg (s-4))]
  by_cases h2 : s ≤ 2
  · have h : 4 ≤ (s-4)^2 := by nlinarith
    have hq : 25/16 ≤ s^2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr h)]
  by_cases h3 : s ≤ 3
  · have h : 1 ≤ (s-4)^2 := by nlinarith
    have hq : 4 ≤ s^2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr h)]
  · have hq : 9 ≤ s^2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg (s-4))]
lemma norm_sq (w : ℂ) : ‖w‖^2 = w.re^2 + w.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply];ring
lemma ratio_bound_y (p : ℂ) (hp : p ∈ frontier G) :
    ‖(0:ℂ)-y‖ / (‖(0:ℂ)-p‖ * ‖y-p‖) ≤ 3/2 := by
  rw [frontier_G] at hp
  have hpi : p.im = 0 := hp.1
  have hpr : 1 ≤ p.re := hp.2
  have h1 := norm_sq p
  have h2 := norm_sq (y-p)
  have hy := norm_sq y
  simp only [sub_re,sub_im,show y.re = 4 from rfl,show y.im = 1 from rfl,hpi,sub_zero] at h2
  change ‖y‖^2 = 4^2+1^2 at hy
  rw [hpi] at h1
  have hn : 0 ≤ ‖p‖ := norm_nonneg _
  have hm : 0 ≤ ‖y-p‖ := norm_nonneg _
  have hp1 : 0 < ‖p‖ := by nlinarith
  have hp2 : 0 < ‖y-p‖ := by nlinarith [sq_nonneg (4-p.re)]
  have hd : 0 < ‖p‖ * ‖y-p‖ := mul_pos hp1 hp2
  simp only [zero_sub, norm_neg]
  apply (div_le_iff₀ hd).mpr
  have hbound := polynomial_bound p.re hpr
  have heq : (‖p‖ * ‖y-p‖)^2 = p.re^2*((p.re-4)^2+1) := by rw [mul_pow,h1,h2];ring
  nlinarith [norm_nonneg y]
lemma y_mem : y ∈ ball G 0 (7/4) := by
  constructor
  · norm_num [G,slit,y]
  · have hne : ((fun p : ℂ => ‖(0:ℂ)-y‖ / (‖(0:ℂ)-p‖ * ‖y-p‖)) '' frontier G).Nonempty := by
      refine ⟨_, ⟨1, ?_, rfl⟩⟩
      rw [frontier_G]; norm_num [slit]
    have h : cassinian G 0 y ≤ 3/2 := csSup_le hne (by
      rintro q ⟨p,hp,rfl⟩;exact ratio_bound_y p hp)
    change cassinian G 0 y < 7/4
    linarith
lemma bounded_z : BddAbove ((fun p : ℂ => ‖(0:ℂ)-z‖ / (‖(0:ℂ)-p‖ * ‖z-p‖)) '' frontier G) := by
  refine ⟨2*‖z‖, ?_⟩
  rintro q ⟨p,hp,rfl⟩
  rw [frontier_G] at hp
  have hpi : p.im = 0 := hp.1
  have hpr : 1 ≤ p.re := hp.2
  have h1 := norm_sq p
  have h2 := norm_sq (z-p)
  simp only [sub_re,sub_im,show z.re = 2 from rfl,show z.im = 1/2 from rfl,hpi,sub_zero] at h2
  rw [hpi] at h1
  have hn : 0 ≤ ‖p‖ := norm_nonneg _
  have hm : 0 ≤ ‖z-p‖ := norm_nonneg _
  have hn1 : 1 ≤ ‖p‖ := by nlinarith
  have hm1 : 1/2 ≤ ‖z-p‖ := by nlinarith [sq_nonneg (2-p.re)]
  have hd : 0 < ‖p‖*‖z-p‖ := by positivity
  simp only [zero_sub,norm_neg]
  apply (div_le_iff₀ hd).mpr
  have hd1 : 1/2 ≤ ‖p‖*‖z-p‖ := by nlinarith
  nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hd1)]
lemma z_not_mem : z ∉ ball G 0 (7/4) := by
  intro hz
  have hp : (2:ℂ) ∈ frontier G := by rw [frontier_G];norm_num [slit]
  have hs : ‖(0:ℂ)-z‖ / (‖(0:ℂ)-(2:ℂ)‖ * ‖z-2‖) ≤ cassinian G 0 z :=
    le_csSup bounded_z ⟨2,hp,rfl⟩
  have h1 := norm_sq z
  have h2 := norm_sq (z-2)
  change ‖z‖^2 = 2^2+(1/2:ℝ)^2 at h1
  simp only [sub_re,sub_im,show z.re = 2 from rfl,show z.im = 1/2 from rfl] at h2
  norm_num only [Complex.re_ofNat, Complex.im_ofNat, sub_self, sub_zero] at h2
  norm_num at h1 h2
  have h3 : ‖z-2‖ = 1/2 := by nlinarith [norm_nonneg (z-2)]
  simp only [zero_sub,norm_neg] at hs
  norm_num [h3] at hs
  have h4 := hz.2
  change cassinian G 0 z < 7/4 at h4
  nlinarith [norm_nonneg z]
lemma midpoint : (1/2:ℝ) • y = z := by apply Complex.ext <;> norm_num [y,z,Complex.smul_re,Complex.smul_im]
theorem counterexample : IsOpen G ∧ IsConnected G ∧ (0:ℂ) ∈ G ∧
    G ≠ Set.univ ∧ StarConvex ℝ (0:ℂ) G ∧ ¬ StarConvex ℝ (0:ℂ) (ball G 0 (7/4)) := by
  refine ⟨G_open,G_connected,zero_mem,?_,star,?_⟩
  · intro h
    have : (1:ℂ) ∈ G := by rw [h];trivial
    norm_num [G,slit] at this
  · intro h
    have hm := h y_mem (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    simp only [smul_zero,zero_add,midpoint] at hm
    exact z_not_mem hm
/-- The compactified boundary point at infinity contributes zero, without changing the supremum. -/
lemma infinity_contribution (U : Set ℂ) (a b : ℂ) (hne : (frontier U).Nonempty)
    (hbd : BddAbove ((fun p : ℂ => ‖a-b‖ / (‖a-p‖ * ‖b-p‖)) '' frontier U)) :
    sSup (insert 0 ((fun p : ℂ => ‖a-b‖ / (‖a-p‖ * ‖b-p‖)) '' frontier U)) = cassinian U a b := by
  let S := ((fun p : ℂ => ‖a-b‖ / (‖a-p‖ * ‖b-p‖)) '' frontier U)
  have hs : S.Nonempty := hne.image _
  have hz : 0 ≤ sSup S := by
    obtain ⟨p,hp⟩ := hne
    exact le_trans (div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (le_csSup hbd ⟨p,hp,rfl⟩)
  change sSup (insert 0 S) = sSup S
  apply le_antisymm
  · apply csSup_le (by simp)
    intro q hq
    rcases hq with rfl | hq
    · exact hz
    · exact le_csSup hbd hq
  · apply csSup_le hs
    intro q hq
    apply le_csSup (hbd.insert 0)
    exact Set.mem_insert_of_mem 0 hq
/-- The conjecture in the Euclidean plane, represented by the complex numbers. -/
def SourceClaim : Prop := ∀ (U : Set ℂ) (a : ℂ) (r : ℝ),
  IsOpen U → IsConnected U → U ≠ univ → a ∈ U → 0 < r →
  StarConvex ℝ a U → StarConvex ℝ a (ball U a r)
theorem source_refutation : ¬ SourceClaim := by
  intro h
  exact counterexample.2.2.2.2.2
    (h G 0 (7/4) G_open G_connected counterexample.2.2.2.1 zero_mem (by norm_num) star)
end
end Cassinian331705
