import Cassinian
open Set Complex
namespace Cassinian331705
noncomputable section
/-- Every finite boundary point is visible along its half-open radial segment. -/
def StrictlyStarlike (a : ℂ) (U : Set ℂ) : Prop :=
  ∀ p ∈ frontier U, ∀ s : ℝ, 0 ≤ s → s < 1 → (1-s) • a + s • p ∈ U
def SourceClaimStrict : Prop := ∀ (U : Set ℂ) (a : ℂ) (r : ℝ),
  IsOpen U → IsConnected U → U ≠ univ → a ∈ U → 0 < r →
  StrictlyStarlike a U → StarConvex ℝ a (ball U a r)
namespace Wedge
-- Equivalent closed half-plane description avoids absolute-value case splits.
def K : Set ℂ := {p | 1 ≤ p.re ∧ 20*p.im ≤ p.re-1 ∧ -(p.re-1) ≤ 20*p.im}
def U : Set ℂ := Kᶜ
lemma closed_K : IsClosed K := by
  exact (isClosed_le continuous_const continuous_re).inter
    ((isClosed_le (continuous_const.mul continuous_im) (continuous_re.sub continuous_const)).inter
      (isClosed_le (continuous_re.sub continuous_const).neg (continuous_const.mul continuous_im)))
lemma open_U : IsOpen U := closed_K.isOpen_compl
lemma zero_U : (0:ℂ) ∈ U := by norm_num [U,K]
lemma star_U : StarConvex ℝ (0:ℂ) U := by
  intro w hw a b ha hb hab
  simp only [U, mem_compl_iff, K, mem_ofPred_eq] at *
  simp only [smul_zero, zero_add, Complex.smul_im, Complex.smul_re, smul_eq_mul]
  intro h
  have hb1 : b ≤ 1 := by linarith
  have hb0 : 0 < b := by
    by_contra hh
    have he : b = 0 := by linarith
    rw [he] at h
    norm_num at h
  apply hw
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (show 0 ≤ w.re by nlinarith [h.1])]
  constructor <;> nlinarith
lemma connected_U : IsConnected U := (star_U.isPathConnected zero_U).isConnected
lemma frontier_subset (p : ℂ) (hp : p ∈ frontier U) :
    1 ≤ p.re ∧ (20*p.im = p.re-1 ∨ 20*p.im = -(p.re-1)) := by
  have hk : p ∈ K := by
    have hh := frontier_subset_closure (s := K)
    rw [U, frontier_compl] at hp
    exact closed_K.closure_eq ▸ hh hp
  have hn : ¬ (20*p.im < p.re-1 ∧ -(p.re-1) < 20*p.im) := by
    intro hh
    have ho : IsOpen {q : ℂ | 20*q.im < q.re-1 ∧ -(q.re-1) < 20*q.im} :=
      (isOpen_lt (continuous_const.mul continuous_im) (continuous_re.sub continuous_const)).inter
        (isOpen_lt (continuous_re.sub continuous_const).neg (continuous_const.mul continuous_im))
    have hi : p ∈ interior K := mem_interior.mpr ⟨_, by
      intro q hq
      exact ⟨by dsimp at hq ⊢; linarith [hq.1,hq.2], le_of_lt hq.1, le_of_lt hq.2⟩, ho, hh⟩
    rw [U,frontier_compl,frontier] at hp
    exact hp.2 hi
  exact ⟨hk.1, by by_contra h; push Not at h; exact hn ⟨lt_of_le_of_ne hk.2.1 h.1, lt_of_le_of_ne hk.2.2 (Ne.symm h.2)⟩⟩
lemma strict_U : StrictlyStarlike 0 U := by
  intro p hp s hs hs1
  have hh := frontier_subset p hp
  simp only [smul_zero,zero_add]
  change ¬ (1 ≤ (s • p).re ∧ 20*(s • p).im ≤ (s • p).re-1 ∧ -((s • p).re-1) ≤ 20*(s • p).im)
  simp only [Complex.smul_re,Complex.smul_im,smul_eq_mul]
  intro h
  rcases hh.2 with he | he <;> nlinarith
lemma boundary (p : ℂ) (hr : 1 ≤ p.re)
    (he : 20*p.im = p.re-1 ∨ 20*p.im = -(p.re-1)) : p ∈ frontier U := by
  have hk : p ∈ K := ⟨hr, by rcases he with h | h <;> constructor <;> linarith⟩
  rw [open_U.frontier_eq]
  refine ⟨?_, by simpa [U] using hk⟩
  apply Metric.mem_closure_iff.mpr
  intro e hepos
  refine ⟨p - (e/2:ℝ), ?_, ?_⟩
  · change ¬ (1 ≤ (p-(e/2:ℝ)).re ∧ 20*(p-(e/2:ℝ)).im ≤ (p-(e/2:ℝ)).re-1 ∧ -((p-(e/2:ℝ)).re-1) ≤ 20*(p-(e/2:ℝ)).im)
    simp only [sub_re,sub_im,ofReal_re,ofReal_im,sub_zero]
    intro h
    rcases he with hh | hh <;> linarith
  · rw [dist_eq_norm]
    have hh : p - (p-(e/2:ℝ)) = (e/2:ℝ) := by ring
    rw [hh, norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hepos)]
    linarith
lemma proper_U : U ≠ univ := by
  intro h
  have hh : (1:ℂ) ∈ U := by rw [h]; trivial
  norm_num [U,K] at hh
lemma frontier_eq : frontier U = {p | 1 ≤ p.re ∧
    (20*p.im = p.re-1 ∨ 20*p.im = -(p.re-1))} := by
  ext p
  exact ⟨frontier_subset p, fun h => boundary p h.1 h.2⟩
lemma K_abs : K = {p : ℂ | 1 ≤ p.re ∧ |p.im| ≤ (p.re-1)/20} := by
  ext p
  simp only [K,mem_ofPred_eq,abs_le]
  constructor
  · rintro ⟨hr,h1,h2⟩
    exact ⟨hr,by constructor <;> linarith⟩
  · rintro ⟨hr,h1,h2⟩
    exact ⟨hr,by constructor <;> linarith⟩
lemma product_lower (A B L M : ℝ) (hA : L ≤ A) (hB : M ≤ B)
    (hL : 0 ≤ L) (hM : 0 ≤ M) : L*M ≤ A*B := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
lemma polynomial (s v : ℝ) (hs : 1 ≤ s) (hv : 20*v ≤ s-1) :
    153/25 < (s^2+v^2)*((4-s)^2+(1-v)^2) := by
  have hA : s^2 ≤ s^2+v^2 := by nlinarith [sq_nonneg v]
  by_cases h1 : s ≤ 5/4
  · have ha : 1 ≤ s^2+v^2 := by nlinarith [sq_nonneg v]
    have hb : 121/16 ≤ (4-s)^2+(1-v)^2 := by nlinarith [sq_nonneg (1-v)]
    have hh := product_lower _ _ _ _ ha hb (by norm_num) (by norm_num)
    linarith
  by_cases h2 : s ≤ 2
  · have ha : 25/16 ≤ s^2+v^2 := by nlinarith [sq_nonneg v]
    have hb : 4+(19/20:ℝ)^2 ≤ (4-s)^2+(1-v)^2 := by nlinarith [sq_nonneg (4-s-2),sq_nonneg (1-v-19/20)]
    have hh := product_lower _ _ _ _ ha hb (by norm_num) (by norm_num)
    norm_num at hh ⊢; linarith
  by_cases h3 : s ≤ 3
  · have ha : 4 ≤ s^2+v^2 := by nlinarith [sq_nonneg v]
    have hb : 1+(9/10:ℝ)^2 ≤ (4-s)^2+(1-v)^2 := by nlinarith [sq_nonneg (4-s-1),sq_nonneg (1-v-9/10)]
    have hh := product_lower _ _ _ _ ha hb (by norm_num) (by norm_num)
    norm_num at hh ⊢; linarith
  by_cases h4 : s ≤ 4
  · have ha : 9 ≤ s^2+v^2 := by nlinarith [sq_nonneg v]
    have hb : (17/20:ℝ)^2 ≤ (4-s)^2+(1-v)^2 := by nlinarith [sq_nonneg (4-s),sq_nonneg (1-v-17/20)]
    have hh := product_lower _ _ _ _ ha hb (by norm_num) (by norm_num)
    norm_num at hh ⊢; linarith
  by_cases h5 : s ≤ 5
  · have ha : 16 ≤ s^2+v^2 := by nlinarith [sq_nonneg v]
    have hb : (4/5:ℝ)^2 ≤ (4-s)^2+(1-v)^2 := by nlinarith [sq_nonneg (4-s),sq_nonneg (1-v-4/5)]
    have hh := product_lower _ _ _ _ ha hb (by norm_num) (by norm_num)
    norm_num at hh ⊢; linarith
  · have ha : 25 ≤ s^2+v^2 := by nlinarith [sq_nonneg v]
    have hb : 1 ≤ (4-s)^2+(1-v)^2 := by nlinarith [sq_nonneg (1-v)]
    have hh := product_lower _ _ _ _ ha hb (by norm_num) (by norm_num)
    linarith
lemma ratio_y (p : ℂ) (hp : p ∈ frontier U) :
    ‖(0:ℂ)-y‖ / (‖(0:ℂ)-p‖ * ‖y-p‖) ≤ 5/3 := by
  have hf := frontier_subset p hp
  have hv : 20*p.im ≤ p.re-1 := by rcases hf.2 with h | h <;> linarith [hf.1]
  have h1 := norm_sq p
  have h2 := norm_sq (y-p)
  have hy := norm_sq y
  change ‖y‖^2 = 4^2+1^2 at hy
  simp only [sub_re,sub_im,show y.re = 4 from rfl,show y.im = 1 from rfl] at h2
  have heq : (‖p‖*‖y-p‖)^2 = (p.re^2+p.im^2)*((4-p.re)^2+(1-p.im)^2) := by rw [mul_pow,h1,h2]
  have hbound := polynomial p.re p.im hf.1 hv
  have hd : 0 < ‖p‖*‖y-p‖ := by nlinarith [mul_nonneg (norm_nonneg p) (norm_nonneg (y-p))]
  simp only [zero_sub,norm_neg]
  apply (div_le_iff₀ hd).mpr
  nlinarith [norm_nonneg y]
lemma y_ball : y ∈ ball U 0 (7/4) := by
  constructor
  · norm_num [U,K,y]
  · have hp : (1:ℂ) ∈ frontier U := boundary 1 (by norm_num) (by norm_num)
    have hn : ((fun p : ℂ => ‖(0:ℂ)-y‖ / (‖(0:ℂ)-p‖ * ‖y-p‖)) '' frontier U).Nonempty := ⟨_,1,hp,rfl⟩
    have hh : cassinian U 0 y ≤ 5/3 := csSup_le hn (by rintro q ⟨p,hp,rfl⟩; exact ratio_y p hp)
    change cassinian U 0 y < 7/4
    linarith
lemma bounded_z_wedge : BddAbove ((fun p : ℂ => ‖(0:ℂ)-z‖ / (‖(0:ℂ)-p‖ * ‖z-p‖)) '' frontier U) := by
  refine ⟨(5/2)*‖z‖, ?_⟩
  rintro q ⟨p,hp,rfl⟩
  have hf := frontier_subset p hp
  have hv : 20*p.im ≤ p.re-1 := by rcases hf.2 with h | h <;> linarith [hf.1]
  have h1 := norm_sq p
  have h2 := norm_sq (z-p)
  simp only [sub_re,sub_im,show z.re = 2 from rfl,show z.im = 1/2 from rfl] at h2
  have hn1 : 1 ≤ ‖p‖ := by nlinarith [norm_nonneg p,sq_nonneg p.im]
  have hm1 : 2/5 ≤ ‖z-p‖ := by
    by_cases hr : p.re ≤ 3
    · have hi : p.im ≤ 1/10 := by linarith
      nlinarith [norm_nonneg (z-p), sq_nonneg (2-p.re),sq_nonneg (1/2-p.im-2/5)]
    · nlinarith [norm_nonneg (z-p), sq_nonneg (1/2-p.im)]
  have hd1 : 2/5 ≤ ‖p‖*‖z-p‖ := by nlinarith
  have hd : 0 < ‖p‖*‖z-p‖ := by linarith
  simp only [zero_sub,norm_neg]
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hd1)]
lemma z_not_ball : z ∉ ball U 0 (7/4) := by
  let p : ℂ := ⟨2,1/20⟩
  have hp : p ∈ frontier U := boundary p (by norm_num [p]) (by left; norm_num [p])
  have hs := le_csSup bounded_z_wedge (show ‖(0:ℂ)-z‖ / (‖(0:ℂ)-p‖ * ‖z-p‖) ∈ (fun p : ℂ => ‖(0:ℂ)-z‖ / (‖(0:ℂ)-p‖ * ‖z-p‖)) '' frontier U from ⟨p,hp,rfl⟩)
  have h1 := norm_sq z
  have h2 := norm_sq (z-p)
  have h3 := norm_sq p
  change ‖z‖^2 = 2^2+(1/2:ℝ)^2 at h1
  change ‖p‖^2 = 2^2+(1/20:ℝ)^2 at h3
  have he : ‖z-p‖^2 = (9/20:ℝ)^2 := by convert h2 using 1; norm_num [z,p]
  have hnorm : ‖z-p‖ = 9/20 := by nlinarith [norm_nonneg (z-p)]
  have hd : 0 < ‖p‖ * ‖z-p‖ := by
    rw [hnorm]
    have hh : 0 < ‖p‖ := by nlinarith [norm_nonneg p]
    positivity
  simp only [zero_sub,norm_neg] at hs
  intro hz
  have hz2 : sSup ((fun a : ℂ => ‖z‖ / (‖a‖ * ‖z-a‖)) '' frontier U) < 7/4 := by
    simpa only [cassinian,zero_sub,norm_neg] using hz.2
  have hh := lt_of_le_of_lt hs hz2
  have hlt := (div_lt_iff₀ hd).mp hh
  rw [hnorm] at hlt
  nlinarith [norm_nonneg z, norm_nonneg p]
lemma ball_not_star : ¬ StarConvex ℝ (0:ℂ) (ball U 0 (7/4)) := by
  intro h
  have hm := h y_ball (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_zero,zero_add,midpoint] at hm
  exact z_not_ball hm
 theorem ordinary_refutation : ¬ SourceClaim := by
  intro h
  exact ball_not_star (h U 0 (7/4) open_U connected_U proper_U zero_U (by norm_num) star_U)
 theorem strict_refutation : ¬ SourceClaimStrict := by
  intro h
  exact ball_not_star (h U 0 (7/4) open_U connected_U proper_U zero_U (by norm_num) strict_U)
lemma slit_not_strict : ¬ StrictlyStarlike 0 G := by
  intro h
  have hp : (2:ℂ) ∈ frontier G := by rw [frontier_G]; norm_num [slit]
  have hh := h 2 hp (1/2) (by norm_num) (by norm_num)
  norm_num [G,slit,Complex.smul_re,Complex.smul_im] at hh
end Wedge
end
end Cassinian331705
