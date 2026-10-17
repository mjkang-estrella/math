import Mathlib

/- Copyright 2026 Myeongjin Kang. MIT.
Finite metric-cover support for CDF098. No full Banach-curve theorem is asserted. -/
namespace CDFLocal

def Covers {α : Type*} [PseudoMetricSpace α] (A : Set α) (c : Finset α) (r : ℝ) : Prop :=
  ∀ x ∈ A, ∃ z ∈ c, dist x z ≤ r

def CoverBound {α : Type*} [PseudoMetricSpace α] (A : Set α) (r : ℝ) (N : ℕ) : Prop :=
  ∃ c : Finset α, c.card ≤ N ∧ Covers A c r

def DoublingBound (α : Type*) [PseudoMetricSpace α] (D : ℕ) : Prop :=
  ∀ x : α, ∀ r : ℝ, 0 < r → CoverBound (Metric.closedBall x r) (r/2) D

theorem covers_mono {α : Type*} [PseudoMetricSpace α] {A B : Set α}
    {c : Finset α} {r t : ℝ} (h : Covers A c r) (hBA : B ⊆ A) (hrt : r ≤ t) :
    Covers B c t := by
  intro x hx
  obtain ⟨z, hz, hdist⟩ := h x (hBA hx)
  exact ⟨z, hz, hdist.trans hrt⟩

/-- Finite centers genuinely compose, with the product cardinality bound. -/
theorem refine_cover {α : Type*} [PseudoMetricSpace α] {A : Set α}
    {c : Finset α} {r t : ℝ} {N M : ℕ} (hc : c.card ≤ N) (hcover : Covers A c r)
    (hlocal : ∀ z : α, CoverBound (Metric.closedBall z r) t M) :
    CoverBound A t (N*M) := by
  classical
  choose d hdcard hdcover using hlocal
  refine ⟨c.biUnion d, ?_, ?_⟩
  · calc
      (c.biUnion d).card ≤ ∑ z ∈ c, (d z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ c, M := Finset.sum_le_sum fun z _ => hdcard z
      _ = c.card*M := by simp
      _ ≤ N*M := Nat.mul_le_mul_right M hc
  · intro x hx
    obtain ⟨z, hz, hdist⟩ := hcover x hx
    obtain ⟨w, hw, hd⟩ := hdcover z x hdist
    exact ⟨w, Finset.mem_biUnion.mpr ⟨z, hz, hw⟩, hd⟩

/-- Every positive-radius ball can be halved q times with D^q centers. -/
theorem iterated_cover {α : Type*} [PseudoMetricSpace α] {D : ℕ}
    (hD : DoublingBound α D) (q : ℕ) (x : α) (r : ℝ) (hr : 0 < r) :
    CoverBound (Metric.closedBall x r) (r/(2:ℝ)^q) (D^q) := by
  classical
  induction q generalizing x r with
  | zero =>
    refine ⟨{x}, by simp, ?_⟩
    intro y hy
    exact ⟨x, by simp, by simpa using hy⟩
  | succ q ih =>
    obtain ⟨c, hc, hcover⟩ := hD x r hr
    have hlocal := fun z : α => ih z (r/2) (by positivity)
    have hh := refine_cover hc hcover hlocal
    convert hh using 1 <;> simp [pow_succ, div_div, mul_comm]

/-- Recenter a finite cover on actual representatives, allowing a metric pullback.
The returned centers lie in A, including when old centers did not. -/
theorem recenter_pullback {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : β → α) {A : Set β} {c : Finset α} {r K : ℝ} (hK : 0 ≤ K)
    (hback : ∀ x y, dist x y ≤ K * dist (f x) (f y))
    (hc : Covers (f '' A) c r) :
    ∃ d : Finset β, d.card ≤ c.card ∧ (↑d : Set β) ⊆ A ∧ Covers A d (2*K*r) := by
  classical
  let live := c.filter fun z => ∃ x ∈ A, dist (f x) z ≤ r
  have hex : ∀ z : live, ∃ x ∈ A, dist (f x) z ≤ r := by
    intro z
    exact (Finset.mem_filter.mp z.property).2
  choose g hgA hgdist using hex
  refine ⟨Finset.univ.image g, ?_, ?_, ?_⟩
  · calc
      (Finset.univ.image g).card ≤ Finset.univ.card := Finset.card_image_le
      _ = live.card := by simp
      _ ≤ c.card := Finset.card_filter_le _ _
  · intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    exact hgA z
  · intro x hx
    obtain ⟨z, hz, hd⟩ := hc (f x) ⟨x, hx, rfl⟩
    let i : live := ⟨z, Finset.mem_filter.mpr ⟨hz, x, hx, hd⟩⟩
    refine ⟨g i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    have htriangle : dist (f x) (f (g i)) ≤ 2*r := by
      have ht := dist_triangle (f x) z (f (g i))
      have hg := hgdist i
      rw [dist_comm z] at ht
      dsimp [i] at hg
      linarith
    calc
      dist x (g i) ≤ K * dist (f x) (f (g i)) := hback x (g i)
      _ ≤ K*(2*r) := mul_le_mul_of_nonneg_left htriangle hK
      _ = 2*K*r := by ring

/-- A concrete separated finite set injects into any sufficiently fine cover. -/
theorem packing_bound {α : Type*} [PseudoMetricSpace α] (p c : Finset α)
    {s t : ℝ} (hsep : ∀ x ∈ p, ∀ y ∈ p, x ≠ y → s < dist x y)
    (hc : Covers (↑p : Set α) c t) (hdiam : 2*t ≤ s) : p.card ≤ c.card := by
  classical
  have hchoices : ∀ x : p, ∃ z ∈ c, dist (x : α) z ≤ t := fun x => hc x x.property
  choose g hgmem hgdist using hchoices
  let f : p → c := fun x => ⟨g x, hgmem x⟩
  have hinj : Function.Injective f := by
    intro x y heq
    apply Subtype.ext
    by_contra hne
    have hs := hsep x x.property y y.property hne
    have he : g x = g y := congrArg Subtype.val heq
    have ht := dist_triangle (x : α) (g x) (y : α)
    rw [dist_comm (g x), he] at ht
    have hx := hgdist x
    rw [he] at hx
    have hy := hgdist y
    linarith
  simpa using Fintype.card_le_of_injective f hinj

theorem doubling_packing {α : Type*} [PseudoMetricSpace α] {D : ℕ}
    (hD : DoublingBound α D) (p : Finset α) (x : α) {R s : ℝ} (hR : 0 < R)
    (hp : (↑p : Set α) ⊆ Metric.closedBall x R)
    (hsep : ∀ u ∈ p, ∀ v ∈ p, u ≠ v → s < dist u v)
    (q : ℕ) (hscale : 2*(R/(2:ℝ)^q) ≤ s) : p.card ≤ D^q := by
  obtain ⟨c, hc, hcover⟩ := iterated_cover hD q x R hR
  exact (packing_bound p c hsep (covers_mono hcover hp le_rfl) hscale).trans hc

/-- Metric embedding transfer; no ambient-center assumption is hidden. -/
theorem doubling_transfer {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {D q : ℕ} (hD : DoublingBound α D) (f : β → α) {K : ℝ} (hK : 0 ≤ K)
    (hforward : ∀ x y, dist (f x) (f y) ≤ dist x y)
    (hback : ∀ x y, dist x y ≤ K * dist (f x) (f y))
    (hbudget : 4*K ≤ (2:ℝ)^q) : DoublingBound β (D^q) := by
  intro x r hr
  obtain ⟨c, hc, hcover⟩ := iterated_cover hD q (f x) r hr
  have himage : f '' Metric.closedBall x r ⊆ Metric.closedBall (f x) r := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hforward y x).trans hy
  obtain ⟨d, hd, _, hdc⟩ := recenter_pullback f hK hback (covers_mono hcover himage le_rfl)
  refine ⟨d, hd.trans hc, covers_mono hdc (Set.Subset.refl _) ?_⟩
  have hp : 0 < (2:ℝ)^q := by positivity
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).2
  have hh := mul_le_mul_of_nonneg_right hbudget hr.le
  have hdv : 4*K*(r/(2:ℝ)^q) ≤ r := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hp).2
    convert hh using 1; ring
  nlinarith

/-- Arbitrary metric subsets inherit D^2 doubling by two halvings/recentering. -/
theorem subset_doubling {α : Type*} [PseudoMetricSpace α] {D : ℕ}
    (hD : DoublingBound α D) (A : Set α) : DoublingBound A (D^2) := by
  apply doubling_transfer hD (Subtype.val : A → α) (K := 1) (by norm_num)
  · intro x y; rfl
  · intro x y; rw [one_mul]; rfl
  · norm_num

/-- Surjective noncontracting 2-Lipschitz placement transfers the full metric space. -/
theorem bilipschitz_doubling {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {D : ℕ} (hD : DoublingBound α D) (f : α → β) (hsurj : Function.Surjective f)
    (hlower : ∀ x y, dist x y ≤ dist (f x) (f y))
    (hupper : ∀ x y, dist (f x) (f y) ≤ 2*dist x y) : DoublingBound β (D^4) := by
  classical
  choose g hg using hsurj
  apply doubling_transfer hD g (K := 2) (by norm_num)
  · intro x y; simpa only [hg] using hlower (g x) (g y)
  · intro x y; simpa only [hg] using hupper (g x) (g y)
  · norm_num

noncomputable def dyadic (k : ℕ) : ℝ := 1/(2:ℝ)^k

theorem dyadic_gap {i j q : ℕ} (h : i+q ≤ j) : dyadic j * (2:ℝ)^q ≤ dyadic i := by
  have hp : (2:ℝ)^(i+q) ≤ (2:ℝ)^j := pow_le_pow_right₀ (by norm_num) h
  rw [pow_add] at hp
  unfold dyadic
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^i)).2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2^j)).2
  convert hp using 1 <;> ring

/-- At most q dyadic scales fit in a half-open multiplicative window of width 2^q. -/
theorem dyadic_window_card (t : Finset ℕ) {L U : ℝ} (q : ℕ)
    (hw : ∀ k ∈ t, L < dyadic k ∧ dyadic k ≤ U) (hwidth : U ≤ (2:ℝ)^q*L) :
    t.card ≤ q := by
  classical
  by_cases ht : t.Nonempty
  · let i := t.min' ht
    have hi : i ∈ t := Finset.min'_mem t ht
    have hsub : t ⊆ Finset.Ico i (i+q) := by
      intro k hk
      have hik : i ≤ k := Finset.min'_le t k hk
      have hki : k < i+q := by
        by_contra hh
        have hg := dyadic_gap (Nat.le_of_not_gt hh)
        have hlt := mul_lt_mul_of_pos_right (hw k hk).1 (by positivity : (0:ℝ)<2^q)
        have hu := (hw i hi).2
        nlinarith
      exact Finset.mem_Ico.mpr ⟨hik, hki⟩
    have hh := Finset.card_le_card hsub
    simpa using hh
  · simp [Finset.not_nonempty_iff_eq_empty.mp ht]

theorem intermediate_scale_count (t : Finset ℕ) {r : ℝ} (hr : 0 < r)
    (hw : ∀ k ∈ t, r/64 < dyadic k ∧ dyadic k ≤ 3*r) : t.card ≤ 8 := by
  apply dyadic_window_card t 8 hw
  norm_num
  linarith

theorem high_scale_count (t : Finset ℕ) {h r : ℝ} (hr : 0 < r) (hh : 2*r < h)
    (hw : ∀ k ∈ t, (h-r)/2 ≤ dyadic k ∧ dyadic k ≤ h+r) : t.card ≤ 4 := by
  apply dyadic_window_card t (L := (h-r)/4) (U := h+r) 4
  · intro k hk
    obtain ⟨hlo, hhi⟩ := hw k hk
    exact ⟨by linarith, hhi⟩
  · norm_num
    linarith

theorem cluster_scale_count (t : Finset ℕ) {r : ℝ} (hr : 0 < r)
    (hw : ∀ k ∈ t, r/4 < dyadic k ∧ dyadic k ≤ 400*r/97) : t.card ≤ 5 := by
  apply dyadic_window_card t 5 hw
  norm_num
  linarith

noncomputable def quarterGrid : Finset ℝ := {0, 1/4, 1/2, 3/4, 1}

theorem quarter_grid_bounds {t : ℝ} (ht : t ∈ quarterGrid) : 0 ≤ t ∧ t ≤ 1 := by
  simp only [quarterGrid, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem quarter_grid_cover {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ u ∈ quarterGrid, |t-u| ≤ 1/4 := by
  by_cases h1 : t ≤ 1/4
  · exact ⟨0, by simp [quarterGrid], abs_le.mpr ⟨by linarith, by linarith⟩⟩
  by_cases h2 : t ≤ 1/2
  · exact ⟨1/4, by simp [quarterGrid], abs_le.mpr ⟨by linarith, by linarith⟩⟩
  by_cases h3 : t ≤ 3/4
  · exact ⟨1/2, by simp [quarterGrid], abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · exact ⟨3/4, by simp [quarterGrid], abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- A genuine normed-space segment of length at most 2r has five half-radius centers
on that segment. Applying it to an intersection portion requires its endpoints. -/
theorem segment_cover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) {r : ℝ} (hlen : dist x y ≤ 2*r) :
    ∃ c : Finset E, c.card ≤ 5 ∧ (↑c : Set E) ⊆ segment ℝ x y ∧
      Covers (segment ℝ x y) c (r/2) := by
  classical
  let c := quarterGrid.image (AffineMap.lineMap x y : ℝ → E)
  refine ⟨c, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by norm_num [quarterGrid])
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    rw [segment_eq_image_lineMap]
    exact ⟨t, quarter_grid_bounds ht, rfl⟩
  · intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨u, hu, htu⟩ := quarter_grid_cover ht.1 ht.2
    refine ⟨AffineMap.lineMap x y u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    rw [dist_lineMap_lineMap, Real.dist_eq]
    have hh := mul_le_mul htu hlen (dist_nonneg : 0 ≤ dist x y) (by norm_num : (0:ℝ) ≤ 1/4)
    linarith

theorem parent_edge_projection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x p : E) {s θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hparent : dist x p ≤ 2*s) : dist (AffineMap.lineMap x p θ) x ≤ 2*s := by
  rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg hθ0]
  have hh := mul_le_mul_of_nonneg_right hθ1 (dist_nonneg : 0 ≤ dist x p)
  linarith

/-- The actual height coordinate of a regular edge controls every meeting scale. -/
theorem edge_height_window {s θ h r : ℝ} (hs : 0 ≤ s) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hball : |(1+θ)*s-h| ≤ r) :
    (h-r)/2 ≤ s ∧ s ≤ h+r := by
  obtain ⟨hl, hu⟩ := abs_le.mp hball
  have hlo := mul_nonneg hθ0 hs
  have hhi := mul_le_mul_of_nonneg_right hθ1 hs
  constructor <;> nlinarith

/-- The grouping estimates are stated for actual distances, with arbitrary endpoints. -/
theorem endpoint_group_diameter {α : Type*} [PseudoMetricSpace α]
    (x y u v c : α) {a b : ℝ} (hxu : dist x u < a) (hyv : dist y v < a)
    (huc : dist u c ≤ b) (hvc : dist v c ≤ b) : dist x y < 2*a+2*b := by
  have h1 := dist_triangle x u y
  have h2 := dist_triangle u v y
  have h3 := dist_triangle u c v
  rw [dist_comm v y] at h2
  rw [dist_comm c v] at h3
  linarith

theorem fine_group_bound {r : ℝ} (hr : 0 < r) :
    2*(r/16)+2*(r/128) < r/2 := by linarith

theorem bottom_group_bound {d r : ℝ} (hd : 0 ≤ d) (hr : 0 < r)
    (h : d^2 ≤ (r/4)^2+(r/8)^2) : d < r/2 := by nlinarith

theorem fine_edge_bound {d s r : ℝ} (hd : 0 ≤ d) (hs : 0 ≤ s) (hr : 0 < r)
    (hscale : s ≤ r/64) (h : d^2 ≤ (2*s)^2+(2*s)^2) : d < r/16 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hscale) (show 0 ≤ r/64+s by positivity)]

/-- Cluster separation from genuine metric triangle inequalities and root separation. -/
theorem cluster_separation {α : Type*} [PseudoMetricSpace α]
    (p q u v : α) {a b : ℝ} (hb : b ≤ a/2) (hroots : a-b ≤ dist u v)
    (hp : dist p u ≤ a/100) (hq : dist q v ≤ b/100) :
    (97/200 : ℝ)*a ≤ dist p q := by
  have h1 := dist_triangle u p v
  have h2 := dist_triangle p q v
  rw [dist_comm u p] at h1
  linarith

theorem meeting_cluster_scale {α : Type*} [PseudoMetricSpace α]
    (p q x : α) {a r : ℝ} (hsep : (97/200:ℝ)*a ≤ dist p q)
    (hp : dist p x ≤ r) (hq : dist q x ≤ r) : a ≤ 400*r/97 := by
  have ht := dist_triangle p x q
  rw [dist_comm x q] at ht
  linarith

theorem low_count {D : ℕ} (hD : 1 ≤ D) : 65*D^9+16*D^4 ≤ 81*D^10 := by
  have h9 : D^9 ≤ D^10 := pow_le_pow_right₀ hD (by omega)
  have h4 : D^4 ≤ D^10 := pow_le_pow_right₀ hD (by omega)
  omega

theorem high_count {D : ℕ} (hD : 1 ≤ D) : 32*D^5+16*D^4 ≤ 48*D^10 := by
  have h5 : D^5 ≤ D^10 := pow_le_pow_right₀ hD (by omega)
  have h4 : D^4 ≤ D^10 := pow_le_pow_right₀ hD (by omega)
  omega

theorem graph_count {D N : ℕ} (hD : 1 ≤ D)
    (h : N ≤ 65*D^9+16*D^4 ∨ N ≤ 32*D^5+16*D^4) : N ≤ 256*D^10 := by
  have hl := low_count hD
  have hh := high_count hD
  omega

def sourceLambda : ℕ := 76800
def witnessD : ℕ := sourceLambda^2
def graphDelta : ℕ := 256*witnessD^10
def curveLambda : ℕ := 10+6*graphDelta^8

theorem constant_identities : witnessD = 5898240000 ∧
    graphDelta = 256*sourceLambda^20 ∧ 0 < curveLambda := by
  constructor
  · norm_num [witnessD, sourceLambda]
  constructor
  · simp [graphDelta, witnessD, ← pow_mul]
  · unfold curveLambda; positivity

theorem curve_count (Delta : ℕ) : 6+5*Delta^8 ≤ 10+6*Delta^8 := by omega

end CDFLocal
