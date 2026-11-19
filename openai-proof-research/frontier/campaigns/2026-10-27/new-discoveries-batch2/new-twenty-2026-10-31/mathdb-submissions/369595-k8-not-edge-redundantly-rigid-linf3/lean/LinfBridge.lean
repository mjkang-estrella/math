import CdkDefs
import K8Comb
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# From edge-redundant rigidity in `ℓ∞^d` to the cut condition

For `ℓ∞^d = (Fin d → ℝ, sup norm)`:

* `dom_of_smooth`: if the norm is smooth at a unit vector `x₀`, then `x₀` has a
  unique coordinate of largest absolute value (`Dom x₀ k`);
* `supportFunctional_eq`: at such a point the support functional is
  `y ↦ x₀ k * y k`;
* `infRigidMotion_const`: every infinitesimal rigid motion of `ℓ∞^d` is constant
  (a translation);
* `good_of_edgeRedundant`: if `(Kₙ, p)` is an edge-redundantly rigid framework in
  `ℓ∞^d`, then every pair has a dominant coordinate, and for every edge `uv`,
  cut and coordinate `k` some edge other than `uv` crossing the cut has colour `k`.
-/

set_option linter.unusedSimpArgs false

namespace CDK

open K8 Filter Topology Matrix

variable {d : ℕ}

/-! ### Norm facts in `ℓ∞^d` -/

theorem norm_eq_of_dom {x : Fin d → ℝ} {k : Fin d} (h : Dom x k) : ‖x‖ = |x k| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    by_cases hj : j = k
    · rw [hj]
    · exact (h j hj).le
  · have := norm_le_pi_norm x k
    rwa [Real.norm_eq_abs] at this

theorem abs_le_norm (x : Fin d → ℝ) (j : Fin d) : |x j| ≤ ‖x‖ := by
  have := norm_le_pi_norm x j
  rwa [Real.norm_eq_abs] at this

theorem exists_max_coord {x : Fin d → ℝ} (hx : ‖x‖ = 1) :
    ∃ k, ‖x‖ = |x k| ∧ ∀ j, |x j| ≤ |x k| := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · exfalso
    have : x = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at hx
    exact zero_ne_one hx
  · obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|) Finset.univ_nonempty
    refine ⟨k, le_antisymm ?_ (abs_le_norm x k), fun j => hk j (Finset.mem_univ _)⟩
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    exact hk j (Finset.mem_univ _)

theorem single_apply_self (k : Fin d) : (Pi.single k (1 : ℝ) : Fin d → ℝ) k = 1 := by
  simp

theorem single_apply_ne {k j : Fin d} (h : j ≠ k) : (Pi.single k (1 : ℝ) : Fin d → ℝ) j = 0 := by
  simp [Pi.single_apply, h]

theorem norm_single_one (k : Fin d) : ‖(Pi.single k (1 : ℝ) : Fin d → ℝ)‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    by_cases h : j = k
    · rw [h, single_apply_self]; simp
    · rw [single_apply_ne h]; simp
  · have := abs_le_norm (Pi.single k (1 : ℝ) : Fin d → ℝ) k
    rwa [single_apply_self, abs_one] at this

/-- The functional `y ↦ a * y k`. -/
def coordFun (a : ℝ) (k : Fin d) : (Fin d → ℝ) →ₗ[ℝ] ℝ := a • LinearMap.proj k

@[simp] theorem coordFun_apply (a : ℝ) (k : Fin d) (y : Fin d → ℝ) : coordFun a k y = a * y k := by
  simp [coordFun]

theorem dualNorm_coordFun {a : ℝ} (ha : |a| = 1) (k : Fin d) : dualNorm (coordFun a k) = 1 := by
  unfold dualNorm
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨_, Pi.single k 1, by simp [norm_single_one], rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hy
    simp only [coordFun_apply, abs_mul, ha, one_mul]
    rw [← hy]; exact abs_le_norm y k
  · intro w hw
    refine ⟨_, ⟨Pi.single k 1, by simp [norm_single_one], rfl⟩, ?_⟩
    simp only [coordFun_apply, single_apply_self, mul_one, ha]
    exact hw

theorem isSupport_coordFun {x₀ : Fin d → ℝ} {k : Fin d} (hk : |x₀ k| = 1) :
    IsSupportFunctional x₀ (coordFun (x₀ k) k) := by
  refine ⟨?_, dualNorm_coordFun hk k⟩
  rw [coordFun_apply, ← abs_mul_abs_self, hk, one_mul]

/-- In `ℓ∞^d`, smoothness at a unit vector forces a unique dominant coordinate. -/
theorem dom_of_smooth {x₀ : Fin d → ℝ} (hx : ‖x₀‖ = 1) (hs : IsSmoothAt x₀) : ∃ k, Dom x₀ k := by
  obtain ⟨k, hk, hmax⟩ := exists_max_coord hx
  refine ⟨k, fun j hj => ?_⟩
  by_contra hle
  have hjk : |x₀ j| = |x₀ k| := le_antisymm (hmax j) (not_lt.mp hle)
  have h1 : |x₀ k| = 1 := by rw [← hk, hx]
  have hsk := isSupport_coordFun (x₀ := x₀) h1
  have hsj := isSupport_coordFun (x₀ := x₀) (k := j) (by rw [hjk, h1])
  have heq := hs.unique hsk hsj
  have := LinearMap.congr_fun heq (Pi.single k 1)
  rw [coordFun_apply, coordFun_apply, single_apply_self, single_apply_ne hj, mul_one,
    mul_zero] at this
  rw [this, abs_zero] at h1
  exact zero_ne_one h1

theorem sum_single (y : Fin d → ℝ) : ∑ i, y i • (Pi.single i (1 : ℝ) : Fin d → ℝ) = y := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem linear_apply_eq (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (y : Fin d → ℝ) :
    φ y = ∑ i, y i * φ (Pi.single i 1) := by
  conv_lhs => rw [← sum_single y]
  rw [map_sum]
  simp [map_smul, smul_eq_mul]

/-- In `ℓ∞^d`, the support functionals at a unit vector with dominant coordinate
`k` are exactly `y ↦ x₀ k * y k`. -/
theorem support_formula {x₀ : Fin d → ℝ} {k : Fin d} (hx : ‖x₀‖ = 1) (hk : Dom x₀ k)
    {φ : (Fin d → ℝ) →ₗ[ℝ] ℝ} (hφ : IsSupportFunctional x₀ φ) (y : Fin d → ℝ) :
    φ y = x₀ k * y k := by
  have h1 : |x₀ k| = 1 := by rw [← norm_eq_of_dom hk, hx]
  have hbdd : BddAbove ((fun x => |φ x|) '' Metric.sphere (0 : Fin d → ℝ) 1) := by
    by_contra hb
    have := Real.sSup_of_not_bddAbove hb
    have h2 := hφ.2
    unfold dualNorm at h2
    rw [this] at h2
    exact zero_ne_one h2
  have hbound : ∀ y : Fin d → ℝ, ‖y‖ = 1 → |φ y| ≤ 1 := by
    intro y hy
    have := le_csSup hbdd ⟨y, by simpa using hy, rfl⟩
    have h2 := hφ.2
    unfold dualNorm at h2
    rwa [h2] at this
  -- `φ` vanishes on the other basis vectors
  have hzero : ∀ j, j ≠ k → φ (Pi.single j 1) = 0 := by
    intro j hj
    have hδ : 0 < 1 - |x₀ j| := by have := hk j hj; linarith
    have hnorm : ∀ s : ℝ, |s| = 1 → ‖x₀ + (s * (1 - |x₀ j|)) • Pi.single j 1‖ = 1 := by
      intro s hs
      apply le_antisymm
      · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
        rw [Real.norm_eq_abs]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hi : i = j
        · subst hi
          rw [single_apply_self, mul_one]
          calc |x₀ i + s * (1 - |x₀ i|)| ≤ |x₀ i| + |s * (1 - |x₀ i|)| := abs_add_le _ _
            _ = 1 := by rw [abs_mul, hs, one_mul, abs_of_pos hδ]; ring
        · rw [single_apply_ne hi, mul_zero, add_zero, ← h1]
          by_cases hik : i = k
          · rw [hik]
          · exact (hk i hik).le
      · have := abs_le_norm (x₀ + (s * (1 - |x₀ j|)) • Pi.single j 1) k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, single_apply_ne (Ne.symm hj),
          mul_zero, add_zero, h1] at this
        exact this
    have hp := hbound _ (hnorm 1 (by simp))
    have hm := hbound _ (hnorm (-1) (by simp))
    rw [map_add, map_smul, hφ.1, smul_eq_mul] at hp hm
    have hp' := (abs_le.mp hp).2
    have hm' := (abs_le.mp hm).2
    have : (1 - |x₀ j|) * φ (Pi.single j 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have hsum : ∀ y : Fin d → ℝ, φ y = y k * φ (Pi.single k 1) := by
    intro y
    rw [linear_apply_eq φ y, Finset.sum_eq_single k]
    · intro j _ hj; rw [hzero j hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hk1 : φ (Pi.single k 1) = x₀ k := by
    have h0 := hφ.1
    rw [hsum x₀] at h0
    have hsq : x₀ k * x₀ k = 1 := by rw [← abs_mul_abs_self, h1, one_mul]
    calc φ (Pi.single k 1) = (x₀ k * x₀ k) * φ (Pi.single k 1) := by rw [hsq, one_mul]
      _ = x₀ k * (x₀ k * φ (Pi.single k 1)) := by ring
      _ = x₀ k := by rw [h0, mul_one]
  rw [hsum y, hk1, mul_comm]

theorem supportFunctional_eq {x₀ : Fin d → ℝ} {k : Fin d} (hx : ‖x₀‖ = 1) (hk : Dom x₀ k)
    (y : Fin d → ℝ) : supportFunctional x₀ y = x₀ k * y k := by
  have h1 : |x₀ k| = 1 := by rw [← norm_eq_of_dom hk, hx]
  have hex : ∃ φ, IsSupportFunctional x₀ φ := ⟨_, isSupport_coordFun h1⟩
  unfold supportFunctional
  rw [dite_eq_left hex]
  exact support_formula hx hk hex.choose_spec y

/-! ### Normalised vectors -/

theorem norm_normalised {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type*}
    {p : V → E} {v w : V} (h : p v ≠ p w) : ‖normalised p v w‖ = 1 := by
  unfold normalised
  have h0 : ‖p v - p w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ h0]

theorem normalised_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type*}
    (p : V → E) (v w : V) : normalised p w v = -normalised p v w := by
  unfold normalised
  rw [norm_sub_rev, ← smul_neg, neg_sub]

theorem dom_smul_iff {x : Fin d → ℝ} {c : ℝ} (hc : 0 < c) {k : Fin d} :
    Dom (c • x) k ↔ Dom x k := by
  unfold Dom
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
  constructor
  · intro h j hj; exact lt_of_mul_lt_mul_left (h j hj) hc.le
  · intro h j hj; exact mul_lt_mul_of_pos_left (h j hj) hc

theorem dom_normalised_iff {V : Type*} {p : V → Fin d → ℝ} {v w : V} (h : p v ≠ p w) {k : Fin d} :
    Dom (normalised p v w) k ↔ Dom (p v - p w) k := by
  unfold normalised
  exact dom_smul_iff (inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr h)))

/-- For an edge of a framework in `ℓ∞^d`: a dominant coordinate `c` of `p v - p w`
and a sign `s` such that the support functionals of the two orientations are
`y ↦ s * y c` and `y ↦ -s * y c`. -/
theorem edge_functionals {V : Type*} {p : V → Fin d → ℝ} {v w : V} (hne : p v ≠ p w)
    (hs : IsSmoothAt (normalised p v w)) :
    ∃ c s, Dom (p v - p w) c ∧ (∀ y, supportFunctional (normalised p v w) y = s * y c) ∧
      (∀ y, supportFunctional (normalised p w v) y = -s * y c) := by
  have hn := norm_normalised hne
  obtain ⟨c, hc⟩ := dom_of_smooth hn hs
  refine ⟨c, normalised p v w c, (dom_normalised_iff hne).mp hc,
    fun y => supportFunctional_eq hn hc y, fun y => ?_⟩
  have hn' : ‖normalised p w v‖ = 1 := norm_normalised (Ne.symm hne)
  have hc' : Dom (normalised p w v) c := by rw [normalised_swap]; exact hc.neg
  rw [supportFunctional_eq hn' hc' y, normalised_swap]
  simp

/-! ### Infinitesimal rigid motions of `ℓ∞^d` are translations -/

theorem coord_deriv_zero {g : ℝ → Fin d → ℝ} {k : Fin d} (hdom : Dom (g 0) k) (hk : g 0 k ≠ 0)
    (hdiff : DifferentiableAt ℝ g 0) (hnorm : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖g t‖ = ‖g 0‖) :
    deriv g 0 k = 0 := by
  have hc : ContinuousAt g 0 := hdiff.continuousAt
  have hci : ∀ i, ContinuousAt (fun t => g t i) 0 := fun i =>
    (continuous_apply i).continuousAt.comp hc
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, j ≠ k → |g t j| < |g t k| := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = k
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · exact ((hci j).abs.eventually_lt (hci k).abs (hdom j hj)).mono fun _ h _ => h
  have hpos : 0 < |g 0 k| := abs_pos.mpr hk
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), |g t k - g 0 k| < |g 0 k| := by
    have : ContinuousAt (fun t => |g t k - g 0 k|) 0 :=
      ((hci k).sub continuousAt_const).abs
    exact this.eventually_lt continuousAt_const (by simpa using hpos)
  have hev3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Ioo (-1 : ℝ) 1 :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hconst : (fun t => g t k) =ᶠ[𝓝 0] fun _ => g 0 k := by
    filter_upwards [hev1, hev2, hev3] with t h1 h2 h3
    have e1 : ‖g t‖ = |g t k| := norm_eq_of_dom h1
    have e0 : ‖g 0‖ = |g 0 k| := norm_eq_of_dom hdom
    have habs : |g t k| = |g 0 k| := by rw [← e1, ← e0, hnorm t h3]
    rcases abs_eq_abs.mp habs with h | h
    · exact h
    · exfalso
      rw [h] at h2
      have : |-g 0 k - g 0 k| = 2 * |g 0 k| := by
        rw [show -g 0 k - g 0 k = -(2 * g 0 k) by ring, abs_neg, abs_mul]; norm_num
      linarith
  have hd : HasDerivAt (fun t => g t k) (deriv g 0 k) 0 :=
    (hasDerivAt_pi.mp hdiff.hasDerivAt) k
  have hd' : HasDerivAt (fun _ : ℝ => g 0 k) (deriv g 0 k) 0 :=
    hd.congr_of_eventuallyEq hconst.symm
  exact hd'.unique (hasDerivAt_const 0 _)

theorem infRigidMotion_coord {η : (Fin d → ℝ) → Fin d → ℝ} (h : IsInfRigidMotion η)
    {x z : Fin d → ℝ} {k : Fin d} (hdom : Dom (z - x) k) (hk : (z - x) k ≠ 0) : η z k = η x k := by
  obtain ⟨m, hm⟩ := h
  let g : ℝ → Fin d → ℝ := fun t => m.α z t - m.α x t
  have hg0 : g 0 = z - x := by simp [g, m.zero]
  have hdiff : DifferentiableAt ℝ g 0 := (m.differentiableAt z).sub (m.differentiableAt x)
  have hnorm : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖g t‖ = ‖g 0‖ := by
    intro t ht
    rw [hg0]
    exact m.isometric z x t ht
  have := coord_deriv_zero (g := g) (by rw [hg0]; exact hdom) (by rw [hg0]; exact hk) hdiff hnorm
  have hder : deriv g 0 = deriv (m.α z) 0 - deriv (m.α x) 0 :=
    deriv_sub (m.differentiableAt z) (m.differentiableAt x)
  rw [hder, Pi.sub_apply, sub_eq_zero] at this
  rw [hm z, hm x]; exact this

/-- Every infinitesimal rigid motion of `ℓ∞^d` is constant. -/
theorem infRigidMotion_const {η : (Fin d → ℝ) → Fin d → ℝ} (h : IsInfRigidMotion η)
    (x y : Fin d → ℝ) : η x = η y := by
  funext k
  set M : ℝ := 2 * ‖x - y‖ + 1 with hM
  have hMpos : 0 < M := by have := norm_nonneg (x - y); linarith
  let z : Fin d → ℝ := x + M • Pi.single k 1
  have hzx : z - x = M • Pi.single k 1 := by simp [z]
  have hzy : ∀ i, (z - y) i = (x - y) i + M * (Pi.single k (1 : ℝ) : Fin d → ℝ) i := by
    intro i; simp [z]; ring
  have h1 : η z k = η x k := by
    apply infRigidMotion_coord h
    · intro j hj
      rw [hzx]
      simp [Pi.smul_apply, single_apply_ne hj, single_apply_self, abs_of_pos hMpos, hMpos]
    · rw [hzx]; simp [hMpos.ne']
  have hyk : (z - y) k = (x - y) k + M := by rw [hzy, single_apply_self, mul_one]
  have hbig : ‖x - y‖ < (z - y) k := by
    rw [hyk]
    have := abs_le_norm (x - y) k
    have := neg_abs_le ((x - y) k)
    linarith
  have h2 : η z k = η y k := by
    apply infRigidMotion_coord h
    · intro j hj
      rw [hzy, single_apply_ne hj, mul_zero, add_zero, abs_of_pos
        (lt_of_le_of_lt (norm_nonneg _) hbig)]
      exact lt_of_le_of_lt (abs_le_norm _ j) hbig
    · exact ne_of_gt (lt_of_le_of_lt (norm_nonneg _) hbig)
  rw [← h1, h2]

/-! ### The cut condition -/

theorem displacement_std {V : Type*} (u : V × Fin d → ℝ) (v : V) :
    displacement (stdBasis d) u v = fun i => u (v, i) := by
  unfold displacement stdBasis
  exact sum_single _

theorem other_left {V : Type*} {v w : V} (h : v ∈ s(v, w)) : Sym2.Mem.other h = w :=
  Sym2.congr_right.mp (Sym2.other_spec h)

theorem other_right {V : Type*} {v w : V} (h : w ∈ s(v, w)) : Sym2.Mem.other h = v := by
  exact Sym2.congr_right.mp ((Sym2.other_spec h).trans Sym2.eq_swap)

/-- The row of the rigidity matrix at an edge `vw` of a framework in `ℓ∞^d`:
`(R(G, p) u)_{vw} = s * (u (v, c) - u (w, c))`, where `c` is the dominant
coordinate of `p v - p w` and `s = ±1`. -/
theorem mulVec_edge {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    {p : V → Fin d → ℝ} (hfw : IsFramework H p) {v w : V} (hadj : H.Adj v w) :
    ∃ c s, Dom (p v - p w) c ∧ s ≠ 0 ∧ ∀ u : V × Fin d → ℝ,
      (rigidityMatrix (stdBasis d) H p *ᵥ u) ⟨s(v, w), hadj⟩ = s * (u (v, c) - u (w, c)) := by
  obtain ⟨hne, hs⟩ := hfw v w hadj
  obtain ⟨c, s, hdom, hφ, hφ'⟩ := edge_functionals hne hs
  have hs0 : s ≠ 0 := by
    have hn := norm_normalised hne
    have hc : Dom (normalised p v w) c := (dom_normalised_iff hne).mpr hdom
    have h1 : |normalised p v w c| = 1 := by rw [← norm_eq_of_dom hc, hn]
    intro h0
    have := (hφ (Pi.single c 1))
    rw [h0, zero_mul, supportFunctional_eq hn hc, single_apply_self, mul_one] at this
    rw [this, abs_zero] at h1
    exact zero_ne_one h1
  refine ⟨c, s, hdom, hs0, fun u => ?_⟩
  set e : H.edgeSet := ⟨s(v, w), hadj⟩
  have hvw' : (e : Sym2 V) = s(v, w) := rfl
  have hvw_ne : v ≠ w := hadj.ne
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  have hrow : ∀ x : V, ∑ i, rigidityMatrix (stdBasis d) H p e (x, i) * u (x, i) =
      if x = v then s * u (v, c) else if x = w then -s * u (w, c) else 0 := by
    intro x
    have hcoef : ∀ (z : Fin d → ℝ) (a : ℝ), (∀ y, supportFunctional z y = a * y c) →
        ∑ i, supportFunctional z (stdBasis d i) * u (x, i) = a * u (x, c) := by
      intro z a hz
      simp only [hz, stdBasis]
      rw [Finset.sum_eq_single c]
      · rw [single_apply_self, mul_one]
      · intro j _ hj; rw [single_apply_ne (Ne.symm hj)]; ring
      · intro h; exact absurd (Finset.mem_univ c) h
    by_cases hxv : x = v
    · subst hxv
      rw [ite_eq_left rfl]
      have hmem : x ∈ (e : Sym2 V) := Sym2.mem_mk_left _ _
      have : ∀ i, rigidityMatrix (stdBasis d) H p e (x, i) =
          supportFunctional (normalised p x w) (stdBasis d i) := by
        intro i
        unfold rigidityMatrix
        rw [dite_eq_left hmem]
        rw [other_left hmem]
      simp only [this]
      exact hcoef _ _ hφ
    · rw [ite_eq_right hxv]
      by_cases hxw : x = w
      · subst hxw
        rw [ite_eq_left rfl]
        have hmem : x ∈ (e : Sym2 V) := Sym2.mem_mk_right _ _
        have : ∀ i, rigidityMatrix (stdBasis d) H p e (x, i) =
            supportFunctional (normalised p x v) (stdBasis d i) := by
          intro i
          unfold rigidityMatrix
          rw [dite_eq_left hmem]
          rw [other_right hmem]
        simp only [this]
        exact hcoef _ _ hφ'
      · rw [ite_eq_right hxw]
        have hnm : x ∉ (e : Sym2 V) := by
          rw [hvw', Sym2.mem_iff]; exact fun h => h.elim hxv hxw
        apply Finset.sum_eq_zero
        intro i _
        unfold rigidityMatrix
        rw [dite_eq_right hnm, zero_mul]
  rw [Finset.sum_congr rfl fun x _ => hrow x]
  rw [Fintype.sum_eq_add v w hvw_ne]
  · rw [ite_eq_left rfl, ite_eq_right (Ne.symm hvw_ne), ite_eq_left rfl]; ring
  · intro x hx
    rw [ite_eq_right hx.1, ite_eq_right hx.2]

/-- An indicator flex: if no edge of `H` with colour `k` crosses the cut `S`,
then the vector equal to `1` in coordinate `k` on `S` and `0` elsewhere lies in
the kernel of the rigidity matrix. -/
theorem indicator_in_kernel {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    {p : V → Fin d → ℝ} (hfw : IsFramework H p) (S : Finset V) (k : Fin d)
    (hno : ∀ a ∈ S, ∀ b, b ∉ S → H.Adj a b → ¬ Dom (p b - p a) k) :
    rigidityMatrix (stdBasis d) H p *ᵥ (fun xi => if xi.2 = k ∧ xi.1 ∈ S then 1 else 0) = 0 := by
  funext e
  obtain ⟨⟨v, w⟩, hvw⟩ := Quot.exists_rep (e : Sym2 V)
  have hadj : H.Adj v w := by
    have := e.2
    rw [← hvw] at this
    exact this
  have he : e = ⟨s(v, w), hadj⟩ := Subtype.ext hvw.symm
  obtain ⟨c, s, hdom, -, hrow⟩ := mulVec_edge hfw hadj
  rw [he, hrow, Pi.zero_apply]
  by_cases hck : c = k
  · subst hck
    by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
    · simp [hv, hw]
    · exact absurd hdom.sub_comm (hno v hv w hw hadj)
    · exact absurd hdom (hno w hw v hv hadj.symm)
    · simp [hv, hw]
  · simp [hck]

/-- Consequences of edge-redundant rigidity of `(Kₙ, p)` in `ℓ∞^d`. -/
theorem good_of_edgeRedundant {n : ℕ} {p : Fin n → Fin d → ℝ}
    (h : IsEdgeRedundantlyRigidFramework (stdBasis d) (completeGraph n) p) :
    (∀ u v : Fin n, u ≠ v → ∃ k, Dom (p v - p u) k) ∧
    (∀ u v : Fin n, u ≠ v → ∀ (S : Finset (Fin n)) (k : Fin d), (∃ a, a ∈ S) → (∃ b, b ∉ S) →
      ∃ a ∈ S, ∃ b, b ∉ S ∧ ¬ (a = u ∧ b = v) ∧ ¬ (a = v ∧ b = u) ∧ Dom (p b - p a) k) := by
  obtain ⟨⟨hfw, -⟩, hdel⟩ := h
  constructor
  · intro u v huv
    have hadj : (completeGraph n).Adj v u := Ne.symm huv
    obtain ⟨hne, hs⟩ := hfw v u hadj
    obtain ⟨k, hk⟩ := dom_of_smooth (norm_normalised hne) hs
    exact ⟨k, (dom_normalised_iff hne).mp hk⟩
  · intro u v huv S k ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩
    by_contra hno
    push Not at hno
    have hmem : s(u, v) ∈ (completeGraph n).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]; exact huv
    obtain ⟨hfw', hker⟩ := hdel _ hmem
    have hno' : ∀ a ∈ S, ∀ b, b ∉ S → ((completeGraph n).deleteEdges {s(u, v)}).Adj a b →
        ¬ Dom (p b - p a) k := by
      intro a ha b hb hab
      rw [SimpleGraph.deleteEdges_adj] at hab
      apply hno a ha b hb
      · intro h1 h2; apply hab.2; rw [h1, h2]; exact Set.mem_singleton _
      · intro h1 h2; apply hab.2; rw [h1, h2, Sym2.eq_swap]; exact Set.mem_singleton _
    obtain ⟨η, hη, hu⟩ := hker _ (indicator_in_kernel hfw' S k hno')
    have ha := hu a₀
    have hb := hu b₀
    rw [displacement_std] at ha hb
    have := congr_fun (ha.trans ((infRigidMotion_const hη (p a₀) (p b₀)).trans hb.symm)) k
    simp [ha₀, hb₀] at this

end CDK
