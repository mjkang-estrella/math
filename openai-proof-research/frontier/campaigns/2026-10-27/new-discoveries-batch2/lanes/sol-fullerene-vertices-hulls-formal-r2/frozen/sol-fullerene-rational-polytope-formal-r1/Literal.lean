import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
namespace FullereneGeometry
abbrev E := Fin 3 → ℝ
def dot (a x : E) : ℝ := ∑ k, a k * x k
def normal (a : E) : E →ₗ[ℝ] ℝ where
  toFun := dot a
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by simp [dot, Finset.mul_sum]; congr 1; ext k; ring
theorem dot_continuous (a : E) : Continuous (dot a) := by
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (continuous_apply k)
def poly {n : ℕ} (q : Fin n → E) : Set E := {x | ∀ i, dot (q i) x ≤ 1}
def facetSection {n : ℕ} (q : Fin n → E) (i : Fin n) : Set E :=
  {x ∈ poly q | dot (q i) x = 1}
theorem poly_closed {n : ℕ} (q : Fin n → E) : IsClosed (poly q) := by
  have hp : poly q = ⋂ i, {x | dot (q i) x ≤ (1 : ℝ)} := by ext x; simp [poly]
  rw [hp]
  exact isClosed_iInter fun i => isClosed_le (dot_continuous (q i)) continuous_const
theorem poly_convex {n : ℕ} (q : Fin n → E) : Convex ℝ (poly q) := by
  intro x hx y hy a b ha hb hab i
  change (normal (q i)) (a • x + b • y) ≤ 1
  rw [map_add, map_smul, map_smul]
  change a * dot (q i) x + b * dot (q i) y ≤ 1
  have h₁ := mul_le_mul_of_nonneg_left (hx i) ha
  have h₂ := mul_le_mul_of_nonneg_left (hy i) hb
  nlinarith
theorem zero_interior {n : ℕ} (q : Fin n → E) : (0 : E) ∈ interior (poly q) := by
  have ho : IsOpen (⋂ i, {x : E | (normal (q i)) x < (1 : ℝ)}) :=
    isOpen_iInter_of_finite fun i => isOpen_lt (dot_continuous (q i)) continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (ho.mem_nhds (by simp))
  intro x hx i
  exact le_of_lt (Set.mem_iInter.mp hx i)

/-- Explicit positive spanning certificate: each signed coordinate is a nonnegative
linear combination of the one-sided normals. This is sufficient for compactness. -/
theorem compact_of_positive_span {n : ℕ} (q : Fin n → E)
    (w : Fin 3 → Bool → Fin n → ℝ)
    (hw : ∀ k s i, 0 ≤ w k s i)
    (hc : ∀ k s x, (∑ i, w k s i * dot (q i) x) =
      (if s then x k else -x k)) : IsCompact (poly q) := by
  let C : E := fun k => max (∑ i, w k true i) (∑ i, w k false i)
  apply (isCompact_Icc : IsCompact (Set.Icc (-C) C)).of_isClosed_subset (poly_closed q)
  intro x hx
  constructor
  · intro k
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hx i) (hw k false i))
    simp only [mul_one] at h
    rw [hc k false x] at h
    have hm := le_max_right (∑ i, w k true i) (∑ i, w k false i)
    change -C k ≤ x k
    dsimp [C]
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    linarith
  · intro k
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hx i) (hw k true i))
    simp only [mul_one] at h
    rw [hc k true x] at h
    exact h.trans (le_max_left _ _)

/-- Feasible active equations that determine a unique point imply genuine extremality. -/
theorem extreme_of_active_unique {n : ℕ} (q : Fin n → E) (x : E)
    (hx : x ∈ poly q) (ids : Fin 3 → Fin n)
    (ha : ∀ k, dot (q (ids k)) x = 1)
    (hu : ∀ y : E, (∀ k, dot (q (ids k)) y = 1) → y = x) :
    x ∈ (poly q).extremePoints ℝ := by
  refine ⟨hx, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a, b, ha', hb', hab, heq⟩ := hseg
  apply hu
  intro k
  have he := congrArg (normal (q (ids k))) heq
  simp only [map_add, map_smul, smul_eq_mul] at he
  change a * dot (q (ids k)) y + b * dot (q (ids k)) z = dot (q (ids k)) x at he
  rw [ha k] at he
  have hy' := hy (ids k)
  have hz' := hz (ids k)
  nlinarith
/-- The converse geometric step: a nonzero direction annihilating all active
normals gives a genuine two-sided feasible perturbation. -/
theorem active_kernel_trivial {n : ℕ} (q : Fin n → E) (x : E)
    (hx : x ∈ (poly q).extremePoints ℝ) (d : E)
    (hd : ∀ i, dot (q i) x = 1 → dot (q i) d = 0) : d = 0 := by
  let U : Set ℝ := ⋂ i, {t | dot (q i) x = 1 ∨ dot (q i) (x + t • d) < 1}
  have ho : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    by_cases h : dot (q i) x = 1
    · simp [h]
    · simp only [h, false_or]
      exact isOpen_lt ((dot_continuous (q i)).comp
        (continuous_const.add (continuous_id.smul continuous_const))) continuous_const
  have hzero : (0 : ℝ) ∈ U := by
    apply Set.mem_iInter.mpr
    intro i
    by_cases h : dot (q i) x = 1
    · exact Or.inl h
    · exact Or.inr (by simpa using lt_of_le_of_ne (hx.1 i) h)
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hzero)
  let t : ℝ := min (-a) b / 2
  have ht : 0 < t := by dsimp [t]; exact half_pos (lt_min (by linarith [hab.1]) hab.2)
  have hta : a < -t := by have := min_le_left (-a) b; dsimp [t] at *; linarith
  have htb : t < b := by have := min_le_right (-a) b; dsimp [t] at *; linarith
  have feasible : ∀ r ∈ Set.Ioo a b, x + r • d ∈ poly q := by
    intro r hr i
    rcases Set.mem_iInter.mp (hsub hr) i with h | h
    · change (normal (q i)) (x + r • d) ≤ 1
      rw [map_add, map_smul]
      change dot (q i) x + r * dot (q i) d ≤ 1
      rw [hd i h, h]; simp
    · exact le_of_lt h
  have hp := feasible t ⟨by linarith [hab.1], htb⟩
  have hm := feasible (-t) ⟨hta, by linarith [hab.2]⟩
  have hs : x ∈ openSegment ℝ (x + t • d) (x + (-t) • d) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext k; simp; ring
  have he := hx.2 hp hm hs
  ext k
  have hk := congrFun he k
  change x k + t * d k = x k at hk
  have hz : t * d k = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ht)
theorem extreme_iff_active_kernel {n : ℕ} (q : Fin n → E) (x : E) :
    x ∈ (poly q).extremePoints ℝ ↔ x ∈ poly q ∧
      ∀ d : E, (∀ i, dot (q i) x = 1 → dot (q i) d = 0) → d = 0 := by
  constructor
  · intro hx
    exact ⟨hx.1, active_kernel_trivial q x hx⟩
  · rintro ⟨hx, hk⟩
    refine ⟨hx, ?_⟩
    intro y hy z hz hseg
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    have hd : y - x = 0 := by
      apply hk
      intro i hi
      have he := congrArg (normal (q i)) heq
      simp only [map_add, map_smul, smul_eq_mul] at he
      change a * dot (q i) y + b * dot (q i) z = dot (q i) x at he
      have hy' := hy i
      have hz' := hz i
      change (normal (q i)) (y - x) = 0
      rw [map_sub]
      change dot (q i) y - dot (q i) x = 0
      rw [hi] at *
      nlinarith
    exact sub_eq_zero.mp hd
theorem facetSection_extreme {n : ℕ} (q : Fin n → E) (i : Fin n) :
    IsExtreme ℝ (poly q) (facetSection q i) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hs
  refine ⟨hx, ?_⟩
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hs
  have he := congrArg (normal (q i)) heq
  simp only [map_add, map_smul, smul_eq_mul] at he
  change a * dot (q i) x + b * dot (q i) y = dot (q i) z at he
  rw [hz.2] at he
  have hx' := hx i
  have hy' := hy i
  nlinarith
end FullereneGeometry
