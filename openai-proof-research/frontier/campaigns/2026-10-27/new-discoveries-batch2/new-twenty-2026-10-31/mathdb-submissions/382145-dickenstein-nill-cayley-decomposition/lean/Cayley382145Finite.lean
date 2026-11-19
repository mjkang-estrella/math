import Cayley382145Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # MathDB 382145: the actual facet normals of a full-dimensional lattice hull are finite

Facets are the native `(n-1)`-dimensional faces. Two facet normals touching the same generators
cut out the same face; the dimension condition forces equal kernels, positivity of the ratio
follows from full dimensionality, and primitivity (via Bézout) forces equality. -/

namespace Cayley382145

open Finset

variable {n : ℕ}

theorem facetOffset_le {V : Finset (Fin n → ℤ)} (hV : V.Nonempty) (c : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ latticeHull V) : facetOffset (latticeHull V) c ≤ intDot c x := by
  obtain ⟨v₀, -, h1, -, h3⟩ := facetOffset_latticeHull hV c
  rw [h1]
  exact h3 x hx

theorem castPt_mem_latticeHull {V : Finset (Fin n → ℤ)} {v : Fin n → ℤ} (hv : v ∈ V) :
    castPt v ∈ latticeHull V :=
  subset_convexHull ℝ _ ⟨v, hv, rfl⟩

theorem intDot_single (c : Fin n → ℤ) (j : Fin n) : intDot c (Pi.single j 1) = (c j : ℝ) := by
  simp [intDot, Pi.single_apply]

/-- If two normals touch the same generators, the face of the first lies in the facet
hyperplane of the second. -/
theorem face_sub_of_touch {V : Finset (Fin n → ℤ)} (hV : V.Nonempty) {a a' : Fin n → ℤ}
    (htouch : ∀ v ∈ V, (intDot a (castPt v) = facetOffset (latticeHull V) a ↔
      intDot a' (castPt v) = facetOffset (latticeHull V) a'))
    {x : Fin n → ℝ} (hx : x ∈ facetFace (latticeHull V) a) :
    intDot a' x = facetOffset (latticeHull V) a' := by
  obtain ⟨hxP, hxb⟩ := hx
  have hxP' : x ∈ convexHull ℝ ((V.image castPt : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    rw [Finset.coe_image]
    exact hxP
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxP'
  have hlin : ∀ c : Fin n → ℤ, intDot c x = ∑ y ∈ V.image castPt, w y * intDot c y := by
    intro c
    rw [← hwx, ← intDotL_apply, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, smul_eq_mul, intDotL_apply]
  have hlow : ∀ c : Fin n → ℤ, ∀ y ∈ V.image castPt, facetOffset (latticeHull V) c ≤ intDot c y := by
    intro c y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact facetOffset_le hV c (castPt_mem_latticeHull hv)
  have hexp : ∀ c : Fin n → ℤ, intDot c x - facetOffset (latticeHull V) c =
      ∑ y ∈ V.image castPt, w y * (intDot c y - facetOffset (latticeHull V) c) := by
    intro c
    rw [Finset.sum_congr rfl (fun y _ => mul_sub (w y) _ _), Finset.sum_sub_distrib, ← hlin c,
      ← Finset.sum_mul, hw1, one_mul]
  have hsum0 : ∑ y ∈ V.image castPt, w y * (intDot a y - facetOffset (latticeHull V) a) = 0 := by
    rw [← hexp a, hxb, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
    mul_nonneg (hw0 y hy) (sub_nonneg.mpr (hlow a y hy)))).mp hsum0
  have hsum1 : ∑ y ∈ V.image castPt, w y * (intDot a' y - facetOffset (latticeHull V) a') = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rcases mul_eq_zero.mp (hterm _ hy) with h | h
    · rw [h, zero_mul]
    · rw [(htouch v hv).mp (sub_eq_zero.mp h), sub_self, mul_zero]
  have := hexp a'
  rw [hsum1] at this
  linarith

/-- The dimension condition on a facet forces kernel inclusion. -/
theorem ker_le_of_face {P : Set (Fin n → ℝ)} {a a' : Fin n → ℤ} (ha : a ≠ 0)
    (hdim : Module.finrank ℝ (affineSpan ℝ (facetFace P a)).direction = n - 1)
    (hsub : ∀ x ∈ facetFace P a, intDot a' x = facetOffset P a') :
    LinearMap.ker (intDotL a) ≤ LinearMap.ker (intDotL a') := by
  set E := (affineSpan ℝ (facetFace P a)).direction with hE
  have hEle : E ≤ LinearMap.ker (intDotL a) ⊓ LinearMap.ker (intDotL a') := by
    rw [hE, direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hx' := hsub x hx
    have hy' := hsub y hy
    have hxa := hx.2
    have hya := hy.2
    simp only [SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker, vsub_eq_sub, map_sub,
      intDotL_apply]
    constructor <;> linarith
  have hrange : Module.finrank ℝ (LinearMap.range (intDotL a)) = 1 := by
    apply le_antisymm
    · calc Module.finrank ℝ (LinearMap.range (intDotL a)) ≤ Module.finrank ℝ ℝ :=
            Submodule.finrank_le _
        _ = 1 := Module.finrank_self ℝ
    · rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      intro h0
      obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
      have := LinearMap.congr_fun h0 (Pi.single i 1)
      rw [intDotL_apply, intDot_single, LinearMap.zero_apply] at this
      exact hi (by exact_mod_cast this)
  have hker : Module.finrank ℝ (LinearMap.ker (intDotL a)) = n - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (intDotL a)
    rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  by_contra hnot
  have hlt : LinearMap.ker (intDotL a) ⊓ LinearMap.ker (intDotL a') < LinearMap.ker (intDotL a) :=
    lt_of_le_of_ne inf_le_left (fun h => hnot (inf_eq_left.mp h))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_mono hEle
  omega

/-- Kernel inclusion gives proportional integer vectors. -/
theorem prop_of_ker_le {a a' : Fin n → ℤ}
    (hker : LinearMap.ker (intDotL a) ≤ LinearMap.ker (intDotL a')) (i₀ j : Fin n) :
    a i₀ * a' j = a' i₀ * a j := by
  have hx : ((a i₀ : ℝ) • (Pi.single j 1 : Fin n → ℝ) - (a j : ℝ) • Pi.single i₀ 1) ∈
      LinearMap.ker (intDotL a) := by
    rw [LinearMap.mem_ker, map_sub, map_smul, map_smul, intDotL_apply, intDotL_apply,
      intDot_single, intDot_single, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
  have h := hker hx
  rw [LinearMap.mem_ker, map_sub, map_smul, map_smul, intDotL_apply, intDotL_apply,
    intDot_single, intDot_single, smul_eq_mul, smul_eq_mul, sub_eq_zero] at h
  have h' : ((a i₀ * a' j : ℤ) : ℝ) = ((a' i₀ * a j : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h'

/-- Primitive, positively proportional integer vectors are equal. -/
theorem eq_of_prop {a a' : Fin n → ℤ} (ha : IsPrimitive a) (ha' : IsPrimitive a') (i₀ : Fin n)
    (hprop : ∀ j, a i₀ * a' j = a' i₀ * a j) (hpos : 0 < a i₀ * a' i₀) : a = a' := by
  obtain ⟨c, hc⟩ := ha.exists_bezout
  obtain ⟨c', hc'⟩ := ha'.exists_bezout
  set p := a i₀ with hp
  set q := a' i₀ with hq
  have hu : p * (∑ j, c j * a' j) = q := by
    calc p * (∑ j, c j * a' j) = ∑ j, c j * (p * a' j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, c j * (q * a j) := Finset.sum_congr rfl fun j _ => by rw [hprop j]
      _ = q * ∑ j, c j * a j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = q := by rw [hc, mul_one]
  have hu' : q * (∑ j, c' j * a j) = p := by
    calc q * (∑ j, c' j * a j) = ∑ j, c' j * (q * a j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, c' j * (p * a' j) := Finset.sum_congr rfl fun j _ => by rw [hprop j]
      _ = p * ∑ j, c' j * a' j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = p := by rw [hc', mul_one]
  have hp0 : p ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have huu : (∑ j, c j * a' j) * (∑ j, c' j * a j) = 1 := by
    apply mul_left_cancel₀ hp0
    rw [← mul_assoc, hu, hu', mul_one]
  have hqp : q = p := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one huu with h | h
    · rw [← hu, h, mul_one]
    · exfalso
      rw [h] at hu
      have : p * q = -(p * p) := by rw [← hu]; ring
      nlinarith [mul_self_nonneg p]
  funext j
  have := hprop j
  rw [hqp] at this
  exact (mul_left_cancel₀ hp0 this).symm

theorem zDot_prop {a a' : Fin n → ℤ} (i₀ : Fin n) (hprop : ∀ j, a i₀ * a' j = a' i₀ * a j)
    (v : Fin n → ℤ) : a i₀ * zDot a' v = a' i₀ * zDot a v := by
  simp only [zDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, hprop j, mul_assoc]

/-- Two facet normals touching the same generators coincide. -/
theorem facetNormal_eq_of_touch {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤)
    {a a' : Fin n → ℤ} (ha : IsFacetNormal (latticeHull V) a) (ha' : IsFacetNormal (latticeHull V) a')
    (htouch : ∀ v ∈ V, (intDot a (castPt v) = facetOffset (latticeHull V) a ↔
      intDot a' (castPt v) = facetOffset (latticeHull V) a')) : a = a' := by
  have hV := nonempty_of_full hfull
  have hane := ha.1.ne_zero
  have hker := ker_le_of_face hane ha.2.2.2 (fun x hx => face_sub_of_touch hV htouch hx)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hane
  have hprop := prop_of_ker_le hker i₀
  obtain ⟨v₀, hv₀, hoff, hmin, -⟩ := facetOffset_latticeHull hV a
  have htv₀ : intDot a' (castPt v₀) = facetOffset (latticeHull V) a' :=
    (htouch v₀ hv₀).mp (by rw [intDot_castPt, hoff])
  obtain ⟨v₁, hv₁, hne⟩ := exists_zDot_ne_of_full hfull hane (zDot a v₀)
  have hD : 0 < zDot a v₁ - zDot a v₀ := by
    have := hmin v₁ hv₁
    omega
  have hD' : 0 ≤ zDot a' v₁ - zDot a' v₀ := by
    have h1 := facetOffset_le hV a' (castPt_mem_latticeHull hv₁)
    rw [← htv₀, intDot_castPt, intDot_castPt] at h1
    have h2 : zDot a' v₀ ≤ zDot a' v₁ := by exact_mod_cast h1
    omega
  have hrel : a i₀ * (zDot a' v₁ - zDot a' v₀) = a' i₀ * (zDot a v₁ - zDot a v₀) := by
    rw [mul_sub, mul_sub, zDot_prop i₀ hprop, zDot_prop i₀ hprop]
  have hq0 : a' i₀ ≠ 0 := by
    intro hq
    apply ha'.1.ne_zero
    funext j
    have := hprop j
    rw [hq, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hi₀
  have hpq : 0 ≤ a i₀ * a' i₀ := by
    rcases lt_or_ge (a i₀ * a' i₀) 0 with h | h
    · exfalso
      have h1 : a i₀ * a' i₀ * (zDot a v₁ - zDot a v₀) =
          a i₀ * a i₀ * (zDot a' v₁ - zDot a' v₀) := by
        linear_combination (-(a i₀)) * hrel
      have h2 := mul_neg_of_neg_of_pos h hD
      have h3 := mul_nonneg (mul_self_nonneg (a i₀)) hD'
      linarith
    · exact h
  have hpos : 0 < a i₀ * a' i₀ := lt_of_le_of_ne hpq (Ne.symm (mul_ne_zero hi₀ hq0))
  exact eq_of_prop ha.1 ha'.1 i₀ hprop hpos

open Classical in
/-- Generators touched by the facet hyperplane of `a`. -/
noncomputable def touchSet (V : Finset (Fin n → ℤ)) (a : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  V.filter (fun v => intDot a (castPt v) = facetOffset (latticeHull V) a)

theorem mem_touchSet {V : Finset (Fin n → ℤ)} {a v : Fin n → ℤ} :
    v ∈ touchSet V a ↔ v ∈ V ∧ intDot a (castPt v) = facetOffset (latticeHull V) a := by
  unfold touchSet
  exact Finset.mem_filter

/-- The set of actual primitive facet normals of a full-dimensional lattice hull is finite. -/
theorem facetNormals_finite {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤) :
    {a | IsFacetNormal (latticeHull V) a}.Finite := by
  apply Set.Finite.of_finite_image (f := touchSet V)
  · apply V.powerset.finite_toSet.subset
    rintro _ ⟨a, -, rfl⟩
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro v hv
    exact (mem_touchSet.mp hv).1
  · intro a ha a' ha' hφ
    apply facetNormal_eq_of_touch hfull ha ha'
    intro v hv
    have h := Finset.ext_iff.mp hφ v
    rw [mem_touchSet, mem_touchSet] at h
    exact ⟨fun h1 => (h.mp ⟨hv, h1⟩).2, fun h1 => (h.mpr ⟨hv, h1⟩).2⟩

end Cayley382145
