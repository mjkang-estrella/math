import Cayley382145Main

/-! # MathDB 382145: non-vacuity check of the native definitions

For the unit segment `[0,1] ⊆ ℝ^1` the actual facet normals are exactly `±1`, the native
Q-codegree evaluates to `2 > (1+1)/2`, and the main theorem applies. This is a sanity witness
only (optional, not part of the endpoint). -/

namespace Cayley382145

open Finset

/-- Generators of the unit segment. -/
def segV : Finset (Fin 1 → ℤ) := {0, fun _ => 1}

/-- The primitive vector `1 ∈ ℤ^1`. -/
def eOne : Fin 1 → ℤ := fun _ => 1

theorem intDot_one (x : Fin 1 → ℝ) : intDot eOne x = x 0 := by simp [intDot, eOne]

theorem intDot_negOne (x : Fin 1 → ℝ) : intDot (-eOne) x = -x 0 := by simp [intDot, eOne]

theorem zero_mem_segV : (0 : Fin 1 → ℤ) ∈ segV := by simp [segV]

theorem eOne_mem_segV : eOne ∈ segV :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem seg_full : affineSpan ℝ (latticeHull segV) = ⊤ := by
  have h0 : castPt (0 : Fin 1 → ℤ) ∈ latticeHull segV := castPt_mem_latticeHull zero_mem_segV
  have h1 : castPt eOne ∈ latticeHull segV := castPt_mem_latticeHull eOne_mem_segV
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)
    ⟨_, h0⟩, eq_top_iff]
  intro x _
  have hv : castPt eOne -ᵥ castPt (0 : Fin 1 → ℤ) ∈ vectorSpan ℝ (latticeHull segV) :=
    vsub_mem_vectorSpan (k := ℝ) h1 h0
  have hx : x = x 0 • (castPt eOne -ᵥ castPt (0 : Fin 1 → ℤ)) := by
    funext i
    obtain rfl := Subsingleton.elim i 0
    simp [castPt, eOne]
  rw [hx]
  exact Submodule.smul_mem _ _ hv

theorem primitive_fin_one {a : Fin 1 → ℤ} (ha : IsPrimitive a) : a = eOne ∨ a = -eOne := by
  have hu := ha (a 0) (fun i => by
    obtain rfl := Subsingleton.elim i 0
    exact dvd_rfl)
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    funext i
    obtain rfl := Subsingleton.elim i 0
    simp [eOne, h]
  · right
    funext i
    obtain rfl := Subsingleton.elim i 0
    simp [eOne, h]

theorem primitive_eOne : IsPrimitive eOne := fun _ hd => isUnit_of_dvd_one (hd 0)

theorem primitive_negOne : IsPrimitive (-eOne) := fun _ hd =>
  isUnit_of_dvd_one (dvd_neg.mp (hd 0))

theorem segV_nonempty : segV.Nonempty := ⟨0, zero_mem_segV⟩

theorem seg_offset_one : facetOffset (latticeHull segV) eOne = 0 := by
  obtain ⟨v₀, hv₀, h1, h2, -⟩ := facetOffset_latticeHull segV_nonempty eOne
  rw [h1]
  simp only [segV, Finset.mem_insert, Finset.mem_singleton] at hv₀
  rcases hv₀ with rfl | rfl
  · simp [zDot]
  · have := h2 0 zero_mem_segV
    simp [zDot, eOne] at this

theorem seg_offset_negOne : facetOffset (latticeHull segV) (-eOne) = -1 := by
  obtain ⟨v₀, hv₀, h1, h2, -⟩ := facetOffset_latticeHull segV_nonempty (-eOne)
  rw [h1]
  simp only [segV, Finset.mem_insert, Finset.mem_singleton] at hv₀
  rcases hv₀ with rfl | rfl
  · have := h2 eOne eOne_mem_segV
    simp [zDot, eOne] at this
  · simp [zDot, eOne]

theorem seg_facet_one : IsFacetNormal (latticeHull segV) eOne := by
  refine ⟨primitive_eOne, fun x hx => facetOffset_le segV_nonempty eOne hx,
    ⟨castPt 0, castPt_mem_latticeHull zero_mem_segV, ?_⟩, ?_⟩
  · rw [seg_offset_one, intDot_one]
    simp [castPt]
  · have hsub : facetFace (latticeHull segV) eOne ⊆ {castPt (0 : Fin 1 → ℤ)} := by
      rintro x ⟨_, hx⟩
      rw [seg_offset_one, intDot_one] at hx
      rw [Set.mem_singleton_iff]
      funext i
      obtain rfl := Subsingleton.elim i 0
      simp [castPt, hx]
    have hle := vectorSpan_mono (k := ℝ) hsub
    rw [vectorSpan_singleton] at hle
    have h0 : Module.finrank ℝ (affineSpan ℝ (facetFace (latticeHull segV) eOne)).direction = 0 := by
      rw [direction_affineSpan, le_bot_iff.mp hle, finrank_bot]
    simpa using h0

theorem seg_facet_negOne : IsFacetNormal (latticeHull segV) (-eOne) := by
  refine ⟨primitive_negOne, fun x hx => facetOffset_le segV_nonempty (-eOne) hx,
    ⟨castPt eOne, castPt_mem_latticeHull eOne_mem_segV, ?_⟩, ?_⟩
  · rw [seg_offset_negOne, intDot_negOne]
    simp [castPt, eOne]
  · have hsub : facetFace (latticeHull segV) (-eOne) ⊆ {castPt eOne} := by
      rintro x ⟨_, hx⟩
      rw [seg_offset_negOne, intDot_negOne] at hx
      rw [Set.mem_singleton_iff]
      funext i
      obtain rfl := Subsingleton.elim i 0
      have hx' : x 0 = 1 := by linarith
      simp [castPt, eOne, hx']
    have hle := vectorSpan_mono (k := ℝ) hsub
    rw [vectorSpan_singleton] at hle
    have h0 : Module.finrank ℝ
        (affineSpan ℝ (facetFace (latticeHull segV) (-eOne))).direction = 0 := by
      rw [direction_affineSpan, le_bot_iff.mp hle, finrank_bot]
    simpa using h0

/-- The actual facet normals of the unit segment are exactly `±1`. -/
theorem seg_facet_iff (a : Fin 1 → ℤ) :
    IsFacetNormal (latticeHull segV) a ↔ a = eOne ∨ a = -eOne := by
  constructor
  · exact fun h => primitive_fin_one h.1
  · rintro (rfl | rfl)
    · exact seg_facet_one
    · exact seg_facet_negOne

/-- The native Q-codegree of the unit segment is `2`. -/
theorem seg_qCodegree : qCodegree (latticeHull segV) = 2 := by
  have hT : IsGreatest {s : ℝ | 0 < s ∧ (adjointSet (latticeHull segV) s).Nonempty} (1 / 2) := by
    refine ⟨⟨by norm_num, fun _ => 1 / 2, fun a ha => ?_⟩, ?_⟩
    · rcases (seg_facet_iff a).mp ha with rfl | rfl
      · rw [seg_offset_one, intDot_one]
        norm_num
      · rw [seg_offset_negOne, intDot_negOne]
        norm_num
    · rintro s ⟨_, x, hx⟩
      have h1 := hx eOne seg_facet_one
      have h2 := hx (-eOne) seg_facet_negOne
      rw [seg_offset_one, intDot_one] at h1
      rw [seg_offset_negOne, intDot_negOne] at h2
      linarith
  rw [qCodegree, hT.csSup_eq]
  norm_num

/-- The hypothesis of the endpoint is satisfiable, and the endpoint applies. -/
theorem seg_hypothesis : (((1 : ℕ) : ℝ) + 1) / 2 < qCodegree (latticeHull segV) := by
  rw [seg_qCodegree]
  norm_num

theorem seg_cayley : ∃ k t : ℕ,
    (k : ℤ) ≤ ⌊2 * (((1 : ℕ) : ℝ) + 1 - qCodegree (latticeHull segV))⌋ ∧
      IsCayleySumIn (latticeHull segV) k t :=
  dickensteinNill_cayley 1 (latticeHull segV) segV rfl seg_full seg_hypothesis

end Cayley382145
