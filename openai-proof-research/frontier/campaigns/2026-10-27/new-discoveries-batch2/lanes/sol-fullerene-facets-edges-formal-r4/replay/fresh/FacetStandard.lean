import FacetDimension
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace FullereneGeometry

/-- The standard maximal nonempty proper convex-face definition of a facet. -/
def MaximalProperFace (P F : Set E) : Prop :=
  ConvexFace P F ∧ F.Nonempty ∧ F ≠ P ∧
    ∀ S, ConvexFace P S → S ≠ P → F ⊆ S → S = F

theorem section_ne_poly {n : ℕ} (q : Fin n → E) (i : Fin n) :
    facetSection q i ≠ poly q := by
  intro he
  have hz : (0:E) ∈ poly q := by intro j; simp [dot]
  have h := (he.symm ▸ hz).2
  norm_num [dot] at h

theorem geometricFacet_eq_section_of_subset {n : ℕ} (q : Fin n → E)
    {F : Set E} (hf : GeometricFacet (poly q) F) (i : Fin n)
    (hi : F ⊆ facetSection q i) : F = facetSection q i := by
  obtain ⟨l,c,_,_,he,hne,hd⟩ := hf
  have hs := section_dimension_le q i (hne.mono hi)
  have hv := vectorSpan_mono ℝ hi
  have hv' : vectorSpan ℝ F = vectorSpan ℝ (facetSection q i) :=
    Submodule.eq_of_le_of_finrank_le hv (by dsimp [affineDimension] at hd hs; omega)
  apply Set.Subset.antisymm hi
  obtain ⟨x,hx⟩ := hne
  intro y hy
  have hdif := vsub_mem_vectorSpan ℝ hy (hi hx)
  rw [← hv'] at hdif
  have hk := vectorSpan_le_plane l c (fun z hz => (he ▸ hz).2) hdif
  change l (y-x) = 0 at hk
  rw [map_sub] at hk
  rw [he]
  exact ⟨hy.1,by linarith [(he ▸ hx).2]⟩

/-- Equivalence with maximal proper faces, including arbitrary non-exposed
convex faces in the maximality quantifier. -/
theorem geometricFacet_iff_maximalProperFace {n : ℕ} (q : Fin n → E)
    (hd : ∀ i, affineDimension (facetSection q i) = 2) (F : Set E) :
    GeometricFacet (poly q) F ↔ MaximalProperFace (poly q) F := by
  constructor
  · intro hf
    have hne := hf.choose_spec.choose_spec.2.2.2.1
    have hp : F ≠ poly q := by
      obtain ⟨i,rfl⟩ := geometricFacet_exhaustion q hf
      exact section_ne_poly q i
    refine ⟨geometricFacet_convexFace (poly_convex q) hf,hne,hp,?_⟩
    intro S hS hSp hFS
    obtain ⟨i,hi⟩ := proper_face_subset_section q hS (hne.mono hFS) hSp
    have he := geometricFacet_eq_section_of_subset q hf i (hFS.trans hi)
    exact Set.Subset.antisymm (he.symm ▸ hi) hFS
  · rintro ⟨hF,hne,hp,hmax⟩
    obtain ⟨i,hi⟩ := proper_face_subset_section q hF hne hp
    have he := hmax (facetSection q i) (facetSection_convexFace q i) (section_ne_poly q i) hi
    rw [← he]
    exact section_is_geometricFacet q i (hne.mono hi) (hd i)
end FullereneGeometry
