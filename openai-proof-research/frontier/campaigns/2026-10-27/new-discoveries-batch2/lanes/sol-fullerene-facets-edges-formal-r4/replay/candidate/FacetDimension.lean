import FaceCore
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Exposed
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace FullereneGeometry

def affineDimension (F : Set E) : ℕ := Module.finrank ℝ (vectorSpan ℝ F)

/-- Literal two-dimensional supporting face, quantified over real functionals. -/
def GeometricFacet (P F : Set E) : Prop :=
  ∃ (l : E →ₗ[ℝ] ℝ) (c : ℝ), l ≠ 0 ∧
    (∀ x ∈ P, l x ≤ c) ∧ F = {x ∈ P | l x = c} ∧
    F.Nonempty ∧ affineDimension F = 2

theorem vectorSpan_le_plane {F : Set E} (l : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hf : ∀ x ∈ F, l x = c) : vectorSpan ℝ F ≤ l.ker := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro v ⟨x,hx,y,hy,rfl⟩
  change l (x-y) = 0
  rw [map_sub,hf x hx,hf y hy,sub_self]

theorem section_dimension_le {n : ℕ} (q : Fin n → E) (i : Fin n)
    (hne : (facetSection q i).Nonempty) : affineDimension (facetSection q i) ≤ 2 := by
  obtain ⟨x,hx⟩ := hne
  have hk : (normal (q i)).ker ≠ ⊤ := by
    intro h
    have hxk : x ∈ (normal (q i)).ker := by rw [h]; trivial
    have : dot (q i) x = 0 := hxk
    linarith [hx.2]
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hk)
  have hle : affineDimension (facetSection q i) ≤ Module.finrank ℝ (normal (q i)).ker :=
    Submodule.finrank_mono (vectorSpan_le_plane (F := facetSection q i) (normal (q i)) 1
    (fun _ h => h.2))
  have he : Module.finrank ℝ E = 3 := Module.finrank_fin_fun ℝ
  have htopp : Module.finrank ℝ (⊤ : Submodule ℝ E) = 3 := by simp
  dsimp [affineDimension] at hle ⊢
  omega

theorem section_dimension_eq {n : ℕ} (q : Fin n → E) (i : Fin n)
    (hn : ¬ Collinear ℝ (facetSection q i))
    (hne : (facetSection q i).Nonempty) : affineDimension (facetSection q i) = 2 := by
  have hle := section_dimension_le q i hne
  have hgt : ¬ affineDimension (facetSection q i) ≤ 1 := by
    exact fun h => hn (collinear_iff_finrank_le_one.mpr h)
  omega

theorem facetSection_convexFace {n : ℕ} (q : Fin n → E) (i : Fin n) :
    ConvexFace (poly q) (facetSection q i) := by
  refine ⟨?_,facetSection_extreme q i⟩
  intro x hx y hy a b ha hb hab
  refine ⟨poly_convex q hx.1 hy.1 ha hb hab, ?_⟩
  change (normal (q i)) (a • x + b • y) = 1
  rw [map_add,map_smul,map_smul]
  change a * dot (q i) x + b * dot (q i) y = 1
  rw [hx.2,hy.2]; linarith

theorem section_is_geometricFacet {n : ℕ} (q : Fin n → E) (i : Fin n)
    (hne : (facetSection q i).Nonempty)
    (hd : affineDimension (facetSection q i) = 2) :
    GeometricFacet (poly q) (facetSection q i) := by
  refine ⟨normal (q i),1,?_,fun x hx => hx i,rfl,hne,hd⟩
  intro h
  obtain ⟨x,hx⟩ := hne
  have : dot (q i) x = 0 := congrArg (fun l : E →ₗ[ℝ] ℝ => l x) h
  linarith [hx.2]

theorem geometricFacet_convexFace {P F : Set E} (hc : Convex ℝ P)
    (hf : GeometricFacet P F) : ConvexFace P F := by
  obtain ⟨l,c,_,hb,rfl,_,_⟩ := hf
  constructor
  · intro x hx y hy a b ha hb' hab
    refine ⟨hc hx.1 hy.1 ha hb' hab,?_⟩
    rw [map_add,map_smul,map_smul,hx.2,hy.2]
    change a*c+b*c=c
    nlinarith [congrArg (fun t : ℝ => t*c) hab]
  · refine ⟨fun _ h => h.1,?_⟩
    intro x hx y hy z hz hs
    refine ⟨hx,?_⟩
    obtain ⟨a,b,ha,hb',hab,he⟩ := hs
    have h := congrArg l he
    rw [map_add,map_smul,map_smul,hz.2] at h
    change a*l x+b*l y=c at h
    have hx' := hb x hx
    have hy' := hb y hy
    apply le_antisymm hx'
    by_contra hn
    have hh : l x < c := lt_of_not_ge hn
    nlinarith [mul_pos ha (sub_pos.mpr hh),
      mul_nonneg hb'.le (sub_nonneg.mpr hy'), congrArg (fun t : ℝ => t*c) hab]

/-- Arbitrary real supporting facets are exhausted, not merely the indexed sections. -/
theorem geometricFacet_exhaustion {n : ℕ} (q : Fin n → E) {F : Set E}
    (hf : GeometricFacet (poly q) F) : ∃ i, F = facetSection q i := by
  obtain ⟨l,c,hl,hb,he,hne,hd⟩ := hf
  have hp : F ≠ poly q := by
    intro h
    have hz : (0:E) ∈ F := h.symm ▸ (by intro i; simp [dot])
    have hc : c = 0 := by have := (he ▸ hz).2; simpa using this.symm
    have hm : ∀ x ∈ poly q, l x = 0 := fun x hx => hc ▸ (he ▸ (h.symm ▸ hx)).2
    -- A strict point of the ambient polytope permits a small step in every direction.
    have hs := zero_interior q
    have hopen := (isOpen_interior.mem_nhds hs)
    have hn : l = 0 := by
      apply LinearMap.ext
      intro x
      have ht : Continuous (fun t : ℝ => t • x) := continuous_id.smul continuous_const
      have hopen' : interior (poly q) ∈ nhds ((0:ℝ) • x) := by simpa using hopen
      have hh : ∀ᶠ t : ℝ in nhds 0, t • x ∈ poly q := by
        filter_upwards [ht.continuousAt.preimage_mem_nhds hopen'] with t ht
        exact interior_subset ht
      obtain ⟨a,b,hab,hab'⟩ := mem_nhds_iff_exists_Ioo_subset.mp hh
      have ht' : 0 < b/2 := by linarith [hab.2]
      have hx := hm ((b/2) • x) (hab' ⟨by linarith [hab.1,hab.2],by linarith [hab.2]⟩)
      rw [map_smul] at hx
      exact (mul_eq_zero.mp hx).resolve_left ht'.ne'
    exact hl hn
  obtain ⟨i,hi⟩ := proper_face_subset_section q
    (geometricFacet_convexFace (poly_convex q) ⟨l,c,hl,hb,he,hne,hd⟩) hne hp
  refine ⟨i,Set.Subset.antisymm hi ?_⟩
  have hs := section_dimension_le q i (hne.mono hi)
  have hv := vectorSpan_mono ℝ hi
  have hv' : vectorSpan ℝ F = vectorSpan ℝ (facetSection q i) :=
    Submodule.eq_of_le_of_finrank_le hv (by dsimp [affineDimension] at hd hs; omega)
  obtain ⟨x,hx⟩ := hne
  intro y hy
  have hdif := vsub_mem_vectorSpan ℝ hy (hi hx)
  rw [← hv'] at hdif
  have hk := vectorSpan_le_plane l c (fun z hz => (he ▸ hz).2) hdif
  change l (y-x) = 0 at hk
  rw [map_sub] at hk
  rw [he]
  exact ⟨hy.1,by linarith [(he ▸ hx).2]⟩

theorem not_collinear_of_minor (a b c : E) (j k : Fin 3)
    (hm : (b j-a j)*(c k-a k)-(b k-a k)*(c j-a j) ≠ 0) :
    ¬ Collinear ℝ ({a,b,c} : Set E) := by
  intro h
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c}:Set E))).mp h
  obtain ⟨r,hr⟩ := hv b (by simp)
  obtain ⟨s,hs⟩ := hv c (by simp)
  apply hm
  rw [hr,hs]
  change (r*v j+a j-a j)*(s*v k+a k-a k)-
    (r*v k+a k-a k)*(s*v j+a j-a j)=0
  ring
end FullereneGeometry
