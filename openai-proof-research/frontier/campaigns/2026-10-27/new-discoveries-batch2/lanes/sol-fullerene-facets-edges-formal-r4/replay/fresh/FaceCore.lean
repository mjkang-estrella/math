import Literal
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace FullereneGeometry

/-- A genuine convex face, using mathlib's segment definition. -/
def ConvexFace (P F : Set E) : Prop := Convex ℝ F ∧ IsExtreme ℝ P F

theorem face_eq_of_strict_point {n : ℕ} (q : Fin n → E) {F : Set E}
    (hf : IsExtreme ℝ (poly q) F) {x : E} (hx : x ∈ F)
    (hs : ∀ i, dot (q i) x < 1) : F = poly q := by
  apply Set.Subset.antisymm hf.subset
  intro y hy
  let U : Set ℝ := ⋂ i, {t | dot (q i) (x + t • (x-y)) < (1 : ℝ)}
  have ho : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt ((dot_continuous (q i)).comp
      (continuous_const.add (continuous_id.smul continuous_const))) continuous_const
  have hz : (0 : ℝ) ∈ U := by simpa [U] using hs
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hz)
  let t := b/2
  have ht : 0 < t := by dsimp [t]; linarith [hab.2]
  have hp : x + t • (x-y) ∈ poly q := by
    intro i
    exact (Set.mem_iInter.mp (hsub ⟨by dsimp [t]; linarith [hab.1,hab.2],
      by dsimp [t]; linarith [hab.2]⟩) i).le
  apply hf.left_mem_of_mem_openSegment hy hp hx
  refine ⟨t/(1+t), 1/(1+t), div_pos ht (by linarith),
    div_pos (by norm_num) (by linarith), ?_, ?_⟩
  · field_simp; ring
  · ext k
    change t/(1+t)*y k + 1/(1+t)*(x k+t*(x k-y k)) = x k
    field_simp; ring

/-- Finite averaging produces a point strict on any specified inequalities,
provided each can be strict somewhere on the convex face. -/
theorem exists_strict_point {n : ℕ} (q : Fin n → E) {F : Set E}
    (hc : Convex ℝ F) (hsub : F ⊆ poly q) (hne : F.Nonempty)
    (hw : ∀ i, ∃ x ∈ F, dot (q i) x < 1) (s : Finset (Fin n)) :
    ∃ x ∈ F, ∀ i ∈ s, dot (q i) x < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => obtain ⟨x,hx⟩ := hne; exact ⟨x,hx,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨x,hx,hxs⟩ := ih
    obtain ⟨y,hy,hyi⟩ := hw i
    refine ⟨(1/2:ℝ) • x + (1/2:ℝ) • y,
      hc hx hy (by norm_num) (by norm_num) (by norm_num), ?_⟩
    intro j hj
    change (normal (q j)) ((1/2:ℝ) • x + (1/2:ℝ) • y) < 1
    rw [map_add,map_smul,map_smul]
    change 1/2 * dot (q j) x + 1/2 * dot (q j) y < 1
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have := hsub hx j; linarith
    · have := hxs j hj; have := hsub hy j; linarith

/-- Every nonempty proper convex face is contained in a defining section.
No relative-interior or exposed-face hypothesis is used. -/
theorem proper_face_subset_section {n : ℕ} (q : Fin n → E) {F : Set E}
    (hf : ConvexFace (poly q) F) (hne : F.Nonempty) (hp : F ≠ poly q) :
    ∃ i, F ⊆ facetSection q i := by
  classical
  by_contra h
  have hw : ∀ i, ∃ x ∈ F, dot (q i) x < 1 := by
    intro i
    have hn : ¬ F ⊆ facetSection q i := fun hs => h ⟨i,hs⟩
    obtain ⟨x,hx,hxi⟩ := Set.not_subset.mp hn
    refine ⟨x,hx,lt_of_le_of_ne (hf.2.subset hx i) ?_⟩
    intro he
    exact hxi ⟨hf.2.subset hx,he⟩
  obtain ⟨x,hx,hs⟩ := exists_strict_point q hf.1 hf.2.subset hne hw Finset.univ
  exact hp (face_eq_of_strict_point q hf.2 hx (fun i => hs i (Finset.mem_univ i)))

theorem section_extremePoints_of_complete {n m : ℕ} (q : Fin n → E)
    (p : Fin m → E) (hv : (poly q).extremePoints ℝ = Set.range p) (i : Fin n) :
    (facetSection q i).extremePoints ℝ = {x ∈ Set.range p | dot (q i) x = 1} := by
  rw [(facetSection_extreme q i).extremePoints_eq, hv]
  ext x
  constructor
  · rintro ⟨hx,hp⟩; exact ⟨hp,hx.2⟩
  · rintro ⟨hp,hi⟩
    have h := hv.symm ▸ hp
    exact ⟨⟨h.1,hi⟩,hp⟩
end FullereneGeometry
