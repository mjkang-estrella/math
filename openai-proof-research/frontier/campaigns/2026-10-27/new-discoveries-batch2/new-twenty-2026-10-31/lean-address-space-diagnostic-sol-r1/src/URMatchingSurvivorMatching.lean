module
public import URMatchingSurvivorGraph
public import URMatchingDeletion
@[expose] public section
namespace URMatching
open scoped Classical
noncomputable def retainedInputs {N : ℕ} (h : ℕ) (σ : PermutationTuples N 100) : Finset (Fin N) :=
  Finset.univ.filter fun x => Sum.inl x ∉ removedVertices N h σ ∧
    Sum.inr (σ 0 x) ∉ removedVertices N h σ
noncomputable def firstEdge {N h : ℕ} (σ : PermutationTuples N 100)
    (x : retainedInputs h σ) : Sym2 (Survivor h σ) :=
  s(⟨Sum.inl x.val, (Finset.mem_filter.mp x.property).2.1⟩,
    ⟨Sum.inr (σ 0 x.val), (Finset.mem_filter.mp x.property).2.2⟩)
noncomputable def firstMatching {N : ℕ} (h : ℕ) (σ : PermutationTuples N 100) :
    Finset (Sym2 (Survivor h σ)) := (retainedInputs h σ).attach.image (firstEdge σ)

theorem firstEdge_injective {N h : ℕ} (σ : PermutationTuples N 100) :
    Function.Injective (firstEdge (h := h) σ) := by
  intro x y he
  have he' := Sym2.eq_iff.mp he
  rcases he' with he' | he'
  · apply Subtype.ext
    exact Sum.inl.inj (congrArg Subtype.val he'.1)
  · have bad := congrArg Subtype.val he'.1
    cases bad

theorem firstMatching_card {N h : ℕ} (σ : PermutationTuples N 100) :
    (firstMatching h σ).card = (retainedInputs h σ).card := by
  classical
  rw [firstMatching, Finset.card_image_of_injective _ (firstEdge_injective σ),
    Finset.card_attach]

theorem firstMatching_isMatching {N h : ℕ} (σ : PermutationTuples N 100) :
    IsMatching (survivorGraph h σ) (firstMatching h σ) := by
  classical
  constructor
  · intro e he
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp he
    exact ⟨0,rfl⟩
  · intro e he f hf v hve hvf
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hf
    have hx : v = ⟨Sum.inl x.val, (Finset.mem_filter.mp x.property).2.1⟩ ∨
        v = ⟨Sum.inr (σ 0 x.val), (Finset.mem_filter.mp x.property).2.2⟩ :=
      Sym2.mem_iff.mp hve
    have hy : v = ⟨Sum.inl y.val, (Finset.mem_filter.mp y.property).2.1⟩ ∨
        v = ⟨Sum.inr (σ 0 y.val), (Finset.mem_filter.mp y.property).2.2⟩ :=
      Sym2.mem_iff.mp hvf
    have hxy : x = y := by
      apply Subtype.ext
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Sum.inl.inj (congrArg Subtype.val (hx.symm.trans hy))
      · have bad := congrArg Subtype.val (hx.symm.trans hy); cases bad
      · have bad := congrArg Subtype.val (hx.symm.trans hy); cases bad
      · exact (σ 0).injective (Sum.inr.inj (congrArg Subtype.val (hx.symm.trans hy)))
    exact congrArg (firstEdge σ) hxy

theorem retainedInputs_bound {N h : ℕ} (σ : PermutationTuples N 100) :
    N ≤ (retainedInputs h σ).card + (removedVertices N h σ).card := by
  classical
  let K := retainedInputs h σ
  let D := removedVertices N h σ
  let L := (Finset.univ : Finset (Fin N)) \ K
  have lost (x : L) : Sum.inl x.val ∈ D ∨ Sum.inr (σ 0 x.val) ∈ D := by
    have hx := (Finset.mem_sdiff.mp x.property).2
    by_cases hl : Sum.inl x.val ∈ D
    · exact Or.inl hl
    · right
      by_contra hr
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl,hr⟩)
  let charge : L → D := fun x => if hx : Sum.inl x.val ∈ D then
    ⟨Sum.inl x.val,hx⟩ else ⟨Sum.inr (σ 0 x.val),(lost x).resolve_left hx⟩
  have hi : Function.Injective charge := by
    intro x y he
    have hv := congrArg Subtype.val he
    apply Subtype.ext
    by_cases hx : Sum.inl x.val ∈ D <;> by_cases hy : Sum.inl y.val ∈ D
    · simp only [charge, dite_eq_left hx, dite_eq_left hy] at hv
      exact Sum.inl.inj hv
    · simp only [charge, dite_eq_left hx, dite_eq_right hy] at hv
      cases hv
    · simp only [charge, dite_eq_right hx, dite_eq_left hy] at hv
      cases hv
    · simp only [charge, dite_eq_right hx, dite_eq_right hy] at hv
      exact (σ 0).injective (Sum.inr.inj hv)
  have hc : L.card ≤ D.card := Finset.card_le_card_of_injective hi
  have ht : L.card + K.card = N := by
    simpa [L] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ K)
  change N ≤ K.card + D.card
  omega

theorem firstMatching_retained {N h : ℕ} (σ : PermutationTuples N 100)
    (hd : 100 * (removedVertices N h σ).card < N) :
    99 * N < 100 * (firstMatching h σ).card := by
  rw [firstMatching_card]
  have hb := retainedInputs_bound (h := h) σ
  omega
end URMatching
