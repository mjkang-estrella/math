module
public import URMatchingURSides
@[expose] public section
namespace URMatching
universe v
variable {V : Type v} [DecidableEq V]

/-- Arbitrary literal edge-set matching, with each edge oriented across a fixed
vertex partition. The indexing and all endpoint disjointness are proved. -/
theorem ur_oriented_empty_rectangle_sides (G : SimpleGraph V) (M : Finset (Sym2 V))
    (P : V → Prop) (ur : IsUR G M)
    (orient : ∀ a ∈ M, ∃ x y, P x ∧ ¬ P y ∧ a = s(x,y)) :
    ∃ A B : Finset V, A.card = M.card / 2 ∧ B.card = M.card / 2 ∧
      (∀ x ∈ A, P x) ∧ (∀ y ∈ B, ¬ P y) ∧
      Disjoint A B ∧ ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
  classical
  have ho : ∀ a : M, ∃ x y, P x ∧ ¬ P y ∧ a.val = s(x,y) :=
    fun a => orient a.val a.property
  choose x y hx hy he using ho
  let f : Sum M M → V := Sum.elim x y
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        have hi : x i ∈ i.val := by rw [he i]; simp
        have hj : x i ∈ j.val := by rw [he j]; simp [show x i = x j from hab]
        have hij := ur.1.2 i.val i.property j.val j.property (x i) hi hj
        exact congrArg Sum.inl (Subtype.ext hij)
      | inr j =>
        change x i = y j at hab
        exact False.elim (hy j (hab ▸ hx i))
    | inr i =>
      cases b with
      | inl j =>
        change y i = x j at hab
        exact False.elim (hy i (hab.symm ▸ hx j))
      | inr j =>
        have hi : y i ∈ i.val := by rw [he i]; simp
        have hj : y i ∈ j.val := by rw [he j]; simp [show y i = y j from hab]
        have hij := ur.1.2 i.val i.property j.val j.property (y i) hi hj
        exact congrArg Sum.inr (Subtype.ext hij)
  let e : Sum M M ↪ V := ⟨f, hf⟩
  have hedges : indexedEdges e (Equiv.refl M) = M := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      change s(x i, y i) ∈ M
      rw [← he i]
      exact i.property
    · intro ha
      exact Finset.mem_image.mpr ⟨⟨a,ha⟩, Finset.mem_univ _, (he ⟨a,ha⟩).symm⟩
  have hu : IsUR G (indexedEdges e (Equiv.refl M)) := hedges.symm ▸ ur
  obtain ⟨A, B, hA, hB, hleft, hright, hd, hempty⟩ := ur_indexed_empty_rectangle_sides G e hu
  refine ⟨A, B, by simpa using hA, by simpa using hB, ?_, ?_, hd, hempty⟩
  · intro w hw
    obtain ⟨i, rfl⟩ := hleft w hw
    exact hx i
  · intro w hw
    obtain ⟨i, rfl⟩ := hright w hw
    exact hy i
end URMatching
