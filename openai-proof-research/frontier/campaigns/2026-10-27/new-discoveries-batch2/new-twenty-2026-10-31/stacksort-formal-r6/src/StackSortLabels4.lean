import StackSortShuffle3Tuples

namespace StackSort.Round4
open Seeds2 Shuffle3
open Classical

/-- The literal section enumerator commutes with relabelling, including surjectivity. -/
theorem sections_map (f : ℕ → ℕ) (r : ℕ) (w : List ℕ) :
    sections r (w.map f) = (sections r w).image (List.map (List.map f)) := by
  induction r generalizing w with
  | zero =>
    by_cases h : w = []
    · simp [h,sections_zero]
    · simp [sections_zero,h]
  | succ r ih =>
    simp only [sections_succ,List.length_map,← List.map_drop,ih]
    rw [Finset.biUnion_image]
    apply Finset.biUnion_congr rfl
    intro k hk
    rw [Finset.image_image,Finset.image_image]
    apply Finset.image_congr
    intro G hG
    simp [List.map_take]

/-- Literal tuples on an arbitrary finite set of labels. -/
def labelledTuples (A : Finset ℕ) (r : ℕ) : Finset (List (List ℕ)) :=
  (labelWords A).biUnion (sections r)

/-- Every labelled tuple is the increasing relabelling of a literal standardized tuple. -/
theorem labelledTuples_eq_image (A : Finset ℕ) (r : ℕ) :
    labelledTuples A r = (tuples A.card r).image (tupleMap (labels A)) := by
  unfold labelledTuples tuples
  rw [labelWords_eq_image]
  simp only [Finset.image_biUnion,sections_map]
  rw [Finset.biUnion_image]
  rfl

 theorem labelledTuples_card (A : Finset ℕ) (r : ℕ) :
    (labelledTuples A r).card = (tuples A.card r).card := by
  rw [labelledTuples_eq_image]
  exact Finset.card_image_of_injective _ (tupleMap_injective _)

/-- Collision families over a prescribed label set, with no restriction beyond literal membership. -/
def labelledPairs (A : Finset ℕ) (r s : ℕ) :=
  ((labelledTuples A r ×ˢ labelledTuples A s).filter
    (fun p => output p.1 = output p.2))

noncomputable def labelledIrreducibles (A : Finset ℕ) (r s : ℕ) := by
  classical
  exact ((labelledTuples A r ×ˢ labelledTuples A s).filter
    (fun p => output p.1 = output p.2 ∧ Irreducible p.1 p.2))

theorem labelledPairs_eq_family (A : Finset ℕ) (r s : ℕ) :
    labelledPairs A r s = tupleFamily A
      ((tuples A.card r ×ˢ tuples A.card s).filter (fun p => output p.1 = output p.2)) := by
  ext p
  simp only [labelledPairs,labelledTuples_eq_image,tupleFamily,
    Finset.mem_filter,Finset.mem_product,Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨F,hF,hp⟩,⟨G,hG,hq⟩⟩,he⟩
    refine ⟨(F,G),⟨⟨hF,hG⟩,?_⟩,Prod.ext hp hq⟩
    exact (tuple_collision_iff (labels A) F G).mp (by simpa only [hp,hq] using he)
  · rintro ⟨⟨F,G⟩,⟨⟨hF,hG⟩,he⟩,hp⟩
    cases hp
    exact ⟨⟨⟨F,hF,rfl⟩,⟨G,hG,rfl⟩⟩,(tuple_collision_iff _ _ _).mpr he⟩

theorem labelledPairs_card (A : Finset ℕ) (r s : ℕ) :
    (labelledPairs A r s).card = XI A.card r s := by
  rw [labelledPairs_eq_family,tupleFamily_card]
  rfl

theorem labelledIrreducibles_eq_family (A : Finset ℕ) (r s : ℕ) :
    labelledIrreducibles A r s = tupleFamily A
      ((tuples A.card r ×ˢ tuples A.card s).filter
        (fun p => output p.1 = output p.2 ∧ Irreducible p.1 p.2)) := by
  classical
  ext p
  simp only [labelledIrreducibles,labelledTuples_eq_image,tupleFamily,
    Finset.mem_filter,Finset.mem_product,Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨F,hF,hp⟩,⟨G,hG,hq⟩⟩,he,hi⟩
    refine ⟨(F,G),⟨⟨hF,hG⟩,?_,?_⟩,Prod.ext hp hq⟩
    · exact (tuple_collision_iff (labels A) F G).mp (by simpa only [hp,hq] using he)
    · exact (irreducible_tupleMap_iff (labels A) F G).mp (by simpa only [hp,hq] using hi)
  · rintro ⟨⟨F,G⟩,⟨⟨hF,hG⟩,he,hi⟩,hp⟩
    cases hp
    exact ⟨⟨⟨F,hF,rfl⟩,⟨G,hG,rfl⟩⟩,(tuple_collision_iff _ _ _).mpr he,
      (irreducible_tupleMap_iff _ _ _).mpr hi⟩

theorem labelledIrreducibles_card (A : Finset ℕ) (r s : ℕ) :
    (labelledIrreducibles A r s).card = II A.card r s := by
  rw [labelledIrreducibles_eq_family,tupleFamily_card]
  rfl

end StackSort.Round4
