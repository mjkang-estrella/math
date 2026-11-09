import StackSortDeletion4
namespace StackSort.Del5
open Seeds2 Round4

theorem childrenTuple_flatten (c : Children) :
    (childrenTuple c).flatten = c.parts.1 ++ c.parts.2 := by
  cases c with
  | leaf => rfl
  | unary b w => cases b <;> simp [childrenTuple, Children.parts]
  | binary L R => simp [childrenTuple, Children.parts]

/-- Cancelling the maximum gives precisely the smaller literal label set. -/
theorem root_labels_iff (m : ℕ) (A : List (List ℕ)) (c : Children) :
    (A ++ [rootWord m c.parts]).flatten ∈ words (m+1) ↔
    (A ++ childrenTuple c).flatten ∈ words m := by
  rw [mem_words, mem_words]
  have hp : (A ++ [rootWord m c.parts]).flatten.Perm
      (m :: (A ++ childrenTuple c).flatten) := by
    simpa [rootWord, childrenTuple_flatten, List.append_assoc] using
      (List.perm_middle (a := m) (l₁ := A.flatten ++ c.parts.1) (l₂ := c.parts.2))
  have hq : (List.range (m+1)).Perm (m :: List.range m) := by
    rw [List.range_succ]
    exact List.perm_append_comm
  constructor
  · intro h
    exact (hp.symm.trans (h.trans hq)).cons_inv
  · intro h
    exact hp.trans ((h.cons m).trans hq.symm)

/-- Exact literal membership, including the zero-size and zero-child cases. -/
theorem delete_last_mem_iff (m : ℕ) (A : List (List ℕ)) (c : Children) :
    A ++ [rootWord m c.parts] ∈ tuples (m+1) (A.length+1) ↔
    A ++ childrenTuple c ∈ tuples m (A.length + childrenArity c) := by
  rw [mem_tuples, mem_tuples, root_labels_iff]
  simp only [List.length_append, List.length_singleton, childrenTuple_length, true_and]
  have hc := childrenTuple_nonempty c
  have hr : rootWord m c.parts ≠ [] := by simp [rootWord]
  constructor
  · rintro ⟨hl, hn⟩
    refine ⟨hl, ?_⟩
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hn w (List.mem_append_left _ hw)
    · exact hc w hw
  · rintro ⟨hl, hn⟩
    refine ⟨hl, ?_⟩
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hn w (List.mem_append_left _ hw)
    · simpa only [List.mem_singleton.mp hw] using hr

/-- Child labels of a reconstructed literal tuple are strictly below its root. -/
theorem children_below_of_mem {m : ℕ} {A : List (List ℕ)} {c : Children}
    (h : A ++ childrenTuple c ∈ tuples m (A.length + childrenArity c)) :
    Below m c.parts.1 ∧ Below m c.parts.2 := by
  have hp := mem_words.mp (mem_tuples.mp h).1
  have hb : ∀ x ∈ c.parts.1 ++ c.parts.2, x < m := by
    intro x hx
    apply List.mem_range.mp
    apply hp.mem_iff.mp
    simp only [List.flatten_append, childrenTuple_flatten, List.mem_append]
    exact Or.inr (List.mem_append.mp hx)
  exact ⟨fun x hx => hb x (List.mem_append_left _ hx),
    fun x hx => hb x (List.mem_append_right _ hx)⟩

/-- A reduced collision on literal labels reconstructs a collision on the next label set. -/
theorem insert_last_collision {m : ℕ} {A B : List (List ℕ)} {c d : Children}
    (hA : A ++ childrenTuple c ∈ tuples m (A.length + childrenArity c))
    (hB : B ++ childrenTuple d ∈ tuples m (B.length + childrenArity d)) :
    output (A ++ [rootWord m c.parts]) = output (B ++ [rootWord m d.parts]) ↔
    output (A ++ childrenTuple c) = output (B ++ childrenTuple d) := by
  obtain ⟨hcL,hcR⟩ := children_below_of_mem hA
  obtain ⟨hdL,hdR⟩ := children_below_of_mem hB
  exact delete_last_collision_iff m A B c d hcL hcR hdL hdR
end StackSort.Del5
