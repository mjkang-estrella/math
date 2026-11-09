import StackSortCut4

namespace StackSort.Round4
open Seeds2

theorem irreducible_single_left (w : List ℕ) (G : List (List ℕ)) :
    Irreducible [w] G := by
  intro k hF _ hpos hlt
  obtain ⟨A,B,he,hk⟩ := hF
  cases A with
  | nil => simp [output] at hk; omega
  | cons u A =>
    have h : w = u ∧ A ++ B = [] := by simpa using he
    have ha : A = [] := (List.append_eq_nil_iff.mp h.2).1
    subst A
    rw [← h.1] at hk
    simp only [output,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
      List.append_nil] at hk hlt
    omega

theorem II_one_left (M s : ℕ) : II M 1 s = XI M 1 s := by
  classical
  unfold II XI
  congr 1
  ext p
  simp only [Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨hp,he,_⟩; exact ⟨hp,he⟩
  · rintro ⟨⟨hF,hG⟩,he⟩
    refine ⟨⟨hF,hG⟩,he,?_⟩
    have hl := (mem_tuples.mp hF).2.1
    obtain ⟨w,hw⟩ := List.length_eq_one_iff.mp hl
    rw [hw]
    exact irreducible_single_left w p.2

/-- The common-cut identity is unconditional when the first tuple has one word. -/
theorem commonCutCount_one_left (M s : ℕ) (hM : 1 ≤ M)
    (hb : 1 ≤ bound M) (hs : 1 ≤ s) (hsB : s ≤ bound M) :
    literalX M 1 s = literalI M 1 s + correction false literalX literalI M 1 s := by
  have hc : correction false literalX literalI M 1 s = 0 := by
    simp [correction,convolution]
  rw [hc,Nat.add_zero]
  simp only [literalX,literalI,ite_eq_right (show M ≠ 0 by omega),
    ite_eq_left (show 1 ≤ 1 ∧ 1 ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M from ⟨le_rfl,hb,hs,hsB⟩)]
  exact (II_one_left M s).symm

end StackSort.Round4
