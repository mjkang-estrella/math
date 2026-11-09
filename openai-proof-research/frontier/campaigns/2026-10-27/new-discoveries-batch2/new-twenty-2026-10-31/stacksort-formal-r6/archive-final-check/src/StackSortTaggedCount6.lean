import StackSortTagged6
noncomputable section
namespace StackSort.Del6
open Seeds2 Round4 Del5 Classical BigOperators

theorem tags_card (m r s : ℕ) :
    (tags m r s).card = ∑ t ∈ Finset.range 3, ∑ u ∈ Finset.range 3,
      mu t * mu u * XI m (r-1+t) (s-1+u) := by
  simp only [tags,Finset.card_sigma,Finset.card_product,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  have he : ∀ p ∈ collisions m (r-1+t) (s-1+u),
      (childChoices (p.1.drop (r-1))).card * (childChoices (p.2.drop (s-1))).card =
        mu t * mu u := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,_⟩
    rcases Finset.mem_product.mp hp with ⟨hF,hG⟩
    have hnF : NonemptyWords (p.1.drop (r-1)) :=
      fun w hw => (mem_tuples.mp hF).2.2 w (List.mem_of_mem_drop hw)
    have hnG : NonemptyWords (p.2.drop (s-1)) :=
      fun w hw => (mem_tuples.mp hG).2.2 w (List.mem_of_mem_drop hw)
    have hlF : (p.1.drop (r-1)).length = t := by
      simp [(mem_tuples.mp hF).2.1]
    have hlG : (p.2.drop (s-1)).length = u := by
      simp [(mem_tuples.mp hG).2.1]
    rw [childChoices_card hnF (by rw [hlF]; have := Finset.mem_range.mp ht; omega),
      childChoices_card hnG (by rw [hlG]; have := Finset.mem_range.mp hu; omega),hlF,hlG]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,smul_eq_mul,collisions,XI]
  ac_rfl

theorem taggedDeletionCount_proved : TaggedDeletionCount := by
  intro M r s _ hr _ hs _
  have he := Nat.card_congr (tagsEquiv (M-1) r s hr hs)
  rw [Nat.card_eq_fintype_card,Fintype.card_coe] at he
  rw [← he,tags_card]
  rfl
end StackSort.Del6
#print axioms StackSort.Del6.taggedDeletionCount_proved
