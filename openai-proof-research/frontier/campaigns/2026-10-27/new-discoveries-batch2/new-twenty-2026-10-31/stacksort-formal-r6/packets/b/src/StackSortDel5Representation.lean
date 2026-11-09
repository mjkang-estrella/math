import StackSortDel5Inverse
namespace StackSort.Del5
open Seeds2 Round4

/-- Every maximum-final literal tuple has an actual reduced representation. -/
theorem maximum_final_representation {m r : ℕ} {F : List (List ℕ)}
    (hF : F ∈ tuples (m+1) r)
    (hlast : (output F).idxOf m + 1 = m+1) :
    ∃ A c, F = A ++ [rootWord m c.parts] ∧ A.length+1 = r ∧
      A ++ childrenTuple c ∈ tuples m (A.length + childrenArity c) := by
  have hp := mem_words.mp (mem_tuples.mp hF).1
  have hlen : (output F).length = m+1 := by simpa using (tuple_output_perm hF).length_eq
  obtain ⟨A,w,he,hm⟩ := maximum_in_last_word (mem_tuples.mp hF).2.2
    (hp.nodup_iff.mpr List.nodup_range) (hp.mem_iff.mpr (by simp))
    (fun x hx => by have := List.mem_range.mp (hp.mem_iff.mp hx); omega)
    (hlast.trans hlen.symm)
  let c := childrenOfParts (rootParts m w)
  have hc : rootWord m c.parts = w := by
    rw [show c.parts = rootParts m w from parts_childrenOfParts _]
    exact rootWord_rootParts m w hm
  have har : A.length+1 = r := by
    have := (mem_tuples.mp hF).2.1
    simpa [he] using this
  refine ⟨A,c,by simpa [hc] using he,har,?_⟩
  apply (delete_last_mem_iff m A c).mp
  simpa [hc,← he,har] using hF

/-- Original tuples recover the prefix and both oriented children uniquely. -/
theorem insertion_injective {m : ℕ} {A B : List (List ℕ)} {c d : Children}
    (hA : A ++ childrenTuple c ∈ tuples m (A.length + childrenArity c))
    (hB : B ++ childrenTuple d ∈ tuples m (B.length + childrenArity d))
    (he : A ++ [rootWord m c.parts] = B ++ [rootWord m d.parts]) :
    A = B ∧ c = d := by
  have hl : A.length = B.length := by
    have := congrArg List.length he
    simp only [List.length_append,List.length_singleton] at this
    omega
  obtain ⟨hAB,hw⟩ := List.append_inj he hl
  have hc := children_below_of_mem hA
  have hd := children_below_of_mem hB
  have hp : c.parts = d.parts := rootWord_injective m c.parts d.parts hc.1 hd.1
    (List.singleton_inj.mp hw)
  exact ⟨hAB, childrenEquiv.injective hp⟩

/-- Every reduced representation reconstructs a maximum-final literal tuple. -/
theorem representation_maximum_final {m : ℕ} {A : List (List ℕ)} {c : Children}
    (hA : A ++ childrenTuple c ∈ tuples m (A.length + childrenArity c)) :
    A ++ [rootWord m c.parts] ∈ tuples (m+1) (A.length+1) ∧
    (output (A ++ [rootWord m c.parts])).idxOf m + 1 = m+1 := by
  have hF := (delete_last_mem_iff m A c).mpr hA
  have hc := children_below_of_mem hA
  have ho := delete_last_output m A c hc.1 hc.2
  have hp := tuple_output_perm hA
  have hn : m ∉ output (A ++ childrenTuple c) := by
    intro h
    have := List.mem_range.mp (hp.mem_iff.mp h)
    omega
  refine ⟨hF,?_⟩
  rw [ho,List.idxOf_append]
  simp [hn,hp.length_eq]

/-- The two representations of a literal maximum-final collision exist together. -/
theorem maximum_final_collision_representation {m r s : ℕ} {F G : List (List ℕ)}
    (hF : F ∈ tuples (m+1) r) (hG : G ∈ tuples (m+1) s)
    (he : output F = output G)
    (hlast : (output F).idxOf m + 1 = m+1) :
    ∃ A B c d, F = A ++ [rootWord m c.parts] ∧
      G = B ++ [rootWord m d.parts] ∧ A.length+1 = r ∧ B.length+1 = s ∧
      A ++ childrenTuple c ∈ tuples m (A.length + childrenArity c) ∧
      B ++ childrenTuple d ∈ tuples m (B.length + childrenArity d) ∧
      output (A ++ childrenTuple c) = output (B ++ childrenTuple d) := by
  obtain ⟨A,c,hFc,hAr,hAc⟩ := maximum_final_representation hF hlast
  obtain ⟨B,d,hGd,hBs,hBd⟩ := maximum_final_representation hG (by rwa [← he])
  refine ⟨A,B,c,d,hFc,hGd,hAr,hBs,hAc,hBd,?_⟩
  apply (insert_last_collision hAc hBd).mp
  rwa [← hFc,← hGd]
end StackSort.Del5
