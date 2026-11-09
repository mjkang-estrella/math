import StackSortSeeds2Maximum
namespace StackSort.Seeds2

 theorem mem_tuples {M r : ℕ} {F : List (List ℕ)} :
    F ∈ tuples M r ↔ F.flatten ∈ words M ∧ F.length = r ∧ ∀ w ∈ F, w ≠ [] := by
  simp only [tuples, Finset.mem_biUnion, mem_sections]
  constructor
  · rintro ⟨w, hw, hl, he, hn⟩
    exact ⟨he ▸ hw, hl, hn⟩
  · rintro ⟨hw, hl, hn⟩
    exact ⟨F.flatten, hw, hl, rfl, hn⟩

 theorem tuple_output_perm {M r : ℕ} {F : List (List ℕ)} (hF : F ∈ tuples M r) :
    (output F).Perm (List.range M) :=
  (output_perm F).trans (mem_words.mp (mem_tuples.mp hF).1)

/-- T2 specialized to the actual labelled tuple domain [0,M+1). -/
 theorem irreducible_tuple_maximum_last {M r t : ℕ} {F G : List (List ℕ)}
    (hF : F ∈ tuples (M+1) r) (hG : G ∈ tuples (M+1) t)
    (he : output F = output G) (hi : Irreducible F G) :
    (output F).idxOf M + 1 = M + 1 := by
  have pF := mem_words.mp (mem_tuples.mp hF).1
  have pG := mem_words.mp (mem_tuples.mp hG).1
  have hlast := irreducible_maximum_last F G M
    (pF.nodup_iff.mpr List.nodup_range) (pG.nodup_iff.mpr List.nodup_range)
    (pF.mem_iff.mpr (by simp)) (pG.mem_iff.mpr (by simp))
    (fun x hx => by have := List.mem_range.mp (pF.mem_iff.mp hx); omega)
    (fun x hx => by have := List.mem_range.mp (pG.mem_iff.mp hx); omega) he hi
  have hlen := (tuple_output_perm hF).length_eq
  simpa using hlast.trans hlen

end StackSort.Seeds2
