import StackSortCut4

namespace StackSort.Round4
open Seeds2

/-- A maximum at the final output position belongs to the last tuple word. -/
theorem maximum_in_last_word {F : List (List ℕ)} {m : ℕ}
    (hF : NonemptyWords F) (hn : F.flatten.Nodup) (hm : m ∈ F.flatten)
    (hb : ∀ x ∈ F.flatten, x ≤ m)
    (hlast : (output F).idxOf m + 1 = (output F).length) :
    ∃ A w, F = A ++ [w] ∧ m ∈ w := by
  obtain ⟨w,hw,hmw⟩ := List.mem_flatten.mp hm
  obtain ⟨A,B,he⟩ := List.append_of_mem hw
  obtain ⟨v,hv⟩ := maximum_terminal w m hmw
    (fun x hx => hb x (List.mem_flatten.mpr ⟨w,hw,hx⟩))
  have hout : output F = (output A ++ v) ++ m :: output B := by
    rw [he,output_append]
    simp [output,hv,List.append_assoc]
  have hnod : ((output A ++ v) ++ m :: output B).Nodup :=
    hout ▸ ((output_perm F).nodup_iff.mpr hn)
  have hnot : m ∉ output A ++ v := by
    intro h
    exact (List.nodup_append.mp hnod).2.2 m h m (by simp) rfl
  rw [hout,List.idxOf_append] at hlast
  simp only [hnot,List.idxOf_cons_self,Nat.zero_add,List.length_append,
    List.length_cons,ite_false] at hlast
  have hz : (output B).length = 0 := by omega
  have hB : NonemptyWords B := by
    rw [he] at hF
    exact fun x hx => hF x (by simp [hx])
  have hnil : B = [] := (output_eq_nil_iff hB).mp (List.length_eq_zero_iff.mp hz)
  exact ⟨A,w,by simpa [hnil] using he,hmw⟩

/-- T2 now locates the maximum in the actual last word of each literal tuple. -/
theorem irreducible_tuple_last_words {M r s : ℕ} {F G : List (List ℕ)}
    (hF : F ∈ tuples (M+1) r) (hG : G ∈ tuples (M+1) s)
    (he : output F = output G) (hi : Irreducible F G) :
    (∃ A w, F = A ++ [w] ∧ M ∈ w) ∧
    (∃ C v, G = C ++ [v] ∧ M ∈ v) := by
  have pF := mem_words.mp (mem_tuples.mp hF).1
  have pG := mem_words.mp (mem_tuples.mp hG).1
  have hlast := irreducible_tuple_maximum_last hF hG he hi
  have hlen : (output F).length = M+1 := by simpa using (tuple_output_perm hF).length_eq
  have hlastF : (output F).idxOf M + 1 = (output F).length := hlast.trans hlen.symm
  have hlastG : (output G).idxOf M + 1 = (output G).length := by rwa [← he]
  exact ⟨maximum_in_last_word (mem_tuples.mp hF).2.2
      (pF.nodup_iff.mpr List.nodup_range) (pF.mem_iff.mpr (by simp))
      (fun x hx => by have := List.mem_range.mp (pF.mem_iff.mp hx); omega) hlastF,
    maximum_in_last_word (mem_tuples.mp hG).2.2
      (pG.nodup_iff.mpr List.nodup_range) (pG.mem_iff.mpr (by simp))
      (fun x hx => by have := List.mem_range.mp (pG.mem_iff.mp hx); omega) hlastG⟩

end StackSort.Round4
