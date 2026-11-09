import ChordModel3Orbits
import ChordComb4Representative
namespace Chord.Round5
open Equiv

/-- Full fuel trace membership is exactly SameCycle, including the starting dart. -/
theorem trace_rawPerm_iff {size} (f : Perm (Fin size)) (i j : Fin size) :
    j.val ∈ trace (Model2.rawPerm f) size i.val [] ↔ Perm.SameCycle f i j := by
  constructor
  · intro h
    rcases Model2.trace_origin _ _ _ _ _ h with h | ⟨k,_,hk⟩
    · exact False.elim (List.not_mem_nil h)
    · apply (Model2.sameCycle_iterate_iff f i j).mpr
      refine ⟨k,Fin.ext ?_⟩
      exact (Model2.rawPerm_iterate f i k).symm.trans hk.symm
  · intro h
    obtain ⟨k,hk⟩ := (Model2.sameCycle_iterate_iff f i j).mp h
    have ht := Model2.trace_contains_iterates (Model2.rawPerm f) size i.val []
      (Model2.rawPerm_lt f) i.isLt (by simp) (by simp) (by simp) k
    simpa only [Model2.rawPerm_iterate, hk] using ht

/-- The frozen EndSame predicate is the genuine face-permutation orbit relation. -/
theorem endSame_iff_sameCycle (n : Nat) (hn : 3 ≤ n) (c : Sides n) :
    Comb4.EndSame n hn c ↔
      Perm.SameCycle (Model2.faceEquiv (r3Block n hn) c)
        ⟨3*(2*n-1)+1,by omega⟩ ⟨0,by omega⟩ := by
  let f := Model2.faceEquiv (r3Block n hn) c
  have he : ∀ i, i < 6*n → Model2.rawPerm f i = face (r3Block n hn) c i := by
    intro i hi
    simp only [Model2.rawPerm, dite_eq_left hi]
    rfl
  have ht := Model3.trace_congr (6*n) (Model2.rawPerm f) (face (r3Block n hn) c)
    (Model2.rawPerm_lt f) he (6*n) (3*(2*n-1)+1) [] (by omega)
  change 0 ∈ trace (face (r3Block n hn) c) (6*n) (3*(2*n-1)+1) [] ↔ _
  rw [← ht]
  exact trace_rawPerm_iff f ⟨3*(2*n-1)+1,by omega⟩ ⟨0,by omega⟩

#print axioms endSame_iff_sameCycle
end Chord.Round5
