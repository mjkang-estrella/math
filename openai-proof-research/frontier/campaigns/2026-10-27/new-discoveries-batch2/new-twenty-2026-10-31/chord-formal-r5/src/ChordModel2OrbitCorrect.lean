import ChordModel2Scan
namespace Chord.Model2
open Function

theorem orbitCounterCorrect : OrbitCounterCorrect := by
  classical
  intro size f
  let R : Nat → Nat → Prop := fun i j =>
    ∃ hi : i < size, ∃ hj : j < size, Equiv.Perm.SameCycle f ⟨i,hi⟩ ⟨j,hj⟩
  have hsymm : ∀ i j, R i j → R j i := by
    rintro i j ⟨hi,hj,h⟩
    exact ⟨hj,hi,h.symm⟩
  have htrans : ∀ i j k, R i j → R j k → R i k := by
    rintro i j k ⟨hi,hj,h⟩ ⟨_,hk,h'⟩
    exact ⟨hi,hk,h.trans h'⟩
  have hreach : ∀ i, i < size → ∀ j, R i j ↔ ∃ k, ((rawPerm f)^[k]) i = j := by
    intro i hi j
    constructor
    · rintro ⟨_,hj,h⟩
      obtain ⟨k,hk⟩ := (sameCycle_iterate_iff f ⟨i,hi⟩ ⟨j,hj⟩).mp h
      refine ⟨k, ?_⟩
      rw [rawPerm_iterate f ⟨i,hi⟩ k, hk]
    · rintro ⟨k,hk⟩
      have he := rawPerm_iterate f ⟨i,hi⟩ k
      have hj : j < size := by rw [hk] at he; rw [he]; exact (f^[k] ⟨i,hi⟩).isLt
      refine ⟨hi,hj,(sameCycle_iterate_iff f ⟨i,hi⟩ ⟨j,hj⟩).mpr ⟨k,?_⟩⟩
      apply Fin.ext
      exact he.symm.trans hk
  have hcount := scan_correct size (rawPerm f) R (rawPerm_lt f) hsymm htrans hreach
  change cycles size (rawPerm f) = _
  rw [hcount]
  symm
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    obtain ⟨_,hmin⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
    rintro j ⟨_,hj,hij⟩
    exact (bounded_minimum_iff f i).mp hmin ⟨j,hj⟩ hij
  · intro i _ j _ he
    exact Fin.ext he
  · intro i hi
    obtain ⟨hi,hmin⟩ := Finset.mem_filter.mp hi
    have hi := Finset.mem_range.mp hi
    refine ⟨⟨i,hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply (bounded_minimum_iff f ⟨i,hi⟩).mpr
    intro j hij
    exact hmin j.val ⟨hi,j.isLt,hij⟩
end Chord.Model2
