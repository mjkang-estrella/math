import IntervalThreshold
import Mathlib.Data.Finset.Max

namespace IntervalWidth
variable {α : Type*} [LinearOrder α] {n : Nat}

/-- Suffix thresholds include a fixed baseline, so empty suffixes are defined. -/
def suffixValues (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) (q : Nat) : Finset α :=
  insert z ((S.filter (fun j => q ≤ block j)).image (fun j => (I j).left))

def suffixHeight (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) (q : Nat) : α :=
  (suffixValues z I S block q).max' (Finset.insert_nonempty _ _)

theorem selected_le_suffix (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) (j : Fin n) (hj : j ∈ S) :
    (I j).left ≤ suffixHeight z I S block (block j) := by
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, Nat.le_refl _⟩, rfl⟩

/-- The later-block buffer guarantees time order for every selected Hall cut. -/
theorem later_suffix_neighbor (z : α) (I : Fin n → Interval α) (S : Finset (Fin n))
    (block : Fin n → Nat) (chronological : ∀ i j, block i < block j → i < j)
    (i : Fin n) (positive : z < (I i).right)
    (hi : (I i).right ≤ suffixHeight z I S block (block i + 1)) :
    i ∈ neighbors I S := by
  classical
  have hm := Finset.max'_mem (suffixValues z I S block (block i + 1))
    (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with hz | hm
  · have he : suffixHeight z I S block (block i + 1) = z := hz
    exact False.elim (not_le_of_gt positive (hi.trans_eq he))
  · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hm
    obtain ⟨hjS, hjb⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, j, hjS, chronological i j (by omega), ?_⟩
    exact hi.trans_eq he.symm

end IntervalWidth
