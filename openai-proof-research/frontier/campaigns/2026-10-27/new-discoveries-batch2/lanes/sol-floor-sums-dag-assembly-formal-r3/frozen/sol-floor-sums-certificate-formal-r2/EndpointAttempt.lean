import Symmetry
import Expansion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
namespace FloorSums
theorem sorted_clamped_attempt : SortedClampedBound := by
  intro m H hm hH hHm a ha hs
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have s01 := hs (show (0 : Fin 4) ≤ 1 by decide)
  have s12 := hs (show (1 : Fin 4) ≤ 2 by decide)
  have s23 := hs (show (2 : Fin 4) ≤ 3 by decide)
  unfold clampedSum
  rw [explicit_sixteen]
  norm_num only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty,
    Fin.reduceFinMk, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
    not_false_eq_true, Fin.isValue, Fin.mk.injEq, OfNat.ofNat_ne_zero,
    reduceCtorEq, or_self, or_false, false_or]
  simp only [clip, min_def, max_def]
  omega
end FloorSums
