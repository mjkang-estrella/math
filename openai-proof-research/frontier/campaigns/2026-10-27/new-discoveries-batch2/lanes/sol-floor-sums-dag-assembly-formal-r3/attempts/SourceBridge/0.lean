import ClipBridge
import Expansion
import Symmetry
import Mathlib.Tactic.Abel
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
def sourceEnv (m H : ℕ) (a : Fin 4 → ℕ) : Vars := ⟨m, H, ((m/3 : ℕ) : ℤ), a 0, a 1, a 2, a 3⟩
theorem sum_match (m H : ℕ) (a : Fin 4 → ℕ) : e11660 (sourceEnv m H a) = FloorSums.clampedSum m H a := by
  unfold FloorSums.clampedSum
  rw [FloorSums.explicit_sixteen]
  norm_num only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty,
    Fin.reduceFinMk, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
    not_false_eq_true, Fin.isValue, Fin.mk.injEq, OfNat.ofNat_ne_zero,
    reduceCtorEq, or_self, or_false, false_or]
  simp only [e5, e6, e8767, e8772, e8777, e8782, e8787, e8792, e8797, e8802, e8807, e8812, e8817, e8822, e8827, e8832, e11642, e11643, e11644, e11645, e11646, e11647, e11648, e11649, e11650, e11651, e11652, e11653, e11654, e11655, e11656, e11657, e11658, e11659, e11660]
  rw [clip_5426 _ H rfl]
  rw [clip_5427 _ H rfl]
  rw [clip_5428 _ H rfl]
  rw [clip_5429 _ H rfl]
  rw [clip_8763 _ H rfl]
  rw [clip_8764 _ H rfl]
  rw [clip_8765 _ H rfl]
  rw [clip_8766 _ H rfl]
  rw [clip_8768 _ H rfl]
  rw [clip_8769 _ H rfl]
  rw [clip_8770 _ H rfl]
  rw [clip_8771 _ H rfl]
  rw [clip_8773 _ H rfl]
  rw [clip_8774 _ H rfl]
  rw [clip_8775 _ H rfl]
  rw [clip_8776 _ H rfl]
  rw [clip_8778 _ H rfl]
  rw [clip_8779 _ H rfl]
  rw [clip_8780 _ H rfl]
  rw [clip_8781 _ H rfl]
  rw [clip_8783 _ H rfl]
  rw [clip_8784 _ H rfl]
  rw [clip_8785 _ H rfl]
  rw [clip_8786 _ H rfl]
  rw [clip_8788 _ H rfl]
  rw [clip_8789 _ H rfl]
  rw [clip_8790 _ H rfl]
  rw [clip_8791 _ H rfl]
  rw [clip_8793 _ H rfl]
  rw [clip_8794 _ H rfl]
  rw [clip_8795 _ H rfl]
  rw [clip_8796 _ H rfl]
  rw [clip_8798 _ H rfl]
  rw [clip_8799 _ H rfl]
  rw [clip_8800 _ H rfl]
  rw [clip_8801 _ H rfl]
  rw [clip_8803 _ H rfl]
  rw [clip_8804 _ H rfl]
  rw [clip_8805 _ H rfl]
  rw [clip_8806 _ H rfl]
  rw [clip_8808 _ H rfl]
  rw [clip_8809 _ H rfl]
  rw [clip_8810 _ H rfl]
  rw [clip_8811 _ H rfl]
  rw [clip_8813 _ H rfl]
  rw [clip_8814 _ H rfl]
  rw [clip_8815 _ H rfl]
  rw [clip_8816 _ H rfl]
  rw [clip_8818 _ H rfl]
  rw [clip_8819 _ H rfl]
  rw [clip_8820 _ H rfl]
  rw [clip_8821 _ H rfl]
  rw [clip_8823 _ H rfl]
  rw [clip_8824 _ H rfl]
  rw [clip_8825 _ H rfl]
  rw [clip_8826 _ H rfl]
  rw [clip_8828 _ H rfl]
  rw [clip_8829 _ H rfl]
  rw [clip_8830 _ H rfl]
  rw [clip_8831 _ H rfl]
  rw [clip_5489 _ H rfl]
  rw [clip_5493 _ H rfl]
  rw [clip_5497 _ H rfl]
  rw [clip_5501 _ H rfl]
  simp only [e2, e5, e7, e9, e12, e17, e43, e44, e45, e108, e109, e110, e266, e267, e530, e531, e532, e535, e538, e541, e544, e545, e546, e549, e552, e555, e558, e559, e560, e563, e566, e569, e572, e573, e576, e579, e582, e585, e586, e587, e590, e593, e596, e599, e600, e603, e606, e609, e612, e613, e616, e619, e622, e625, e626, e629, e632, e635, e638, e639, e640, e643, e646, e649, e652, e653, e656, e659, e662, e665, e666, e669, e672, e675, e678, e679, e682, e685, e688, e691, e692, e695, e698, e701, e704, e705, e708, e711, e714, e717, e718, e721, e724, e727, e730, e731, e732, e733, e734, sourceEnv]
  simp only [neg_mul, one_mul, neg_one_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  abel
end Assembly
