import Finite
namespace AK350721
open Finset
def p0 : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 5, 0, 4, 8, 6, 7]
  invFun := ![4, 0, 1, 2, 5, 3, 7, 8, 6]
  left_inv := by decide
  right_inv := by decide
theorem p0_sets : rlmv p0 = R9 ∧ excv p0 = E9 := by decide
theorem p0_inv : invCount p0 = 7 := by decide
theorem p0_cycle : cycleGe 3 p0 := by
  unfold cycleGe
  decide
def p1 : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 5, 0, 8, 4, 6, 7]
  invFun := ![4, 0, 1, 2, 6, 3, 7, 8, 5]
  left_inv := by decide
  right_inv := by decide
theorem p1_sets : rlmv p1 = R9 ∧ excv p1 = E9 := by decide
theorem p1_inv : invCount p1 = 8 := by decide
theorem p1_cycle : cycleGe 3 p1 := by
  unfold cycleGe
  decide
def p2 : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 5, 8, 0, 4, 6, 7]
  invFun := ![5, 0, 1, 2, 6, 3, 7, 8, 4]
  left_inv := by decide
  right_inv := by decide
theorem p2_sets : rlmv p2 = R9 ∧ excv p2 = E9 := by decide
theorem p2_inv : invCount p2 = 9 := by decide
theorem p2_cycle : cycleGe 3 p2 := by
  unfold cycleGe
  decide
def p3 : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 0, 5, 4, 8, 6, 7]
  invFun := ![3, 0, 1, 2, 5, 4, 7, 8, 6]
  left_inv := by decide
  right_inv := by decide
theorem p3_sets : rlmv p3 = R9 ∧ excv p3 = E9 := by decide
theorem p3_inv : invCount p3 = 6 := by decide
theorem p3_cycle : ¬ cycleGe 3 p3 := by
  unfold cycleGe
  decide
def p4 : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 0, 5, 8, 4, 6, 7]
  invFun := ![3, 0, 1, 2, 6, 4, 7, 8, 5]
  left_inv := by decide
  right_inv := by decide
theorem p4_sets : rlmv p4 = R9 ∧ excv p4 = E9 := by decide
theorem p4_inv : invCount p4 = 7 := by decide
theorem p4_cycle : cycleGe 3 p4 := by
  unfold cycleGe
  decide
def p5 : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 8, 5, 0, 4, 6, 7]
  invFun := ![5, 0, 1, 2, 6, 4, 7, 8, 3]
  left_inv := by decide
  right_inv := by decide
theorem p5_sets : rlmv p5 = R9 ∧ excv p5 = E9 := by decide
theorem p5_inv : invCount p5 = 10 := by decide
theorem p5_cycle : cycleGe 3 p5 := by
  unfold cycleGe
  decide
def p6 : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 0, 5, 4, 6, 8, 7]
  invFun := ![3, 0, 1, 2, 5, 4, 6, 8, 7]
  left_inv := by decide
  right_inv := by decide
theorem p6_sets : rlmv p6 = R9 ∧ excv p6 = E9 := by decide
theorem p6_inv : invCount p6 = 5 := by decide
theorem p6_cycle : ¬ cycleGe 3 p6 := by
  unfold cycleGe
  decide
def p7 : Equiv.Perm (Fin 9) where
  toFun := ![1, 2, 3, 5, 0, 4, 6, 8, 7]
  invFun := ![4, 0, 1, 2, 5, 3, 6, 8, 7]
  left_inv := by decide
  right_inv := by decide
theorem p7_sets : rlmv p7 = R9 ∧ excv p7 = E9 := by decide
theorem p7_inv : invCount p7 = 6 := by decide
theorem p7_cycle : ¬ cycleGe 3 p7 := by
  unfold cycleGe
  decide
theorem p0_partition : p0.partition.parts = (↑([6, 3] : List ℕ) : Multiset ℕ) := by decide
theorem p1_partition : p1.partition.parts = (↑([9] : List ℕ) : Multiset ℕ) := by decide
theorem p2_partition : p2.partition.parts = (↑([5, 4] : List ℕ) : Multiset ℕ) := by decide
theorem p3_partition : p3.partition.parts = (↑([4, 3, 2] : List ℕ) : Multiset ℕ) := by decide
theorem p4_partition : p4.partition.parts = (↑([5, 4] : List ℕ) : Multiset ℕ) := by decide
theorem p5_partition : p5.partition.parts = (↑([9] : List ℕ) : Multiset ℕ) := by decide
theorem p6_partition : p6.partition.parts = (↑([4, 2, 2, 1] : List ℕ) : Multiset ℕ) := by decide
theorem p7_partition : p7.partition.parts = (↑([6, 2, 1] : List ℕ) : Multiset ℕ) := by decide
end AK350721
