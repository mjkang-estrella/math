import Concrete
import Arithmetic
namespace AK350721
open Finset

theorem characterization9 (pi : Equiv.Perm (Fin 9)) :
    rlmv pi = R9 ∧ excv pi = E9 ↔
      pi = p0 ∨ pi = p1 ∨ pi = p2 ∨ pi = p3 ∨ pi = p4 ∨ pi = p5 ∨ pi = p6 ∨ pi = p7 := by
  constructor
  · rintro ⟨hr, he⟩
    obtain ⟨h1, h2, h3, h7⟩ := forced9 pi hr he
    have lo (v : Fin 9) (hv : v ≠ 1 ∧ v ≠ 2 ∧ v ≠ 3 ∧ v ≠ 7) :
        3 ≤ (pi.symm v).val ∧ (pi.symm v).val ≤ 7 := by
      have hne1 := Fin.val_injective.ne (pi.symm.injective.ne hv.1)
      have hne2 := Fin.val_injective.ne (pi.symm.injective.ne hv.2.1)
      have hne3 := Fin.val_injective.ne (pi.symm.injective.ne hv.2.2.1)
      have hne7 := Fin.val_injective.ne (pi.symm.injective.ne hv.2.2.2)
      rw [h1] at hne1
      rw [h2] at hne2
      rw [h3] at hne3
      rw [h7] at hne7
      have := (pi.symm v).isLt
      omega
    have ex (v : Fin 9) : pi.symm v < v ↔ v ∈ E9 := by
      rw [← he]; simp [excv]
    have ne4 : 4 ≤ (pi.symm 4).val := by
      have h := (ex 4).not.mpr (by decide)
      exact Nat.le_of_not_gt h
    have ne6 : 6 ≤ (pi.symm 6).val := by
      have h := (ex 6).not.mpr (by decide)
      exact Nat.le_of_not_gt h
    have ex5 : (pi.symm 5).val ≤ 4 := by
      have h := (ex 5).mpr (by decide)
      omega
    have o04 := minima_positions pi (show 0 ∈ rlmv pi by rw [hr]; decide)
      (show 4 ∈ rlmv pi by rw [hr]; decide) (by decide)
    have o46 := minima_positions pi (show 4 ∈ rlmv pi by rw [hr]; decide)
      (show 6 ∈ rlmv pi by rw [hr]; decide) (by decide)
    have h := tail_arithmetic (pi.symm 0).val (pi.symm 4).val (pi.symm 5).val (pi.symm 6).val (pi.symm 8).val
      (lo 0 (by decide))
      (lo 4 (by decide))
      (lo 5 (by decide))
      (lo 6 (by decide))
      (lo 8 (by decide))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (0 : Fin 9) ≠ 4 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (0 : Fin 9) ≠ 5 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (0 : Fin 9) ≠ 6 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (0 : Fin 9) ≠ 8 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (4 : Fin 9) ≠ 5 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (4 : Fin 9) ≠ 6 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (4 : Fin 9) ≠ 8 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (5 : Fin 9) ≠ 6 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (5 : Fin 9) ≠ 8 by decide)))
      (Fin.val_injective.ne (pi.symm.injective.ne (show (6 : Fin 9) ≠ 8 by decide)))
      o04 o46 ne4 ne6 ex5
    rcases h with h | h | h | h | h | h | h | h
    · have hp : pi.symm = p6.symm := by
        apply Equiv.ext
        intro v
        apply Fin.ext
        fin_cases v
        · change (pi.symm (0 : Fin 9)).val = 3
          omega
        · change (pi.symm (1 : Fin 9)).val = 0
          omega
        · change (pi.symm (2 : Fin 9)).val = 1
          omega
        · change (pi.symm (3 : Fin 9)).val = 2
          omega
        · change (pi.symm (4 : Fin 9)).val = 5
          omega
        · change (pi.symm (5 : Fin 9)).val = 4
          omega
        · change (pi.symm (6 : Fin 9)).val = 6
          omega
        · change (pi.symm (7 : Fin 9)).val = 8
          omega
        · change (pi.symm (8 : Fin 9)).val = 7
          omega
      have : pi = p6 := by simpa using congrArg Equiv.symm hp
      tauto
    · have hp : pi.symm = p3.symm := by
        apply Equiv.ext
        intro v
        apply Fin.ext
        fin_cases v
        · change (pi.symm (0 : Fin 9)).val = 3
          omega
        · change (pi.symm (1 : Fin 9)).val = 0
          omega
        · change (pi.symm (2 : Fin 9)).val = 1
          omega
        · change (pi.symm (3 : Fin 9)).val = 2
          omega
        · change (pi.symm (4 : Fin 9)).val = 5
          omega
        · change (pi.symm (5 : Fin 9)).val = 4
          omega
        · change (pi.symm (6 : Fin 9)).val = 7
          omega
        · change (pi.symm (7 : Fin 9)).val = 8
          omega
        · change (pi.symm (8 : Fin 9)).val = 6
          omega
      have : pi = p3 := by simpa using congrArg Equiv.symm hp
      tauto
    · have hp : pi.symm = p4.symm := by
        apply Equiv.ext
        intro v
        apply Fin.ext
        fin_cases v
        · change (pi.symm (0 : Fin 9)).val = 3
          omega
        · change (pi.symm (1 : Fin 9)).val = 0
          omega
        · change (pi.symm (2 : Fin 9)).val = 1
          omega
        · change (pi.symm (3 : Fin 9)).val = 2
          omega
        · change (pi.symm (4 : Fin 9)).val = 6
          omega
        · change (pi.symm (5 : Fin 9)).val = 4
          omega
        · change (pi.symm (6 : Fin 9)).val = 7
          omega
        · change (pi.symm (7 : Fin 9)).val = 8
          omega
        · change (pi.symm (8 : Fin 9)).val = 5
          omega
      have : pi = p4 := by simpa using congrArg Equiv.symm hp
      tauto
    · have hp : pi.symm = p7.symm := by
        apply Equiv.ext
        intro v
        apply Fin.ext
        fin_cases v
        · change (pi.symm (0 : Fin 9)).val = 4
          omega
        · change (pi.symm (1 : Fin 9)).val = 0
          omega
        · change (pi.symm (2 : Fin 9)).val = 1
          omega
        · change (pi.symm (3 : Fin 9)).val = 2
          omega
        · change (pi.symm (4 : Fin 9)).val = 5
          omega
        · change (pi.symm (5 : Fin 9)).val = 3
          omega
        · change (pi.symm (6 : Fin 9)).val = 6
          omega
        · change (pi.symm (7 : Fin 9)).val = 8
          omega
        · change (pi.symm (8 : Fin 9)).val = 7
          omega
      have : pi = p7 := by simpa using congrArg Equiv.symm hp
      tauto
    · have hp : pi.symm = p0.symm := by
        apply Equiv.ext
        intro v
        apply Fin.ext
        fin_cases v
        · change (pi.symm (0 : Fin 9)).val = 4
          omega
        · change (pi.symm (1 : Fin 9)).val = 0
          omega
        · change (pi.symm (2 : Fin 9)).val = 1
          omega
        · change (pi.symm (3 : Fin 9)).val = 2
          omega
        · change (pi.symm (4 : Fin 9)).val = 5
          omega
        · change (pi.symm (5 : Fin 9)).val = 3
          omega
        · change (pi.symm (6 : Fin 9)).val = 7
          omega
        · change (pi.symm (7 : Fin 9)).val = 8
          omega
        · change (pi.symm (8 : Fin 9)).val = 6
          omega
      have : pi = p0 := by simpa using congrArg Equiv.symm hp
      tauto
    · have hp : pi.symm = p1.symm := by
        apply Equiv.ext
        intro v
        apply Fin.ext
        fin_cases v
        · change (pi.symm (0 : Fin 9)).val = 4
          omega
        · change (pi.symm (1 : Fin 9)).val = 0
          omega
        · change (pi.symm (2 : Fin 9)).val = 1
          omega
        · change (pi.symm (3 : Fin 9)).val = 2
          omega
        · change (pi.symm (4 : Fin 9)).val = 6
          omega
        · change (pi.symm (5 : Fin 9)).val = 3
          omega
        · change (pi.symm (6 : Fin 9)).val = 7
          omega
        · change (pi.symm (7 : Fin 9)).val = 8
          omega
        · change (pi.symm (8 : Fin 9)).val = 5
          omega
      have : pi = p1 := by simpa using congrArg Equiv.symm hp
      tauto
    · have hp : pi.symm = p2.symm := by
        apply Equiv.ext
        intro v
        apply Fin.ext
        fin_cases v
        · change (pi.symm (0 : Fin 9)).val = 5
          omega
        · change (pi.symm (1 : Fin 9)).val = 0
          omega
        · change (pi.symm (2 : Fin 9)).val = 1
          omega
        · change (pi.symm (3 : Fin 9)).val = 2
          omega
        · change (pi.symm (4 : Fin 9)).val = 6
          omega
        · change (pi.symm (5 : Fin 9)).val = 3
          omega
        · change (pi.symm (6 : Fin 9)).val = 7
          omega
        · change (pi.symm (7 : Fin 9)).val = 8
          omega
        · change (pi.symm (8 : Fin 9)).val = 4
          omega
      have : pi = p2 := by simpa using congrArg Equiv.symm hp
      tauto
    · have hp : pi.symm = p5.symm := by
        apply Equiv.ext
        intro v
        apply Fin.ext
        fin_cases v
        · change (pi.symm (0 : Fin 9)).val = 5
          omega
        · change (pi.symm (1 : Fin 9)).val = 0
          omega
        · change (pi.symm (2 : Fin 9)).val = 1
          omega
        · change (pi.symm (3 : Fin 9)).val = 2
          omega
        · change (pi.symm (4 : Fin 9)).val = 6
          omega
        · change (pi.symm (5 : Fin 9)).val = 4
          omega
        · change (pi.symm (6 : Fin 9)).val = 7
          omega
        · change (pi.symm (7 : Fin 9)).val = 8
          omega
        · change (pi.symm (8 : Fin 9)).val = 3
          omega
      have : pi = p5 := by simpa using congrArg Equiv.symm hp
      tauto
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact p0_sets
    · exact p1_sets
    · exact p2_sets
    · exact p3_sets
    · exact p4_sets
    · exact p5_sets
    · exact p6_sets
    · exact p7_sets
end AK350721
