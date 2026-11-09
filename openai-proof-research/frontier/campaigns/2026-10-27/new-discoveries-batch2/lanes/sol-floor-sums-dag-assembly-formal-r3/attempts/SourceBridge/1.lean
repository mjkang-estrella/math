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

theorem canonical_5426 (m H : ℕ) (a : Fin 4 → ℕ) : e5426 (sourceEnv m H a) = FloorSums.clip H ((0 : ℤ) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_5426 _ H rfl]
  congr 1
  change (((0 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = ((0 : ℤ) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_5427 (m H : ℕ) (a : Fin 4 → ℕ) : e5427 (sourceEnv m H a) = FloorSums.clip H ((0 : ℤ) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_5427 _ H rfl]
  congr 1
  change (((0 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = ((0 : ℤ) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_5428 (m H : ℕ) (a : Fin 4 → ℕ) : e5428 (sourceEnv m H a) = FloorSums.clip H ((0 : ℤ) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_5428 _ H rfl]
  congr 1
  change (((0 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = ((0 : ℤ) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_5429 (m H : ℕ) (a : Fin 4 → ℕ) : e5429 (sourceEnv m H a) = FloorSums.clip H ((0 : ℤ) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_5429 _ H rfl]
  congr 1
  change (((0 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = ((0 : ℤ) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8763 (m H : ℕ) (a : Fin 4 → ℕ) : e8763 (sourceEnv m H a) = FloorSums.clip H ((a 0 : ℤ) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8763 _ H rfl]
  congr 1
  change ((((a 0 : ℤ)) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = ((a 0 : ℤ) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8764 (m H : ℕ) (a : Fin 4 → ℕ) : e8764 (sourceEnv m H a) = FloorSums.clip H ((a 0 : ℤ) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8764 _ H rfl]
  congr 1
  change ((((a 0 : ℤ)) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = ((a 0 : ℤ) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8765 (m H : ℕ) (a : Fin 4 → ℕ) : e8765 (sourceEnv m H a) = FloorSums.clip H ((a 0 : ℤ) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8765 _ H rfl]
  congr 1
  change ((((a 0 : ℤ)) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = ((a 0 : ℤ) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8766 (m H : ℕ) (a : Fin 4 → ℕ) : e8766 (sourceEnv m H a) = FloorSums.clip H ((a 0 : ℤ) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8766 _ H rfl]
  congr 1
  change ((((a 0 : ℤ)) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = ((a 0 : ℤ) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8768 (m H : ℕ) (a : Fin 4 → ℕ) : e8768 (sourceEnv m H a) = FloorSums.clip H ((a 1 : ℤ) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8768 _ H rfl]
  congr 1
  change ((((a 1 : ℤ)) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = ((a 1 : ℤ) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8769 (m H : ℕ) (a : Fin 4 → ℕ) : e8769 (sourceEnv m H a) = FloorSums.clip H ((a 1 : ℤ) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8769 _ H rfl]
  congr 1
  change ((((a 1 : ℤ)) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = ((a 1 : ℤ) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8770 (m H : ℕ) (a : Fin 4 → ℕ) : e8770 (sourceEnv m H a) = FloorSums.clip H ((a 1 : ℤ) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8770 _ H rfl]
  congr 1
  change ((((a 1 : ℤ)) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = ((a 1 : ℤ) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8771 (m H : ℕ) (a : Fin 4 → ℕ) : e8771 (sourceEnv m H a) = FloorSums.clip H ((a 1 : ℤ) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8771 _ H rfl]
  congr 1
  change ((((a 1 : ℤ)) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = ((a 1 : ℤ) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8773 (m H : ℕ) (a : Fin 4 → ℕ) : e8773 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 1 : ℤ)) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8773 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 1 : ℤ)) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8774 (m H : ℕ) (a : Fin 4 → ℕ) : e8774 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 1 : ℤ)) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8774 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 1 : ℤ)) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8775 (m H : ℕ) (a : Fin 4 → ℕ) : e8775 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 1 : ℤ)) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8775 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 1 : ℤ)) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8776 (m H : ℕ) (a : Fin 4 → ℕ) : e8776 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 1 : ℤ)) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8776 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 1 : ℤ)) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8778 (m H : ℕ) (a : Fin 4 → ℕ) : e8778 (sourceEnv m H a) = FloorSums.clip H ((a 2 : ℤ) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8778 _ H rfl]
  congr 1
  change ((((a 2 : ℤ)) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = ((a 2 : ℤ) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8779 (m H : ℕ) (a : Fin 4 → ℕ) : e8779 (sourceEnv m H a) = FloorSums.clip H ((a 2 : ℤ) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8779 _ H rfl]
  congr 1
  change ((((a 2 : ℤ)) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = ((a 2 : ℤ) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8780 (m H : ℕ) (a : Fin 4 → ℕ) : e8780 (sourceEnv m H a) = FloorSums.clip H ((a 2 : ℤ) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8780 _ H rfl]
  congr 1
  change ((((a 2 : ℤ)) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = ((a 2 : ℤ) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8781 (m H : ℕ) (a : Fin 4 → ℕ) : e8781 (sourceEnv m H a) = FloorSums.clip H ((a 2 : ℤ) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8781 _ H rfl]
  congr 1
  change ((((a 2 : ℤ)) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = ((a 2 : ℤ) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8783 (m H : ℕ) (a : Fin 4 → ℕ) : e8783 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8783 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8784 (m H : ℕ) (a : Fin 4 → ℕ) : e8784 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8784 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8785 (m H : ℕ) (a : Fin 4 → ℕ) : e8785 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8785 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8786 (m H : ℕ) (a : Fin 4 → ℕ) : e8786 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8786 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8788 (m H : ℕ) (a : Fin 4 → ℕ) : e8788 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8788 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8789 (m H : ℕ) (a : Fin 4 → ℕ) : e8789 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8789 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8790 (m H : ℕ) (a : Fin 4 → ℕ) : e8790 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8790 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8791 (m H : ℕ) (a : Fin 4 → ℕ) : e8791 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8791 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + (a 2 : ℤ)) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8793 (m H : ℕ) (a : Fin 4 → ℕ) : e8793 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + (a 2 : ℤ))) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8793 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + (a 2 : ℤ))) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8794 (m H : ℕ) (a : Fin 4 → ℕ) : e8794 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + (a 2 : ℤ))) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8794 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + (a 2 : ℤ))) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8795 (m H : ℕ) (a : Fin 4 → ℕ) : e8795 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + (a 2 : ℤ))) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8795 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + (a 2 : ℤ))) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8796 (m H : ℕ) (a : Fin 4 → ℕ) : e8796 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + (a 2 : ℤ))) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8796 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + (a 2 : ℤ))) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8798 (m H : ℕ) (a : Fin 4 → ℕ) : e8798 (sourceEnv m H a) = FloorSums.clip H ((a 3 : ℤ) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8798 _ H rfl]
  congr 1
  change ((((a 3 : ℤ)) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = ((a 3 : ℤ) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8799 (m H : ℕ) (a : Fin 4 → ℕ) : e8799 (sourceEnv m H a) = FloorSums.clip H ((a 3 : ℤ) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8799 _ H rfl]
  congr 1
  change ((((a 3 : ℤ)) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = ((a 3 : ℤ) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8800 (m H : ℕ) (a : Fin 4 → ℕ) : e8800 (sourceEnv m H a) = FloorSums.clip H ((a 3 : ℤ) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8800 _ H rfl]
  congr 1
  change ((((a 3 : ℤ)) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = ((a 3 : ℤ) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8801 (m H : ℕ) (a : Fin 4 → ℕ) : e8801 (sourceEnv m H a) = FloorSums.clip H ((a 3 : ℤ) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8801 _ H rfl]
  congr 1
  change ((((a 3 : ℤ)) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = ((a 3 : ℤ) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8803 (m H : ℕ) (a : Fin 4 → ℕ) : e8803 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8803 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8804 (m H : ℕ) (a : Fin 4 → ℕ) : e8804 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8804 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8805 (m H : ℕ) (a : Fin 4 → ℕ) : e8805 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8805 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8806 (m H : ℕ) (a : Fin 4 → ℕ) : e8806 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8806 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8808 (m H : ℕ) (a : Fin 4 → ℕ) : e8808 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8808 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8809 (m H : ℕ) (a : Fin 4 → ℕ) : e8809 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8809 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8810 (m H : ℕ) (a : Fin 4 → ℕ) : e8810 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8810 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8811 (m H : ℕ) (a : Fin 4 → ℕ) : e8811 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8811 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8813 (m H : ℕ) (a : Fin 4 → ℕ) : e8813 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8813 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8814 (m H : ℕ) (a : Fin 4 → ℕ) : e8814 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8814 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8815 (m H : ℕ) (a : Fin 4 → ℕ) : e8815 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8815 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8816 (m H : ℕ) (a : Fin 4 → ℕ) : e8816 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8816 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8818 (m H : ℕ) (a : Fin 4 → ℕ) : e8818 (sourceEnv m H a) = FloorSums.clip H (((a 2 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8818 _ H rfl]
  congr 1
  change (((a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 2 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8819 (m H : ℕ) (a : Fin 4 → ℕ) : e8819 (sourceEnv m H a) = FloorSums.clip H (((a 2 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8819 _ H rfl]
  congr 1
  change (((a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 2 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8820 (m H : ℕ) (a : Fin 4 → ℕ) : e8820 (sourceEnv m H a) = FloorSums.clip H (((a 2 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8820 _ H rfl]
  congr 1
  change (((a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 2 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8821 (m H : ℕ) (a : Fin 4 → ℕ) : e8821 (sourceEnv m H a) = FloorSums.clip H (((a 2 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8821 _ H rfl]
  congr 1
  change (((a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 2 : ℤ) + (a 3 : ℤ)) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8823 (m H : ℕ) (a : Fin 4 → ℕ) : e8823 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8823 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8824 (m H : ℕ) (a : Fin 4 → ℕ) : e8824 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8824 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8825 (m H : ℕ) (a : Fin 4 → ℕ) : e8825 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8825 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8826 (m H : ℕ) (a : Fin 4 → ℕ) : e8826 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8826 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_8828 (m H : ℕ) (a : Fin 4 → ℕ) : e8828 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_8828 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_8829 (m H : ℕ) (a : Fin 4 → ℕ) : e8829 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_8829 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_8830 (m H : ℕ) (a : Fin 4 → ℕ) : e8830 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_8830 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_8831 (m H : ℕ) (a : Fin 4 → ℕ) : e8831 (sourceEnv m H a) = FloorSums.clip H (((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_8831 _ H rfl]
  congr 1
  change (((a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ))) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem canonical_5489 (m H : ℕ) (a : Fin 4 → ℕ) : e5489 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ)))) + (H : ℤ) - 1 * (m : ℤ)) := by
  rw [clip_5489 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((1 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ)))) + (H : ℤ) - 1 * (m : ℤ))
  omega
theorem canonical_5493 (m H : ℕ) (a : Fin 4 → ℕ) : e5493 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ)))) + (H : ℤ) - 2 * (m : ℤ)) := by
  rw [clip_5493 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((2 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ)))) + (H : ℤ) - 2 * (m : ℤ))
  omega
theorem canonical_5497 (m H : ℕ) (a : Fin 4 → ℕ) : e5497 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ)))) + (H : ℤ) - 3 * (m : ℤ)) := by
  rw [clip_5497 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((3 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ)))) + (H : ℤ) - 3 * (m : ℤ))
  omega
theorem canonical_5501 (m H : ℕ) (a : Fin 4 → ℕ) : e5501 (sourceEnv m H a) = FloorSums.clip H (((a 0 : ℤ) + ((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ)))) + (H : ℤ) - 4 * (m : ℤ)) := by
  rw [clip_5501 _ H rfl]
  congr 1
  change (((a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) + (a 3 : ℤ) + (H : ℤ)) - ((4 : ℤ) * (m : ℤ))) = (((a 0 : ℤ) + ((a 1 : ℤ) + ((a 2 : ℤ) + (a 3 : ℤ)))) + (H : ℤ) - 4 * (m : ℤ))
  omega
theorem sum_match (m H : ℕ) (a : Fin 4 → ℕ) : e11660 (sourceEnv m H a) = FloorSums.clampedSum m H a := by
  unfold FloorSums.clampedSum
  rw [FloorSums.explicit_sixteen]
  norm_num only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    Fin.reduceFinMk, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
    not_false_eq_true, Fin.isValue, Fin.mk.injEq, OfNat.ofNat_ne_zero,
    reduceCtorEq, or_self, or_false, false_or]
  simp only [e5, e6, e8767, e8772, e8777, e8782, e8787, e8792, e8797, e8802, e8807, e8812, e8817, e8822, e8827, e8832, e11642, e11643, e11644, e11645, e11646, e11647, e11648, e11649, e11650, e11651, e11652, e11653, e11654, e11655, e11656, e11657, e11658, e11659, e11660]
  rw [canonical_5426]
  rw [canonical_5427]
  rw [canonical_5428]
  rw [canonical_5429]
  rw [canonical_8763]
  rw [canonical_8764]
  rw [canonical_8765]
  rw [canonical_8766]
  rw [canonical_8768]
  rw [canonical_8769]
  rw [canonical_8770]
  rw [canonical_8771]
  rw [canonical_8773]
  rw [canonical_8774]
  rw [canonical_8775]
  rw [canonical_8776]
  rw [canonical_8778]
  rw [canonical_8779]
  rw [canonical_8780]
  rw [canonical_8781]
  rw [canonical_8783]
  rw [canonical_8784]
  rw [canonical_8785]
  rw [canonical_8786]
  rw [canonical_8788]
  rw [canonical_8789]
  rw [canonical_8790]
  rw [canonical_8791]
  rw [canonical_8793]
  rw [canonical_8794]
  rw [canonical_8795]
  rw [canonical_8796]
  rw [canonical_8798]
  rw [canonical_8799]
  rw [canonical_8800]
  rw [canonical_8801]
  rw [canonical_8803]
  rw [canonical_8804]
  rw [canonical_8805]
  rw [canonical_8806]
  rw [canonical_8808]
  rw [canonical_8809]
  rw [canonical_8810]
  rw [canonical_8811]
  rw [canonical_8813]
  rw [canonical_8814]
  rw [canonical_8815]
  rw [canonical_8816]
  rw [canonical_8818]
  rw [canonical_8819]
  rw [canonical_8820]
  rw [canonical_8821]
  rw [canonical_8823]
  rw [canonical_8824]
  rw [canonical_8825]
  rw [canonical_8826]
  rw [canonical_8828]
  rw [canonical_8829]
  rw [canonical_8830]
  rw [canonical_8831]
  rw [canonical_5489]
  rw [canonical_5493]
  rw [canonical_5497]
  rw [canonical_5501]
  simp only [one_mul, neg_mul, neg_one_mul]
  abel
end Assembly
