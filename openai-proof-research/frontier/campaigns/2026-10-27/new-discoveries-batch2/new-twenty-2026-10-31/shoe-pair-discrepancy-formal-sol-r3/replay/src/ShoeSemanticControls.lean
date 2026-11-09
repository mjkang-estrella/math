import ShoeEndpoint
import ShoeControls
namespace Shoe

def sameSideSample (n : ℕ) : ℕ := if n = 1 then 1 else 0

theorem same_side_repeat_control :
    sameSideSample 0 = sameSideSample 2 ∧ ¬ HasMatch sameSideSample 3 := by
  constructor
  · norm_num [sameSideSample]
  · rintro ⟨a,b,ha,hb,he⟩
    have hB : b = 0 := by omega
    have hA : a = 0 ∨ a = 1 := by omega
    subst b
    rcases hA with rfl | rfl <;> norm_num [sameSideSample] at he

theorem source_fallback_control (p : DiscreteLaw ℕ) (c d : ℕ) :
    sourceDiscrepancy p c = sourceDiscrepancy p d := by
  unfold sourceDiscrepancy
  rw [sourceY_eq,sourceY_eq]

theorem all_laws_control (p : DiscreteLaw ℕ) :
    sourceDiscrepancy p 0 ≤ 255/256 := sourceDiscrepancy_bound p 0
end Shoe
