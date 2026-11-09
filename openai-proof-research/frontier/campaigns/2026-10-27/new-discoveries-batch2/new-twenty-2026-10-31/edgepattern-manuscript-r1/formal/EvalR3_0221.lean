import ChecksR3_0221_0
import ChecksR3_0221_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0221 : MaskR3.best (graph ⟨0,2,2,1⟩) = {1990} := by
  apply MaskR3.best_of_checks (graph ⟨0,2,2,1⟩) 7 {1990} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨0,2,2,1⟩) 7 {1990} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0221_0
    · exact check_0221_1
    · exact check_0221_2
    · exact check_0221_3
    · exact check_0221_4
    · exact check_0221_5
    · exact check_0221_6
    · exact check_0221_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0221 : totals ⟨0,2,2,1⟩ 0 = 1 ∧ totals ⟨0,2,2,1⟩ 1 = 1 ∧ totals ⟨0,2,2,1⟩ 2 = 5 := by
  unfold totals
  rw [best_0221]
  decide
theorem count_0221 : count ⟨0,2,2,1⟩ = 1 := by
  unfold count
  rw [best_0221]
  decide
theorem bound_0221 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,2,2,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0221.1, totals_0221.2.1, totals_0221.2.2, count_0221]
end EdgePattern.TreeModelsR3
