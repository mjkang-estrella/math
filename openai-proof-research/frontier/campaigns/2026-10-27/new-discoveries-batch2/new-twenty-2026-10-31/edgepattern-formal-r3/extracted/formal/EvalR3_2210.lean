import ChecksR3_2210_0
import ChecksR3_2210_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2210 : MaskR3.best (graph ⟨2,2,1,0⟩) = {1009,2017} := by
  apply MaskR3.best_of_checks (graph ⟨2,2,1,0⟩) 7 {1009,2017} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨2,2,1,0⟩) 7 {1009,2017} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2210_0
    · exact check_2210_1
    · exact check_2210_2
    · exact check_2210_3
    · exact check_2210_4
    · exact check_2210_5
    · exact check_2210_6
    · exact check_2210_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2210 : totals ⟨2,2,1,0⟩ 0 = 2 ∧ totals ⟨2,2,1,0⟩ 1 = 3 ∧ totals ⟨2,2,1,0⟩ 2 = 9 := by
  unfold totals
  rw [best_2210]
  decide
theorem count_2210 : count ⟨2,2,1,0⟩ = 2 := by
  unfold count
  rw [best_2210]
  decide
theorem bound_2210 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,2,1,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2210.1, totals_2210.2.1, totals_2210.2.2, count_2210]
end EdgePattern.TreeModelsR3
