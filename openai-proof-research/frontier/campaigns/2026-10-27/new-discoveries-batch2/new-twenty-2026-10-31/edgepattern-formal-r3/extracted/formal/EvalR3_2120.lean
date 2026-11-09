import ChecksR3_2120_0
import ChecksR3_2120_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2120 : MaskR3.best (graph ⟨2,1,2,0⟩) = {2017} := by
  apply MaskR3.best_of_checks (graph ⟨2,1,2,0⟩) 7 {2017} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨2,1,2,0⟩) 7 {2017} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2120_0
    · exact check_2120_1
    · exact check_2120_2
    · exact check_2120_3
    · exact check_2120_4
    · exact check_2120_5
    · exact check_2120_6
    · exact check_2120_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2120 : totals ⟨2,1,2,0⟩ 0 = 1 ∧ totals ⟨2,1,2,0⟩ 1 = 1 ∧ totals ⟨2,1,2,0⟩ 2 = 5 := by
  unfold totals
  rw [best_2120]
  decide
theorem count_2120 : count ⟨2,1,2,0⟩ = 1 := by
  unfold count
  rw [best_2120]
  decide
theorem bound_2120 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,1,2,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2120.1, totals_2120.2.1, totals_2120.2.2, count_2120]
end EdgePattern.TreeModelsR3
