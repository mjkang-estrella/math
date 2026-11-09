import ChecksR3_2021_0
import ChecksR3_2021_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2021 : MaskR3.best (graph ⟨2,0,2,1⟩) = {1994} := by
  apply MaskR3.best_of_checks (graph ⟨2,0,2,1⟩) 7 {1994} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨2,0,2,1⟩) 7 {1994} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2021_0
    · exact check_2021_1
    · exact check_2021_2
    · exact check_2021_3
    · exact check_2021_4
    · exact check_2021_5
    · exact check_2021_6
    · exact check_2021_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2021 : totals ⟨2,0,2,1⟩ 0 = 1 ∧ totals ⟨2,0,2,1⟩ 1 = 1 ∧ totals ⟨2,0,2,1⟩ 2 = 5 := by
  unfold totals
  rw [best_2021]
  decide
theorem count_2021 : count ⟨2,0,2,1⟩ = 1 := by
  unfold count
  rw [best_2021]
  decide
theorem bound_2021 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,0,2,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2021.1, totals_2021.2.1, totals_2021.2.2, count_2021]
end EdgePattern.TreeModelsR3
