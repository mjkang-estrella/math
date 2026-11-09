import ChecksR3_2022_0
import ChecksR3_2022_1
import ChecksR3_2022_2
import ChecksR3_2022_3
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2022 : MaskR3.best (graph ⟨2,0,2,2⟩) = {4042} := by
  apply MaskR3.best_of_checks (graph ⟨2,0,2,2⟩) 8 {4042} (by decide) (by decide)
  have hall : ∀ b : Fin 16, MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2022_0
    · exact check_2022_1
    · exact check_2022_2
    · exact check_2022_3
    · exact check_2022_4
    · exact check_2022_5
    · exact check_2022_6
    · exact check_2022_7
    · exact check_2022_8
    · exact check_2022_9
    · exact check_2022_10
    · exact check_2022_11
    · exact check_2022_12
    · exact check_2022_13
    · exact check_2022_14
    · exact check_2022_15
  intro m hm ho
  change m < 4096 at hm
  let b : Fin 16 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2022 : totals ⟨2,0,2,2⟩ 0 = 1 ∧ totals ⟨2,0,2,2⟩ 1 = 1 ∧ totals ⟨2,0,2,2⟩ 2 = 6 := by
  unfold totals
  rw [best_2022]
  decide
theorem count_2022 : count ⟨2,0,2,2⟩ = 1 := by
  unfold count
  rw [best_2022]
  decide
theorem bound_2022 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,0,2,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2022.1, totals_2022.2.1, totals_2022.2.2, count_2022]
end EdgePattern.TreeModelsR3
