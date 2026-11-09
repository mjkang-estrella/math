import ChecksR3_1022_0
import ChecksR3_1022_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1022 : MaskR3.best (graph ⟨1,0,2,2⟩) = {1934,1994} := by
  apply MaskR3.best_of_checks (graph ⟨1,0,2,2⟩) 7 {1934,1994} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1022_0
    · exact check_1022_1
    · exact check_1022_2
    · exact check_1022_3
    · exact check_1022_4
    · exact check_1022_5
    · exact check_1022_6
    · exact check_1022_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1022 : totals ⟨1,0,2,2⟩ 0 = 2 ∧ totals ⟨1,0,2,2⟩ 1 = 3 ∧ totals ⟨1,0,2,2⟩ 2 = 9 := by
  unfold totals
  rw [best_1022]
  decide
theorem count_1022 : count ⟨1,0,2,2⟩ = 2 := by
  unfold count
  rw [best_1022]
  decide
theorem bound_1022 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,0,2,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1022.1, totals_1022.2.1, totals_1022.2.2, count_1022]
end EdgePattern.TreeModelsR3
