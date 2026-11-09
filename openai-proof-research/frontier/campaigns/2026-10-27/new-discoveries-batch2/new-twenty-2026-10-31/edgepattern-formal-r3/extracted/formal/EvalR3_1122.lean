import ChecksR3_1122_0
import ChecksR3_1122_1
import ChecksR3_1122_2
import ChecksR3_1122_3
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1122 : MaskR3.best (graph ⟨1,1,2,2⟩) = {3854,3914,3974,4033,4034} := by
  apply MaskR3.best_of_checks (graph ⟨1,1,2,2⟩) 7 {3854,3914,3974,4033,4034} (by decide) (by decide)
  have hall : ∀ b : Fin 16, MaskR3.blockCheck (graph ⟨1,1,2,2⟩) 7 {3854,3914,3974,4033,4034} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1122_0
    · exact check_1122_1
    · exact check_1122_2
    · exact check_1122_3
    · exact check_1122_4
    · exact check_1122_5
    · exact check_1122_6
    · exact check_1122_7
    · exact check_1122_8
    · exact check_1122_9
    · exact check_1122_10
    · exact check_1122_11
    · exact check_1122_12
    · exact check_1122_13
    · exact check_1122_14
    · exact check_1122_15
  intro m hm ho
  change m < 4096 at hm
  let b : Fin 16 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1122 : totals ⟨1,1,2,2⟩ 0 = 5 ∧ totals ⟨1,1,2,2⟩ 1 = 4 ∧ totals ⟨1,1,2,2⟩ 2 = 26 := by
  unfold totals
  rw [best_1122]
  decide
theorem count_1122 : count ⟨1,1,2,2⟩ = 5 := by
  unfold count
  rw [best_1122]
  decide
theorem bound_1122 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,1,2,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1122.1, totals_1122.2.1, totals_1122.2.2, count_1122]
end EdgePattern.TreeModelsR3
