import ChecksR3_1221_0
import ChecksR3_1221_1
import ChecksR3_1221_2
import ChecksR3_1221_3
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1221 : MaskR3.best (graph ⟨1,2,2,1⟩) = {2017,3974,4033,4034} := by
  apply MaskR3.best_of_checks (graph ⟨1,2,2,1⟩) 7 {2017,3974,4033,4034} (by decide) (by decide)
  have hall : ∀ b : Fin 16, MaskR3.blockCheck (graph ⟨1,2,2,1⟩) 7 {2017,3974,4033,4034} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1221_0
    · exact check_1221_1
    · exact check_1221_2
    · exact check_1221_3
    · exact check_1221_4
    · exact check_1221_5
    · exact check_1221_6
    · exact check_1221_7
    · exact check_1221_8
    · exact check_1221_9
    · exact check_1221_10
    · exact check_1221_11
    · exact check_1221_12
    · exact check_1221_13
    · exact check_1221_14
    · exact check_1221_15
  intro m hm ho
  change m < 4096 at hm
  let b : Fin 16 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1221 : totals ⟨1,2,2,1⟩ 0 = 4 ∧ totals ⟨1,2,2,1⟩ 1 = 2 ∧ totals ⟨1,2,2,1⟩ 2 = 22 := by
  unfold totals
  rw [best_1221]
  decide
theorem count_1221 : count ⟨1,2,2,1⟩ = 4 := by
  unfold count
  rw [best_1221]
  decide
theorem bound_1221 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,2,2,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1221.1, totals_1221.2.1, totals_1221.2.2, count_1221]
end EdgePattern.TreeModelsR3
