import ChecksR3_2112_0
import ChecksR3_2112_1
import ChecksR3_2112_2
import ChecksR3_2112_3
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2112 : MaskR3.best (graph ⟨2,1,1,2⟩) = {3537,3786,4033,4034} := by
  apply MaskR3.best_of_checks (graph ⟨2,1,1,2⟩) 7 {3537,3786,4033,4034} (by decide) (by decide)
  have hall : ∀ b : Fin 16, MaskR3.blockCheck (graph ⟨2,1,1,2⟩) 7 {3537,3786,4033,4034} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2112_0
    · exact check_2112_1
    · exact check_2112_2
    · exact check_2112_3
    · exact check_2112_4
    · exact check_2112_5
    · exact check_2112_6
    · exact check_2112_7
    · exact check_2112_8
    · exact check_2112_9
    · exact check_2112_10
    · exact check_2112_11
    · exact check_2112_12
    · exact check_2112_13
    · exact check_2112_14
    · exact check_2112_15
  intro m hm ho
  change m < 4096 at hm
  let b : Fin 16 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2112 : totals ⟨2,1,1,2⟩ 0 = 4 ∧ totals ⟨2,1,1,2⟩ 1 = 2 ∧ totals ⟨2,1,1,2⟩ 2 = 22 := by
  unfold totals
  rw [best_2112]
  decide
theorem count_2112 : count ⟨2,1,1,2⟩ = 4 := by
  unfold count
  rw [best_2112]
  decide
theorem bound_2112 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,1,1,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2112.1, totals_2112.2.1, totals_2112.2.2, count_2112]
end EdgePattern.TreeModelsR3
