import ChecksR3_2211_0
import ChecksR3_2211_1
import ChecksR3_2211_2
import ChecksR3_2211_3
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2211 : MaskR3.best (graph ⟨2,2,1,1⟩) = {1009,2017,3025,4033,4034} := by
  apply MaskR3.best_of_checks (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} (by decide) (by decide)
  have hall : ∀ b : Fin 16, MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2211_0
    · exact check_2211_1
    · exact check_2211_2
    · exact check_2211_3
    · exact check_2211_4
    · exact check_2211_5
    · exact check_2211_6
    · exact check_2211_7
    · exact check_2211_8
    · exact check_2211_9
    · exact check_2211_10
    · exact check_2211_11
    · exact check_2211_12
    · exact check_2211_13
    · exact check_2211_14
    · exact check_2211_15
  intro m hm ho
  change m < 4096 at hm
  let b : Fin 16 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2211 : totals ⟨2,2,1,1⟩ 0 = 5 ∧ totals ⟨2,2,1,1⟩ 1 = 4 ∧ totals ⟨2,2,1,1⟩ 2 = 26 := by
  unfold totals
  rw [best_2211]
  decide
theorem count_2211 : count ⟨2,2,1,1⟩ = 5 := by
  unfold count
  rw [best_2211]
  decide
theorem bound_2211 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,2,1,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2211.1, totals_2211.2.1, totals_2211.2.2, count_2211]
end EdgePattern.TreeModelsR3
