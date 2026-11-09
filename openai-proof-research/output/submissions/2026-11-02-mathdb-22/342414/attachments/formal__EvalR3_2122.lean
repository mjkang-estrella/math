import ChecksR3_2122_0
import ChecksR3_2122_1
import ChecksR3_2122_2
import ChecksR3_2122_3
import ChecksR3_2122_4
import ChecksR3_2122_5
import ChecksR3_2122_6
import ChecksR3_2122_7
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2122 : MaskR3.best (graph ⟨2,1,2,2⟩) = {7882,8129,8130} := by
  apply MaskR3.best_of_checks (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} (by decide) (by decide)
  have hall : ∀ b : Fin 32, MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2122_0
    · exact check_2122_1
    · exact check_2122_2
    · exact check_2122_3
    · exact check_2122_4
    · exact check_2122_5
    · exact check_2122_6
    · exact check_2122_7
    · exact check_2122_8
    · exact check_2122_9
    · exact check_2122_10
    · exact check_2122_11
    · exact check_2122_12
    · exact check_2122_13
    · exact check_2122_14
    · exact check_2122_15
    · exact check_2122_16
    · exact check_2122_17
    · exact check_2122_18
    · exact check_2122_19
    · exact check_2122_20
    · exact check_2122_21
    · exact check_2122_22
    · exact check_2122_23
    · exact check_2122_24
    · exact check_2122_25
    · exact check_2122_26
    · exact check_2122_27
    · exact check_2122_28
    · exact check_2122_29
    · exact check_2122_30
    · exact check_2122_31
  intro m hm ho
  change m < 8192 at hm
  let b : Fin 32 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2122 : totals ⟨2,1,2,2⟩ 0 = 3 ∧ totals ⟨2,1,2,2⟩ 1 = 1 ∧ totals ⟨2,1,2,2⟩ 2 = 20 := by
  unfold totals
  rw [best_2122]
  decide
theorem count_2122 : count ⟨2,1,2,2⟩ = 3 := by
  unfold count
  rw [best_2122]
  decide
theorem bound_2122 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,1,2,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2122.1, totals_2122.2.1, totals_2122.2.2, count_2122]
end EdgePattern.TreeModelsR3
