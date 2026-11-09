import ChecksR3_2221_0
import ChecksR3_2221_1
import ChecksR3_2221_2
import ChecksR3_2221_3
import ChecksR3_2221_4
import ChecksR3_2221_5
import ChecksR3_2221_6
import ChecksR3_2221_7
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2221 : MaskR3.best (graph ⟨2,2,2,1⟩) = {4065,8129,8130} := by
  apply MaskR3.best_of_checks (graph ⟨2,2,2,1⟩) 8 {4065,8129,8130} (by decide) (by decide)
  have hall : ∀ b : Fin 32, MaskR3.blockCheck (graph ⟨2,2,2,1⟩) 8 {4065,8129,8130} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2221_0
    · exact check_2221_1
    · exact check_2221_2
    · exact check_2221_3
    · exact check_2221_4
    · exact check_2221_5
    · exact check_2221_6
    · exact check_2221_7
    · exact check_2221_8
    · exact check_2221_9
    · exact check_2221_10
    · exact check_2221_11
    · exact check_2221_12
    · exact check_2221_13
    · exact check_2221_14
    · exact check_2221_15
    · exact check_2221_16
    · exact check_2221_17
    · exact check_2221_18
    · exact check_2221_19
    · exact check_2221_20
    · exact check_2221_21
    · exact check_2221_22
    · exact check_2221_23
    · exact check_2221_24
    · exact check_2221_25
    · exact check_2221_26
    · exact check_2221_27
    · exact check_2221_28
    · exact check_2221_29
    · exact check_2221_30
    · exact check_2221_31
  intro m hm ho
  change m < 8192 at hm
  let b : Fin 32 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2221 : totals ⟨2,2,2,1⟩ 0 = 3 ∧ totals ⟨2,2,2,1⟩ 1 = 1 ∧ totals ⟨2,2,2,1⟩ 2 = 20 := by
  unfold totals
  rw [best_2221]
  decide
theorem count_2221 : count ⟨2,2,2,1⟩ = 3 := by
  unfold count
  rw [best_2221]
  decide
theorem bound_2221 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,2,2,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2221.1, totals_2221.2.1, totals_2221.2.2, count_2221]
end EdgePattern.TreeModelsR3
