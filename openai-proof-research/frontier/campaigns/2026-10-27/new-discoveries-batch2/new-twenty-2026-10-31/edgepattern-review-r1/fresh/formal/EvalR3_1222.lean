import ChecksR3_1222_0
import ChecksR3_1222_1
import ChecksR3_1222_2
import ChecksR3_1222_3
import ChecksR3_1222_4
import ChecksR3_1222_5
import ChecksR3_1222_6
import ChecksR3_1222_7
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1222 : MaskR3.best (graph ⟨1,2,2,2⟩) = {8070,8129,8130} := by
  apply MaskR3.best_of_checks (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} (by decide) (by decide)
  have hall : ∀ b : Fin 32, MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1222_0
    · exact check_1222_1
    · exact check_1222_2
    · exact check_1222_3
    · exact check_1222_4
    · exact check_1222_5
    · exact check_1222_6
    · exact check_1222_7
    · exact check_1222_8
    · exact check_1222_9
    · exact check_1222_10
    · exact check_1222_11
    · exact check_1222_12
    · exact check_1222_13
    · exact check_1222_14
    · exact check_1222_15
    · exact check_1222_16
    · exact check_1222_17
    · exact check_1222_18
    · exact check_1222_19
    · exact check_1222_20
    · exact check_1222_21
    · exact check_1222_22
    · exact check_1222_23
    · exact check_1222_24
    · exact check_1222_25
    · exact check_1222_26
    · exact check_1222_27
    · exact check_1222_28
    · exact check_1222_29
    · exact check_1222_30
    · exact check_1222_31
  intro m hm ho
  change m < 8192 at hm
  let b : Fin 32 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1222 : totals ⟨1,2,2,2⟩ 0 = 3 ∧ totals ⟨1,2,2,2⟩ 1 = 1 ∧ totals ⟨1,2,2,2⟩ 2 = 20 := by
  unfold totals
  rw [best_1222]
  decide
theorem count_1222 : count ⟨1,2,2,2⟩ = 3 := by
  unfold count
  rw [best_1222]
  decide
theorem bound_1222 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,2,2,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1222.1, totals_1222.2.1, totals_1222.2.2, count_1222]
end EdgePattern.TreeModelsR3
