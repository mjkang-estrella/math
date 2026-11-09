import ChecksR3_2212_0
import ChecksR3_2212_1
import ChecksR3_2212_2
import ChecksR3_2212_3
import ChecksR3_2212_4
import ChecksR3_2212_5
import ChecksR3_2212_6
import ChecksR3_2212_7
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2212 : MaskR3.best (graph ⟨2,2,1,2⟩) = {7121,8129,8130} := by
  apply MaskR3.best_of_checks (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} (by decide) (by decide)
  have hall : ∀ b : Fin 32, MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2212_0
    · exact check_2212_1
    · exact check_2212_2
    · exact check_2212_3
    · exact check_2212_4
    · exact check_2212_5
    · exact check_2212_6
    · exact check_2212_7
    · exact check_2212_8
    · exact check_2212_9
    · exact check_2212_10
    · exact check_2212_11
    · exact check_2212_12
    · exact check_2212_13
    · exact check_2212_14
    · exact check_2212_15
    · exact check_2212_16
    · exact check_2212_17
    · exact check_2212_18
    · exact check_2212_19
    · exact check_2212_20
    · exact check_2212_21
    · exact check_2212_22
    · exact check_2212_23
    · exact check_2212_24
    · exact check_2212_25
    · exact check_2212_26
    · exact check_2212_27
    · exact check_2212_28
    · exact check_2212_29
    · exact check_2212_30
    · exact check_2212_31
  intro m hm ho
  change m < 8192 at hm
  let b : Fin 32 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2212 : totals ⟨2,2,1,2⟩ 0 = 3 ∧ totals ⟨2,2,1,2⟩ 1 = 1 ∧ totals ⟨2,2,1,2⟩ 2 = 20 := by
  unfold totals
  rw [best_2212]
  decide
theorem count_2212 : count ⟨2,2,1,2⟩ = 3 := by
  unfold count
  rw [best_2212]
  decide
theorem bound_2212 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,2,1,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2212.1, totals_2212.2.1, totals_2212.2.2, count_2212]
end EdgePattern.TreeModelsR3
