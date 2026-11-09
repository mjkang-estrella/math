import ChecksR3_2220_0
import ChecksR3_2220_1
import ChecksR3_2220_2
import ChecksR3_2220_3
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2220 : MaskR3.best (graph ⟨2,2,2,0⟩) = {4065} := by
  apply MaskR3.best_of_checks (graph ⟨2,2,2,0⟩) 8 {4065} (by decide) (by decide)
  have hall : ∀ b : Fin 16, MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2220_0
    · exact check_2220_1
    · exact check_2220_2
    · exact check_2220_3
    · exact check_2220_4
    · exact check_2220_5
    · exact check_2220_6
    · exact check_2220_7
    · exact check_2220_8
    · exact check_2220_9
    · exact check_2220_10
    · exact check_2220_11
    · exact check_2220_12
    · exact check_2220_13
    · exact check_2220_14
    · exact check_2220_15
  intro m hm ho
  change m < 4096 at hm
  let b : Fin 16 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2220 : totals ⟨2,2,2,0⟩ 0 = 1 ∧ totals ⟨2,2,2,0⟩ 1 = 1 ∧ totals ⟨2,2,2,0⟩ 2 = 6 := by
  unfold totals
  rw [best_2220]
  decide
theorem count_2220 : count ⟨2,2,2,0⟩ = 1 := by
  unfold count
  rw [best_2220]
  decide
theorem bound_2220 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,2,2,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2220.1, totals_2220.2.1, totals_2220.2.2, count_2220]
end EdgePattern.TreeModelsR3
