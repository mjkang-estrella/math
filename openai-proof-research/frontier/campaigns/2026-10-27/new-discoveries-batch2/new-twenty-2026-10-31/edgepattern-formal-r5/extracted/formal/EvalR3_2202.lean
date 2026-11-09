import ChecksR3_2202_0
import ChecksR3_2202_1
import ChecksR3_2202_2
import ChecksR3_2202_3
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2202 : MaskR3.best (graph ⟨2,2,0,2⟩) = {4049} := by
  apply MaskR3.best_of_checks (graph ⟨2,2,0,2⟩) 8 {4049} (by decide) (by decide)
  have hall : ∀ b : Fin 16, MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2202_0
    · exact check_2202_1
    · exact check_2202_2
    · exact check_2202_3
    · exact check_2202_4
    · exact check_2202_5
    · exact check_2202_6
    · exact check_2202_7
    · exact check_2202_8
    · exact check_2202_9
    · exact check_2202_10
    · exact check_2202_11
    · exact check_2202_12
    · exact check_2202_13
    · exact check_2202_14
    · exact check_2202_15
  intro m hm ho
  change m < 4096 at hm
  let b : Fin 16 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2202 : totals ⟨2,2,0,2⟩ 0 = 1 ∧ totals ⟨2,2,0,2⟩ 1 = 1 ∧ totals ⟨2,2,0,2⟩ 2 = 6 := by
  unfold totals
  rw [best_2202]
  decide
theorem count_2202 : count ⟨2,2,0,2⟩ = 1 := by
  unfold count
  rw [best_2202]
  decide
theorem bound_2202 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,2,0,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2202.1, totals_2202.2.1, totals_2202.2.2, count_2202]
end EdgePattern.TreeModelsR3
