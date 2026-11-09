import ChecksR3_1202_0
import ChecksR3_1202_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1202 : MaskR3.best (graph ⟨1,2,0,2⟩) = {2001} := by
  apply MaskR3.best_of_checks (graph ⟨1,2,0,2⟩) 7 {2001} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨1,2,0,2⟩) 7 {2001} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1202_0
    · exact check_1202_1
    · exact check_1202_2
    · exact check_1202_3
    · exact check_1202_4
    · exact check_1202_5
    · exact check_1202_6
    · exact check_1202_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1202 : totals ⟨1,2,0,2⟩ 0 = 1 ∧ totals ⟨1,2,0,2⟩ 1 = 1 ∧ totals ⟨1,2,0,2⟩ 2 = 5 := by
  unfold totals
  rw [best_1202]
  decide
theorem count_1202 : count ⟨1,2,0,2⟩ = 1 := by
  unfold count
  rw [best_1202]
  decide
theorem bound_1202 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,2,0,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1202.1, totals_1202.2.1, totals_1202.2.2, count_1202]
end EdgePattern.TreeModelsR3
