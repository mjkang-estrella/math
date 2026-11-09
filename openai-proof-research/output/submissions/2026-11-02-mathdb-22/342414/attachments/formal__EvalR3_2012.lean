import ChecksR3_2012_0
import ChecksR3_2012_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2012 : MaskR3.best (graph ⟨2,0,1,2⟩) = {1994} := by
  apply MaskR3.best_of_checks (graph ⟨2,0,1,2⟩) 7 {1994} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2012_0
    · exact check_2012_1
    · exact check_2012_2
    · exact check_2012_3
    · exact check_2012_4
    · exact check_2012_5
    · exact check_2012_6
    · exact check_2012_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2012 : totals ⟨2,0,1,2⟩ 0 = 1 ∧ totals ⟨2,0,1,2⟩ 1 = 1 ∧ totals ⟨2,0,1,2⟩ 2 = 5 := by
  unfold totals
  rw [best_2012]
  decide
theorem count_2012 : count ⟨2,0,1,2⟩ = 1 := by
  unfold count
  rw [best_2012]
  decide
theorem bound_2012 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,0,1,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2012.1, totals_2012.2.1, totals_2012.2.2, count_2012]
end EdgePattern.TreeModelsR3
