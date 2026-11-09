import ChecksR3_2201_0
import ChecksR3_2201_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2201 : MaskR3.best (graph ⟨2,2,0,1⟩) = {1009,2001} := by
  apply MaskR3.best_of_checks (graph ⟨2,2,0,1⟩) 7 {1009,2001} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2201_0
    · exact check_2201_1
    · exact check_2201_2
    · exact check_2201_3
    · exact check_2201_4
    · exact check_2201_5
    · exact check_2201_6
    · exact check_2201_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2201 : totals ⟨2,2,0,1⟩ 0 = 2 ∧ totals ⟨2,2,0,1⟩ 1 = 3 ∧ totals ⟨2,2,0,1⟩ 2 = 9 := by
  unfold totals
  rw [best_2201]
  decide
theorem count_2201 : count ⟨2,2,0,1⟩ = 2 := by
  unfold count
  rw [best_2201]
  decide
theorem bound_2201 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,2,0,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2201.1, totals_2201.2.1, totals_2201.2.2, count_2201]
end EdgePattern.TreeModelsR3
