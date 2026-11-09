import ChecksR3_0122_0
import ChecksR3_0122_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0122 : MaskR3.best (graph ⟨0,1,2,2⟩) = {1934,1990} := by
  apply MaskR3.best_of_checks (graph ⟨0,1,2,2⟩) 7 {1934,1990} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨0,1,2,2⟩) 7 {1934,1990} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0122_0
    · exact check_0122_1
    · exact check_0122_2
    · exact check_0122_3
    · exact check_0122_4
    · exact check_0122_5
    · exact check_0122_6
    · exact check_0122_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0122 : totals ⟨0,1,2,2⟩ 0 = 2 ∧ totals ⟨0,1,2,2⟩ 1 = 3 ∧ totals ⟨0,1,2,2⟩ 2 = 9 := by
  unfold totals
  rw [best_0122]
  decide
theorem count_0122 : count ⟨0,1,2,2⟩ = 2 := by
  unfold count
  rw [best_0122]
  decide
theorem bound_0122 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,1,2,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0122.1, totals_0122.2.1, totals_0122.2.2, count_0122]
end EdgePattern.TreeModelsR3
