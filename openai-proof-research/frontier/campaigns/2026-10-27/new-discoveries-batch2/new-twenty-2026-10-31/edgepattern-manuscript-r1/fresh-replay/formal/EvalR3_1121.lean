import ChecksR3_1121_0
import ChecksR3_1121_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1121 : MaskR3.best (graph ⟨1,1,2,1⟩) = {993,1806,1866,1926,1985,1986} := by
  apply MaskR3.best_of_checks (graph ⟨1,1,2,1⟩) 6 {993,1806,1866,1926,1985,1986} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨1,1,2,1⟩) 6 {993,1806,1866,1926,1985,1986} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1121_0
    · exact check_1121_1
    · exact check_1121_2
    · exact check_1121_3
    · exact check_1121_4
    · exact check_1121_5
    · exact check_1121_6
    · exact check_1121_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1121 : totals ⟨1,1,2,1⟩ 0 = 6 ∧ totals ⟨1,1,2,1⟩ 1 = 5 ∧ totals ⟨1,1,2,1⟩ 2 = 25 := by
  unfold totals
  rw [best_1121]
  decide
theorem count_1121 : count ⟨1,1,2,1⟩ = 6 := by
  unfold count
  rw [best_1121]
  decide
theorem bound_1121 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,1,2,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1121.1, totals_1121.2.1, totals_1121.2.2, count_1121]
end EdgePattern.TreeModelsR3
