import ChecksR3_2111_0
import ChecksR3_2111_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2111 : MaskR3.best (graph ⟨2,1,1,1⟩) = {497,993,1489,1738,1985,1986} := by
  apply MaskR3.best_of_checks (graph ⟨2,1,1,1⟩) 6 {497,993,1489,1738,1985,1986} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨2,1,1,1⟩) 6 {497,993,1489,1738,1985,1986} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2111_0
    · exact check_2111_1
    · exact check_2111_2
    · exact check_2111_3
    · exact check_2111_4
    · exact check_2111_5
    · exact check_2111_6
    · exact check_2111_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2111 : totals ⟨2,1,1,1⟩ 0 = 6 ∧ totals ⟨2,1,1,1⟩ 1 = 5 ∧ totals ⟨2,1,1,1⟩ 2 = 25 := by
  unfold totals
  rw [best_2111]
  decide
theorem count_2111 : count ⟨2,1,1,1⟩ = 6 := by
  unfold count
  rw [best_2111]
  decide
theorem bound_2111 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,1,1,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2111.1, totals_2111.2.1, totals_2111.2.2, count_2111]
end EdgePattern.TreeModelsR3
