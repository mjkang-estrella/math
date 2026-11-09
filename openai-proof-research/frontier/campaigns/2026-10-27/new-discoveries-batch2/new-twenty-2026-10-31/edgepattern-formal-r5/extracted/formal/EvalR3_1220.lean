import ChecksR3_1220_0
import ChecksR3_1220_1
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1220 : MaskR3.best (graph ⟨1,2,2,0⟩) = {2017} := by
  apply MaskR3.best_of_checks (graph ⟨1,2,2,0⟩) 7 {2017} (by decide) (by decide)
  have hall : ∀ b : Fin 8, MaskR3.blockCheck (graph ⟨1,2,2,0⟩) 7 {2017} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1220_0
    · exact check_1220_1
    · exact check_1220_2
    · exact check_1220_3
    · exact check_1220_4
    · exact check_1220_5
    · exact check_1220_6
    · exact check_1220_7
  intro m hm ho
  change m < 2048 at hm
  let b : Fin 8 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1220 : totals ⟨1,2,2,0⟩ 0 = 1 ∧ totals ⟨1,2,2,0⟩ 1 = 1 ∧ totals ⟨1,2,2,0⟩ 2 = 5 := by
  unfold totals
  rw [best_1220]
  decide
theorem count_1220 : count ⟨1,2,2,0⟩ = 1 := by
  unfold count
  rw [best_1220]
  decide
theorem bound_1220 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,2,2,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1220.1, totals_1220.2.1, totals_1220.2.2, count_1220]
end EdgePattern.TreeModelsR3
