import ChecksR3_1210_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1210 : MaskR3.best (graph ⟨1,2,1,0⟩) = {497,993} := by
  apply MaskR3.best_of_checks (graph ⟨1,2,1,0⟩) 6 {497,993} (by decide) (by decide)
  have hall : ∀ b : Fin 4, MaskR3.blockCheck (graph ⟨1,2,1,0⟩) 6 {497,993} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1210_0
    · exact check_1210_1
    · exact check_1210_2
    · exact check_1210_3
  intro m hm ho
  change m < 1024 at hm
  let b : Fin 4 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1210 : totals ⟨1,2,1,0⟩ 0 = 2 ∧ totals ⟨1,2,1,0⟩ 1 = 3 ∧ totals ⟨1,2,1,0⟩ 2 = 7 := by
  unfold totals
  rw [best_1210]
  decide
theorem count_1210 : count ⟨1,2,1,0⟩ = 2 := by
  unfold count
  rw [best_1210]
  decide
theorem bound_1210 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,2,1,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1210.1, totals_1210.2.1, totals_1210.2.2, count_1210]
end EdgePattern.TreeModelsR3
