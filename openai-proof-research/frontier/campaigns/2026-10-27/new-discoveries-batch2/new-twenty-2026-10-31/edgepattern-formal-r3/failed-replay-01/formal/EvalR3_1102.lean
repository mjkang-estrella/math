import ChecksR3_1102_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1102 : MaskR3.best (graph ⟨1,1,0,2⟩) = {977} := by
  apply MaskR3.best_of_checks (graph ⟨1,1,0,2⟩) 6 {977} (by decide) (by decide)
  have hall : ∀ b : Fin 4, MaskR3.blockCheck (graph ⟨1,1,0,2⟩) 6 {977} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1102_0
    · exact check_1102_1
    · exact check_1102_2
    · exact check_1102_3
  intro m hm ho
  change m < 1024 at hm
  let b : Fin 4 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1102 : totals ⟨1,1,0,2⟩ 0 = 1 ∧ totals ⟨1,1,0,2⟩ 1 = 1 ∧ totals ⟨1,1,0,2⟩ 2 = 4 := by
  unfold totals
  rw [best_1102]
  decide
theorem count_1102 : count ⟨1,1,0,2⟩ = 1 := by
  unfold count
  rw [best_1102]
  decide
theorem bound_1102 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,1,0,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1102.1, totals_1102.2.1, totals_1102.2.2, count_1102]
end EdgePattern.TreeModelsR3
