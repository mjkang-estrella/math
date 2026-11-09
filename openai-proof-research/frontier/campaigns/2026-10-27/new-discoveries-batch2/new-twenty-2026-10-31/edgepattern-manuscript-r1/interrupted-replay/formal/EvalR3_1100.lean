import ChecksR3_1100_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1100 : MaskR3.best (graph ⟨1,1,0,0⟩) = {241} := by
  apply MaskR3.best_of_checks (graph ⟨1,1,0,0⟩) 5 {241} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨1,1,0,0⟩) 5 {241} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1100_0
  intro m hm ho
  change m < 256 at hm
  let b : Fin 1 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1100 : totals ⟨1,1,0,0⟩ 0 = 1 ∧ totals ⟨1,1,0,0⟩ 1 = 2 ∧ totals ⟨1,1,0,0⟩ 2 = 2 := by
  unfold totals
  rw [best_1100]
  decide
theorem count_1100 : count ⟨1,1,0,0⟩ = 1 := by
  unfold count
  rw [best_1100]
  decide
theorem bound_1100 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,1,0,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1100.1, totals_1100.2.1, totals_1100.2.2, count_1100]
end EdgePattern.TreeModelsR3
