import ChecksR3_0111_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0111 : MaskR3.best (graph ⟨0,1,1,1⟩) = {398,454} := by
  apply MaskR3.best_of_checks (graph ⟨0,1,1,1⟩) 5 {398,454} (by decide) (by decide)
  have hall : ∀ b : Fin 2, MaskR3.blockCheck (graph ⟨0,1,1,1⟩) 5 {398,454} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0111_0
    · exact check_0111_1
  intro m hm ho
  change m < 512 at hm
  let b : Fin 2 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0111 : totals ⟨0,1,1,1⟩ 0 = 2 ∧ totals ⟨0,1,1,1⟩ 1 = 3 ∧ totals ⟨0,1,1,1⟩ 2 = 5 := by
  unfold totals
  rw [best_0111]
  decide
theorem count_0111 : count ⟨0,1,1,1⟩ = 2 := by
  unfold count
  rw [best_0111]
  decide
theorem bound_0111 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,1,1,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0111.1, totals_0111.2.1, totals_0111.2.2, count_0111]
end EdgePattern.TreeModelsR3
