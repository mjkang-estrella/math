import ChecksR3_0201_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0201 : MaskR3.best (graph ⟨0,2,0,1⟩) = {241,244,454,465,468} := by
  apply MaskR3.best_of_checks (graph ⟨0,2,0,1⟩) 5 {241,244,454,465,468} (by decide) (by decide)
  have hall : ∀ b : Fin 2, MaskR3.blockCheck (graph ⟨0,2,0,1⟩) 5 {241,244,454,465,468} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0201_0
    · exact check_0201_1
  intro m hm ho
  change m < 512 at hm
  let b : Fin 2 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0201 : totals ⟨0,2,0,1⟩ 0 = 3 ∧ totals ⟨0,2,0,1⟩ 1 = 9 ∧ totals ⟨0,2,0,1⟩ 2 = 13 := by
  unfold totals
  rw [best_0201]
  decide
theorem count_0201 : count ⟨0,2,0,1⟩ = 5 := by
  unfold count
  rw [best_0201]
  decide
theorem bound_0201 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,2,0,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0201.1, totals_0201.2.1, totals_0201.2.2, count_0201]
end EdgePattern.TreeModelsR3
