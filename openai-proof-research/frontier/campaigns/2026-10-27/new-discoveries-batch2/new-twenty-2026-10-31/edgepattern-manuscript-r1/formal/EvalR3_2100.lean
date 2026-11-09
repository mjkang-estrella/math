import ChecksR3_2100_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2100 : MaskR3.best (graph ⟨2,1,0,0⟩) = {497} := by
  apply MaskR3.best_of_checks (graph ⟨2,1,0,0⟩) 6 {497} (by decide) (by decide)
  have hall : ∀ b : Fin 2, MaskR3.blockCheck (graph ⟨2,1,0,0⟩) 6 {497} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2100_0
    · exact check_2100_1
  intro m hm ho
  change m < 512 at hm
  let b : Fin 2 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2100 : totals ⟨2,1,0,0⟩ 0 = 1 ∧ totals ⟨2,1,0,0⟩ 1 = 2 ∧ totals ⟨2,1,0,0⟩ 2 = 3 := by
  unfold totals
  rw [best_2100]
  decide
theorem count_2100 : count ⟨2,1,0,0⟩ = 1 := by
  unfold count
  rw [best_2100]
  decide
theorem bound_2100 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,1,0,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2100.1, totals_2100.2.1, totals_2100.2.2, count_2100]
end EdgePattern.TreeModelsR3
