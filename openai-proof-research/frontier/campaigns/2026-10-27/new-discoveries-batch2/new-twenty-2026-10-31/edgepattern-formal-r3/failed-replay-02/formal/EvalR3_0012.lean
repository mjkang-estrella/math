import ChecksR3_0012_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0012 : MaskR3.best (graph ⟨0,0,1,2⟩) = {462} := by
  apply MaskR3.best_of_checks (graph ⟨0,0,1,2⟩) 6 {462} (by decide) (by decide)
  have hall : ∀ b : Fin 2, MaskR3.blockCheck (graph ⟨0,0,1,2⟩) 6 {462} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0012_0
    · exact check_0012_1
  intro m hm ho
  change m < 512 at hm
  let b : Fin 2 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0012 : totals ⟨0,0,1,2⟩ 0 = 1 ∧ totals ⟨0,0,1,2⟩ 1 = 2 ∧ totals ⟨0,0,1,2⟩ 2 = 3 := by
  unfold totals
  rw [best_0012]
  decide
theorem count_0012 : count ⟨0,0,1,2⟩ = 1 := by
  unfold count
  rw [best_0012]
  decide
theorem bound_0012 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,0,1,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0012.1, totals_0012.2.1, totals_0012.2.2, count_0012]
end EdgePattern.TreeModelsR3
