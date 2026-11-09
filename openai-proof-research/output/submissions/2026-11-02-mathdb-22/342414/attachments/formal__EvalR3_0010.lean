import ChecksR3_0010_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0010 : MaskR3.best (graph ⟨0,0,1,0⟩) = {60,78,108} := by
  apply MaskR3.best_of_checks (graph ⟨0,0,1,0⟩) 4 {60,78,108} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨0,0,1,0⟩) 4 {60,78,108} (b.val * 128) 128 := by
    intro b
    fin_cases b
    · exact check_0010_0
  intro m hm ho
  change m < 128 at hm
  let b : Fin 1 := ⟨m / 128, by omega⟩
  let i : Fin 128 := ⟨m % 128, by omega⟩
  have he : b.val * 128 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0010 : totals ⟨0,0,1,0⟩ 0 = 1 ∧ totals ⟨0,0,1,0⟩ 1 = 9 ∧ totals ⟨0,0,1,0⟩ 2 = 2 := by
  unfold totals
  rw [best_0010]
  decide
theorem count_0010 : count ⟨0,0,1,0⟩ = 3 := by
  unfold count
  rw [best_0010]
  decide
theorem bound_0010 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,0,1,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0010.1, totals_0010.2.1, totals_0010.2.2, count_0010]
end EdgePattern.TreeModelsR3
