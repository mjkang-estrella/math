import ChecksR3_0000_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0000 : MaskR3.best (graph ⟨0,0,0,0⟩) = {60} := by
  apply MaskR3.best_of_checks (graph ⟨0,0,0,0⟩) 4 {60} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨0,0,0,0⟩) 4 {60} (b.val * 64) 64 := by
    intro b
    fin_cases b
    · exact check_0000_0
  intro m hm ho
  change m < 64 at hm
  let b : Fin 1 := ⟨m / 64, by omega⟩
  let i : Fin 64 := ⟨m % 64, by omega⟩
  have he : b.val * 64 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0000 : totals ⟨0,0,0,0⟩ 0 = 0 ∧ totals ⟨0,0,0,0⟩ 1 = 4 ∧ totals ⟨0,0,0,0⟩ 2 = 0 := by
  unfold totals
  rw [best_0000]
  decide
theorem count_0000 : count ⟨0,0,0,0⟩ = 1 := by
  unfold count
  rw [best_0000]
  decide
theorem bound_0000 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,0,0,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0000.1, totals_0000.2.1, totals_0000.2.2, count_0000]
end EdgePattern.TreeModelsR3
