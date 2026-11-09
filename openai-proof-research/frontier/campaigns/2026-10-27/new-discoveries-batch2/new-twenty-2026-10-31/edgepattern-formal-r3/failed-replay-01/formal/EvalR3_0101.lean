import ChecksR3_0101_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0101 : MaskR3.best (graph ⟨0,1,0,1⟩) = {60,113,116,142,156,198,209,212} := by
  apply MaskR3.best_of_checks (graph ⟨0,1,0,1⟩) 4 {60,113,116,142,156,198,209,212} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨0,1,0,1⟩) 4 {60,113,116,142,156,198,209,212} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0101_0
  intro m hm ho
  change m < 256 at hm
  let b : Fin 1 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0101 : totals ⟨0,1,0,1⟩ 0 = 4 ∧ totals ⟨0,1,0,1⟩ 1 = 18 ∧ totals ⟨0,1,0,1⟩ 2 = 10 := by
  unfold totals
  rw [best_0101]
  decide
theorem count_0101 : count ⟨0,1,0,1⟩ = 8 := by
  unfold count
  rw [best_0101]
  decide
theorem bound_0101 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,1,0,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0101.1, totals_0101.2.1, totals_0101.2.2, count_0101]
end EdgePattern.TreeModelsR3
