import ChecksR3_1001_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1001 : MaskR3.best (graph ⟨1,0,0,1⟩) = {60,113,120,142,156,202,209,216} := by
  apply MaskR3.best_of_checks (graph ⟨1,0,0,1⟩) 4 {60,113,120,142,156,202,209,216} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨1,0,0,1⟩) 4 {60,113,120,142,156,202,209,216} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1001_0
  intro m hm ho
  change m < 256 at hm
  let b : Fin 1 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1001 : totals ⟨1,0,0,1⟩ 0 = 4 ∧ totals ⟨1,0,0,1⟩ 1 = 18 ∧ totals ⟨1,0,0,1⟩ 2 = 10 := by
  unfold totals
  rw [best_1001]
  decide
theorem count_1001 : count ⟨1,0,0,1⟩ = 8 := by
  unfold count
  rw [best_1001]
  decide
theorem bound_1001 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,0,0,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1001.1, totals_1001.2.1, totals_1001.2.2, count_1001]
end EdgePattern.TreeModelsR3
