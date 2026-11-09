import ChecksR3_1101_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1101 : MaskR3.best (graph ⟨1,1,0,1⟩) = {241,465} := by
  apply MaskR3.best_of_checks (graph ⟨1,1,0,1⟩) 5 {241,465} (by decide) (by decide)
  have hall : ∀ b : Fin 2, MaskR3.blockCheck (graph ⟨1,1,0,1⟩) 5 {241,465} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1101_0
    · exact check_1101_1
  intro m hm ho
  change m < 512 at hm
  let b : Fin 2 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1101 : totals ⟨1,1,0,1⟩ 0 = 2 ∧ totals ⟨1,1,0,1⟩ 1 = 3 ∧ totals ⟨1,1,0,1⟩ 2 = 5 := by
  unfold totals
  rw [best_1101]
  decide
theorem count_1101 : count ⟨1,1,0,1⟩ = 2 := by
  unfold count
  rw [best_1101]
  decide
theorem bound_1101 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,1,0,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1101.1, totals_1101.2.1, totals_1101.2.2, count_1101]
end EdgePattern.TreeModelsR3
