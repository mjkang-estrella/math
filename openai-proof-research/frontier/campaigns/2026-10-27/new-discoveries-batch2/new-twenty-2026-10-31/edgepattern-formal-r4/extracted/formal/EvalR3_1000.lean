import ChecksR3_1000_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1000 : MaskR3.best (graph ⟨1,0,0,0⟩) = {60,113,120} := by
  apply MaskR3.best_of_checks (graph ⟨1,0,0,0⟩) 4 {60,113,120} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨1,0,0,0⟩) 4 {60,113,120} (b.val * 128) 128 := by
    intro b
    fin_cases b
    · exact check_1000_0
  intro m hm ho
  change m < 128 at hm
  let b : Fin 1 := ⟨m / 128, by omega⟩
  let i : Fin 128 := ⟨m % 128, by omega⟩
  have he : b.val * 128 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1000 : totals ⟨1,0,0,0⟩ 0 = 1 ∧ totals ⟨1,0,0,0⟩ 1 = 9 ∧ totals ⟨1,0,0,0⟩ 2 = 2 := by
  unfold totals
  rw [best_1000]
  decide
theorem count_1000 : count ⟨1,0,0,0⟩ = 3 := by
  unfold count
  rw [best_1000]
  decide
theorem bound_1000 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,0,0,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1000.1, totals_1000.2.1, totals_1000.2.2, count_1000]
end EdgePattern.TreeModelsR3
