import ChecksR3_1010_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1010 : MaskR3.best (graph ⟨1,0,1,0⟩) = {60,113,120,142,172,202,225,232} := by
  apply MaskR3.best_of_checks (graph ⟨1,0,1,0⟩) 4 {60,113,120,142,172,202,225,232} (by decide) (by decide)
  have hall : ∀ b : Fin 1, MaskR3.blockCheck (graph ⟨1,0,1,0⟩) 4 {60,113,120,142,172,202,225,232} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1010_0
  intro m hm ho
  change m < 256 at hm
  let b : Fin 1 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1010 : totals ⟨1,0,1,0⟩ 0 = 4 ∧ totals ⟨1,0,1,0⟩ 1 = 18 ∧ totals ⟨1,0,1,0⟩ 2 = 10 := by
  unfold totals
  rw [best_1010]
  decide
theorem count_1010 : count ⟨1,0,1,0⟩ = 8 := by
  unfold count
  rw [best_1010]
  decide
theorem bound_1010 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,0,1,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1010.1, totals_1010.2.1, totals_1010.2.2, count_1010]
end EdgePattern.TreeModelsR3
