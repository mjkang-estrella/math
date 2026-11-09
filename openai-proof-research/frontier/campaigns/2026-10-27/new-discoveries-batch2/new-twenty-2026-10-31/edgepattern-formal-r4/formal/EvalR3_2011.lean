import ChecksR3_2011_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2011 : MaskR3.best (graph ⟨2,0,1,1⟩) = {970} := by
  apply MaskR3.best_of_checks (graph ⟨2,0,1,1⟩) 6 {970} (by decide) (by decide)
  have hall : ∀ b : Fin 4, MaskR3.blockCheck (graph ⟨2,0,1,1⟩) 6 {970} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2011_0
    · exact check_2011_1
    · exact check_2011_2
    · exact check_2011_3
  intro m hm ho
  change m < 1024 at hm
  let b : Fin 4 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2011 : totals ⟨2,0,1,1⟩ 0 = 1 ∧ totals ⟨2,0,1,1⟩ 1 = 1 ∧ totals ⟨2,0,1,1⟩ 2 = 4 := by
  unfold totals
  rw [best_2011]
  decide
theorem count_2011 : count ⟨2,0,1,1⟩ = 1 := by
  unfold count
  rw [best_2011]
  decide
theorem bound_2011 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,0,1,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2011.1, totals_2011.2.1, totals_2011.2.2, count_2011]
end EdgePattern.TreeModelsR3
