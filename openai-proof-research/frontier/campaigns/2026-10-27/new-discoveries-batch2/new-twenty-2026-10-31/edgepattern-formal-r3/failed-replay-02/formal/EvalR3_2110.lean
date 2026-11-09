import ChecksR3_2110_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2110 : MaskR3.best (graph ⟨2,1,1,0⟩) = {497,993} := by
  apply MaskR3.best_of_checks (graph ⟨2,1,1,0⟩) 6 {497,993} (by decide) (by decide)
  have hall : ∀ b : Fin 4, MaskR3.blockCheck (graph ⟨2,1,1,0⟩) 6 {497,993} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2110_0
    · exact check_2110_1
    · exact check_2110_2
    · exact check_2110_3
  intro m hm ho
  change m < 1024 at hm
  let b : Fin 4 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2110 : totals ⟨2,1,1,0⟩ 0 = 2 ∧ totals ⟨2,1,1,0⟩ 1 = 3 ∧ totals ⟨2,1,1,0⟩ 2 = 7 := by
  unfold totals
  rw [best_2110]
  decide
theorem count_2110 : count ⟨2,1,1,0⟩ = 2 := by
  unfold count
  rw [best_2110]
  decide
theorem bound_2110 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,1,1,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2110.1, totals_2110.2.1, totals_2110.2.2, count_2110]
end EdgePattern.TreeModelsR3
