import ChecksR3_0220_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0220 : MaskR3.best (graph ⟨0,2,2,0⟩) = {966,993,996} := by
  apply MaskR3.best_of_checks (graph ⟨0,2,2,0⟩) 6 {966,993,996} (by decide) (by decide)
  have hall : ∀ b : Fin 4, MaskR3.blockCheck (graph ⟨0,2,2,0⟩) 6 {966,993,996} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0220_0
    · exact check_0220_1
    · exact check_0220_2
    · exact check_0220_3
  intro m hm ho
  change m < 1024 at hm
  let b : Fin 4 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0220 : totals ⟨0,2,2,0⟩ 0 = 2 ∧ totals ⟨0,2,2,0⟩ 1 = 4 ∧ totals ⟨0,2,2,0⟩ 2 = 12 := by
  unfold totals
  rw [best_0220]
  decide
theorem count_0220 : count ⟨0,2,2,0⟩ = 3 := by
  unfold count
  rw [best_0220]
  decide
theorem bound_0220 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,2,2,0⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0220.1, totals_0220.2.1, totals_0220.2.2, count_0220]
end EdgePattern.TreeModelsR3
