import ChecksR3_0202_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_0202 : MaskR3.best (graph ⟨0,2,0,2⟩) = {966,977,980} := by
  apply MaskR3.best_of_checks (graph ⟨0,2,0,2⟩) 6 {966,977,980} (by decide) (by decide)
  have hall : ∀ b : Fin 4, MaskR3.blockCheck (graph ⟨0,2,0,2⟩) 6 {966,977,980} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_0202_0
    · exact check_0202_1
    · exact check_0202_2
    · exact check_0202_3
  intro m hm ho
  change m < 1024 at hm
  let b : Fin 4 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_0202 : totals ⟨0,2,0,2⟩ 0 = 2 ∧ totals ⟨0,2,0,2⟩ 1 = 4 ∧ totals ⟨0,2,0,2⟩ 2 = 12 := by
  unfold totals
  rw [best_0202]
  decide
theorem count_0202 : count ⟨0,2,0,2⟩ = 3 := by
  unfold count
  rw [best_0202]
  decide
theorem bound_0202 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨0,2,0,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_0202.1, totals_0202.2.1, totals_0202.2.2, count_0202]
end EdgePattern.TreeModelsR3
