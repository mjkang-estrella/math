import ChecksR3_2002_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_2002 : MaskR3.best (graph ⟨2,0,0,2⟩) = {970,977,984} := by
  apply MaskR3.best_of_checks (graph ⟨2,0,0,2⟩) 6 {970,977,984} (by decide) (by decide)
  have hall : ∀ b : Fin 4, MaskR3.blockCheck (graph ⟨2,0,0,2⟩) 6 {970,977,984} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_2002_0
    · exact check_2002_1
    · exact check_2002_2
    · exact check_2002_3
  intro m hm ho
  change m < 1024 at hm
  let b : Fin 4 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_2002 : totals ⟨2,0,0,2⟩ 0 = 2 ∧ totals ⟨2,0,0,2⟩ 1 = 4 ∧ totals ⟨2,0,0,2⟩ 2 = 12 := by
  unfold totals
  rw [best_2002]
  decide
theorem count_2002 : count ⟨2,0,0,2⟩ = 3 := by
  unfold count
  rw [best_2002]
  decide
theorem bound_2002 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨2,0,0,2⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_2002.1, totals_2002.2.1, totals_2002.2.2, count_2002]
end EdgePattern.TreeModelsR3
