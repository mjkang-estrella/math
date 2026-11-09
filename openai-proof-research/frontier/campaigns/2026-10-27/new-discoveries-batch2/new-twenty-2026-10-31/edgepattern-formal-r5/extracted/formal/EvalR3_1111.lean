import ChecksR3_1111_0
namespace EdgePattern.TreeModelsR3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem best_1111 : MaskR3.best (graph ⟨1,1,1,1⟩) = {241,481,721,782,842,902,961,962} := by
  apply MaskR3.best_of_checks (graph ⟨1,1,1,1⟩) 5 {241,481,721,782,842,902,961,962} (by decide) (by decide)
  have hall : ∀ b : Fin 4, MaskR3.blockCheck (graph ⟨1,1,1,1⟩) 5 {241,481,721,782,842,902,961,962} (b.val * 256) 256 := by
    intro b
    fin_cases b
    · exact check_1111_0
    · exact check_1111_1
    · exact check_1111_2
    · exact check_1111_3
  intro m hm ho
  change m < 1024 at hm
  let b : Fin 4 := ⟨m / 256, by omega⟩
  let i : Fin 256 := ⟨m % 256, by omega⟩
  have he : b.val * 256 + i.val = m := by dsimp [b,i]; omega
  have h := hall b i
  rw [he] at h
  exact h ho

theorem totals_1111 : totals ⟨1,1,1,1⟩ 0 = 8 ∧ totals ⟨1,1,1,1⟩ 1 = 8 ∧ totals ⟨1,1,1,1⟩ 2 = 24 := by
  unfold totals
  rw [best_1111]
  decide
theorem count_1111 : count ⟨1,1,1,1⟩ = 8 := by
  unfold count
  rw [best_1111]
  decide
theorem bound_1111 : 1 ≤ ∑ i : Fin 3, Concrete.alpha i * occupancy ⟨1,1,1,1⟩ i := by
  simp only [Fin.sum_univ_succ]
  norm_num [Concrete.alpha, occupancy, totals_1111.1, totals_1111.2.1, totals_1111.2.2, count_1111]
end EdgePattern.TreeModelsR3
